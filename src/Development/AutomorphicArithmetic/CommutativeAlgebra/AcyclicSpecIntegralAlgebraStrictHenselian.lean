module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyFunctorialityAxiomsHold

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyclicSpecFiniteAlgebraStrictHenselian
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedCohomologySpecProdBijectiveProd
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.SectionRestriction

variable {R : Type} [CommRing R]

private theorem pl_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem pl_id {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem pl_zero {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem pl_add {K L : Cx R} (f g : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (f + g) F n x = HK.pull R f F n x + HK.pull R g F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [HK.pull, HK.pull, HK.pull, HK.pre, HK.pre, HK.pre, cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

private theorem split_bij {K₁ K₂ L : Cx R} (c₁ : K₁ ⟶ L) (c₂ : K₂ ⟶ L) (hd : IsIso (biprod.desc c₁ c₂))
    (F : Shv R) (n : ℤ) :
    Function.Bijective fun x : HK R L F n => (HK.pull R c₁ F n x, HK.pull R c₂ F n x) := by
  set d := biprod.desc c₁ c₂ with hdd
  let r₁ : L ⟶ K₁ := inv d ≫ biprod.fst
  let r₂ : L ⟶ K₂ := inv d ≫ biprod.snd
  have e₁ : c₁ = biprod.inl ≫ d := by simp [hdd]
  have e₂ : c₂ = biprod.inr ≫ d := by simp [hdd]
  have h11 : c₁ ≫ r₁ = 𝟙 _ := by simp [r₁, e₁]
  have h12 : c₁ ≫ r₂ = 0 := by simp [r₂, e₁]
  have h21 : c₂ ≫ r₁ = 0 := by simp [r₁, e₂]
  have h22 : c₂ ≫ r₂ = 𝟙 _ := by simp [r₂, e₂]
  have hs : r₁ ≫ c₁ + r₂ ≫ c₂ = 𝟙 _ := by
    have : d = biprod.fst ≫ c₁ + biprod.snd ≫ c₂ := biprod.desc_eq
    calc r₁ ≫ c₁ + r₂ ≫ c₂ = inv d ≫ (biprod.fst ≫ c₁ + biprod.snd ≫ c₂) := by
          simp [r₁, r₂, Preadditive.comp_add]
      _ = 𝟙 _ := by rw [← this]; simp
  have hx : ∀ x : HK R L F n, x = HK.pull R r₁ F n (HK.pull R c₁ F n x) + HK.pull R r₂ F n (HK.pull R c₂ F n x) := by
    intro x
    rw [← pl_comp, ← pl_comp, ← pl_add, hs, pl_id]
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [hx x, hx y, h1, h2]
  · rintro ⟨a, b⟩
    refine ⟨HK.pull R r₁ F n a + HK.pull R r₂ F n b, Prod.ext ?_ ?_⟩
    · simp only [map_add (f := _)]
      rw [← pl_comp, ← pl_comp, h11, h12, pl_id, pl_zero, add_zero]
    · simp only [map_add (f := _)]
      rw [← pl_comp, ← pl_comp, h21, h22, pl_id, pl_zero, zero_add]

private theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality g.op).symm x

private theorem sec_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

private theorem sec_bij (F : Shv R) (A B : Type) [CommRing A] [CommRing B] :
    Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) =>
      ((Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s : Sec F (Spec (CommRingCat.of A))),
       (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s : Sec F (Spec (CommRingCat.of B)))) := by
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose _ (forget _)).obj F).property)
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (A × B)) := Spec.map (CommRingCat.ofHom (RingHom.fst A B))
  let b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (A × B)) := Spec.map (CommRingCat.ofHom (RingHom.snd A B))
  have ea : coprod.inl ≫ coprodSpec A B = a := coprodSpec_inl A B
  have eb : coprod.inr ≫ coprodSpec A B = b := coprodSpec_inr A B
  have hop : IsLimit (BinaryFan.mk a.op b.op) := by
    refine BinaryFan.IsLimit.mk _ (fun f g => (inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop).op) ?_ ?_ ?_
    · intro T f g
      apply Quiver.Hom.unop_inj
      change a ≫ inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop = f.unop
      rw [← ea, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inl_desc]
    · intro T f g
      apply Quiver.Hom.unop_inj
      change b ≫ inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop = g.unop
      rw [← eb, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inr_desc]
    · intro T f g m h₁ h₂
      apply Quiver.Hom.unop_inj
      have h₁' : a ≫ m.unop = f.unop := congrArg Quiver.Hom.unop h₁
      have h₂' : b ≫ m.unop = g.unop := congrArg Quiver.Hom.unop h₂
      rw [Quiver.Hom.unop_op, IsIso.eq_inv_comp]
      apply coprod.hom_ext
      · rw [coprod.inl_desc, reassoc_of% ea]
        exact h₁'
      · rw [coprod.inr_desc, reassoc_of% eb]
        exact h₂'
  have hl := (isLimitMapConeBinaryFanEquiv G a.op b.op) (isLimitOfPreserves G hop)
  let e := hl.conePointUniqueUpToIso (Types.binaryProductLimit _ _)
  have he := (isIso_iff_bijective e.hom).1 inferInstance
  exact he

private theorem free_iso {X Y Z : Scheme.{0}} (a : Y ⟶ X) (b : Z ⟶ X)
    (hb : ∀ F : Shv R, Function.Bijective fun s : Sec F X => ((Sec.res a s : Sec F Y), (Sec.res b s : Sec F Z))) :
    IsIso (biprod.desc ((free R).map (yoneda.map a)) ((free R).map (yoneda.map b))) := by
  let P₁ : PSh := yoneda.obj Y
  let P₂ : PSh := yoneda.obj Z
  let Q : PSh := yoneda.obj X
  let a' : (free R).obj P₁ ⟶ (free R).obj Q := (free R).map (yoneda.map a)
  let b' : (free R).obj P₂ ⟶ (free R).obj Q := (free R).map (yoneda.map b)
  let T : Shv R := (free R).obj P₁ ⊞ (free R).obj P₂
  let g₁ : Sec ((free R).obj P₁) Y := freeGen R P₁ _ (𝟙 _)
  let g₂ : Sec ((free R).obj P₂) Z := freeGen R P₂ _ (𝟙 _)
  let gQ : Sec ((free R).obj Q) X := freeGen R Q _ (𝟙 _)
  obtain ⟨s, hs⟩ := (hb T).2 (Sec.map biprod.inl g₁, Sec.map biprod.inr g₂)
  have hs₁ : Sec.res a s = Sec.map biprod.inl g₁ := congrArg Prod.fst hs
  have hs₂ : Sec.res b s = Sec.map biprod.inr g₂ := congrArg Prod.snd hs
  obtain ⟨hex, hext, hres, hmap⟩ := free_hom_sections R Q T
  obtain ⟨φ, hφ⟩ := hex (fun U x => Sec.res x s) (fun V U g x => (res_comp g x s).symm)
  have gen₁ : ∀ (U : Scheme.{0}) (x : U ⟶ Y), freeGen R P₁ U x = Sec.res x g₁ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R P₁ T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have gen₂ : ∀ (U : Scheme.{0}) (x : U ⟶ Z), freeGen R P₂ U x = Sec.res x g₂ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R P₂ T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have genQ : ∀ (U : Scheme.{0}) (x : U ⟶ X), freeGen R Q U x = Sec.res x gQ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R Q T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have ma : ∀ (U : Scheme.{0}) (x : U ⟶ Y), Sec.map a' (freeGen R P₁ U x) = freeGen R Q U (x ≫ a) :=
    fun U x => (free_hom_sections R P₁ T).2.2.2 Q (yoneda.map a) U x
  have mb : ∀ (U : Scheme.{0}) (x : U ⟶ Z), Sec.map b' (freeGen R P₂ U x) = freeGen R Q U (x ≫ b) :=
    fun U x => (free_hom_sections R P₂ T).2.2.2 Q (yoneda.map b) U x
  have hdφ₁ : a' ≫ φ = biprod.inl := by
    refine (free_hom_sections R P₁ T).2.1 _ _ fun U x => ?_
    rw [sec_comp, ma, hφ, res_comp, hs₁, sec_nat, ← gen₁]
  have hdφ₂ : b' ≫ φ = biprod.inr := by
    refine (free_hom_sections R P₂ T).2.1 _ _ fun U x => ?_
    rw [sec_comp, mb, hφ, res_comp, hs₂, sec_nat, ← gen₂]
  have hsQ : Sec.map (biprod.desc a' b') s = gQ := by
    refine (hb ((free R).obj Q)).1 (Prod.ext ?_ ?_)
    · change Sec.res a (Sec.map (biprod.desc a' b') s) = Sec.res a gQ
      rw [sec_nat, hs₁, ← sec_comp, biprod.inl_desc, ← genQ, ma]
      rfl
    · change Sec.res b (Sec.map (biprod.desc a' b') s) = Sec.res b gQ
      rw [sec_nat, hs₂, ← sec_comp, biprod.inr_desc, ← genQ, mb]
      rfl
  refine ⟨φ, ?_, ?_⟩
  · apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      exact hdφ₁
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      exact hdφ₂
  · refine (free_hom_sections R Q ((free R).obj Q)).2.1 _ _ fun U x => ?_
    change Sec.map (biprod.desc a' b') (Sec.map φ (freeGen R Q U x)) = freeGen R Q U x
    rw [hφ, ← sec_nat, hsQ, genQ]

end UpperTheory.SectionRestriction

theorem UpperTheory.twistedCohomology_specProd_bijective_prod :
    ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ), Function.Bijective fun x : Ht q (sp (A × B)) n i => (pull _ (spMap (RingHom.fst A B)) (tw q i) n x, pull _ (spMap (RingHom.snd A B)) (tw q i) n x) := by
  intro q A B _ _ n i
  have h2 := GlobalTheory.EtC.chains_disc_biprod_isIso (ZMod q) _ _ (UpperTheory.SectionRestriction.free_iso _ _ fun F => UpperTheory.SectionRestriction.sec_bij F A B)
  exact UpperTheory.SectionRestriction.split_bij ((chains (ZMod q)).map (spMap (RingHom.fst A B)))
    ((chains (ZMod q)).map (spMap (RingHom.snd A B))) h2 (tw q i) n
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.AcycFin

private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  exact Algebra.IsAlgebraic.isSepClosed (F := K)

private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨_, hk⟩ := hO
  haveI : IsLocalHom (algebraMap O T) :=
    ((IsLocalRing.local_hom_tfae (algebraMap O T)).out 1 5).mpr
      (GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T))
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := inferInstance
  exact ⟨hT, sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)⟩

private theorem acyc_of_equiv {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : Acyc q (sp A)) : Acyc q (sp B) := by
  intro n i hn
  haveI := h n i hn
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    have h0 : CommRingCat.ofHom (e.symm : B →+* A) ≫ CommRingCat.ofHom (e : A →+* B) = 𝟙 _ := by
      ext x
      simp
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, h0, Spec.map_id]
    exact sch.map_id _
  have key : Function.LeftInverse (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n) := fun x => by
    rw [← pull_comp, hid, pull_id]
  exact key.injective.subsingleton

private theorem acyc_prod {q : ℕ} {A B : Type} [CommRing A] [CommRing B]
    (hA : Acyc q (sp A)) (hB : Acyc q (sp B)) : Acyc q (sp (A × B)) := by
  intro n i hn
  haveI := hA n i hn
  haveI := hB n i hn
  exact ⟨fun x y => (UpperTheory.twistedCohomology_specProd_bijective_prod q A B n i).1
    (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

private theorem acyc_of_subsingleton {q : ℕ} {A : Type} [CommRing A] [Subsingleton A] :
    Acyc q (sp A) := by
  intro n i hn
  have hfs : RingHom.fst A A = RingHom.snd A A := by
    ext x
    exact Subsingleton.elim _ _
  obtain ⟨_, hsurj⟩ := UpperTheory.twistedCohomology_specProd_bijective_prod q A A n i
  refine ⟨fun u v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj (u, v)
  rw [hfs] at hx
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2]

private theorem acyc_pi (q : ℕ) (ι : Type) [Finite ι] :
    ∀ (T : ι → Type) [∀ i, CommRing (T i)], (∀ i, Acyc q (sp (T i))) →
      Acyc q (sp (Π i, T i)) := by
  refine Finite.induction_empty_option (P := fun α => ∀ (T : α → Type) [∀ i, CommRing (T i)],
      (∀ i, Acyc q (sp (T i))) → Acyc q (sp (Π i, T i))) ?_ ?_ ?_ ι
  · intro α β e ih T _ hT
    exact acyc_of_equiv (RingEquiv.piCongrLeft T e) (ih (fun a => T (e a)) (fun a => hT (e a)))
  · intro T _ _
    exact acyc_of_subsingleton
  · intro α _ ih T _ hT
    exact acyc_of_equiv RingEquiv.piOptionEquivProd.symm
      (acyc_prod (hT none) (ih (fun a => T (some a)) (fun a => hT (some a))))

end UpperTheory.Cb.AcycFin


open UpperTheory.Cb.AcycFin in
theorem UpperTheory.acyclic_spec_finite_algebra_strictHenselian :
    ∀ (q : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A], SH O → IsUnit (q : O) → Acyc q (sp A) := by
  intro q O A _ _ _ _ hO _
  obtain ⟨hH, hk⟩ := hO
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  refine acyc_of_equiv e.symm.toRingEquiv (acyc_pi q ι T fun j => ?_)
  obtain ⟨h1, h2⟩ := hT j
  haveI := h2
  have hs : SH (T j) := sh_of_finite O (T j) ⟨hH, hk⟩ h1
  intro n i hn
  exact UpperTheory.etaleCohomology_functorialityAxioms_hold (ZMod q) (T j) hs (tw q i) n hn
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TwistCohomologyCommutesWithFilteredColimits
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.twistCohomology_commutes_with_filtered_colimits :
    GlobalTheory.EtC.B1 := by
  intro q J _ _ D c hc n i
  have hF : GlobalTheory.EtC.Finitary (tw q i) := GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary (ZMod q) (tw q i) hF J D c hc n
  exact ⟨fun x _ => h1 x, fun j y _ hy => h2 j y hy⟩
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.IntegralColim

variable (O R : Type) [CommRing O] [CommRing R] [Algebra O R]

private abbrev FJ : Type := {S : Subalgebra O R // Module.Finite O S}

private noncomputable def FD : FJ O R ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of S.1
  map {S T} f := CommRingCat.ofHom (Subalgebra.inclusion (show S.1 ≤ T.1 from leOfHom f)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private noncomputable def FC : Cocone (FD O R) where
  pt := CommRingCat.of R
  ι :=
    { app := fun S => CommRingCat.ofHom S.1.val.toRingHom
      naturality := fun _ _ _ => by ext; rfl }

variable {O R}

private theorem finite_sup (S T : FJ O R) : Module.Finite O ↥(S.1 ⊔ T.1) := by
  haveI := S.2
  haveI := T.2
  exact Subalgebra.finite_sup S.1 T.1

private instance : IsDirected (FJ O R) (· ≤ ·) :=
  ⟨fun S T => ⟨⟨S.1 ⊔ T.1, finite_sup S T⟩, le_sup_left (a := S.1), le_sup_right (a := S.1)⟩⟩

variable [Algebra.IsIntegral O R]

private theorem finite_adjoin (x : R) : Module.Finite O ↥(Algebra.adjoin O ({x} : Set R)) :=
  Module.Finite.iff_fg.mpr (IsIntegral.fg_adjoin_singleton (Algebra.IsIntegral.isIntegral x))

private noncomputable def gen (x : R) : FJ O R := ⟨Algebra.adjoin O {x}, finite_adjoin x⟩

private theorem mem_gen (x : R) : x ∈ (gen (O := O) x).1 := Algebra.subset_adjoin rfl

private instance : Nonempty (FJ O R) := ⟨gen 0⟩

private instance : IsFiltered (FJ O R) := inferInstance

private noncomputable def descFun (s : Cocone (FD O R)) (x : R) : s.pt :=
  (s.ι.app (gen x)).hom (⟨x, mem_gen x⟩ : (gen (O := O) x).1)

private theorem descFun_eq (s : Cocone (FD O R)) (S : FJ O R) (x : R) (hx : x ∈ S.1) :
    (s.ι.app S).hom (⟨x, hx⟩ : S.1) = descFun s x := by
  let U : FJ O R := ⟨S.1 ⊔ (gen x).1, finite_sup S (gen x)⟩
  have hS : S ≤ U := le_sup_left (a := S.1)
  have hG : gen x ≤ U := le_sup_right (a := S.1)
  unfold descFun
  rw [← s.w (homOfLE hS), ← s.w (homOfLE hG)]
  rfl

end UpperTheory.IntegralColim

namespace UpperTheory.IntegralColim
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Algebra.IsIntegral O R]

private theorem two (x y : R) : ∃ S : FJ O R, x ∈ S.1 ∧ y ∈ S.1 :=
  ⟨⟨(gen (O := O) x).1 ⊔ (gen (O := O) y).1, finite_sup _ _⟩,
    (le_sup_left : (gen (O := O) x).1 ≤ _) (mem_gen x),
    (le_sup_right : (gen (O := O) y).1 ≤ _) (mem_gen y)⟩

private noncomputable def descHom (s : Cocone (FD O R)) : R →+* s.pt where
  toFun := descFun s
  map_one' := by
    have h := descFun_eq s (gen 1) 1 (one_mem _)
    rw [← h]
    exact map_one (s.ι.app (gen (O := O) (1 : R))).hom
  map_zero' := by
    have h := descFun_eq s (gen 0) 0 (zero_mem _)
    rw [← h]
    exact map_zero (s.ι.app (gen (O := O) (0 : R))).hom
  map_mul' x y := by
    obtain ⟨S, hx, hy⟩ := two (O := O) x y
    rw [← descFun_eq s S x hx, ← descFun_eq s S y hy, ← descFun_eq s S (x * y) (mul_mem hx hy)]
    exact map_mul (s.ι.app S).hom (⟨x, hx⟩ : S.1) (⟨y, hy⟩ : S.1)
  map_add' x y := by
    obtain ⟨S, hx, hy⟩ := two (O := O) x y
    rw [← descFun_eq s S x hx, ← descFun_eq s S y hy, ← descFun_eq s S (x + y) (add_mem hx hy)]
    exact map_add (s.ι.app S).hom (⟨x, hx⟩ : S.1) (⟨y, hy⟩ : S.1)

private noncomputable def isColim : IsColimit (FC O R) where
  desc s := CommRingCat.ofHom (descHom s)
  fac s S := by
    ext ⟨x, hx⟩
    exact (descFun_eq s S x hx).symm
  uniq s m hm := by
    refine CommRingCat.hom_ext (RingHom.ext fun (x : R) => ?_)
    have h := congrArg (fun f => f.hom (⟨x, mem_gen x⟩ : (gen (O := O) x).1)) (hm (gen x))
    exact h

end UpperTheory.IntegralColim

theorem UpperTheory.acyclic_spec_integral_algebra_strictHenselian :
    ∀ (q : ℕ) (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [Algebra.IsIntegral O R], SH O → IsUnit (q : O) → Acyc q (sp R) := by
  intro q O R _ _ _ _ hO hq n i hn
  have hqR : IsUnit (q : R) := by
    simpa using hq.map (algebraMap O R)
  have hz : ∀ x : Ht q (sp R) n i, x = 0 := by
    intro x
    obtain ⟨j, y, hy⟩ := (UpperTheory.twistCohomology_commutes_with_filtered_colimits q (UpperTheory.IntegralColim.FD O R) (UpperTheory.IntegralColim.FC O R)
      UpperTheory.IntegralColim.isColim n i).1 x hqR
    haveI := j.2
    have hA : Acyc q (sp j.1) := UpperTheory.acyclic_spec_finite_algebra_strictHenselian q O j.1 hO hq
    haveI := hA n i hn
    have hy0 : y = 0 := Subsingleton.elim (α := Ht q (sp j.1) n i) y 0
    rw [← hy, hy0]
    exact map_zero _
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  intro R _ F
  have hc : ∀ {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n : ℤ),
      ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := by
    intro E E' E'' f g n
    funext x
    exact pull_comp R f g F n x
  have hid : ∀ (E : Spc) (n : ℤ), ⇑(pull R (𝟙 E) F n) = id := by
    intro E n
    funext x
    exact pull_id R E F n x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f hf n
    haveI := hf
    have h1 : Function.LeftInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc (inv f) f n) x
      rw [IsIso.inv_hom_id, hid] at this
      exact this.symm
    have h2 : Function.RightInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc f (inv f) n) x
      rw [IsIso.hom_inv_id, hid] at this
      exact this.symm
    exact ⟨h1.injective, h2.surjective⟩
  · intro E E' E'' f g
    refine ⟨?_, ?_, ?_⟩
    · intro hf hg n
      rw [hc]
      exact (hf n).comp (hg n)
    · intro hf hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff' (hf n) _).mp this
    · intro hg hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff _ (hg n)).mp this
  · intro E E' f hq n
    exact GlobalTheory.T.quasiIso_hypercohomology_bijective R ((chains R).map f) F n
  · intro E E' f hf
    constructor
    · intro h n hn
      haveI := h n hn
      exact (hf n).1.subsingleton
    · intro h n hn
      haveI := h n hn
      exact (Equiv.ofBijective _ (hf n)).symm.subsingleton

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  first | (exact @GlobalTheory.EtC.eqv_basic) | (exact GlobalTheory.EtC.eqv_basic) | (intros; apply GlobalTheory.EtC.eqv_basic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpec
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
open ClsSpec

theorem one_eq_of_ev (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0)
    (hα : ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) :
    CohomologyClass.mk α = one q E := by
  obtain ⟨β, hβ, hβv⟩ := one_spec q E hE
  rw [← hβ]
  congr 1
  refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using h.symm
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hE U ⟨x⟩)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1, hα _ _ ζ, hβv _ _ ζ]
  | succ p =>
    have hs : s < 0 := by omega
    haveI := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs
    exact Subsingleton.elim _ _

theorem pull_one (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') :
    pull _ f _ _ (one q E') = one q E := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨β, hβ, hβv⟩ := one_spec q E' hE'
  rw [← hβ]
  refine one_eq_of_ev q E hE _ fun U x ζ => ?_
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f β.1 0 0 _ U x).trans (hβv U (x.map f) ζ)

theorem rootClass_eq_secClass {q : ℕ} (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    rootClass i ζ = secClass (tw q i) (twGen i ζ) := by
  unfold rootClass secClass
  congr 1
  funext c
  apply propext
  constructor
  · rintro ⟨α, hα, h⟩
    exact ⟨α, hα, (h X (𝟙 X)).trans (ClsSpec.res_id _)⟩
  · rintro ⟨α, hα, h⟩
    refine ⟨α, hα, fun U x => ?_⟩
    have e := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1 0 0 (by simp) U X x (𝟙 X)
    rw [h] at e
    refine e.symm.trans ?_
    congr 1

theorem one_root_spec : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = one q E ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ∧ (∀ E : Spc, Inv q E → ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) → CohomologyClass.mk α = one q E) ∧ (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧ ∀ (i : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), rootClass i ζ = secClass (tw q i) (twGen i ζ) :=
  fun q _ => ⟨fun E hE => one_spec q E hE, fun E hE α hα => one_eq_of_ev q E hE α hα,
    fun f hE' => pull_one q f hE', fun i _ ζ => rootClass_eq_secClass i ζ⟩

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistUnitClass_rootClass_spec : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = one q E ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ∧ (∀ E : Spc, Inv q E → ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) → CohomologyClass.mk α = one q E) ∧ (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧ ∀ (i : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), rootClass i ζ = secClass (tw q i) (twGen i ζ) := by
  first | (exact @GlobalTheory.EtC.one_root_spec) | (exact GlobalTheory.EtC.one_root_spec) | (intros; apply GlobalTheory.EtC.one_root_spec  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem secMap_secRes_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem secRes_secRes {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  change (F.obj.map k.op).hom ((F.obj.map g.op).hom x) = (F.obj.map (k ≫ g).op).hom x
  rw [op_comp, Functor.map_comp, ModuleCat.comp_apply]

theorem classes_die_on_etale_cover : A5 := by
  intro R _ X F n hn x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have hsch := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (n - 1) n (n + 1) (by omega) rfl
  have hres := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X
  set z := ev α.1 0 n (by simp) X (𝟙 X) with hz
  have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := (hsch.2 α).1
  have hloc := hres.2.2.1 (n - 1) n (n + 1) hn (by omega) z rfl hdz
  rw [loc_iff_etale_affine_points] at hloc
  swap
  · rintro V W g k ⟨y, hy⟩
    refine ⟨Sec.res k y, ?_⟩
    rw [secMap_secRes_comm, hy, secRes_secRes]
  choose V g _ hg hmem y hy using hloc
  let f : (∐ V) ⟶ X := Sigma.desc g
  have hιf : ∀ i, Sigma.ι V i ≫ f = g i := fun i => Sigma.ι_desc g i
  refine ⟨∐ V, f, ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hg
  · refine ⟨fun p => ?_⟩
    obtain ⟨q, hq⟩ := hmem p
    refine ⟨Sigma.ι V p q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hιf, hq]
  · obtain ⟨a, ha⟩ := (sec_sigma_bijective R ((res R F).X (n - 1)) V).2 y
    have hda : Sec.map ((res R F).d (n - 1) n) a = Sec.res f z := by
      apply (sec_sigma_bijective R ((res R F).X n) V).1
      funext i
      have hai : Sec.res (Sigma.ι V i) a = y i := congrFun ha i
      change Sec.res (Sigma.ι V i) (Sec.map _ a) = Sec.res (Sigma.ι V i) (Sec.res f z)
      rw [← secMap_secRes_comm, hai, hy, secRes_secRes, hιf]
    have hY := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (∐ V) (res R F) (n - 1) n (n + 1) (by omega) rfl
    have hev := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := n)
    let α' : Cocycle ((chains R).obj (sch.obj (∐ V))) (res R F) n :=
      zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)
    change CohomologyClass.mk α' = 0
    rw [(hY.2 α').2]
    refine ⟨a, ?_⟩
    rw [hda]
    have h1 := (hev.2.2.2.1 (sch.map f) α.1 0 n (by simp) (∐ V) (𝟙 (∐ V)))
    have h2 := (hev.2.1 α.1 0 n (by simp) (∐ V) X f (𝟙 X))
    change _ = ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ (∐ V) (𝟙 (∐ V))
    rw [h1, hz, h2]
    rfl

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover : GlobalTheory.EtC.A5 := by
  first | exact @GlobalTheory.EtC.classes_die_on_etale_cover | exact GlobalTheory.EtC.classes_die_on_etale_cover | (intros; apply GlobalTheory.EtC.classes_die_on_etale_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SectionClass

variable (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})

theorem exists_cocycle (s : Sec F X) :
    ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0, ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  have hz : Sec.map ((res R F).d 0 1) (Sec.map (resι R F) s) = 0 :=
    ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).2 ⟨s, rfl⟩
  obtain ⟨α, h0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).1 _ hz
  refine ⟨α, (h0 X (𝟙 X)).trans ?_⟩
  simp [Sec.res]

theorem mk_eq_iff (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    CohomologyClass.mk α = CohomologyClass.mk β ↔
      ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) := by
  have h2 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 (α - β)).2
  have hsub : ev (α - β).1 0 0 (by simp) X (𝟙 X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).2.1
    simpa using this
  have hss : Subsingleton (Sec ((res R F).X (-1)) X) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.2.2 (-1) (by norm_num)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, h2, hsub]
  have hz : Sec.map ((res R F).d (-1) 0) (0 : Sec ((res R F).X (-1)) X) = 0 := map_zero _
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (0 : Sec ((res R F).X 0) X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
      rw [← hz, ← Subsingleton.elim y 0]; exact hy
    exact (sub_eq_zero.1 hy'.symm)
  · intro h
    refine ⟨0, ?_⟩
    rw [hz, h, sub_self]

theorem secClass_spec (s : Sec F X) : ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = secClass F s ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  obtain ⟨α, h⟩ := exists_cocycle R F X s
  exact pick_spec (P := fun c => ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = c ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s) ⟨_, α, rfl, h⟩

theorem spec_iff (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s := by
  obtain ⟨α₀, h1, h2⟩ := secClass_spec R F X s
  rw [← h1, mk_eq_iff, h2]

end GlobalTheory.EtC.SectionClass


open GlobalTheory.EtC.SectionClass in
theorem GlobalTheory.EtC.secClass_props : ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), (∀ (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0), ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s) ∧ Function.Bijective (secClass F (X := X)) ∧ (∀ s t : Sec F X, secClass F (s + t) = secClass F s + secClass F t) ∧ (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (secClass F s) = secClass F (Sec.res f s)) ∧ ∀ {G : Shv R} (φ : F ⟶ G) (s : Sec F X), HK.post R _ φ 0 (secClass F s) = secClass G (Sec.map φ s) := by
  intro R _ F X
  refine ⟨spec_iff R F X, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s t hst
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    have h3 := (spec_iff R F X t α).2 (h1.trans hst)
    exact (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.1 (h2.symm.trans h3)
  · intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective
    have hd := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
    obtain ⟨a, ha⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).1 hd
    exact ⟨a, ((spec_iff R F X a α).1 ha.symm).symm⟩
  · intro s t
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    obtain ⟨β, h3, h4⟩ := secClass_spec R F X t
    rw [← h1, ← h3, ← CohomologyClass.mk_add]
    symm
    refine (spec_iff R F X (s + t) (α + β)).1 ?_
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).1
    simp only [Cocycle.coe_add] at this ⊢
    rw [this, h2, h4]
    exact (map_add ((resι R F).hom.app (op X)).hom s t).symm
  · intro Y f s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R F Y _ _).1 ?_
    have e4 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.1 (sch.map f) α.1 0 0 (by simp) Y (𝟙 Y)
    have e2 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.1 α.1 0 0 (by simp) Y X f (𝟙 X)
    have hx1 : Sx.map (p := 0) (sch.map f) (𝟙 Y : Sx (sch.obj Y) 0 Y) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.map, sch]
      exact Category.id_comp f
    have hx2 : Sx.res f (𝟙 X : Sx (sch.obj X) 0 X) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.res, sch]
      exact Category.comp_id f
    change ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add 0)) 0 0 _ Y (𝟙 Y) = _
    rw [e4, hx1, ← hx2, ← e2, h2]
    exact (NatTrans.naturality_apply (resι R F).hom f.op s).symm
  · intro G φ s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R G X _ _).1 ?_
    have e5 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.2 (resMap R φ) α.1 0 0 (by simp) X (𝟙 X)
    have hc := ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.2 G φ).2
    change ev (α.1.comp (Cochain.ofHom (resMap R φ)) (add_zero 0)) 0 0 _ X (𝟙 X) = _
    rw [e5, h2]
    change ((resι R F ≫ (resMap R φ).f 0).hom.app (op X)).hom s = _
    rw [hc]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeZeroSectionClass_properties : ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), (∀ (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0), ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s) ∧ Function.Bijective (secClass F (X := X)) ∧ (∀ s t : Sec F X, secClass F (s + t) = secClass F s + secClass F t) ∧ (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (secClass F s) = secClass F (Sec.res f s)) ∧ ∀ {G : Shv R} (φ : F ⟶ G) (s : Sec F X), HK.post R _ φ 0 (secClass F s) = secClass G (Sec.map φ s) := by
  first | exact @GlobalTheory.EtC.secClass_props | exact GlobalTheory.EtC.secClass_props | (intros; apply GlobalTheory.EtC.secClass_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditive
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace KumNat
open ClsSpec

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) {s : ℤ} (hs : s < 0) :
    Subsingleton (Sec ((res R F).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) (p s h U x) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 α β p s h U x).2.1

variable {q : ℕ}

theorem kum_unique [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ γ' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h₁' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ' 1 0 (by simp) U x = 0)
    (h₂' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ' 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    change U ⟶ X at x
    refine sep (ClsSpec.loc_mono (root_loc (unit_res x hX) (umap x u)) fun V g ⟨v, hv⟩ => ?_)
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 0 1 _ V U g x]
    have hv' : v ^ q = umap (g ≫ x) u := by rw [hv, umap_comp]
    exact (h₂ V (g ≫ x) v hv').trans (h₂' V (g ≫ x) v hv').symm
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact (h₁ U x).trans (h₁' U x).symm
  | p + 2 =>
    haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
    exact Subsingleton.elim _ _

theorem eq_zero_of_kumT [NeZero q] (ht : kumT q = 0) {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = 0 :=
  kum_unique hX u h₁ h₂ (fun U x => ev_zero (E := sch.obj X) _ _ _ _ _)
    (fun U x v _ => (ev_zero (E := sch.obj X) _ _ _ _ _).trans (by rw [ht]; exact (smap_zero _).symm))

theorem kum_pull [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ) (hX : IsUnit (q : Γ(X, ⊤))) :
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u) := by
  obtain ⟨γ, hγ, h₁, h₂⟩ := kum_spec q hX u
  obtain ⟨γ', hγ', h₁', h₂'⟩ := kum_spec q (unit_res f hX) (umap f u)
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine Cocycle.ext (kum_unique (unit_res f hX) (umap f u) (fun U y => ?_) (fun U y v hv => ?_) h₁' h₂')
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 1 0 _ U y = 0
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 _ U y]
    exact h₁ U (y ≫ f)
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 0 1 _ U y = _
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 _ U y]
    exact h₂ U (y ≫ f) v (by rw [hv, umap_comp])

theorem kum_mul [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u₁ u₂ : (Γ(X, ⊤))ˣ) :
    kum q (u₁ * u₂) = kum q u₁ + kum q u₂ := by
  obtain ⟨γ₁, e₁, a₁, b₁⟩ := kum_spec q hX u₁
  obtain ⟨γ₂, e₂, a₂, b₂⟩ := kum_spec q hX u₂
  obtain ⟨γ₃, e₃, a₃, b₃⟩ := kum_spec q hX (u₁ * u₂)
  rw [← e₁, ← e₂, ← e₃, eq_comm, ← CohomologyClass.mk_add, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨e, he, hw⟩ := exists_two_family ht (E := sch.obj X) (p := 0) (fun U (x : U ⟶ X) => unit_res x hX)
      (fun U (x : U ⟶ X) => umap x u₁) (fun U (x : U ⟶ X) => umap x u₂)
      (fun V U g (x : U ⟶ X) => umap_comp g x u₁) (fun V U g (x : U ⟶ X) => umap_comp g x u₂)
    obtain ⟨β, c₁, c₂⟩ := exists_single (I := res _ (tw q 1)) (n := 0) 0 0 (by simp) e he
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    rw [Cocycle.coe_sub, Cocycle.coe_add, ev_sub', ev_add]
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      have hxU := unit_res (show U ⟶ X from x) hX
      refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hxU (umap (show U ⟶ X from x) u₁))
        (root_loc hxU (umap (show U ⟶ X from x) u₂))) ?_)
      rintro V g ⟨⟨v, hv⟩, w, hw'⟩
      have hv' : v ^ q = umap (show V ⟶ X from x.res g) u₁ := by rw [hv]; exact (umap_comp g _ u₁).symm
      have hw'' : w ^ q = umap (show V ⟶ X from x.res g) u₂ := by rw [hw']; exact (umap_comp g _ u₂).symm
      have hvw : (v * w) ^ q = umap (show V ⟶ X from x.res g) (u₁ * u₂) := by rw [mul_pow, hv', hw'', map_mul]
      rw [res_map, he V U g x, res_sub, res_add, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₁.1 0 1 _ V U g x,
        (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₂.1 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₃.1 0 1 _ V U g x]
      rw [hw V (x.res g) v w hv' hw'', b₁ V (x.res g) v hv', b₂ V (x.res g) w hw'', b₃ V (x.res g) _ hvw, smap_sub,
        smap_add]
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a₁ U x, a₂ U x, a₃ U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · refine ⟨0, ?_⟩
    rw [δ_zero, Cocycle.coe_sub, Cocycle.coe_add, eq_zero_of_kumT ht hX u₁ a₁ b₁, eq_zero_of_kumT ht hX u₂ a₂ b₂,
      eq_zero_of_kumT ht hX _ a₃ b₃]
    simp

theorem kum_pow_self [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) : kum q (u ^ q) = 0 := by
  obtain ⟨γ, e, a, b⟩ := kum_spec q hX (u ^ q)
  rw [← e, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨β, c₁, c₂⟩ := exists_single (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) 0 0 (by simp)
      (fun U (x : U ⟶ X) => kumT q U (umap x u))
      (fun V U g (x : U ⟶ X) => (ht.1 V U g _ (unit_res x hX)).trans (congrArg (kumT q V) (umap_comp g x u).symm))
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      change U ⟶ X at x
      exact (b U x _ (by rw [← map_pow])).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · exact ⟨0, by rw [δ_zero, eq_zero_of_kumT ht hX _ a b]⟩

end KumNat


open KumNat in
theorem kum_cocycle_natural_additive : ∀ (q : ℕ) [NeZero q], (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧ ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u → ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧ ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 := by
  intro q _
  exact ⟨fun X u hX => kum_spec q hX u, fun f u hX => kum_pull f u hX, fun u v hX => ⟨kum_mul hX u v, kum_pow_self hX u⟩⟩

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive : ∀ (q : ℕ) [NeZero q], (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), GlobalTheory.EtC.ev (R := ZMod q) γ.1 1 0 (by simp) U x = 0) ∧ ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u → GlobalTheory.EtC.ev (R := ZMod q) γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧ ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 := by
  first | (exact @GlobalTheory.EtC.kum_cocycle_natural_additive) | (exact GlobalTheory.EtC.kum_cocycle_natural_additive) | (intros; apply GlobalTheory.EtC.kum_cocycle_natural_additive  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverRingLocalizationChart
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cover_ring_localization_chart : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (∀ J, I ⊆ J → rB k K x I ≤ rB k K x J) ∧ ∀ y : K, y ∈ rB k K x I ↔ ∃ N : ℕ, y * algebraMap F K (∏ j ∈ I, x j / x i) ^ N ∈ rB k K x {i} := by
  first | (exact @GlobalTheory.PD.rB_mono_loc) | (exact GlobalTheory.PD.rB_mono_loc) | (intros; apply GlobalTheory.PD.rB_mono_loc <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequence
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CoefSeq

variable {R : Type} [CommRing R]

end GlobalTheory.EtC.CoefSeq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_comp_injective {A B C C' : Type*} [Zero C] [Zero C'] {f : A → B} {g : B → C}
    {β : C → C'} (hfg : Function.Exact f g) (hβ : Function.Injective β) (h0 : β 0 = 0) :
    Function.Exact f (β ∘ g) := by
  intro y
  rw [← hfg y, Function.comp_apply, ← h0]
  exact hβ.eq_iff

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_conj_bijection_middle {A B B' C : Type*} [Zero C] {f : A → B} {g : B → C}
    (β : B → B') (δ : B' → B) (hδβ : ∀ b, δ (β b) = b) (hβδ : ∀ b', β (δ b') = b')
    (hfg : Function.Exact f g) : Function.Exact (β ∘ f) (g ∘ δ) := by
  intro y
  rw [Function.comp_apply, hfg (δ y)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [Function.comp_apply, hx, hβδ]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Function.comp_apply, hδβ]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_comp_surjective {A A' B C : Type*} [Zero C] {f : A → B} {g : B → C}
    {γ : A' → A} (hfg : Function.Exact f g) (hγ : Function.Surjective γ) :
    Function.Exact (f ∘ γ) g := by
  intro y
  rw [hfg y, Set.range_comp, hγ.range_eq, Set.image_univ]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.coefSeq_exact : _root_.GlobalTheory.EtC.A7 := by
  unfold _root_.GlobalTheory.EtC.A7
  intro R _ S hS
  obtain ⟨e, ⟨hom⟩⟩ := _root_.GlobalTheory.EtC.cone_resMap_homotopyEquiv R S hS
  refine ⟨_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
    (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1), fun K n => ?_⟩
  obtain ⟨ex₁, ex₂, ex₃⟩ :=
    _root_.GlobalTheory.EtC.coneSeqTgt_exact R K (_root_.GlobalTheory.EtC.resMap R S.f) n
  have hinvhom : ∀ x, _root_.GlobalTheory.EtC.cpush K e.inv n (_root_.GlobalTheory.EtC.cpush K e.hom n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyHomInvId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hhominv : ∀ x, _root_.GlobalTheory.EtC.cpush K e.hom n (_root_.GlobalTheory.EtC.cpush K e.inv n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyInvHomId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hg : ⇑(_root_.GlobalTheory.EtC.HK.post R K S.g n) =
      ⇑(_root_.GlobalTheory.EtC.cpush K e.hom n) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K (mappingCone.inr (_root_.GlobalTheory.EtC.resMap R S.f)) n) := by
    funext x
    show _root_.GlobalTheory.EtC.cpush K (_root_.GlobalTheory.EtC.resMap R S.g) n x = _
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K hom, _root_.GlobalTheory.EtC.InjResCmp.cpush_comp]
    rfl
  have hδ : ⇑(_root_.GlobalTheory.EtC.HK.ext R K
      (_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
        (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1)) n (n + 1) rfl) =
      ⇑(_root_.GlobalTheory.EtC.cpost K (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) n (n + 1) rfl) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K e.inv n) := by
    funext y
    exact ((_root_.GlobalTheory.cocycle_comp_assoc_classes R (add_zero n) (zero_add 1) rfl rfl).2.2
      y (Cocycle.ofHom e.inv) (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)))
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact exact_comp_injective ex₁ (Function.LeftInverse.injective hinvhom) (map_zero _)
  · rw [hg, hδ]
    exact exact_conj_bijection_middle _ _ hinvhom hhominv ex₂
  · rw [hδ]
    exact exact_comp_surjective ex₃ (Function.LeftInverse.surjective hinvhom)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_coefficient_longExactSequence : GlobalTheory.EtC.A7 := by
  first | (exact @GlobalTheory.EtC.coefSeq_exact) | (exact GlobalTheory.EtC.coefSeq_exact) | (intros; apply GlobalTheory.EtC.coefSeq_exact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeResolutionLocalChaseOnSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeResolutionLocalChaseOnSupport
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeChase

variable {R : Type} [CommRing R]

theorem map_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

theorem map_congr {F G : Shv R} {a b : F ⟶ G} (h : a = b) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a x = Sec.map b x := by rw [h]

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem map_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := map_add _ _ _

theorem map_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := map_neg _ _

theorem map_zero' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := map_zero _

theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ _ _

theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem res_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := congrArg (fun t => t.hom x) (a.hom.naturality g.op)
  exact this.symm

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  have := congrArg (fun t => t.hom x) (F.obj.map_comp g.op k.op)
  exact this

theorem comm' {I J : Cx R} (f : I ⟶ J) (i j : ℤ) {U : Scheme.{0}} (x : Sec (I.X i) U) :
    Sec.map (J.d i j) (Sec.map (f.f i) x) = Sec.map (f.f j) (Sec.map (I.d i j) x) :=
  map_congr (f.comm i j) x

theorem mappingCone_resolution_localChase_of_succ (E : Spc) {F G : Shv R} (φ : F ⟶ G)
    (hφ : ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U)))
    (U : Scheme.{0}) (hU : Nonempty (Sx E 0 U)) (m n k l : ℤ) (hm : m + 1 = n) (hk : n + 1 = k) (hl : k + 1 = l)
    (b₁ : Sec ((res R F).X k) U) (b₂ : Sec ((res R G).X n) U)
    (h₁ : Sec.map ((res R F).d k l) b₁ = 0)
    (h₂ : Sec.map ((resMap R φ).f k) b₁ + Sec.map ((res R G).d n k) b₂ = 0) :
    Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X m) V),
      Sec.map ((res R F).d n k) a₁ = -Sec.res g b₁ ∧
      Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d m n) a₂ = Sec.res g b₂ := by
  obtain ⟨Lall, Lmono, -, -, Ltrans, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  have hι := ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.2 G φ).2
  have hd := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.1
  rcases lt_or_ge n 0 with hn | hn
  · have hb₂ : b₂ = 0 := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G U).2.2.2 n hn).elim _ _
    have hb₁ : b₁ = 0 := by
      rcases lt_or_ge k 0 with hk0 | hk0
      · exact ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 k hk0).elim _ _
      · obtain rfl : k = 0 := by omega
        obtain rfl : l = 1 := by omega
        obtain ⟨s, rfl⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).1 b₁).1 h₁
        rw [hb₂, map_zero', add_zero, ← map_comp, map_congr hι, map_comp] at h₂
        have h3 : Sec.map φ s = 0 := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G U).2.1 (by rw [h₂, map_zero'])
        have h4 : s = 0 := (hφ U hU).1 (by rw [h3, map_zero'])
        rw [h4, map_zero']
    refine Lall _ _ fun V g => ⟨0, 0, ?_, ?_⟩
    · rw [hb₁, map_zero', res_zero, neg_zero]
    · rw [hb₂, map_zero', map_zero', res_zero, add_zero]
  · apply Ltrans
    refine Lmono _ _ _ ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.1 n k l (by omega) hk b₁ hl h₁) ?_
    rintro V g ⟨y, hy⟩
    have hc : Sec.map ((res R G).d n k) (Sec.res g b₂ + Sec.map ((resMap R φ).f n) y) = 0 := by
      rw [map_add', comm', hy, ← res_map, ← res_map, ← res_add, add_comm, h₂, res_zero]
    rcases lt_or_eq_of_le hn with hn' | hn'
    · refine Lmono _ _ _ ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G V).2.2.1 m n k hn' hm _ hk hc) ?_
      rintro W j ⟨z, hz⟩
      refine ⟨-Sec.res j y, z, ?_, ?_⟩
      · rw [map_neg', ← res_map, hy, res_comp]
      · rw [hz, map_neg', res_add, res_map, res_comp]; abel
    · subst hn'
      obtain rfl : k = 1 := by omega
      obtain ⟨s, hs⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G V).1 _).1 hc
      obtain ⟨x⟩ := hU
      obtain ⟨t, rfl⟩ := (hφ V ⟨Sx.res g x⟩).2 s
      refine Lall _ _ fun W j => ⟨Sec.res j (-y + Sec.map (resι R F) t), 0, ?_, ?_⟩
      · rw [← res_map, map_add', map_neg', hy, ← map_comp, map_congr hd, map_zero_hom, add_zero, res_comp]
        exact map_neg _ _
      · rw [map_zero', add_zero, ← res_map, map_add', map_neg', ← map_comp, map_congr hι, map_comp, hs, res_comp]
        congr 1
        abel

theorem chase : ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G), (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) → ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b₁ : Sec ((res R F).X (n + 1)) U) (b₂ : Sec ((res R G).X n) U), Sec.map ((res R F).d (n + 1) (n + 2)) b₁ = 0 → Sec.map ((resMap R φ).f (n + 1)) b₁ + Sec.map ((res R G).d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X (n - 1)) V), Sec.map ((res R F).d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d (n - 1) n) a₂ = Sec.res g b₂ :=
  fun _ _ E _ _ φ hφ U hU n b₁ b₂ h₁ h₂ =>
    mappingCone_resolution_localChase_of_succ E φ hφ U hU (n - 1) n (n + 1) (n + 2) (by ring) rfl (by ring) b₁ b₂ h₁ h₂

end GlobalTheory.EtC.ConeChase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeResolutionLocalChaseOnSupportStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_resolution_localChase_on_support : ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G), (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) → ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b₁ : Sec ((res R F).X (n + 1)) U) (b₂ : Sec ((res R G).X n) U), Sec.map ((res R F).d (n + 1) (n + 2)) b₁ = 0 → Sec.map ((resMap R φ).f (n + 1)) b₁ + Sec.map ((res R G).d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X (n - 1)) V), Sec.map ((res R F).d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d (n - 1) n) a₂ = Sec.res g b₂ := by
  first | (exact @GlobalTheory.EtC.ConeChase.chase) | (exact GlobalTheory.EtC.ConeChase.chase) | (intros; apply GlobalTheory.EtC.ConeChase.chase  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeLocallyExactOfComponentSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeLocallyExactOfComponentSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeSec

variable {R : Type} [CommRing R]

lemma smap_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

lemma smap_add {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

lemma smap_neg {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-a) x = -Sec.map a x := rfl

lemma smap_sub {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a - b) x = Sec.map a x - Sec.map b x := rfl

lemma smap_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

lemma smap_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := (a.hom.app (op U)).hom.map_add x y

lemma smap_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := (a.hom.app (op U)).hom.map_neg x

lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

lemma smap_zero {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := (a.hom.app (op U)).hom.map_zero

lemma sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := (F.obj.map g.op).hom.map_add x y

end GlobalTheory.EtC.ConeSec


open GlobalTheory.EtC.ConeSec in
theorem GlobalTheory.EtC.cone_sec_exact : ∀ (R : Type) [CommRing R] {I J : Cx R} (f : I ⟶ J) (U : Scheme.{0}) (n : ℤ), (∀ (b₁ : Sec (I.X (n + 1)) U) (b₂ : Sec (J.X n) U), Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 → Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec (I.X n) V) (a₂ : Sec (J.X (n - 1)) V), Sec.map (I.d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map (f.f n) a₁ + Sec.map (J.d (n - 1) n) a₂ = Sec.res g b₂) → ∀ b : Sec ((mappingCone f).X n) U, Sec.map ((mappingCone f).d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec ((mappingCone f).X (n - 1)) V, Sec.map ((mappingCone f).d (n - 1) n) a = Sec.res g b := by
  intro R _ I J f U n hyp b hb
  obtain ⟨b₁, hb₁⟩ : ∃ x, Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) b = x := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x, Sec.map ((mappingCone.snd f).v n n (add_zero n)) b = x := ⟨_, rfl⟩
  have h1 : Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_fst_v f n (n + 1) (n + 2) rfl (by ring))
    simp only [smap_comp, smap_neg, hb, smap_zero, hb₁] at e
    exact neg_eq_zero.mp e.symm
  have h2 : Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_snd_v f n (n + 1) rfl)
    simp only [smap_comp, smap_add, hb, smap_zero, hb₁, hb₂] at e
    exact e.symm
  have hid := congrArg (fun φ => Sec.map φ b) (mappingCone.id_X f n (n + 1) rfl)
  simp only [smap_comp, smap_add, smap_id, hb₁, hb₂] at hid
  obtain ⟨S, hS, h⟩ := hyp b₁ b₂ h1 h2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a₁, a₂, e1, e2⟩ := h V g hg
  refine ⟨Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁ + Sec.map ((mappingCone.inr f).f (n - 1)) a₂, ?_⟩
  have k1 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (f.f n) a₁) -
        Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.map (I.d n (n + 1)) a₁) := by
    rw [← smap_comp, mappingCone.inl_v_d f n (n - 1) (n + 1) (by ring) (by ring), smap_sub, smap_comp, smap_comp]
  have k2 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inr f).f (n - 1)) a₂) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (J.d (n - 1) n) a₂) := by
    rw [← smap_comp, mappingCone.inr_f_d, smap_comp]
  have k3 : Sec.res g b = Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.res g b₁) +
      Sec.map ((mappingCone.inr f).f n) (Sec.res g b₂) := by
    rw [← hid, sres_add, sres_map, sres_map]
  rw [smap_add', k1, k2, e1, k3, ← e2, smap_add', smap_neg']
  abel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeLocallyExactOfComponentSectionsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_locallyExact_of_component_sections : ∀ (R : Type) [CommRing R] {I J : Cx R} (f : I ⟶ J) (U : Scheme.{0}) (n : ℤ), (∀ (b₁ : Sec (I.X (n + 1)) U) (b₂ : Sec (J.X n) U), Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 → Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec (I.X n) V) (a₂ : Sec (J.X (n - 1)) V), Sec.map (I.d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map (f.f n) a₁ + Sec.map (J.d (n - 1) n) a₂ = Sec.res g b₂) → ∀ b : Sec ((mappingCone f).X n) U, Sec.map ((mappingCone f).d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec ((mappingCone f).X (n - 1)) V, Sec.map ((mappingCone f).d (n - 1) n) a = Sec.res g b := by
  first | exact @GlobalTheory.EtC.cone_sec_exact | exact GlobalTheory.EtC.cone_sec_exact | (intros; apply GlobalTheory.EtC.cone_sec_exact; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeLocalization

theorem cone_kinj (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (mappingCone (resMap R φ)).IsKInjective := by
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G).2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G).2.2.1
  haveI : ∀ n, Injective ((mappingCone (resMap R φ)).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resMap R φ) n (n + 1) rfl).symm inferInstance
  haveI : (mappingCone (resMap R φ)).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  exact isKInjective_of_injective _ (-1)

theorem cone_loc (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G)
    (hφ : ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) :
    ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec ((mappingCone (resMap R φ)).X n) U),
      Sec.map ((mappingCone (resMap R φ)).d n (n + 1)) b = 0 →
      Loc U fun V g => ∃ a : Sec ((mappingCone (resMap R φ)).X (n - 1)) V,
        Sec.map ((mappingCone (resMap R φ)).d (n - 1) n) a = Sec.res g b := by
  intro U hU n b hb
  exact GlobalTheory.T.mappingCone_locallyExact_of_component_sections R (resMap R φ) U n (GlobalTheory.T.mappingCone_resolution_localChase_on_support R E φ hφ U hU n) b hb

end GlobalTheory.EtC.ConeLocalization

theorem GlobalTheory.EtC.a10 : GlobalTheory.EtC.A10 := by
  intro R _ E F G φ hφ
  haveI := GlobalTheory.EtC.ConeLocalization.cone_kinj R φ
  have hC := GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support R E (mappingCone (resMap R φ)) (GlobalTheory.EtC.ConeLocalization.cone_loc R E φ hφ)
  have ex := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R ((chains R).obj E) (resMap R φ)
  intro n
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := ((ex m).2.2 x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact ((ex n).1 y).1 (Subsingleton.elim _ _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_bijective_of_support_bijective : GlobalTheory.EtC.A10 := by
  first | (exact @GlobalTheory.EtC.a10) | (exact GlobalTheory.EtC.a10) | (intros; apply GlobalTheory.EtC.a10  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpecStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) (U : Scheme.{0}) (a : Sec F U), (restrMap φ F).app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  first | (exact @GlobalTheory.EtC.restrMap_spec') | (exact GlobalTheory.EtC.restrMap_spec') | (intros; apply GlobalTheory.EtC.restrMap_spec'  <;> assumption)
end

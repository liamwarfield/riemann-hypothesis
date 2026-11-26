module

public import Development.EtaleCohomology.KummerTheory.FivePf
public import Development.EtaleCohomology.KummerTheory.DictNormalPf

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.EtaleKummerDegreeZeroCohomologyOfTwistSectionCla
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def Cls0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) → CohomologyClass.mk α = CohomologyClass.mk β

def OneEx : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  ∃ c : Ht q (sp A) 0 0, ∃ α : Cocycle ((chains (ZMod q)).obj (sp A)) (res (ZMod q) (tw q 0)) 0,
    CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : Sx (sp A) 0 U) (ζ : Prim q Γ(U, ⊤)),
      ev α.1 0 0 (by simp) U x = resGen 0 ζ

theorem etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex (hT : TwSec) (hC : Cls0) (hO : OneEx) : H0 := by
  intro h9 q _ A _ hA hq
  obtain ⟨hne, hb⟩ := hT q A hA hq
  obtain ⟨ζ⟩ := hne
  have hb0 := hb 0 ζ
  obtain ⟨_, e, -, he⟩ := h9 (ZMod q) (tw q 0)
  have hone : one q (sp A) = e (Spec (CommRingCat.of A)) (twGen 0 ζ) := by
    obtain ⟨α, hα, hv⟩ := pick_spec (hO q A hA hq)
    have hα' : CohomologyClass.mk α = one q (sp A) := hα
    obtain ⟨β, hβ, hβv⟩ := he (Spec (CommRingCat.of A)) (twGen 0 ζ)
    rw [← hα', ← hβ]
    exact hC _ _ _ α β ((hv _ (𝟙 _) ζ).trans hβv.symm)
  have hlin : ∀ t : ZMod q, t • one q (sp A) =
      e (Spec (CommRingCat.of A)) ((ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := by
    intro t
    rw [hone]
    have h1 : t = ((t.val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val t).symm
    have h2 : (ULift.up t : ULift.{1} (ZMod q)) = ((t.val : ℕ) : ULift.{1} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast]; exact h1
    rw [h2, Nat.cast_smul_eq_nsmul, map_nsmul]
    conv_lhs => rw [h1]
    rw [Nat.cast_smul_eq_nsmul]
  have hfun : (fun t : ZMod q => t • one q (sp A)) =
      (e (Spec (CommRingCat.of A))) ∘ (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := funext hlin
  rw [hfun]
  exact (e _).bijective.comp hb0

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.OneExPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def TwRes0 : Prop := ∀ (q : ℕ) [NeZero q] {U X : Scheme.{0}} (x : U ⟶ X) (ζ₀ : Prim q Γ(X, ⊤)) (ζ : Prim q Γ(U, ⊤)),
  Sec.res x (twGen 0 ζ₀) = twGen 0 ζ

def DegreeZeroSectionExists : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom s) h).symm

theorem OneEx_of (hT : TwSec) (hR : TwRes0) (hS : DegreeZeroSectionExists) : OneEx := by
  intro q _ A _ hA hq
  obtain ⟨⟨ζ₀⟩, -⟩ := hT q A hA hq
  obtain ⟨α, hα⟩ := hS (ZMod q) (tw q 0) (Spec (CommRingCat.of A)) (twGen 0 ζ₀)
  refine ⟨_, α, rfl, ?_⟩
  intro U x ζ
  refine (hα U x).trans ((sec_res_map (resι (ZMod q) (tw q 0)) (x : U ⟶ Spec (CommRingCat.of A)) (twGen 0 ζ₀)).trans ?_)
  rw [hR q (x : U ⟶ Spec (CommRingCat.of A)) ζ₀ ζ]
  rfl

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.FixStalk
section -- merged from Development.EtaleCohomology.KummerTheory.EtaleNormalizedFreeChainsDifferentialOneZeroEqZe
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.S0

variable (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})

def eta (s : Sec F X) : (freeP R).obj (yoneda.obj X) ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun (x : ULift.{1} (unop U ⟶ X)) => Sec.res (ULift.down x) s)
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro x
    simp only [freeP, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change (F.obj.map (g.unop ≫ x.down).op).hom s = (F.obj.map g).hom ((F.obj.map x.down.op).hom s)
    rw [op_comp, Functor.map_comp]
    rfl

def gmap (s : Sec F X) : (free R).obj (yoneda.obj X) ⟶ F :=
  ⟨sheafifyLift Scheme.etaleTopology (eta R F X s) F.property⟩

theorem gmap_app (s : Sec F X) (U : Scheme.{0}) (x : U ⟶ X) :
    ((gmap R F X s).hom.app (op U)).hom (freeGen R (yoneda.obj X) U x) = Sec.res x s := by
  have h := congrArg (fun f => (f.app (op U)).hom
      (ModuleCat.freeMk (show uliftFunctor.{1, 0}.obj ((yoneda.obj X).obj (op U)) from ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta R F X s) F.property)
  exact h.trans (ModuleCat.freeDesc_apply _ _)

theorem etale_normalized_free_chains_differential_one_zero_eq_zero : ((chainsN R).obj (sch.obj X)).d 1 0 = 0 := by
  simp [chainsN, AlgebraicTopology.alternatingFaceMapComplex_obj_d, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    Fin.sum_univ_two, SimplicialObject.δ, sch]
  rfl

theorem d10 : ((chains R).obj (sch.obj X)).d (-1) 0 ≫ (chainsXIso R (sch.obj X) 0).hom = 0 := by
  dsimp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq ((chainsN R).obj (sch.obj X)) ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl]
  rw [etale_normalized_free_chains_differential_one_zero_eq_zero]
  simp only [Limits.zero_comp, Limits.comp_zero]
  all_goals exact Limits.zero_comp

theorem resι_d : resι R F ≫ (res R F).d 0 1 = 0 := by
  rw [resι]
  refine (Category.assoc _ _ _).trans ?_
  erw [(injectiveResolution F).ι'.comm 0 1]
  simp
  all_goals rfl

def fz (s : Sec F X) : ((chains R).obj (sch.obj X)).X (-((0 : ℕ) : ℤ)) ⟶ (res R F).X 0 :=
  (chainsXIso R (sch.obj X) 0).hom ≫ gmap R F X s ≫ resι R F

theorem fz_d (s : Sec F X) : fz R F X s ≫ (res R F).d 0 1 = 0 := by
  have h : (gmap R F X s ≫ resι R F) ≫ (res R F).d 0 1 = 0 := by
    rw [Category.assoc, resι_d, Limits.comp_zero]
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun t => (chainsXIso R (sch.obj X) 0).hom ≫ t) h).trans Limits.comp_zero

theorem d_fz (s : Sec F X) : ((chains R).obj (sch.obj X)).d (-1) (-((0 : ℕ) : ℤ)) ≫ fz R F X s = 0 := by
  simp only [fz]
  rw [← Category.assoc]
  erw [d10]
  exact Limits.zero_comp

def coc (s : Sec F X) : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 :=
  Cocycle.mk (Cochain.single (fz R F X s) 0) 1 (zero_add 1) (by
    rw [Cochain.δ_single (fz R F X s) 0 1 (zero_add 1) (-1) 1 (by norm_num) rfl, fz_d, d_fz,
      Cochain.single_zero, Cochain.single_zero, smul_zero, add_zero])

theorem coc_ev (s : Sec F X) (U : Scheme.{0}) (x : U ⟶ X) :
    ev (coc R F X s).1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s) := by
  rw [sec_res_map]
  simp only [ev, coc, Cocycle.mk_coe, Cochain.single_v, fz, Iso.inv_hom_id_assoc]
  change ((resι R F).hom.app (op U)).hom (((gmap R F X s).hom.app (op U)).hom (freeGen R (yoneda.obj X) U x)) = _
  rw [gmap_app]

end LateralTheory.KummerTheory.S0

namespace LateralTheory.KummerTheory

theorem Sec0Ex_of : DegreeZeroSectionExists := fun R _ F X s => ⟨S0.coc R F X s, S0.coc_ev R F X s⟩

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.PrimIsPrimitiveRoot
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (f : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res f (twGen i ζ) = twGen i (Prim.map f.appTop.hom ζ) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality f.op
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))
  simp only [ModuleCat.hom_comp] at h2
  unfold twGen ofRings.sec
  rw [← Finsupp.mapDomain_single]
  exact h2.symm

theorem twGen_zero_eq {q : ℕ} {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨c, hc⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} {K : Type} [Field K] (μ : Prim q K) : IsPrimitiveRoot μ.1 q := by
  obtain ⟨z, hz1, hz2⟩ := μ
  have : NeZero (q : K) := ⟨hz1.ne_zero⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  rw [aeval_def, algebraMap_int_eq] at hz2
  show Polynomial.eval z (cyclotomic q K) = 0
  rw [← map_cyclotomic_int, Polynomial.eval_map]
  exact hz2

theorem local_pow {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (x : U) :
    ∃ (h : Γ(U, ⊤)) (a : (ZMod q)ˣ), x ∈ U.basicOpen h ∧ h * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0 := by
  let e := (U.evaluation ⊤ x trivial).hom
  have hζ := prim_isPrimitiveRoot (Prim.map e ζ)
  have hξ := prim_isPrimitiveRoot (Prim.map e ξ)
  obtain ⟨i, hi, hie⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hcop : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (hie ▸ hξ)
  have hav : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  obtain ⟨k, hk⟩ := binomExpansion ((X : Polynomial Γ(U, ⊤)) ^ q - 1) ξ.1
    (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1)
  have hξq := prim_pow ξ
  have hζq : (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]
  refine ⟨(q : Γ(U, ⊤)) * ξ.1 ^ (q - 1) + k * (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1),
    ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x (show x ∈ (⊤ : U.Opens) from trivial)]
    have hy : e (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) = 0 := by
      rw [map_sub, map_pow, hav, sub_eq_zero]
      exact hie
    have hq : ((q : ℕ) : U.residueField x) ≠ 0 := (Prim.map e ξ).2.1.ne_zero
    change e _ ≠ 0
    rw [map_add (f := _), map_mul, map_mul, hy, mul_zero, add_zero, map_pow, map_natCast]
    exact mul_ne_zero hq (pow_ne_zero _ (hξ.ne_zero (NeZero.ne q)))
  · have hs : ξ.1 + (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) =
        ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val := by ring
    rw [hs] at hk
    simp only [eval_sub, eval_pow, eval_X, eval_one, hζq, hξq, sub_self, derivative_sub, derivative_X_pow,
      derivative_one, sub_zero, eval_mul, eval_C] at hk
    linear_combination hk

theorem sec_eq_of_cover {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} {ι : Type} (V : ι → U.Opens)
    (hV : TopologicalSpace.IsOpenCover V) (s t : Sec F U) (h : ∀ i, Sec.res (V i).ι s = Sec.res (V i).ι t) :
    s = t := by
  let S : Sieve U := {
    arrows := fun W f => Sec.res f s = Sec.res f t
    downward_closed := by
      intro W W' f hf g
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hf ⊢
      rw [hf] }
  have hS : S ∈ Scheme.etaleTopology U := by
    apply Scheme.zariskiTopology_le_etaleTopology
    refine Scheme.zariskiTopology.superset_covering ?_
      (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover V hV))
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W f ⟨i⟩
    exact h i
  have hsh : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.property)
  exact (hsh S hS).isSeparatedFor.ext fun W f hf => hf

theorem twGen_zero_indep {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) :
    twGen 0 ξ = twGen 0 ζ := by
  choose h a hx hh using fun x : U => local_pow ζ ξ x
  refine sec_eq_of_cover (fun x => U.basicOpen (h x)) ?_ _ _ fun x => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hx y⟩
  rw [twGen_res, twGen_res]
  apply twGen_zero_eq _ _ (a x)
  change (U.basicOpen (h x)).ι.appTop.hom ξ.1 = (U.basicOpen (h x)).ι.appTop.hom ζ.1 ^ _
  rw [← map_pow, ← sub_eq_zero, ← map_sub]
  have hu : IsUnit ((U.basicOpen (h x)).ι.appTop.hom (h x)) := by
    rw [Scheme.Opens.ι_appTop]
    have key : ∀ (W : U.Opens) (hW : W = U.basicOpen (h x)) (hle : W ≤ ⊤),
        IsUnit (U.presheaf.map (homOfLE hle).op (h x)) := by
      rintro W rfl hle
      exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace (h x)
    exact key _ (Scheme.Opens.ι_image_top _) _
  exact hu.mul_right_eq_zero.1 (by rw [← map_mul, hh x, map_zero])

theorem TwRes0_of : TwRes0 := by
  intro q _ U X x ζ₀ ζ
  rw [twGen_res]
  exact twGen_zero_indep _ _

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.ResNegZero
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DegreeZeroClassRestriction

theorem res_neg_zero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  apply HomologicalComplex.isZero_extend_X
  intro i hi
  have h' : ((i : ℕ) : ℤ) = s := hi
  omega

def asHom {X U : Scheme.{0}} (x : Sx (sch.obj X) 0 U) : U ⟶ X := by
  unfold sch at x; exact x

def ofHom {X U : Scheme.{0}} (g : U ⟶ X) : Sx (sch.obj X) 0 U := by
  unfold sch; exact g

theorem res_ofHom {X U : Scheme.{0}} (x : Sx (sch.obj X) 0 U) : Sx.res (asHom x) (ofHom (𝟙 X)) = x := by
  change asHom x ≫ 𝟙 X = x
  exact Category.comp_id (asHom x)

theorem cochain_eq (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (α β : Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
    (h : ev α 0 0 (by simp) X (𝟙 X) = ev β 0 0 (by simp) X (𝟙 X)) : α = β := by
  apply LateralTheory.KummerTheory.AW.ev_ext
  intro p s hp U x
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using hp.symm
    have key : ∀ γ : Cochain ((chains R).obj (sch.obj X)) (res R F) 0,
        ev γ 0 0 hp U x = Sec.res (asHom x) (ev γ 0 0 hp X (ofHom (𝟙 X))) := by
      intro γ
      rw [LateralTheory.KummerTheory.AW.ev_res]
      rw [res_ofHom]
    rw [key α, key β]
    exact congrArg _ h
  | succ k =>
    have hs : s < 0 := by omega
    rw [LateralTheory.KummerTheory.AW.ev_eq, LateralTheory.KummerTheory.AW.ev_eq, (res_neg_zero R F s hs).eq_of_tgt
      ((chainsXIso R (sch.obj X) (k + 1)).inv ≫ α.v _ _ hp) ((chainsXIso R (sch.obj X) (k + 1)).inv ≫ β.v _ _ hp)]

end LateralTheory.KummerTheory.DegreeZeroClassRestriction

theorem LateralTheory.KummerTheory.Cls0_of (_hT : LateralTheory.KummerTheory.TwSec) : LateralTheory.KummerTheory.Cls0 := by
  intro R _ F X α β h
  have e : α.1 = β.1 := LateralTheory.KummerTheory.DegreeZeroClassRestriction.cochain_eq R F X α.1 β.1 h
  exact congrArg CohomologyClass.mk (Cocycle.ext e)
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.StalkPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

theorem stalk_neg (h9 : A9) (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
    (A : CommRingCat.{0}) (s : R ⟶ A) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ)
    (n : ℤ) (hn : n < 0) : IsoUpTo N (lh q p (Spec.map s) i r c M n) := by
  have : Subsingleton (Ht q (sch.obj (pullback p (Spec.map s))) n i) := (h9 (ZMod q) (tw q i)).1 _ n hn
  haveI : ∀ a : Fin (M + 1), Subsingleton (Ht q (sch.obj (Spec A)) (n - ((a : ℕ) : ℤ)) 0) :=
    fun a => (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  refine ⟨fun y _ => ?_, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  funext a t
  exact Subsingleton.elim _ _

def ExtOne : Prop := DivisorNaturality → DivisorRingCompatibility → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R A : CommRingCat.{0}} (p : X ⟶ Spec R)
  (s : R ⟶ A), IsUnit (q : A) → ∀ (a i : ℤ) (x : Ht q (sch.obj X) a i) (t : ZMod q),
    ext q p (Spec.map s) a a i x ((t • one q (sch.obj (Spec A))).cast (by ring) rfl) =
      t • pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ x

def StalkTop : Prop := DivisorNaturality → DivisorRingCompatibility → A9 → B2 → H0 → ExtOne → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}}
  {R : CommRingCat.{0}} (p : X ⟶ Spec R) (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ), Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i) →
  (∀ a ≤ M, IsoUpTo N (comb q (c a))) → ∀ n : ℤ, 0 ≤ n → n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)

theorem inv_sch (q : ℕ) {X : Scheme.{0}} (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U ⟨g⟩
  have g' : U ⟶ X := g
  simpa using hq.map g'.appTop.hom

theorem unit_spec (q : ℕ) {A : CommRingCat.{0}} (hq : IsUnit (q : A)) : IsUnit (q : Γ(Spec A, ⊤)) := by
  simpa using hq.map (Scheme.ΓSpecIso A).inv.hom

theorem pull_zsmul {E E' : Spc} (f : E ⟶ E') (q : ℕ) [NeZero q] {n i : ℤ} (t : ZMod q) (x : Ht q E' n i) :
    pull _ f _ _ (t • x) = t • pull _ f _ _ x := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem cast_cast' (q : ℕ) {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem pull_cast (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast h1 h2) = Ht.cast h1 h2 (pull _ f _ _ x : Ht q E n i) := by
  subst h1 h2; rfl

theorem cast_smul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (t : ZMod q) (x : Ht q E n i) :
    (t • x).cast h1 h2 = t • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem cup_cast_r (q : ℕ) {E : Spc} {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (y : Ht q E m j) : cup q a (y.cast h1 h2) = (cup q a y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cup_smul_r (q : ℕ) [NeZero q] {E : Spc} {n m i j : ℤ} (t : ZMod q) (a : Ht q E n i) (y : Ht q E m j) :
    cup q a (t • y) = t • cup q a y := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem unit_map (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) : IsUnit (q : Γ(Y, ⊤)) := by
  simpa using hq.map f.appTop.hom

theorem extOne_pf : ExtOne := by
  intro h6n h6r q _ X R A p s hq a i x t
  have hI := inv_sch q (unit_spec q hq)
  have hP := inv_sch q (unit_map q (pullback.snd p (Spec.map s)) (unit_spec q hq))
  unfold ext
  rw [pull_cast, pull_zsmul, (h6n q).2.1 _ hI, cup_cast_r, cup_smul_r, (h6r q _).2.2, (h6r q _).1 hP]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_smul', cast_cast']
  rfl

theorem cast_zero' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

theorem cast_nsmul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (N : ℕ) (x : Ht q E n i) :
    (N • x).cast h1 h2 = N • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem ext_zero (q : ℕ) [NeZero q] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i) :
    ext q pX pY a n i x 0 = 0 := by
  unfold ext; rw [map_zero, map_zero, cast_zero']

theorem stalkTop_pf : StalkTop := by
  intro h6n h6r h9 hb2 h0 hE q _ X R p A s hA hq i r c M N he hc n hn0 hnM
  lift n to ℕ using hn0
  have hnM' : n ≤ M := by exact_mod_cast hnM
  have hqA : IsUnit (q : A) := by simpa using hq.map s.hom
  let a : Fin (M + 1) := ⟨n, by omega⟩
  have hsub : ∀ b : Fin (M + 1), b ≠ a → Subsingleton (Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0) := by
    intro b hb
    have hb' : (b : ℕ) ≠ n := fun h => hb (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hb' with h | h
    · exact hb2 (ZMod q) A hA (tw q 0) _ (by omega)
    · exact (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  have hH := h0 h9 q A hA hqA
  have hex : ∀ z : Ht q (sch.obj (Spec A)) ((n : ℤ) - (n : ℤ)) 0, ∃ t : ZMod q,
      z = (t • one q (sch.obj (Spec A))).cast (by ring) rfl := by
    intro z
    obtain ⟨t, ht⟩ := hH.2 (z.cast (by ring) rfl)
    refine ⟨t, ?_⟩
    rw [show t • one q (sch.obj (Spec A)) = _ from ht, cast_cast']; rfl
  have hform : ∀ (y : ∀ b : Fin (M + 1), Fin (r b) → Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0)
      (t : Fin (r n) → ZMod q), (∀ u, y a u = (t u • one q (sch.obj (Spec A))).cast (by ring) rfl) →
      lh q p (Spec.map s) i r c M n y = pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ (comb q (c n) t) := by
    intro y t hy
    unfold lh comb
    rw [Fintype.sum_eq_single a]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hy u, pull_zsmul]
      exact hE h6n h6r q p s hqA n i (c n u) (t u)
    · intro b hb
      haveI := hsub b hb
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [Subsingleton.elim (y b u) 0, ext_zero]
  have hbij := he (n : ℤ)
  refine ⟨fun y hy0 => ?_, fun b => ?_⟩
  · choose t ht using fun u => hex (y a u)
    rw [hform y t ht] at hy0
    have hc0 : comb q (c n) t = 0 := hbij.1 (by rw [hy0, map_zero])
    have hNt := (hc n hnM').1 t hc0
    funext b u
    by_cases hb : b = a
    · subst hb
      show N • y a u = 0
      rw [ht u]
      have e1 : N • t u = 0 := by simpa using congrFun hNt u
      rw [← cast_nsmul', ← smul_assoc, e1, zero_smul, cast_zero']
    · haveI := hsub b hb
      exact Subsingleton.elim _ _
  · obtain ⟨w, rfl⟩ := hbij.2 b
    obtain ⟨t, ht⟩ := (hc n hnM').2 w
    refine ⟨Pi.single a (fun u => (t u • one q (sch.obj (Spec A))).cast (by ring) rfl), ?_⟩
    rw [hform _ t (fun u => by rw [Pi.single_eq_same]), ht, map_nsmul]

theorem Stalk_of (h0 : H0) : Stalk := by
  intro h6n h6r h9 hb2 q _ X R p A s hA hq i r c M N he hc n hn
  by_cases hneg : n < 0
  · exact stalk_neg h9 q p A s i r c M N n hneg
  · exact stalkTop_pf h6n h6r h9 hb2 h0 extOne_pf q p A s hA hq i r c M N he hc n (by omega) hn
end LateralTheory.KummerTheory
end
end

theorem LateralTheory.Fix.Stalk.intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := by
  have hT : LateralTheory.KummerTheory.TwSec :=
    LateralTheory.KummerTheory.TwSec_of LateralTheory.KummerTheory.PrimTors_of
      (LateralTheory.KummerTheory.SecSH_of LateralTheory.KummerTheory.ShSectPf.ShSect_of)
  exact LateralTheory.KummerTheory.Stalk_of
    (LateralTheory.KummerTheory.etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex hT (LateralTheory.KummerTheory.Cls0_of hT)
      (LateralTheory.KummerTheory.OneEx_of hT LateralTheory.KummerTheory.TwRes0_of LateralTheory.KummerTheory.Sec0Ex_of))
end

namespace LateralTheory.Fin.Stalk
theorem etale_cohomology_stalk_compatibility_finite_coefficients_holds : LateralTheory.KummerTheory.Stalk := by
  apply LateralTheory.Fix.Stalk.intersectionNumber_baseChange
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := etale_cohomology_stalk_compatibility_finite_coefficients_holds
end LateralTheory.Fin.Stalk

module

public import Development.EtaleCohomology.KummerTheory.BockCut
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
public import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.LHCutGlue
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem ghostSec_of (hG : Ghost) (h1 : Corep) (h2 : HomKill) : GhostSec := by
  intro Λ _ S C hi hz N m hl j hj U x hx
  have : C.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi => hz i hi)
  obtain ⟨P, z, hP⟩ := h1 Λ S U
  obtain ⟨f, rfl⟩ := (hP (C.X j)).2 x
  obtain ⟨g, hg⟩ := hG (SlShv Λ S) C hi N m (fun j hj => h2 Λ S C N j (hl j hj)) j hj P f
    ((hP _).1 (hx.trans rfl))
  refine ⟨(g.hom.app (op U)).hom z, ?_⟩
  have := congrArg (fun φ : P ⟶ C.X j => (φ.hom.app (op U)).hom z) hg
  refine this.trans ?_
  generalize N ^ (m + 1) = k
  induction k with
  | zero => simp only [zero_smul]; rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

theorem glob_of (h1 : ConeCx) (h2 : GhostSec) : Glob := by
  intro Λ _ I J K μ hJ hK X S p r M γ hc N m hl j hj U x hx
  obtain ⟨C, hi, hz, e, he, hd⟩ := h1 Λ μ hJ hK p r M γ hc
  have hloc : ∀ j : ℤ, j < m → CxLoc C N j := by
    intro j hj U x hx u
    obtain ⟨V, g, hg, y, hy⟩ := hl j hj U (e j U x) (by rw [← hd j (j + 1) rfl, hx, map_zero]) u
    refine ⟨V, g, hg, (e _ V).symm y, (e j V).injective ?_⟩
    rw [hd (j - 1) j (by omega), AddEquiv.apply_symm_apply, hy, map_nsmul, he]
  obtain ⟨y, hy⟩ := h2 Λ S C hi hz N m hloc j hj U ((e j U).symm x) ((e (j + 1) U).injective (by
    rw [hd j (j + 1) rfl, AddEquiv.apply_symm_apply, hx, map_zero]))
  refine ⟨e _ U y, ?_⟩
  rw [← hd (j - 1) j (by omega), hy, map_nsmul, AddEquiv.apply_symm_apply]

theorem clsMore_of (hD : Dict) : ClsMore := by
  intro Λ _ I X n
  obtain ⟨_, d2, d3, d4, _⟩ := hD Λ I X n
  have h0 : IsCls (0 : CochainComplex.HomComplex.CohomologyClass ((chains Λ).obj (sch.obj X)) I n) 0 := by
    obtain ⟨a, ha⟩ := d2 0
    have := (d4 _ _ _ _ ha (d4 _ _ _ _ ha ha).2).1
    rwa [add_neg_cancel, add_neg_cancel] at this
  refine ⟨h0, ?_, ?_, ?_⟩
  · intro N x a h
    induction N with
    | zero => rw [zero_nsmul, zero_nsmul]; exact h0
    | succ N ih => rw [succ_nsmul, succ_nsmul]; exact (d4 _ _ _ _ ih h).1
  · intro ι _ x a h
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact h0
    | insert t s ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht]; exact (d4 _ _ _ _ (h t) ih).1
  · intro m hm x x' a a' h h'
    obtain rfl : m = n - 1 := by omega
    have := (d3 _ _ (d4 _ _ _ _ h (d4 _ _ _ _ h' h').2).1).2
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg, sub_eq_zero] at this

theorem lh_of (hD : Dict) (hG : Ghost) (h1 : LocKer) (h2 : LocCok) (h3 : LocCone) (h4 : ExIso) (h5 : ConeCx) (h6 : Corep)
    (h7 : HomKill) : LH :=
  goal_of hD h1 h2 h3 (glob_of h5 (ghostSec_of hG h6 h7)) h4

end LateralTheory.KummerTheory.LHCut
end

section -- merged from Development.EtaleCohomology.KummerTheory.FlasquePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.FlasquePf

variable {R : Type} [CommRing R]

def toG (G : Shv R) {W : Scheme.{0}} (t : Sec G W) : (freeP R).obj (yoneda.obj W) ⟶ G.obj where
  app V := ModuleCat.freeDesc
    (TypeCat.ofHom fun (f : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj V)) => (Sec.res f.down t : G.obj.obj V))
  naturality V V' h := by
    apply ModuleCat.free_hom_ext
    intro x
    change ModuleCat.freeDesc _ ((ModuleCat.free _).map (uliftFunctor.map ((yoneda.obj W).map h))
      (ModuleCat.freeMk x)) = (G.obj.map h).hom (ModuleCat.freeDesc _ (ModuleCat.freeMk x))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change (G.obj.map (h.unop ≫ x.down).op).hom t = (G.obj.map h).hom ((G.obj.map x.down.op).hom t)
    rw [op_comp, Functor.map_comp]
    rfl

def ofSec (G : Shv R) {W : Scheme.{0}} (t : Sec G W) : (free R).obj (yoneda.obj W) ⟶ G :=
  ((sheafificationAdjunction _ _).homEquiv _ G).symm (toG G t)

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (h : V ⟶ U) (x : P.obj (op U)) :
    Sec.res h (freeGen R P U x) = freeGen R P V (P.map h.op x) := by
  unfold freeGen Sec.res
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
    (sheafify Scheme.etaleTopology ((freeP R).obj P)).map h.op).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.naturality]
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
    ((ModuleCat.free _).map _ (ModuleCat.freeMk _)) = _
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom y)
    (ModuleCat.free_map_apply _ _)

theorem freeGen_map {P Q : PSh} (m : P ⟶ Q) {V : Scheme.{0}} (x : P.obj (op V)) :
    (((free R).map m).hom.app (op V)).hom (freeGen R P V x) = freeGen R Q V (m.app _ x) := by
  unfold freeGen
  calc _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyMap Scheme.etaleTopology ((freeP R).map m)).app
        (op V)).hom (ModuleCat.freeMk (ULift.up x)) := rfl
    _ = (((freeP R).map m ≫ toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom
        (ModuleCat.freeMk (ULift.up x)) := by rw [toSheafify_naturality]
    _ = _ := by
      change ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom
        ((ModuleCat.free _).map _ (ModuleCat.freeMk _)) = _
      exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom y)
        (ModuleCat.free_map_apply _ _)

theorem ofSec_gen (G : Shv R) {W : Scheme.{0}} (t : Sec G W) :
    ((ofSec G t).hom.app (op W)).hom (freeGen R (yoneda.obj W) W (𝟙 W)) = t := by
  have h : toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj W)) ≫ (ofSec G t).hom = toG G t :=
    toSheafify_sheafifyLift _ _ _
  have h2 : ((ofSec G t).hom.app (op W)).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj W))).app
      (op W)).hom (ModuleCat.freeMk (ULift.up (𝟙 W)))) = ((toG G t).app (op W)).hom (ModuleCat.freeMk (ULift.up (𝟙 W))) := by
    rw [← h]; rfl
  unfold freeGen
  rw [h2]
  change (ModuleCat.freeDesc _ (ModuleCat.freeMk _)) = t
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  change (G.obj.map (𝟙 (op W))).hom t = t
  rw [CategoryTheory.Functor.map_id]
  rfl

instance mono_freeP {W U : Scheme.{0}} (a : W ⟶ U) [Mono a] : Mono ((freeP R).map (yoneda.map a)) := by
  have : ∀ V, Mono (((freeP R).map (yoneda.map a)).app V) := by
    intro V
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (Finsupp.mapDomain _)
    apply Finsupp.mapDomain_injective
    intro x y e
    apply ULift.ext
    exact (cancel_mono a).1 (congrArg ULift.down e)
  exact NatTrans.mono_of_mono_app _

instance mono_free {W U : Scheme.{0}} (a : W ⟶ U) [Mono a] : Mono ((free R).map (yoneda.map a)) := by
  change Mono ((presheafToSheaf _ _).map ((freeP R).map (yoneda.map a)))
  infer_instance

theorem Flasque_of : LateralTheory.KummerTheory.ContCut.Flasque := by
  intro R _ G _ W U a _ t
  let φ := ofSec G t
  let ψ := Injective.factorThru φ ((free R).map (yoneda.map a))
  have hψ : (free R).map (yoneda.map a) ≫ ψ = φ := Injective.comp_factorThru _ _
  refine ⟨(ψ.hom.app (op U)).hom (freeGen R (yoneda.obj U) U (𝟙 U)), ?_⟩
  change (G.obj.map a.op).hom ((ψ.hom.app (op U)).hom _) = t
  have nat := congrArg (fun k => k.hom (freeGen R (yoneda.obj U) U (𝟙 U))) (ψ.hom.naturality a.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at nat
  rw [← nat]
  change (ψ.hom.app (op W)).hom (Sec.res a (freeGen R (yoneda.obj U) U (𝟙 U))) = t
  rw [freeGen_res]
  have e : (yoneda.obj U).map a.op (𝟙 U) = (yoneda.map a).app (op W) (𝟙 W) := by simp
  rw [e, ← freeGen_map]
  rw [← ofSec_gen G t]
  exact congrArg (fun k => (k.hom.app (op W)).hom (freeGen R (yoneda.obj W) W (𝟙 W))) hψ

end LateralTheory.KummerTheory.FlasquePf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.AdicLimPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def AdicKer : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ (n : ℤ) (k : ℕ) (x : Hl l E n i), lev l x k = 0 →
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y

def AdicFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), (∀ k : ℕ, Finite (Ht (l ^ k) E n i)) →
  (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) →
    Module.Finite ℤ_[l] (Hl l E n i)

def AdicCok : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l E (n + 1) i) →
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z

theorem AdicLim_of (hK : AdicKer) (hF : AdicFin) (hC : AdicCok) : AdicLim := by
  intro hA l _ E i hB hFin n
  have hker : ∀ m : ℤ, ∀ (k : ℕ) (x : Hl l E m i), lev l x k = 0 → ∃ y : Hl l E m i, x = ((l : ℤ_[l]) ^ k) • y :=
    fun m => hK hA l E i hB hFin m
  have hfin : ∀ m : ℤ, Module.Finite ℤ_[l] (Hl l E m i) := fun m => hF l E m i (fun k => hFin k m) (hker m)
  exact ⟨hfin n, hker n, hC hA l E i hB hFin n (hfin (n + 1))⟩

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.SecSHPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SecSHPf

theorem bij_of_top (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (hU : ∀ S ∈ Scheme.etaleTopology U, S (𝟙 U)) : Function.Bijective (ofRings.sec (R := R) M U) := by
  constructor
  · intro x y hxy
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) x y hxy
    have := hU _ h
    simp [Presheaf.equalizerSieve] at this
    exact this
  · intro s
    have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) s
    obtain ⟨t, ht⟩ := hU _ h
    refine ⟨t, ?_⟩
    simp at ht
    exact ht

def ShSect : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
  Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _

theorem top_of_sect (hs : ShSect) (A : Type) [CommRing A] (hA : SH A) :
    ∀ S ∈ Scheme.etaleTopology (Spec (CommRingCat.of A)), S (𝟙 _) := by
  intro S hS
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀).1
    (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  have hsurj : Surjective (𝒰.f i) := by
    refine ⟨fun p => ?_⟩
    have hsp : p ⤳ (𝒰.f i) y := by
      rw [hy]; exact IsLocalRing.specializes_closedPoint (R := A) p
    obtain ⟨y', -, hy'⟩ := Flat.generalizingMap (𝒰.f i) hsp
    exact ⟨y', hy'⟩
  obtain ⟨s, hs'⟩ := hs A ⟨hH, hsc⟩ _ (𝒰.f i) he hsurj
  have := S.downward_closed (hle (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)) s
  rwa [hs'] at this

end LateralTheory.KummerTheory.SecSHPf

namespace LateralTheory.KummerTheory

theorem SecSH_of (h : SecSHPf.ShSect) : SecSH := by
  intro A _ hA R _ M
  exact SecSHPf.bij_of_top R M _ (SecSHPf.top_of_sect h A hA)

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.GluePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.GluePf

def pc (U V : Scheme.{0}) : Bool → Scheme.{0} := fun b => Bool.rec V U b

def pm {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) : ∀ b : Bool, pc U V b ⟶ X :=
  fun b => Bool.rec (motive := fun b => pc U V b ⟶ X) g f b

theorem mem_cover {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Sieve.generate (Presieve.ofArrows (pc U V) (pm f g)) ∈ Scheme.etaleTopology X := by
  obtain ⟨hf, hg, -, hcov⟩ := h
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩
  · rcases hcov x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · cases i
    · exact (inferInstance : Etale g)
    · exact (inferInstance : Etale f)

theorem sheafFor {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V)
    (f : U ⟶ X) (g : V ⟶ X) (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Presieve.IsSheafFor (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
      (Presieve.ofArrows (pc U V) (pm f g)) := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property
  rw [Presieve.isSheafFor_iff_generate]
  exact hG.isSheafFor _ (mem_cover a b f g h)

theorem compat {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V}
    {f : U ⟶ X} {g : V ⟶ X} (hpb : IsPullback a b f g) {s : Sec G U} {t : Sec G V}
    (hst : Sec.res a s = Sec.res b t) {Z : Scheme.{0}} (gi : Z ⟶ U) (gj : Z ⟶ V) (e : gi ≫ f = gj ≫ g) :
    (G.obj.map gi.op).hom s = (G.obj.map gj.op).hom t := by
  obtain ⟨l, hl1, hl2⟩ := hpb.exists_lift gi gj e
  subst hl1 hl2
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (G.obj.map l.op).hom hst

theorem Glue_of : LateralTheory.KummerTheory.ContCut.Glue := by
  intro R _ G W U V X a b f g h
  have hS := sheafFor G a b f g h
  rw [Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨hf, hg, hpb, -⟩ := h
  refine ⟨fun z hz1 hz2 => ?_, fun s t hst => ?_⟩
  · have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g)
        (fun _ => (0 : Sec G _)) := by
      intro i j Z gi gj _
      change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
      simp
    obtain ⟨t, -, ht⟩ := hS _ hc
    have e1 := ht z (fun i => by cases i <;> assumption)
    have e2 := ht 0 (fun i => by
      change (G.obj.map _).hom 0 = 0
      simp)
    rw [e1, e2]
  · let x : ∀ i, Sec G (pc U V i) := fun i => Bool.rec (motive := fun i => Sec G (pc U V i)) t s i
    have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g) x := by
      intro i j Z gi gj e
      change (G.obj.map gi.op).hom (x i) = (G.obj.map gj.op).hom (x j)
      cases i <;> cases j
      · have : gi = gj := (cancel_mono g).1 e
        subst this; rfl
      · exact (compat G hpb hst gj gi e.symm).symm
      · exact compat G hpb hst gi gj e
      · have : gi = gj := (cancel_mono f).1 e
        subst this; rfl
    obtain ⟨z, hz, -⟩ := hS x hc
    exact ⟨z, hz true, hz false⟩

end LateralTheory.KummerTheory.GluePf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.DictPfEv
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem ev_add (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev, Cochain.add_v, Preadditive.comp_add]

theorem ev_neg (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (-α) p s h U x = -ev α p s h U x := by
  have h0 : ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← ev_add, neg_add_cancel, h0]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem val_res' (R : Type) [CommRing R] {P : PSh} {F : Shv R} (φ : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : P.obj (op U)) :
    Sec.res g ((φ.hom.app (op U)).hom (freeGen R P U x)) = (φ.hom.app (op V)).hom (freeGen R P V (P.map g.op x)) := by
  have e1 := congrArg (fun (f : ((free R).obj P).obj.obj (op U) ⟶ F.obj.obj (op V)) => f.hom (freeGen R P U x)) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
  refine e1.symm.trans (congrArg _ ?_)
  have e2 := congrArg (fun (f : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj P).obj.obj (op V)) => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at e2
  unfold freeGen
  refine e2.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_res (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) :=
  val_res' R _ V U g x

theorem free_gen_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have e := congrArg (fun (φ : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj Q).obj.obj (op U)) =>
    φ.hom (ModuleCat.freeMk (ULift.up x))) (congrArg (fun η => η.app (op U)) (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f)))
  erw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply] at e
  unfold freeGen
  refine e.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single

theorem chainsXIso_nat (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) = (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, chainsN, Functor.comp_map, ComplexShape.embeddingDownNat, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  erw [Iso.inv_hom_id_assoc]
  rfl
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_pre (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} {E' : Spc} (f : E' ⟶ E)
    (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_nat, Category.assoc]
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom y) (free_gen_map R _ U x)

theorem evLin : EvLin := fun R _ E I n =>
  ⟨fun α β p s h U x => ⟨ev_add R α β p s h U x, ev_neg R α p s h U x⟩,
   fun α p s h V U g x => ev_res R α p s h V U g x,
   fun f α p s h U x => ev_pre R f α p s h U x⟩
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem Dict_of' (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := Dict_of evLin hE hN hZ
end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.ZHomPf
noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ZHomPf

def linOf {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} ℤ) M] [Module (ULift.{1} ℤ) N]
    (f : M →+ N) : M →ₗ[ULift.{1} ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    have h : ((r.down : ℤ) : ULift.{1} ℤ) = r := by ext; simp
    simp only [RingHom.id_apply]
    rw [← h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem ZHom_of : LateralTheory.KummerTheory.BockCut.ZHom := by
  intro F G f hf
  refine ⟨⟨{ app := fun U => ModuleCat.ofHom (linOf (f U.unop)), naturality := ?_ }⟩, ?_⟩
  · intro X Y g
    ext a
    exact (hf Y.unop X.unop g.unop a).symm
  · intro U a
    rfl

end LateralTheory.KummerTheory.ZHomPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.TwExtPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwExtPf

theorem sep {M : Shv ℤ} {U : Scheme.{0}} (x y : Sec M U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated M U S hS x y (fun V g hg => hP _ g hg)

theorem TwExt_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hM : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.TwExt := by
  intro Q _ i M φ ψ h
  refine (hM ℤ φ).2.2.2 ψ fun U a => ?_
  obtain ⟨S, hS, hP⟩ := (hT Q i).1 U a
  refine sep _ _ ⟨S, hS, fun V g hg => ?_⟩
  have nφ : Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (φ.hom.naturality g.op).symm
  have nψ : Sec.res g (Sec.map ψ a) = Sec.map ψ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (ψ.hom.naturality g.op).symm
  show Sec.res g (Sec.map φ a) = Sec.res g (Sec.map ψ a)
  rw [nφ, nψ]
  have ha : Sec.res g a = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = c • LateralTheory.KummerTheory.BockCut.genZ i ζ := hP V g hg
  rcases ha with h0 | ⟨ζ, c, hc⟩
  · have e : (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = 0 := h0
    rw [e]; simp only [Sec.map, map_zero]
  · rw [hc]; have hh := h V ζ; simp only [Sec.map] at hh ⊢; rw [map_nsmul, map_nsmul, hh]

end LateralTheory.KummerTheory.TwExtPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.DictZeroPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DZ

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have e := LateralTheory.KummerTheory.AW.ev_add (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rw [add_zero] at e
  simpa using e.symm

end LateralTheory.KummerTheory.DZ

open LateralTheory.KummerTheory.DZ LateralTheory.EtaleFoundations in
theorem LateralTheory.KummerTheory.DictZero_of : LateralTheory.KummerTheory.DictZero := by
  intro R _ I X n α hα
  refine ⟨?_, ?_⟩
  · rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n + 1) rfl α.1 n (n + 1) (by simp) (by simp) X (𝟙 X), Cocycle.δ_eq_zero]
    exact ev_zero' R _ _ _ _ _
  · rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α (n - 1) (by omega)]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 (n - 1) (by simp) X (𝟙 X), ?_⟩
      rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n) (by omega) β (n - 1) n (by simp) (by simp) X (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data R (a0 X I (n - 1) y) (etaleSimplicialCochain_scheme_section_extension_naturality X I (n - 1) y)
      refine ⟨γ, LateralTheory.KummerTheory.AW.ev_ext _ _ ?_⟩
      intro p s h U x
      cases p with
      | zero =>
        obtain rfl : s = n := by omega
        rw [LateralTheory.KummerTheory.AW.ev_delta_zero (m := s) (by omega) γ (s - 1) s (by simp) h U x, hγ, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        refine (map_res _ _ _).trans ?_
        exact (congrArg (Sec.res _) hy).trans (LateralTheory.KummerTheory.AW.ev_res α.1 0 s _ x (𝟙 X))
      | succ p =>
        rw [hα p s h U x, LateralTheory.KummerTheory.AW.ev_delta_succ (m := n) (by omega) γ p (-((p + 1 : ℕ) : ℤ) + (n - 1)) s rfl h U x]
        simp only [hγ]
        cases p with
        | zero =>
          obtain rfl : s = n - 1 := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.PlaceExPf
noncomputable section

namespace LateralTheory.KummerTheory

def PlaceGood (k K : Type) [Field k] [Field K] [Algebra k K] (A : LocalSubring K) : Prop :=
  (∀ c : k, algebraMap k K c ∈ A.toSubring) ∧
    ∀ a ∈ A.toSubring, ∃ c : k, a = algebraMap k K c ∨ (a - algebraMap k K c)⁻¹ ∉ A.toSubring

def PlaceZorn : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K],
  ∃ A : LocalSubring K, PlaceGood k K A ∧ ∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A

def PlaceStep : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → (∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A) →
    ∀ x : K, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring

theorem PlaceEx_of (h1 : PlaceZorn) (h2 : PlaceStep) : PlaceEx := by
  intro k K _ _ _ _ _
  obtain ⟨A, hA, hmax⟩ := h1 k K
  have hv := h2 k K A hA hmax
  let T : ValuationSubring K := ⟨A.toSubring, hv⟩
  let σ : k →+* T := (algebraMap k K).codRestrict T (fun c => hA.1 c)
  refine ⟨T, σ, fun x => rfl, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hA.2 a a.2
  refine ⟨c, ?_⟩
  simp only [RingHom.comp_apply]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  have hK : ((σ c : K) - (a : K)) * (w : K) = 1 := by
    have := congrArg (fun z : T => (z : K)) hw
    simpa using this
  rcases hc with h | h
  · have : (σ c : K) - (a : K) = 0 := by rw [h]; simp [σ]
    rw [this, zero_mul] at hK; exact zero_ne_one hK
  · apply h
    have hinv : ((σ c : K) - (a : K))⁻¹ = (w : K) := inv_eq_of_mul_eq_one_right hK
    have : ((a : K) - algebraMap k K c)⁻¹ = -(w : K) := by
      rw [← hinv, ← inv_neg, neg_sub]; rfl
    rw [this]; exact T.neg_mem _ w.2

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.BcHomIsPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.BCPf
open LateralTheory.KummerTheory.ContCut

@[reassoc] theorem bcHom_fst {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.fst p (Spec.map s) = pullback.fst r (Spec.map s) ≫ f := by
  unfold bcHom pullback.map; exact pullback.lift_fst _ _ _

theorem bcHom_snd {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.snd p (Spec.map s) = pullback.snd r (Spec.map s) := by
  unfold bcHom pullback.map; rw [pullback.lift_snd, Category.comp_id]

theorem bcHom_isPullback {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    IsPullback (bcHom f p r e s) (pullback.fst r (Spec.map s)) (pullback.fst p (Spec.map s)) f := by
  have big : IsPullback (bcHom f p r e s ≫ pullback.snd p (Spec.map s)) (pullback.fst r (Spec.map s))
      (Spec.map s) (f ≫ p) := by
    rw [bcHom_snd, e]; exact (IsPullback.of_hasPullback r (Spec.map s)).flip
  exact IsPullback.of_right big (bcHom_fst f p r e s) (IsPullback.of_hasPullback p (Spec.map s)).flip

theorem bcHom_open {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) [IsOpenImmersion f] : IsOpenImmersion (bcHom f p r e s) :=
  MorphismProperty.of_isPullback (bcHom_isPullback f p r e s).flip ‹_›

theorem bcHom_range {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) (x : ↥(pullback p (Spec.map s))) (hx : pullback.fst p (Spec.map s) x ∈ Set.range f) :
    x ∈ Set.range (bcHom f p r e s) := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (bcHom_isPullback f p r e s) x u hu.symm
  exact ⟨q, hq⟩

theorem BC_of : BC := by
  intro R A s W U V X a b f g p pU pV pW ea eb ef eg h
  obtain ⟨hf, hg, hpb, hcov⟩ := h
  refine ⟨bcHom_open f p pU ef s, bcHom_open g p pV eg s, ?_, ?_⟩
  · have sq1 : IsPullback (pullback.fst pW (Spec.map s)) (bcHom b pV pW eb s) b (pullback.fst pV (Spec.map s)) :=
      (bcHom_isPullback b pV pW eb s).flip
    have big0 := sq1.paste_horiz hpb
    have big : IsPullback (bcHom a pU pW ea s ≫ pullback.fst pU (Spec.map s)) (bcHom b pV pW eb s) f
        (bcHom g p pV eg s ≫ pullback.fst p (Spec.map s)) := by
      rw [bcHom_fst, bcHom_fst]; exact big0
    refine IsPullback.of_right big ?_ (bcHom_isPullback f p pU ef s).flip
    apply pullback.hom_ext
    · simp only [Category.assoc, bcHom_fst, bcHom_fst_assoc]; rw [hpb.w]
    · simp only [Category.assoc, bcHom_snd]
  · intro x
    rcases hcov (pullback.fst p (Spec.map s) x) with hx | hx
    · exact Or.inl (bcHom_range f p pU ef s x hx)
    · exact Or.inr (bcHom_range g p pV eg s x hx)

end LateralTheory.KummerTheory.BCPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.NatLESPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex Pretriangulated GlobalTheory.EtC

namespace LateralTheory.KummerTheory.NatLESPf
open LateralTheory.KummerTheory.BockCut

theorem exact_transport {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] (eA : A ≃+ A') (eB : B ≃+ B') (eC : C ≃+ C')
    (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
    (hf : ∀ x, eB (f x) = f' (eA x)) (hg : ∀ x, eC (g x) = g' (eB x)) (h : Function.Exact f' g') :
    Function.Exact f g := by
  intro y
  constructor
  · intro hy
    have : g' (eB y) = 0 := by rw [← hg, hy, map_zero]
    obtain ⟨x', hx'⟩ := (h (eB y)).1 this
    refine ⟨eA.symm x', eB.injective ?_⟩
    rw [hf, AddEquiv.apply_symm_apply, hx']
  · rintro ⟨x, rfl⟩
    apply eC.injective
    rw [hg, hf, map_zero]
    exact (h _).2 ⟨_, rfl⟩

theorem NatLES_of (hD : DerDict) : NatLES := by
  intro R _ K
  letI := HasDerivedCategory.standard (Shv R)
  obtain ⟨e, he⟩ := hD R K
  let F := preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj K))
  have hpost : ∀ {X Y : Shv R} (φ : X ⟶ Y) (n : ℤ) (x : HK R K X n),
      e Y n (HK.post R K φ n x) = (F.shift n).map ((DerivedCategory.singleFunctor (Shv R) 0).map φ) (e X n x) := by
    intro X Y φ n x
    rw [he]; rfl
  let d : ∀ (S : ShortComplex (Shv R)), S.ShortExact → ∀ n : ℤ, HK R K S.X₃ n →+ HK R K S.X₁ (n + 1) :=
    fun S hS n => (e S.X₁ (n + 1)).symm.toAddMonoidHom.comp
      ((F.homologySequenceδ hS.singleTriangle n (n + 1) rfl).hom.comp (e S.X₃ n).toAddMonoidHom)
  have hd : ∀ (S : ShortComplex (Shv R)) (hS : S.ShortExact) (n : ℤ) (x : HK R K S.X₃ n),
      e S.X₁ (n + 1) (d S hS n x) = F.homologySequenceδ hS.singleTriangle n (n + 1) rfl (e S.X₃ n x) := by
    intro S hS n x
    exact AddEquiv.apply_symm_apply _ _
  refine ⟨d, fun S hS n => ⟨?_, ?_, ?_⟩, ?_⟩
  · have := F.homologySequence_exact₂ _ hS.singleTriangle_distinguished n
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₁ n) (e S.X₂ n) (e S.X₃ n) _ _ _ _ (hpost _ n) (hpost _ n) this
  · have := F.homologySequence_exact₃ _ hS.singleTriangle_distinguished n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₂ n) (e S.X₃ n) (e S.X₁ (n + 1)) _ _ _ _ (hpost _ n) (hd S hS n) this
  · have := F.homologySequence_exact₁ _ hS.singleTriangle_distinguished n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₃ n) (e S.X₁ (n + 1)) (e S.X₂ (n + 1)) _ _ _ _ (hd S hS n)
      (hpost _ (n + 1)) this
  · intro S T hS hT φ n x
    apply (e T.X₁ (n + 1)).injective
    rw [hpost, hd, hd, hpost]
    have := F.homologySequenceδ_naturality (φ := ShortComplex.ShortExact.singleTriangle.map hS hT φ) (n₀ := n) (n₁ := n + 1) (h := rfl)
    have h2 := ConcreteCategory.congr_hom this
      (show ((F.shift n).obj hS.singleTriangle.obj₃ : Type _) from e S.X₃ n x)
    exact h2.symm
end LateralTheory.KummerTheory.NatLESPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.RestrResPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RestrResPf

instance restrAdditive (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) : (restr φ).Additive where
  map_add {X Y f g} := by
    ext U x
    rfl

theorem restr_exact (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S)
    (C : ShortComplex (Shv S)) (h : C.Exact) : (C.map (restr φ)).Exact :=
  (hex R (C.map (restr φ))).2 (fun U b hb => (hex S C).1 h U b hb)

theorem restr_preservesHomology (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (R S : Type) [CommRing R] [CommRing S]
    (φ : R →+* S) : (restr φ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (restr_exact hex R S φ)

theorem single_key (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F).f 0 =
    (restr φ).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp

theorem RestrRes_of (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) :
    LateralTheory.KummerTheory.BockCut.RestrRes := by
  intro R S _ _ φ F
  haveI := restr_preservesHomology hex R S φ
  let M := (restr φ).mapHomologicalComplex (ComplexShape.up ℤ)
  let T : Cx R := M.obj (res S F)
  let σ : SemiMap (res S F) T :=
    { app := fun U s => AddMonoidHom.mk' (fun a => (show Sec (T.X s) U from a)) (fun _ _ => rfl)
      nat := fun _ _ _ => rfl
      comm := fun _ _ _ _ => rfl }
  haveI : QuasiIso (resAug F) := (hres S F).2.2.2.1
  have hq2 : QuasiIso (M.map (resAug F)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (resAug F) (restr φ)
  let e := (HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F
  have hq1 : QuasiIso e := @quasiIso_of_isIso _ _ _ _ _ _ _ e inferInstance (fun _ => inferInstance) (fun _ => inferInstance)
  let ε : sgl ((restr φ).obj F) ⟶ T := e ≫ M.map (resAug F)
  refine ⟨T, σ, ε, ?_, fun U s => Function.bijective_id, ?_⟩
  · first
      | exact quasiIso_comp (hφ := hq1) (hφ' := hq2)
      | exact @quasiIso_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq1 hq2
  · intro U a
    have h2 : Sec.map (e.f 0) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv
        (show Sec ((restr φ).obj F) U from a)) =
        Sec.map ((restr φ).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv)
        (show Sec ((restr φ).obj F) U from a) :=
      congrArg (fun f => Sec.map f (show Sec ((restr φ).obj F) U from a)) (single_key R S φ F)
    change Sec.map ((restr φ).map ((resAug F).f 0)) (Sec.map (e.f 0)
      (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv
        (show Sec ((restr φ).obj F) U from a))) = _
    rw [h2]
    rfl

end LateralTheory.KummerTheory.RestrResPf
end

section -- merged from Development.EtaleCohomology.KummerTheory.LimOfIso
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AffPf
open LateralTheory.KummerTheory.ContCut

theorem lim_of_iso {J : Type} [SmallCategory J] {K : Type 1} [Category.{0} K] {G G' : K ⥤ AddCommGrpCat.{1}}
    (e : G ≅ G') {D : J ⥤ K} (c : Cocone D) (h : Lim G c) : Lim G' c := by
  have nat : ∀ {a b : K} (f : a ⟶ b) (z : G.obj a), (G'.map f).hom ((e.hom.app a).hom z) = (e.hom.app b).hom ((G.map f).hom z) := by
    intro a b f z
    have := congrArg (fun φ => φ.hom z) (e.hom.naturality f)
    simpa using this.symm
  have inv : ∀ (a : K) (z : G'.obj a), (e.hom.app a).hom ((e.inv.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.inv_hom_id_app a)
    simpa using this
  have inv' : ∀ (a : K) (z : G.obj a), (e.inv.app a).hom ((e.hom.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.hom_inv_id_app a)
    simpa using this
  have natc : ∀ (j : J) (z : G.obj (D.obj j)), (G'.map (c.ι.app j)).hom ((e.hom.app (D.obj j)).hom z) =
      (e.hom.app c.pt).hom ((G.map (c.ι.app j)).hom z) := fun j z => nat (c.ι.app j) z
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := h.1 ((e.inv.app c.pt).hom x)
    refine ⟨j, (e.hom.app (D.obj j)).hom y, ?_⟩
    rw [natc, hy, inv]
  · have h0 : (G.map (c.ι.app j)).hom ((e.inv.app (D.obj j)).hom y) = 0 := by
      have h1 := natc j ((e.inv.app (D.obj j)).hom y)
      rw [inv, hy] at h1
      have h2 := congrArg (e.inv.app c.pt).hom h1
      rw [inv', map_zero] at h2
      exact h2.symm
    obtain ⟨k, f, hf⟩ := h.2 j _ h0
    refine ⟨k, f, ?_⟩
    have h1 := nat (D.map f) ((e.inv.app (D.obj j)).hom y)
    rw [inv, hf, map_zero] at h1
    exact h1

theorem Aff_of (hR : AffRing) : Aff := by
  intro hb q X _ R p hq J _ _ D c hc n i
  obtain ⟨T, ⟨e⟩, hmap, hcol⟩ := hR p
  obtain ⟨hT⟩ := hcol c hc
  have unit : ∀ A, IsUnit ((q : ℕ) : T.obj A) := by
    intro A
    obtain ⟨φ⟩ := hmap A
    simpa using hq.map φ.hom
  have key : Lim (T ⋙ Scheme.Spec.rightOp ⋙ Hf (tw q i) n) c := by
    have hB := hb q (D ⋙ T) (T.mapCocone c) hT n i
    refine ⟨fun x => ?_, fun j y hy => ?_⟩
    · obtain ⟨j, y, hy⟩ := hB.1 x (unit c.pt)
      exact ⟨j, y, hy⟩
    · obtain ⟨k, f, hf⟩ := hB.2 j y (unit (D.obj j)) hy
      exact ⟨k, f, hf⟩
  exact lim_of_iso (Functor.isoWhiskerRight e (Hf (tw q i) n)).symm c key

end LateralTheory.KummerTheory.AffPf

end
end

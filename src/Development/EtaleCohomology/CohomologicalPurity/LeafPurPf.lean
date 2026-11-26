module

public import Development.EtaleCohomology.CohomologicalPurity.LeafGysinPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPurPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurPf

def actH (q : ℕ) {P : Arrow Spc} (n : ℤ) {m i j : ℤ} (b : Hs q P m j) :
    Ht q P.right n i →+ Hs q P (n + m) (i + j) where
  toFun a := Hs.act q a b
  map_zero' := by
    apply Subtype.ext
    simp [Hs.act, Hs.proj]
  map_add' x y := by
    apply Subtype.ext
    simp only [Hs.act, Hs.proj, map_add (f := _), AddMonoidHom.add_apply, AddSubgroup.coe_add]
    abel

theorem bij_comp {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C] {f : B →+ C} {g : A →+ B}
    (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (f.comp g) := by
  rw [AddMonoidHom.coe_comp]; exact hf.comp hg

def purT {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) (P : SP d) (n i : ℤ) :
    Ht q (sch.obj P.Z) n i →+ Hs q (opn P.U) (n + 2 * d) (i + d) := by
  classical
  exact if h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) then
    haveI : NeZero q := ⟨h.1⟩
    ((AddEquiv.ofBijective _ (((T P).ok q h.2).2.2.1 (n + 2 * d) (i + d))).symm.toAddMonoidHom.comp
      (actH q (P := abv P.U (T P).π) n (i := i) (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)))).comp
      ((AddEquiv.ofBijective _ (((T P).ok q h.2).1 i n)).symm.toAddMonoidHom.comp
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n))
  else 0

theorem purT_bij {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) : Function.Bijective (purT T q P n i) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  unfold purT
  rw [dite_eq_left h]
  refine bij_comp (bij_comp (AddEquiv.bijective _) ?_) (bij_comp (AddEquiv.bijective _) (((T P).ok q hq).2.1 i n))
  exact ((T P).ok q hq).2.2.2 n i

def TubeRef {d : ℕ} (T : ∀ P : SP d, Tube P) : Prop := ∀ (P' P : SP d) (φ : P'.Hom P),
  ∃ (T' : Tube P') (a : T'.E ⟶ (T P').E) (b : T'.E ⟶ (T P).E), a ≫ (T P').π = T'.π ∧ b ≫ (T P).π = T'.π ≫ sch.map φ.f

end PurPf

open PurPf

def EtalePurityNaturality : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P), TubeRef T →
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (purT T q P n i a) = purT T q P' n i (pull _ (sch.map φ.g) _ _ a)

def EtalePurityProjection : Prop := Hyp → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    (Hs.fgt q (opn P.U) (n + m + 2 * d) (i + j + d) (purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)) :
      Ht q (sch.obj P.X) (n + m + 2 * d) (i + j + d)) =
      (cup q a (Hs.fgt q (opn P.U) (m + 2 * d) (j + d) (purT T q P m j b) : Ht q (sch.obj P.X) (m + 2 * d) (j + d))).cast
        (by ring) (by ring)

def EtalePurityReduction : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    (purT T r P n i (red q r _ _ _ a)).1 = red q r _ _ _ (purT T q P n i a).1

theorem EtalePurity_of_parts (hCl : LeafCl) (hTube : LeafTube) (hN : EtalePurityNaturality) (hP : EtalePurityProjection) (hR : EtalePurityReduction) :
    LeafPur := by
  intro hH d
  obtain ⟨T, hT⟩ := hTube hH d
  exact ⟨purT T, fun q _ P hq =>
    ⟨purT_bij T q P hq, hN hH hCl d T hT q P hq, hP hH d T q P hq, hR hH hCl d T q P hq⟩⟩

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

section Pf
variable {R : Type} [CommRing R] {A B D : Cx R} {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R}

theorem pb_δ (f : A ⟶ B) {n m : ℤ} (c : Cochain B I n) : pb f (δ n m c) = δ n m (pb f c) := by
  simp [pb]

theorem pb_sub (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c - c') = pb f c - pb f c' := by
  simp [pb]

theorem pb_zero (f : A ⟶ B) {n : ℤ} : pb f (0 : Cochain B I n) = 0 := by
  simp [pb]

theorem pb_add (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c + c') = pb f c + pb f c' := by
  simp [pb]

theorem Tri.sub {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a - a') (c - c') (b - b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_sub, h1, h1', Cocycle.coe_sub]
  · rw [Cocycle.coe_sub, pb_sub, h2, h2', δ_sub]
  · rw [Cocycle.coe_sub, pb_sub, h3, h3', sub_zero]

theorem Tri.add {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a + a') (c + c') (b + b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_add, h1, h1', Cocycle.coe_add]
  · rw [Cocycle.coe_add, pb_add, h2, h2', δ_add]
  · rw [Cocycle.coe_add, pb_add, h3, h3', add_zero]

theorem Good.mk_zero (hG : Good i l r I) {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (ha : a ∈ coboundaries A I n) : CohomologyClass.mk b = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨f, hf⟩ := (mem_coboundaries_iff a (n - 1) (by omega)).1 ha
  obtain ⟨g, hg⟩ := hG.surj (n - 1) f
  obtain ⟨e, he1, he2⟩ := hG.glue n (c - δ (n - 1) n g) 0 (by
    rw [pb_sub, pb_δ, hg, hf, h1, sub_self, pb_zero])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff b n rfl]
  refine ⟨e, hG.ext (n + 1) _ _ ?_ ?_⟩
  · rw [pb_δ, he1, h2, δ_sub, δ_δ, sub_zero]
  · rw [pb_δ, he2, h3, δ_zero]

theorem Good.mk_eq (hG : Good i l r I) {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n}
    {b b' : Cocycle D I (n + 1)} (h : Tri i l r a c b) (h' : Tri i l r a' c' b')
    (ha : a - a' ∈ coboundaries A I n) : CohomologyClass.mk b = CohomologyClass.mk b' := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
  exact hG.mk_zero (h.sub h') ha

theorem tri_zero {n : ℤ} : Tri i l r (0 : Cocycle A I n) 0 (0 : Cocycle D I (n + 1)) :=
  ⟨by rw [pb_zero, Cocycle.coe_zero], by rw [Cocycle.coe_zero, pb_zero, δ_zero], by rw [Cocycle.coe_zero, pb_zero]⟩

theorem Tri.ker {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)} (h : Tri i l r a c b) :
    CohomologyClass.mk b ∈ (hpb r I (n + 1)).ker := by
  rw [AddMonoidHom.mem_ker, hpb, cpre_mk, CohomologyClass.mk_eq_zero_iff]
  have : zcomp (Cocycle.ofHom r) b (zero_add (n + 1)) = 0 := Cocycle.ext (by
    change pb r b.1 = _
    rw [h.2.2, Cocycle.coe_zero])
  rw [this]
  exact zero_mem _

theorem LeafDelta_of : LeafDelta := by
  intro R _ A B D i l r I hG n
  choose c b hcb using fun a : Cocycle A I n => hG.tri a
  let F : Cocycle A I n →+ (hpb r I (n + 1)).ker :=
    AddMonoidHom.mk' (fun a => ⟨CohomologyClass.mk (b a), (hcb a).ker⟩) (fun a a' => by
      apply Subtype.ext
      change CohomologyClass.mk (b (a + a')) = CohomologyClass.mk (b a) + CohomologyClass.mk (b a')
      rw [← CohomologyClass.mk_add]
      exact hG.mk_eq (hcb _) ((hcb a).add (hcb a')) (by rw [sub_self]; exact zero_mem _))
  refine ⟨CohomologyClass.descAddMonoidHom F ?_, ?_⟩
  · intro a ha
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    change CohomologyClass.mk (b a) = 0
    rw [← CohomologyClass.mk_zero D I (n + 1)]
    exact hG.mk_eq (hcb a) tri_zero (by rw [sub_zero]; exact ha)
  · intro a c' b' h
    change CohomologyClass.mk (b a) = _
    exact hG.mk_eq (hcb a) h (by rw [sub_self]; exact zero_mem _)

end Pf
end LateralTheory.CohomologicalPurity.Bd
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.FreePMapMk
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

namespace GenPf

variable (R : Type) [CommRing R]

abbrev mk {P : PSh} {U : Scheme.{0}} (x : P.obj (op U)) : ((freeP R).obj P).obj (op U) :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj (op U))) (ULift.up x)

theorem freePresheaf_obj_map_mk (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (mk R x) = mk R (P.map g.op x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

theorem freePresheaf_map_app_mk {P P' : PSh} (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (mk R x) = mk R (f.app (op U) x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

theorem part1 (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom k (mk R x))
    ((toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_obj_map_mk] at h
  exact h.symm

theorem part2 (P P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom (NatTrans.app k (op U)) (mk R x))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_map_app_mk] at h
  exact h.symm

def adjE (P : PSh) (G : Shv R) : ((free R).obj P ⟶ G) ≃ ((freeP R).obj P ⟶ G.obj) :=
  (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv ((freeP R).obj P) G

theorem adjE_apply (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) :
    adjE R P G φ = toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P) ≫ φ.hom :=
  Adjunction.homEquiv_unit _ _ _ _

theorem adjE_gen (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    ((adjE R P G φ).app (op U)).hom (mk R x) = Sec.map φ (freeGen R P U x) := by
  rw [adjE_apply]; rfl

theorem part3 (P : PSh) (G : Shv R) (φ ψ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) :
    φ = ψ := by
  apply (adjE R P G).injective
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨U⟩ := U
  apply ModuleCat.free_hom_ext
  rintro ⟨y⟩
  exact (adjE_gen R P G φ U y).trans ((h U y).trans (adjE_gen R P G ψ U y).symm)

def descP (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun y => t U.unop (ULift.down y))
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    obtain ⟨U⟩ := U
    obtain ⟨V⟩ := V
    rintro ⟨y⟩
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    erw [freePresheaf_obj_map_mk R P g.unop y, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (ht g.unop y).symm

theorem freePresheafDesc_app_mk (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((descP R P G t ht).app (op U)).hom (mk R x) = t U x := by
  simp only [descP]
  exact ModuleCat.freeDesc_apply _ _

theorem part4 (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x := by
  refine ⟨(adjE R P G).symm (descP R P G t ht), fun U x => ?_⟩
  rw [← adjE_gen, Equiv.apply_symm_apply, freePresheafDesc_app_mk]

end GenPf

theorem LeafGen_of : LeafGen := by
  intro R _ P
  exact ⟨fun g x => GenPf.part1 R P g x, fun P' f U x => GenPf.part2 R P P' f U x,
    fun G φ ψ h => GenPf.part3 R P G φ ψ h, fun G t ht => GenPf.part4 R P G t ht⟩

end LateralTheory.CohomologicalPurity.Bd
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafImgPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd
namespace ImgPf

variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}
  (T0 : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s))

def T' (E : Spc) (p s : ℤ) : (((chains S).obj E).X p ⟶ I.X s) →+ (((chains R).obj E).X p ⟶ J.X s) :=
  if h : -(((-p).toNat : ℕ) : ℤ) = p then
    { toFun := fun φ => (((chains R).obj E).XIsoOfEq h).inv ≫ (chainsXIso R E _).hom ≫
        T0 _ s ((chainsXIso S E _).inv ≫ (((chains S).obj E).XIsoOfEq h).hom ≫ φ)
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add] }
  else 0

theorem T'_eq (E : Spc) (k : ℕ) (s : ℤ) (φ : ((chains S).obj E).X (-(k : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s φ = (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
  have key : ∀ (k' : ℕ) (h' : -(k' : ℤ) = -(k : ℤ)), (((chains R).obj E).XIsoOfEq h').inv ≫ (chainsXIso R E k').hom ≫
      T0 _ s ((chainsXIso S E k').inv ≫ (((chains S).obj E).XIsoOfEq h').hom ≫ φ) =
      (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
    intro k' h'
    obtain rfl : k' = k := by omega
    simp [HomologicalComplex.XIsoOfEq_rfl]
  unfold T'
  rw [dite_eq_left (by simp)]
  exact key _ _

theorem T'_pos (E : Spc) (p s : ℤ) (hp : 0 < p) : T' T0 E p s = 0 := by
  unfold T'
  rw [dite_eq_right (by omega)]

theorem T'_comp_d (E : Spc) (p s t : ℤ) (φ : ((chains S).obj E).X p ⟶ I.X s)
    (hd : ∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T0 P t (φ ≫ I.d s t) = T0 P s φ ≫ J.d s t) :
    T' T0 E p t (φ ≫ I.d s t) = T' T0 E p s φ ≫ J.d s t := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [T'_eq, T'_eq, ← Category.assoc, hd, Category.assoc]
  · rw [T'_pos T0 E p t hp, T'_pos T0 E p s hp]
    simp

theorem T'_free (E E' : Spc) (k k' : ℕ) (s : ℤ) {ι : Type} [Fintype ι] (c : ι → ℤ)
    (u : ι → (E.obj (op (SimplexCategory.mk k)) ⟶ E'.obj (op (SimplexCategory.mk k'))))
    (gS : ((chains S).obj E).X (-(k : ℤ)) ⟶ ((chains S).obj E').X (-(k' : ℤ)))
    (gR : ((chains R).obj E).X (-(k : ℤ)) ⟶ ((chains R).obj E').X (-(k' : ℤ)))
    (hS : gS = (chainsXIso S E k).hom ≫ (∑ i, c i • (free S).map (u i)) ≫ (chainsXIso S E' k').inv)
    (hR : gR = (chainsXIso R E k).hom ≫ (∑ i, c i • (free R).map (u i)) ≫ (chainsXIso R E' k').inv)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ)
    (φ : ((chains S).obj E').X (-(k' : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s (gS ≫ φ) = gR ≫ T' T0 E' (-(k' : ℤ)) s φ := by
  rw [T'_eq, T'_eq, hS, hR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul, hn]

theorem T'_d (E : Spc) (p p' s : ℤ) (h : p + 1 = p') (φ : ((chains S).obj E).X p' ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).obj E).d p p' ≫ φ) = ((chains R).obj E).d p p' ≫ T' T0 E p' s φ := by
  rcases lt_or_ge p 0 with hp | hp
  · obtain ⟨k, rfl, rfl⟩ : ∃ k : ℕ, p = -((k + 1 : ℕ) : ℤ) ∧ p' = -(k : ℤ) := ⟨(-p - 1).toNat, by omega, by omega⟩
    refine T'_free T0 E E k.succ k s (fun i : Fin (k + 2) => ((-1 : ℤ) ^ (i : ℕ))) (fun i => E.δ i) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extend_d_eq ((chainsN S).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
    · refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
  · have hz : ((chains S).obj E).d p p' = 0 := by
      apply (HomologicalComplex.isZero_extend_X _ _ p' ?_).eq_of_tgt
      intro i hi
      change -(i : ℤ) = p' at hi
      omega
    rw [hz, T'_pos T0 E p' s (by omega)]
    simp

theorem T'_map (E E' : Spc) (f : E ⟶ E') (p s : ℤ) (φ : ((chains S).obj E').X p ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).map f).f p ≫ φ) = ((chains R).map f).f p ≫ T' T0 E' p s φ := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    refine T'_free T0 E E' k k s (fun _ : Unit => 1) (fun _ => f.app _) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extendMap_f ((chainsN S).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
    · refine (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
  · rw [T'_pos T0 E p s hp, T'_pos T0 E' p s hp]
    simp

def TC (E : Spc) (n : ℤ) : Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n where
  toFun α := Cochain.mk fun p q h => T' T0 E p q (α.v p q h)
  map_zero' := Cochain.ext _ _ fun p q h => by simp
  map_add' α β := Cochain.ext _ _ fun p q h => by simp [Cochain.add_v]

theorem TC_v (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p q : ℤ) (h : p + n = q) :
    (TC T0 E n α).v p q h = T' T0 E p q (α.v p q h) :=
  Cochain.mk_v (fun p q h => T' T0 E p q (α.v p q h)) p q h

end ImgPf

open ImgPf in
theorem LeafImg_of (hI : LeafImgHom) : LeafImg := by
  intro S R _ _ I J ρ
  obtain ⟨T0, hgen, hd, hn⟩ := hI S R I J ρ
  refine ⟨fun E n => TC T0 E n, ?_, ?_, ?_⟩
  · intro E n α p s h U x
    unfold ev
    rw [TC_v, T'_eq, Iso.inv_hom_id_assoc]
    exact hgen _ _ _ U x
  · intro E n m α
    by_cases hnm : n + 1 = m
    · refine Cochain.ext _ _ fun p q hpq => ?_
      rw [TC_v, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
        map_add, Units.smul_def, Units.smul_def, map_zsmul, T'_comp_d T0 E _ _ _ _ hd, TC_v, TC_v,
        T'_d T0 E p (p + 1) q rfl _ hn]
    · rw [δ_shape n m hnm, δ_shape n m hnm, map_zero]
  · intro E E' f n α
    refine Cochain.ext _ _ fun p q hpq => ?_
    simp only [pb, TC_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    exact T'_map T0 E E' f p q _ hn

end LateralTheory.CohomologicalPurity.Bd
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfMono
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfCone
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem sqw {R : Type} [CommRing R] {K L K' L' : Cx R} {f : K ⟶ L} {f' : K' ⟶ L'} {a : K ⟶ K'} {b : L ⟶ L'}
    (comm : f ≫ b = a ≫ f') (n : ℤ) : f.f n ≫ b.f n = a.f n ≫ f'.f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, comm]

theorem chains_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map P'.hom ≫ (chains R).map φ.right = (chains R).map φ.left ≫ (chains R).map P.hom := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ).symm

def coneMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    CochainComplex.mappingCone ((chains R).map P'.hom) ⟶ CochainComplex.mappingCone ((chains R).map P.hom) :=
  CochainComplex.mappingCone.map _ _ ((chains R).map φ.left) ((chains R).map φ.right) (chains_sq R φ)

def LeafConeQI : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → QuasiIso (coneMap (ZMod q) φ)

def LeafHsRel : Prop := A1 → ∀ (q : ℕ) (i : ℤ), ∃ e : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
    (Hs q P n i ≃+ Hrel (ZMod q) P.hom (tw q i) n),
  ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom) (n : ℤ) (x : Hs q P n i),
    e P' n h' (Hs.pull q φ n i x) = HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (e P n h x)

def LeafChainsMono : Prop := ∀ (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E), Mono f → ∀ n : ℤ, Mono (((chains R).map f).f n)

def LeafCokIso : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (chains_sq (ZMod q) φ) n))

def LeafConeCok : Prop := ∀ (R : Type) [CommRing R] {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L')
  (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f'), (∀ n, Mono (f.f n)) → (∀ n, Mono (f'.f n)) →
  (∀ n, IsIso (cokernel.map _ _ _ _ (sqw comm n))) → QuasiIso (CochainComplex.mappingCone.map f f' a b comm)

theorem leafExcSp_of (hQ : LeafConeQI) (hR : LeafHsRel) : LeafExcSp := by
  intro h1 q P' P φ hpb hc n i
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  obtain ⟨e, he⟩ := hR h1 q i
  have := hQ q φ hpb hc
  have hb : Function.Bijective (HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n) := h1 (ZMod q) _ (tw q i) n
  have : (Hs.pull q φ n i : Hs q P n i → Hs q P' n i) =
      (e P' n hm').symm ∘ HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n ∘ e P n hm := by
    funext x
    simp [← he P' P φ hm' hm n x]
  rw [this]
  exact (e P' n hm').symm.bijective.comp (hb.comp (e P n hm).bijective)

theorem leafConeQI_of (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) : LeafConeQI := by
  intro q P' P φ hpb hc
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  exact hC (ZMod q) _ _ _ _ (chains_sq (ZMod q) φ) (hM _ _ hm') (hM _ _ hm) (hK q φ hpb hc)

theorem leafExcSp_of' (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) (hR : LeafHsRel) : LeafExcSp :=
  leafExcSp_of (leafConeQI_of hM hK hC) hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

open GlobalTheory.EtC in
theorem leafConeCok : LeafConeCok := by
  intro R _ K L K' L' f f' a b comm hf hf' hi
  have hm : Mono f := HomologicalComplex.mono_of_mono_f _ hf
  have hm' : Mono f' := HomologicalComplex.mono_of_mono_f _ hf'
  let S₁ := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let S₂ := ShortComplex.mk f' (cokernel.π f') (cokernel.condition f')
  have h₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) hm inferInstance
  have h₂ : S₂.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f')) hm' inferInstance
  let τ : S₁ ⟶ S₂ := { τ₁ := a, τ₂ := b, τ₃ := cokernel.map f f' a b comm, comm₁₂ := comm.symm, comm₂₃ := by simp [S₁, S₂] }
  have iso3 : IsIso (cokernel.map f f' a b comm) := by
    have : ∀ n, IsIso ((cokernel.map f f' a b comm).f n) := by
      intro n
      have e₁ := (h₁.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      have e₂ := (h₂.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      let i₁ : cokernel (f.f n) ≅ (cokernel f).X n := (colimit.isColimit _).coconePointUniqueUpToIso e₁
      let i₂ : cokernel (f'.f n) ≅ (cokernel f').X n := (colimit.isColimit _).coconePointUniqueUpToIso e₂
      have key : (cokernel.map f f' a b comm).f n = i₁.inv ≫ cokernel.map _ _ _ _ (sqw comm n) ≫ i₂.hom := by
        rw [Iso.eq_inv_comp]
        refine (cancel_epi (cokernel.π (f.f n))).1 ?_
        have p₁ : cokernel.π (f.f n) ≫ i₁.hom = (cokernel.π f).f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₁ WalkingParallelPair.one
        have p₂ : cokernel.π (f'.f n) ≫ i₂.hom = (cokernel.π f').f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₂ WalkingParallelPair.one
        rw [← Category.assoc, p₁, cokernel.π_desc_assoc, Category.assoc, p₂, ← HomologicalComplex.comp_f,
          ← HomologicalComplex.comp_f, cokernel.π_desc]
      rw [key]; infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have q1 := CochainComplex.mappingCone.quasiIso_descShortComplex h₁
  have q2 := CochainComplex.mappingCone.quasiIso_descShortComplex h₂
  have e := CochainComplex.mappingCone.map_descShortComplex S₁ S₂ τ
  have : QuasiIso (CochainComplex.mappingCone.map f f' a b comm ≫ CochainComplex.mappingCone.descShortComplex S₂) := by
    rw [show CochainComplex.mappingCone.map f f' a b comm = CochainComplex.mappingCone.map S₁.f S₂.f τ.τ₁ τ.τ₂ τ.comm₁₂.symm from rfl, e]
    infer_instance
  exact (quasiIso_iff_comp_right _ (CochainComplex.mappingCone.descShortComplex S₂)).1 this

theorem etaleSplitExcision_of_mono_cokernel_relative (hM : LeafChainsMono) (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  leafExcSp_of' hM hK leafConeCok hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem free_mono (R : Type) [CommRing R] {A B : PSh} (g : A ⟶ B) [Mono g] : Mono ((free R).map g) := by
  have : Mono ((freeP R).map g) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 (inferInstance)
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (g.app U))).hom
    have hu : Function.Injective (uliftFunctor.{1}.map (g.app U)) := by
      intro a b h
      exact ULift.ext (hg (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  change Mono ((presheafToSheaf _ _).map ((freeP R).map g))
  infer_instance

theorem leafChainsMono : LeafChainsMono := by
  intro R _ E' E f hf n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    change Mono ((HomologicalComplex.extendMap ((chainsN R).map f) _).f _)
    rw [HomologicalComplex.extendMap_f _ _ h]
    have : Mono (f.app (op (SimplexCategory.mk p))) := by
      rw [NatTrans.mono_iff_mono_app] at hf
      exact hf _
    have : Mono (((chainsN R).map f).f p) := by
      change Mono ((AlgebraicTopology.AlternatingFaceMapComplex.map _).f p)
      rw [AlgebraicTopology.AlternatingFaceMapComplex.map_f]
      exact free_mono R _
    infer_instance
  · push Not at hn
    refine ⟨fun g h _ => ?_⟩
    exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)).eq_of_tgt _ _

theorem etaleSplitExcision_of_cokernel_relative (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  etaleSplitExcision_of_mono_cokernel_relative leafChainsMono hK hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcPPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP

def LeafFive : Prop := ∀ δ, IsBd δ → ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Mono P'.hom → Mono P.hom →
  (∀ i, Eqv _ φ.left (tw q i)) → (∀ i, Eqv _ φ.right (tw q i)) → Exc q φ

def LeafChartFact : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
  (I : Ideal (MvPolynomial (Fin d) R)), Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) →
  ∀ Φ : opn (off (MvPolynomial (Fin d) R) I) ⟶ pr d R,
  Φ.right = (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
    sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) →
  ∃ (P : Arrow Spc) (α : opn (off (MvPolynomial (Fin d) R) I) ⟶ P) (β : P ⟶ pr d R), α ≫ β = Φ ∧
    Mono (opn (off (MvPolynomial (Fin d) R) I)).hom ∧ Mono P.hom ∧
    (∀ i, Eqv _ α.left (tw q i)) ∧ (∀ i, Eqv _ α.right (tw q i)) ∧
    IsPullback P.hom β.left β.right (pr d R).hom ∧ Cover2 (ZMod q) β.right (pr d R).hom

theorem dbl_hom_ext {P : Arrow Spc} {X : Spc} {f g : dbl P ⟶ X} (h0 : dbl.inl P ≫ f = dbl.inl P ≫ g)
    (h1 : dbl.inr P ≫ f = dbl.inr P ≫ g) : f = g := pushout.hom_ext h0 h1

theorem dbl_map_comp {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) :
    dbl.map (α ≫ β) = dbl.map α ≫ dbl.map β := by
  apply dbl_hom_ext
  · rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, Arrow.comp_right, Category.assoc]
  · rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem pull_comp_apply (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (α ≫ β) n i x = Hs.pull q α n i (Hs.pull q β n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (α ≫ β)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map α) _ n (GlobalTheory.EtC.pull _ (dbl.map β) _ n x.1)
  rw [dbl_map_comp, pull_comp]

theorem exc_comp (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (hα : Exc q α) (hβ : Exc q β) :
    Exc q (α ≫ β) := fun n i => by
  have : (Hs.pull q (α ≫ β) n i : Hs q P n i → Hs q P'' n i) = Hs.pull q α n i ∘ Hs.pull q β n i :=
    funext (pull_comp_apply q α β n i)
  rw [this]
  exact (hα n i).comp (hβ n i)

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = GlobalTheory.EtC.pull _ φ.right _ n (Hs.fgt q P n i x) := by
  change GlobalTheory.EtC.pull _ (dbl.inl P') _ n (GlobalTheory.EtC.pull _ (dbl.map φ) _ n x.1) =
    GlobalTheory.EtC.pull _ φ.right _ n (GlobalTheory.EtC.pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, inl_map, pull_comp]

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (c : Ht q P.right n i) :
    GlobalTheory.EtC.pull _ P'.hom (tw q i) n (GlobalTheory.EtC.pull _ φ.right _ n c) =
      GlobalTheory.EtC.pull _ φ.left _ n (GlobalTheory.EtC.pull _ P.hom (tw q i) n c) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem five (δ : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), Ht q P.left n i →+ Hs q P (n + 1) i) (hδ : IsBd δ)
    (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom)
    (hl : ∀ i, Eqv _ φ.left (tw q i)) (hr : ∀ i, Eqv _ φ.right (tw q i)) (m i : ℤ) :
    Function.Bijective (Hs.pull q φ (m + 1) i) := by
  obtain ⟨hex, hnat, -⟩ := hδ
  obtain ⟨-, e2, e3⟩ := hex q P h m i
  obtain ⟨-, e2', e3'⟩ := hex q P' h' m i
  obtain ⟨e1, -, -⟩ := hex q P h (m + 1) i
  obtain ⟨e1', -, -⟩ := hex q P' h' (m + 1) i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hf : Hs.fgt q P (m + 1) i x = 0 := by
      apply (hr i (m + 1)).1
      rw [← fgt_pull, hx, map_zero, map_zero]
    obtain ⟨u, rfl⟩ := (e3 x).1 hf
    have hu : δ q P' m i (GlobalTheory.EtC.pull _ φ.left _ m u) = 0 := by rw [← hnat q P' P φ h' h m i u]; exact hx
    obtain ⟨w', hw'⟩ := (e2' _).1 hu
    obtain ⟨w, rfl⟩ := (hr i m).2 w'
    rw [res_pull] at hw'
    have := (hl i m).1 hw'
    rw [← this]
    exact (e2 _).2 ⟨w, rfl⟩
  · intro y
    obtain ⟨c, hc⟩ := (hr i (m + 1)).2 (Hs.fgt q P' (m + 1) i y)
    have hc0 : GlobalTheory.EtC.pull _ P.hom (tw q i) (m + 1) c = 0 := by
      apply (hl i (m + 1)).1
      rw [← res_pull, hc, map_zero]
      exact (e1' _).2 ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := (e1 c).1 hc0
    have hd : Hs.fgt q P' (m + 1) i (y - Hs.pull q φ (m + 1) i x) = 0 := by
      rw [map_sub, fgt_pull, hx, hc, sub_self]
    obtain ⟨u', hu'⟩ := (e3' _).1 hd
    obtain ⟨u, rfl⟩ := (hl i m).2 u'
    refine ⟨x + δ q P m i u, ?_⟩
    rw [map_add (f := _), hnat q P' P φ h' h m i u, hu', add_sub_cancel]

theorem leafFive : LeafFive := by
  intro δ hδ q P' P φ h' h hl hr n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five δ hδ q φ h' h hl hr m i

end LateralTheory.CohomologicalPurity.Thom.ExcP

namespace LateralTheory.CohomologicalPurity.Thom

theorem excision_of_thom_chart_factorization (hBd : LeafBd) (hSp : LeafExcSp) (hFact : ExcP.LeafChartFact) :
    LeafExcP := by
  intro hH q _ d R _ I hI hq Φ hΦ
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨P, α, β, hαβ, hm1, hm2, hl, hr, hpb, hcov⟩ := hFact hH q d R I hI hq Φ hΦ
  rw [← hαβ]
  exact ExcP.exc_comp q α β (ExcP.leafFive δ hδ q α hm1 hm2 hl hr) (hSp hH.1 q β hpb hcov)

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTauPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem cast_inj {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Function.Injective (Ht.cast (q := q) (E := E) h1 h2) := by
  subst h1; subst h2; intro a b h; exact h

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Ht.cast (q := q) (E := E) h1 h2 0 = 0 := by
  subst h1; subst h2; rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n) (h4 : i' = i)
    (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = a := by
  subst h1; subst h2; rfl

def LeafTauRes : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) a,
  pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a

def LeafTauU : Prop := LeafPB → LeafTail → Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R],
  IsUnit (q : R) → ∀ n i : ℤ, Function.Bijective (poly q (d + 1) 1 R d n i)

def LeafTauLin : Prop := ∀ (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) a b,
  poly q N k R m n i (a - b) = poly q N k R m n i a - poly q N k R m n i b

def LeafTauFgt : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] (P : Arrow Spc) (n m i j : ℤ) (a : Ht q P.right n i)
  (b : Hs q P m j), Hs.fgt q P _ _ (Hs.act q a b) = cup q a (Hs.fgt q P _ _ b)

def LeafTauTop : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (n i : ℤ) (x : Ht q (sp R) n i)
  (a : ∀ j : Fin d, Ht q (sp R) (2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) ((d : ℤ) - ((j : ℕ) : ℤ))),
  ∃ e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)),
    e (Fin.last d) = x.cast (by simp) (by simp) ∧
    cup q (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ x)
      (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d a) =
      poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) e

theorem cast_sub {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a b : Ht q E n i) :
    Ht.cast h1 h2 (a - b) = Ht.cast h1 h2 a - Ht.cast h1 h2 b := by
  subst h1; subst h2; rfl

theorem tauLin : LeafTauLin := by
  intro q N k R _ m n i a b
  unfold poly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.sub_apply, map_sub, map_sub, AddMonoidHom.sub_apply, cast_sub]

theorem tauFgt : LeafTauFgt := by
  intro h q _ P n m i j a b
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change pull _ (dbl.inl P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 - pull _ (dbl.fold P) _ _
    (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) = cup q a (pull _ (dbl.inl P) _ _ b.1)
  rw [map_sub, (h q).1, (h q).1, hb, map_zero, map_zero, map_zero, sub_zero, ← pull_comp, inl_fold, pull_id]

theorem poly_zero (hL : LeafTauLin) (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) :
    poly q N k R m n i 0 = 0 := by
  have h := hL q N k R m n i 0 0
  rw [sub_zero, sub_self] at h
  exact h

theorem LeafTau_of (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail) (hR : LeafTauRes)
    (hU : LeafTauU) (hL : LeafTauLin) (hF : LeafTauFgt) (hT : LeafTauTop) : LeafTau := by
  intro H q _ d R _ hq
  obtain ⟨δ, hδ, -, -⟩ := hBd
  have hm : Mono (pr d R).hom := hG.1 d R
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hUb := hU hPB hTl H q d R hq
  have hPB' := hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq
  have hpoly0 := poly_zero hL
  have hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0 :=
    fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩
  have hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i) := by
    intro N i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨u, rfl⟩ := ((hδ q _ hm n i).2.2 σ).1 hσ
    obtain ⟨a, ha⟩ := (hUb n i).2 u
    exact ((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR H q d R d n i a).trans ha⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))
    have hy : pull _ (pr d R).hom (tw q d) _
        (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0 := by
      refine (map_add _ _ _).trans ?_
      rw [hR H q d R d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]
      exact add_neg_cancel _
    obtain ⟨τ, hτ⟩ := ((hδ q _ hm _ _).1 _).1 hy
    refine ⟨τ, ⟨0 - b, hτ⟩, ?_⟩
    rintro τ' ⟨a', ha'⟩
    have e1 := hres0 _ _ τ'
    rw [ha'] at e1
    have e2 := (map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1
    rw [hR H q d R d (2 * d) d a'] at e2
    have hab : a' = 0 - b := (hUb _ _).1 (by
      rw [hL, hpoly0, zero_sub, hb]
      exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))
    apply hinj
    rw [ha', hτ, hab]
  · rintro τ ⟨a, ha⟩ n i
    constructor
    · intro x y hxy
      obtain ⟨ex, hex, hex'⟩ := hT H q d R n i x a
      obtain ⟨ey, hey, hey'⟩ := hT H q d R n i y a
      have h1 := congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy
      dsimp only at h1
      have fx := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ
      have fy := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ
      rw [ha] at fx fy
      replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))
      have h2 := congrFun ((hPB' _ _).1 h1) (Fin.last d)
      rw [hex, hey] at h2
      exact cast_inj _ _ h2
    · intro σ
      obtain ⟨c, hc⟩ := (hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
      have k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n := by
        simp only [Fin.val_last]; ring
      have k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i := by
        simp only [Fin.val_last]; ring
      refine ⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩
      obtain ⟨e, he, he'⟩ := hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a
      have hlast : (e - c) (Fin.last d) = 0 := by
        rw [Pi.sub_apply, he, cast_cast, sub_self]
      have hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc) := by
        unfold poly
        rw [Fin.sum_univ_castSucc, hlast]
        simp only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]
        rfl
      have hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _
            (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by
        have hfx := hF h6 q (pr d R) n (2 * d) i d
          (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ
        rw [ha] at hfx
        rw [hL, map_sub, hc]
        exact congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
          (he'.symm.trans hfx.symm)
      have hg : (fun j : Fin d => (e - c) j.castSucc) = 0 := (hUb _ _).1 (by
        rw [hpoly0, ← hR H, ← hsnoc, hd]
        exact hres0 _ _ _)
      rw [hg, hpoly0] at hsnoc
      rw [hsnoc] at hd
      replace hd := hd.symm
      rw [map_sub] at hd
      exact hinj _ _ (sub_eq_zero.mp hd)

end LateralTheory.CohomologicalPurity.Thom
end
end

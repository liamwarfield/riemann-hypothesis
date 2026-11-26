module

public import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainEvaluationPrecompSpaceMap
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainEvaluationAdditive : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x

def EtaleSimplicialCochainEvaluationRestrictionNaturality : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)

def EtaleSimplicialCochainExtOfEvaluation : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β

def EtaleSimplicialCochainEvaluationPrecompSpaceMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)

def EtaleSimplicialCochainEvaluationPostcompComplexMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations.BasicPf
variable {R : Type} [CommRing R]

lemma app_add {A B : Shv R} (φ ψ : A ⟶ B) (U : Scheme.{0}) (y : Sec A U) :
    ((φ + ψ).hom.app (op U)).hom y = (φ.hom.app (op U)).hom y + (ψ.hom.app (op U)).hom y := by
  rfl

noncomputable def evH {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (by
    intro α β
    show ((((chainsXIso R E p).inv ≫ (α + β).v _ _ h).hom.app (op U))).hom _ = _
    rw [Cochain.add_v, Preadditive.comp_add, app_add]
    rfl)

theorem lin : EtaleSimplicialCochainEvaluationAdditive := by
  intro R _ E I n α β p s h U x
  exact ⟨map_add (evH p s h U x) α β, map_sub (evH p s h U x) α β, map_zero (evH p s h U x),
    fun c => map_zsmul (evH p s h U x) c α⟩

theorem cx : EtaleSimplicialCochainEvaluationPostcompComplexMap := by
  intro R _ E I n J m α p s h U x
  show ((((chainsXIso R E p).inv ≫ (α.comp (Cochain.ofHom m) (add_zero n)).v _ _ h).hom.app (op U))).hom _ = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

lemma freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  erw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

theorem nat : EtaleSimplicialCochainEvaluationRestrictionNaturality := by
  intro R _ E I n α p s h V U g x
  show Sec.res g ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom (freeGen R _ U x)) =
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom (freeGen R _ V (x.res g)))
  rw [show x.res g = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← freeGen_res]
  simp only [Sec.res]
  exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R _ U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)).symm

lemma freeGen_map {P Q : PSh} (η : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map η).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (η.app (op U) x) := by
  unfold freeGen
  erw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← toSheafify_naturality, NatTrans.comp_app, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

theorem spc : LateralTheory.EtaleFoundations.EtaleSimplicialCochainEvaluationPrecompSpaceMap := by
  intro R _ E I n E' f α p s h U x
  have key : (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
    simp only [chains, chainsXIso, Functor.comp_map]
    erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl, Iso.inv_hom_id_assoc]
    rfl
  show ((((chainsXIso R E' p).inv ≫ ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v _ _ h).hom.app (op U))).hom _ = ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U))).hom (freeGen R _ U (x.map f))
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, key, Category.assoc]
  show (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom ((((free R).map (f.app (op (SimplexCategory.mk p)))).hom.app (op U)).hom (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

theorem ext : LateralTheory.EtaleFoundations.EtaleSimplicialCochainExtOfEvaluation := by
  intro R _ E I n α β hev
  apply Cochain.ext
  intro a b hab
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k:ℤ) := ⟨a.natAbs, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    apply (sheafToPresheaf _ _).map_injective
    apply sheafify_hom_ext _ _ _ (I.X b).property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨y⟩
    exact hev k b hab U.unop y
  · apply (HomologicalComplex.isZero_extend_X _ _ a _).eq_of_src
    intro i hi
    change -(i:ℤ) = a at hi
    omega

end LateralTheory.EtaleFoundations.BasicPf

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components : EtaleSimplicialCochainEvaluationProperties := by
  intro R _ E I n
  exact ⟨BasicPf.lin R, BasicPf.nat R, BasicPf.ext R, BasicPf.spc R, BasicPf.cx R⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSimplicialSchemeCocycleVanishingAtIdIsCobou
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma cob_altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if k % 2 = 0 then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have : (j + j) % 2 = 0 := by omega
      have h2 : (j + j + 1) % 2 ≠ 0 := by omega
      simp [this, h2, ← two_mul, pow_mul]
    · have : (2 * j + 1) % 2 ≠ 0 := by omega
      have h2 : (2 * j + 1 + 1) % 2 = 0 := by omega
      simp [this, h2, pow_succ, pow_mul]

lemma cob_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (z : Sec F U) :
    Sec.map φ (c • z) = c • Sec.map φ z := by
  simp [Sec.map]

lemma cob_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := by
  simp [Sec.map]

lemma cob_res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (z : Sec F U) :
    Sec.res g (c • z) = c • Sec.res g z := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations

noncomputable def cobB {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ) (hmn : m + 1 = n)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + m = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
  fun p s h U x => if p % 2 = 1 then ((n.negOnePow : ℤ)) • ev α (p + 1) s (by push_cast; omega) U
    (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) else 0

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialScheme_cocycle_vanishing_at_id_isCoboundary_of_evaluati (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary := by
  intro R _ X I m n hmn α h0
  have hεε : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul]; rfl

  have hnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (cobB X I m n hmn α.1 p s h U x) = cobB X I m n hmn α.1 p s h V (x.res g) := by
    intro p s h V U g x
    unfold cobB
    split_ifs
    · rw [cob_res_zsmul]
      exact congrArg (((n.negOnePow : ℤ)) • ·) ((hb R).2.1 α.1 (p + 1) s _ V U g (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)))
    · simp [Sec.res]
  obtain ⟨β, hβ⟩ := hmk R (cobB X I m n hmn α.1) hnat
  refine ⟨β, ?_⟩

  have hα0 : ∀ U (x : Sx (sch.obj X) 0 U), ev α.1 0 n (by simp) U x = 0 := by
    intro U x
    have e : ev α.1 0 n (by simp) U x = Sec.res (x : U ⟶ X) (ev α.1 0 n (by simp) X (𝟙 X)) := by
      rw [(hb R).2.1 α.1 0 n (by simp) U X x (𝟙 X)]; rfl
    rw [e, h0]; simp [Sec.res]

  have hcyc : ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 2 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + n = t) U
      (x : Sx (sch.obj X) (p + 2) U), p % 2 = 0 →
      Sec.map (I.d s t) (ev α.1 (p + 2) s hs U x) = (n.negOnePow : ℤ) • ev α.1 (p + 1) t ht U
        (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
    intro p s t hs ht U x hp
    have e := (hdl R rfl α.1 U).2 (p + 1) s t hs (by push_cast at ht ⊢; omega) x
    rw [Cocycle.δ_eq_zero, ((hb R (E := sch.obj X) (I := I) (n := n + 1)).1 0 0 (p + 1 + 1) t _ U x).2.2.1] at e
    have hsum : ∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ) • ev α.1 (p + 1) t (by push_cast at ht ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ)) • ev α.1 (p + 1) t ht U
          (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, if_neg (by omega), one_smul, Int.negOnePow_succ, Units.smul_def] at e
    rw [eq_comm, add_eq_zero_iff_eq_neg] at e
    rw [e]; simp
  apply (hb R).2.2.1
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    rw [(hdl R hmn β U).1 x, hβ, hα0]
    simp [cobB, cob_map_zero]
  | succ p =>
    rw [(hdl R hmn β U).2 p (-((p + 1 : ℕ) : ℤ) + m) s rfl h x]
    simp only [hβ]
    have hsum : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ)) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U
          (show Sx (sch.obj X) p U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, Units.smul_def]
    rcases Nat.even_or_odd p with ⟨j, rfl⟩ | ⟨j, rfl⟩
    ·
      have h1 : (j + j + 1) % 2 = 1 := by omega
      have h2 : (j + j + 2) % 2 = 0 := by omega
      simp only [cobB, h1, h2, ↓reduceIte, zero_smul, smul_zero, add_zero]
      rw [cob_map_zsmul]
      have hc := hcyc (j + j) (-((j + j + 1 : ℕ) : ℤ) + m) s (by push_cast; omega) (by push_cast at h ⊢; omega) U x (by omega)
      erw [hc]
      rw [smul_smul, hεε, one_smul]
    · have h1 : (2 * j + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * j + 1 + 2) % 2 = 1 := by omega
      have h3 : (2 * j + 1) % 2 = 1 := by omega
      simp only [cobB, h1, h2, h3, ↓reduceIte, one_ne_zero, one_smul, smul_smul]
      rw [if_neg (by omega), cob_map_zero, zero_add, one_mul, hεε, one_smul]
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsCochainMkOfCompatibleSectio
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}

noncomputable def eta (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (Sx E p U.unop))
    (M := (I.X s).obj.obj U) (TypeCat.ofHom fun (y : ULift.{1} (Sx E p U.unop)) => a p s h U.unop y.down)
  naturality U V f := by
    refine ModuleCat.free_hom_ext (X := ULift.{1} (Sx E p U.unop)) (fun y => ?_)
    have := ha p s h V.unop U.unop f.unop y.down
    simp only [Sec.res, Sx.res, Quiver.Hom.op_unop] at this
    change (ModuleCat.freeDesc (M := (I.X s).obj.obj V)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p V.unop)) => a p s h V.unop z.down))
        ((ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) =>
          ULift.up.{1} ((E.obj (op (SimplexCategory.mk p))).map f z.down)) (ModuleCat.freeMk y)) =
      ((I.X s).obj.map f) (ModuleCat.freeDesc (M := (I.X s).obj.obj U)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) => a p s h U.unop z.down) (ModuleCat.freeMk y))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

noncomputable def mF (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ (I.X s)).symm
    (eta a ha p s h)

lemma mF_gen (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((mF a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology.{0} (eta a ha p s h) (I.X s).property
  have e2 := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) e
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e2
  exact e2.trans (ModuleCat.freeDesc_apply _ _)

noncomputable def mC (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun i j hij => if hi : i ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-i).toNat).hom ≫ mF a ha (-i).toNat j (by omega)
  else 0

lemma mC_v (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (mC a ha).v _ _ h = (chainsXIso R E p).hom ≫ mF a ha p s h := by
  have key : ∀ (q : ℕ), q = p → ∀ (e : -(p : ℤ) = -(q : ℤ)) (h' : -(q : ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ (chainsXIso R E q).hom ≫ mF a ha q s h' =
        (chainsXIso R E p).hom ≫ mF a ha p s h := by
    rintro q rfl e h'
    simp
  rw [mC, Cochain.mk_v, dite_eq_left (by omega)]
  exact key _ (by omega) _ _

end LateralTheory.EtaleFoundations.MkPf

open LateralTheory.EtaleFoundations LateralTheory.EtaleFoundations.MkPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections : EtaleSimplicialCochainExistsFromNaturalSections := by
  intro R _ E I n a ha
  refine ⟨mC a ha, fun p s h U x => ?_⟩
  unfold ev
  rw [mC_v, Iso.inv_hom_id_assoc]
  exact mF_gen a ha p s h U x
end

namespace LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass

theorem delta : LateralTheory.EtaleFoundations.EtaleSimplicialCochainEvaluationDifferentialFormula := LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds

theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSchemeGlobalSectionCohomologyClass :=
  LateralTheory.EtaleFoundations.etaleSimplicialCochain_scheme_class_of_evaluation_properties LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections delta
    LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components
    (LateralTheory.EtaleFoundations.etaleSimplicialScheme_cocycle_vanishing_at_id_isCoboundary_of_evaluati LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections delta
      LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components)

end LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass

module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveComplexProductSectionMapQuasiIso
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallySurjectiveMultiplicativeGroupKunnethMap

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

noncomputable section

namespace UpperTheory.Kun

variable {R : Type} [CommRing R]

abbrev sh (Q : Cx R) : Cx R := (CategoryTheory.shiftFunctor (Cx R) (-1 : ℤ)).obj Q

abbrev LL (I Q : Cx R) : Cx R := I ⊞ sh Q

def c₁ {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} : Sec ((LL I Q).X s) T →+ Sec (I.X s) T :=
  ((((biprod.fst : LL I Q ⟶ I).f s).hom.app (op T)).hom).toAddMonoidHom

def c₂ {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} : Sec ((LL I Q).X s) T →+ Sec (Q.X (s + -1)) T :=
  ((((biprod.snd : LL I Q ⟶ sh Q).f s).hom.app (op T)).hom).toAddMonoidHom

def cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : Sec ((LL I Q).X s) T :=
  Sec.map ((biprod.inl : I ⟶ LL I Q).f s) a + Sec.map ((biprod.inr : sh Q ⟶ LL I Q).f s) (show Sec ((sh Q).X s) T from b)

def psi (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) (T : Scheme.{0}) (s : ℤ) :
    Sec ((LL I Q).X s) T →+ Sec (I.X s) (W ⨯ T) :=
  AddMonoidHom.mk' (fun x => Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ x) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ x)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z))
    (fun x y => by
      simp only [map_add (f := _), LinearMap.add_apply, smul_add]
      abel)

def inL {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) : Cocycle K (LL I Q) n :=
  zcomp α₁ (Cocycle.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
    ((n.negOnePow : ℤˣ) : ℤ) • zcomp (α₂.rightShift (-1) n (by omega)) (Cocycle.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n)

def sg {X : Scheme.{0}} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj (sch.obj X)) I n) : Sec (I.X n) X :=
  ev α.1 0 n (by simp) X (𝟙 X)

end UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

theorem res_id {F : Shv R} {X : Scheme.{0}} (b : Sec F X) : Sec.res (𝟙 X) b = b := by
  change (F.obj.map (𝟙 (op X))).hom b = b
  rw [F.obj.map_id]
  rfl

theorem res_res {F : Shv R} {X Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) (b : Sec F X) :
    Sec.res g (Sec.res f b) = Sec.res (g ≫ f) b := by
  change _ = (F.obj.map (f.op ≫ g.op)).hom b
  rw [F.obj.map_comp]
  rfl

theorem map_map {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

theorem map_idS {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem map_zeroS {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem map_addS {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

theorem c₁_cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : c₁ (cc (I := I) (Q := Q) a b) = a := by
  have h1 : ((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.fst : LL I Q ⟶ I).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]
  have h2 : ((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.fst : LL I Q ⟶ I).f s) = 0 := by
    rw [← HomologicalComplex.comp_f, biprod.inr_fst, HomologicalComplex.zero_f]
  unfold cc
  rw [map_add (f := _)]
  change Sec.map _ (Sec.map _ a) + Sec.map _ (Sec.map _ _) = a
  rw [map_map, map_map, h1, h2, map_idS, map_zeroS, add_zero]

theorem c₂_cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : c₂ (cc (I := I) (Q := Q) a b) = b := by
  have h1 : ((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s) = 0 := by
    rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]
  have h2 : ((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]
  unfold cc
  rw [map_add (f := _)]
  change (Sec.map (((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s)) a +
    Sec.map (((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s)) (show Sec ((sh Q).X s) T from b) : Sec ((sh Q).X s) T) = b
  rw [h1, h2, map_zeroS, zero_add]
  rfl

theorem cc_c {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (x : Sec ((LL I Q).X s) T) : cc (c₁ x) (c₂ x) = x := by
  have h : ((biprod.fst : LL I Q ⟶ I).f s) ≫ ((biprod.inl : I ⟶ LL I Q).f s) +
      ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  change Sec.map _ (Sec.map _ x) + Sec.map _ (Sec.map _ x) = x
  rw [map_map, map_map, ← map_addS, h, map_idS]

theorem LLsec_ext {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (x y : Sec ((LL I Q).X s) T) (h₁ : c₁ x = c₁ y) (h₂ : c₂ x = c₂ y) : x = y := by
  rw [← cc_c x, ← cc_c y, h₁, h₂]

theorem c₁_res {I Q : Cx R} {V T : Scheme.{0}} {s : ℤ} (g : V ⟶ T) (x : Sec ((LL I Q).X s) T) : c₁ (Sec.res g x) = Sec.res g (c₁ x) :=
  (res_map _ g x).symm

theorem c₂_res {I Q : Cx R} {V T : Scheme.{0}} {s : ℤ} (g : V ⟶ T) (x : Sec ((LL I Q).X s) T) : c₂ (Sec.res g x) = Sec.res g (c₂ x) :=
  (res_map ((biprod.snd : LL I Q ⟶ sh Q).f s) g x).symm

theorem c₁_d {I Q : Cx R} {T : Scheme.{0}} (s t : ℤ) (x : Sec ((LL I Q).X s) T) : c₁ (Sec.map ((LL I Q).d s t) x) = Sec.map (I.d s t) (c₁ x) := by
  change Sec.map _ (Sec.map _ x) = Sec.map _ (Sec.map _ x)
  rw [map_map, map_map, (biprod.fst : LL I Q ⟶ I).comm]

theorem sh_d (Q : Cx R) (s t : ℤ) : (sh Q).d s t = - Q.d (s + -1) (t + -1) := by
  have : (sh Q).d s t = (-1 : ℤ).negOnePow • Q.d (s + -1) (t + -1) := CochainComplex.shiftFunctor_obj_d' _ _ _ _
  rw [this]
  simp

theorem c₂_d {I Q : Cx R} {T : Scheme.{0}} (s t : ℤ) (x : Sec ((LL I Q).X s) T) :
    c₂ (Sec.map ((LL I Q).d s t) x) = - Sec.map (Q.d (s + -1) (t + -1)) (c₂ x) := by
  have h := (biprod.snd : LL I Q ⟶ sh Q).comm s t
  have e : ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ (sh Q).d s t =
      -(((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ (show (sh Q).X s ⟶ (sh Q).X t from Q.d (s + -1) (t + -1))) := by
    rw [sh_d]
    exact Preadditive.comp_neg _ _
  change Sec.map _ (Sec.map _ x) = _
  rw [map_map, ← h, e]
  rfl

theorem sg_pull {X Y : Scheme.{0}} {I : Cx R} {n : ℤ} (f : Y ⟶ X) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    sg (zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)) = Sec.res f (sg α) := by
  let k := op (SimplexCategory.mk 0)
  let g := (sch.map f).app k
  have hChains : (chainsXIso R (sch.obj Y) 0).inv ≫ ((chains R).map (sch.map f)).f (-((0 : ℕ) : ℤ)) =
      (free R).map g ≫ (chainsXIso R (sch.obj X) 0).inv := by
    have h : ((chains R).map (sch.map f)).f (-((0 : ℕ) : ℤ)) =
        (chainsXIso R (sch.obj Y) 0).hom ≫ ((chainsN R).map (sch.map f)).f 0 ≫
          (chainsXIso R (sch.obj X) 0).inv :=
      HomologicalComplex.extendMap_f ((chainsN R).map (sch.map f))
        ComplexShape.embeddingDownNat (i := 0) rfl
    rw [h, Iso.inv_hom_id_assoc]
    rfl
  have hMap : Sec.map ((free R).map g) (freeGen R ((sch.obj Y).obj k) Y (𝟙 Y)) =
      freeGen R ((sch.obj X).obj k) Y f := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map (yoneda.map f))) (op Y))
      (ModuleCat.freeMk (ULift.up (𝟙 Y)))
    have hGen : ((freeP R).map (yoneda.map f)).app (op Y) (ModuleCat.freeMk (ULift.up (𝟙 Y))) =
        ModuleCat.freeMk (ULift.up f) := by
      change (ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom (fun x : ULift (Y ⟶ Y) => ULift.up (x.down ≫ f)))
        (ModuleCat.freeMk (ULift.up (𝟙 Y))) = _
      rw [ModuleCat.free_map_apply]
      exact congrArg (fun a : Y ⟶ X => ModuleCat.freeMk (ULift.up a)) (Category.id_comp f)
    exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj X))).app (op Y)).hom hGen)
  have hRes : Sec.res f (freeGen R ((sch.obj X).obj k) X (𝟙 X)) = freeGen R ((sch.obj X).obj k) Y f := by
    have h := ConcreteCategory.congr_hom
      ((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj X))).naturality f.op)
      (ModuleCat.freeMk (ULift.up (𝟙 X)))
    have hGen : ((freeP R).obj (yoneda.obj X)).map f.op (ModuleCat.freeMk (ULift.up (𝟙 X))) =
        ModuleCat.freeMk (ULift.up f) := by
      change (ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom (fun x : ULift (X ⟶ X) => ULift.up (f ≫ x.down)))
        (ModuleCat.freeMk (ULift.up (𝟙 X))) = _
      rw [ModuleCat.free_map_apply]
      exact congrArg (fun a : Y ⟶ X => ModuleCat.freeMk (ULift.up a)) (Category.comp_id f)
    exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj X))).app (op Y)).hom hGen)
  change Sec.map ((chainsXIso R (sch.obj Y) 0).inv ≫
      ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)).v _ _ (by simp))
      (freeGen R ((sch.obj Y).obj k) Y (𝟙 Y)) =
    Sec.res f (Sec.map ((chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (by simp))
      (freeGen R ((sch.obj X).obj k) X (𝟙 X)))
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, hChains, Category.assoc,
    ← map_map, hMap, res_map, hRes]

theorem sg_sub {X : Scheme.{0}} {I : Cx R} {n : ℤ} (α β : Cocycle ((chains R).obj (sch.obj X)) I n) : sg (α - β) = sg α - sg β := by
  change ev (α.1 - β.1) 0 n (by simp) X (𝟙 X) = sg α - sg β
  simp only [sg, ev, Cochain.sub_v, Preadditive.comp_sub]
  rfl

theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y :=
  map_add _ _ _

theorem res_units {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (ε : ℤˣ) (x : Sec F U) : Sec.res g (ε • x) = ε • Sec.res g x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

theorem psi_nat (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) {T' T : Scheme.{0}} (g : T' ⟶ T) (s : ℤ)
    (a : Sec ((LL I Q).X s) T) : Sec.res (prod.map (𝟙 W) g) (psi W μ z T s a) = psi W μ z T' s (Sec.res g a) := by
  change Sec.res (prod.map (𝟙 W) g) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
    Sec.res (prod.snd : W ⨯ T' ⟶ T') (c₁ (Sec.res g a)) +
      s.negOnePow • μ.mul (W ⨯ T') (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T' ⟶ T') (c₂ (Sec.res g a))) (Sec.res (prod.fst : W ⨯ T' ⟶ W) z)
  rw [res_add, res_units, μ.nat, c₁_res, c₂_res, res_res, res_res, res_res, res_res, res_res]
  simp

theorem LL_inj {I Q : Cx R} (hI : ∀ s, Injective (I.X s)) (hQ : ∀ s, Injective (Q.X s)) (s : ℤ) : Injective ((LL I Q).X s) := by
  have hQ' : Injective ((sh Q).X s) := hQ (s + -1)
  have h : ((biprod.fst : LL I Q ⟶ I).f s) ≫ ((biprod.inl : I ⟶ LL I Q).f s) +
      ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  refine ⟨fun {X Y} g f _ => ?_⟩
  haveI := hI s
  obtain ⟨h₁, e₁⟩ := Injective.factors (g ≫ (biprod.fst : LL I Q ⟶ I).f s) f
  obtain ⟨h₂, e₂⟩ := Injective.factors (g ≫ (biprod.snd : LL I Q ⟶ sh Q).f s) f
  refine ⟨h₁ ≫ (biprod.inl : I ⟶ LL I Q).f s + h₂ ≫ (biprod.inr : sh Q ⟶ LL I Q).f s, ?_⟩
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, e₁, e₂, Category.assoc, Category.assoc, ← Preadditive.comp_add, h, Category.comp_id]

theorem LL_ge (I Q : Cx R) [I.IsStrictlyGE 0] [Q.IsStrictlyGE 0] : (LL I Q).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hI := I.isZero_of_isStrictlyGE 0 i hi
  have hQ : IsZero ((sh Q).X i) := Q.isZero_of_isStrictlyGE 0 (i + -1) (by omega)
  have h : ((biprod.fst : LL I Q ⟶ I).f i) ≫ ((biprod.inl : I ⟶ LL I Q).f i) +
      ((biprod.snd : LL I Q ⟶ sh Q).f i) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f i) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  rw [IsZero.iff_id_eq_zero, ← h, hI.eq_of_tgt ((biprod.fst : LL I Q ⟶ I).f i) 0, hQ.eq_of_tgt ((biprod.snd : LL I Q ⟶ sh Q).f i) 0]
  simp

end UpperTheory.Kun
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyClassInLSurjectiveAndInjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun.InL

variable {R : Type} [CommRing R]

private theorem sgn {A : Type*} [AddCommGroup A] (a b : ℤˣ) (x : A) : b • a • a • b • x = x := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;> simp

private theorem inL_coe {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      n.negOnePow • (α₂.1.rightShift (-1) n (by omega)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl

private theorem inL_fst {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n) = α₁.1 := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_fst, biprod.inr_fst, Cochain.comp_id]
  simp

private theorem inL_snd {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) =
      n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_snd, biprod.inr_snd, Cochain.comp_id]
  simp

private theorem decomp {K I Q : Cx R} {n : ℤ} (x : Cochain K (LL I Q) n) :
    (x.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n)).comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      (x.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) = x := by
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.comp_add, ← Cochain.ofHom_add, biprod.total, Cochain.comp_id]

private theorem unsh {K Q : Cx R} {m n : ℤ} (h : m + 1 = n) (ε : ℤˣ) (y : Cocycle K (sh Q) n) :
    ∃ a : Cocycle K Q m, ε • a.1.rightShift (-1) n (by omega) = y.1 := by
  have hy : n + -1 = m := by omega
  refine ⟨Cocycle.mk (ε • y.1.rightUnshift m hy) (m + 1) rfl ?_, ?_⟩
  · rw [δ_units_smul, Cochain.δ_rightUnshift _ m hy (m + 1) (n + 1) (by omega), Cocycle.δ_eq_zero]
    simp
  · change ε • (ε • y.1.rightUnshift m hy).rightShift (-1) n hy = y.1
    rw [Cochain.rightShift_units_smul, Cochain.rightShift_rightUnshift, smul_smul, Int.units_mul_self, one_smul]

end UpperTheory.Kun.InL

open UpperTheory.Kun.InL in
theorem UpperTheory.cohomologyClass_inL_surjective_and_injective :
    ∀ (R : Type) [CommRing R] {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n),
        (∀ x : Cocycle K (LL I Q) n, ∃ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk x = CohomologyClass.mk (inL h α₁ α₂)) ∧
        ∀ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk (inL h α₁ α₂) = 0 → CohomologyClass.mk α₁ = 0 ∧ CohomologyClass.mk α₂ = 0 := by
  intro R _ K I Q m n h
  refine ⟨fun x => ?_, fun α₁ α₂ h0 => ?_⟩
  · obtain ⟨a, ha⟩ := unsh (K := K) (Q := Q) h n.negOnePow (zcomp x (Cocycle.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n))
    refine ⟨zcomp x (Cocycle.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n), a, ?_⟩
    congr 1
    apply Cocycle.ext
    rw [inL_coe]
    have e : n.negOnePow • a.1.rightShift (-1) n (by omega) = x.1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) := ha
    rw [← Cochain.units_smul_comp, e]
    exact (decomp x.1).symm
  · obtain ⟨p, hp, y, hy⟩ := (CohomologyClass.mk_eq_zero_iff _).1 h0
    have hy' : δ p n y = (inL h α₁ α₂).1 := hy
    constructor
    · rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨p, hp, y.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero p), ?_⟩
      rw [δ_comp_ofHom, hy', inL_fst]
    · rw [CohomologyClass.mk_eq_zero_iff]
      have hs : δ p n (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)) =
          n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
        rw [δ_comp_ofHom, hy', inL_snd]
      have hn : n + -1 = m := by omega
      have e : δ (p + -1) m ((y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl) =
          (-1 : ℤ).negOnePow • n.negOnePow • α₂.1 := by
        rw [Cochain.δ_rightUnshift _ (p + -1) rfl m n hn, hs, Cochain.rightUnshift_units_smul, Cochain.rightUnshift_rightShift]
      refine ⟨p + -1, by omega, n.negOnePow • (-1 : ℤ).negOnePow •
        (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl, ?_⟩
      rw [δ_units_smul, δ_units_smul, e, sgn]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExteriorCupCocycleExistsOfPairing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem sub_self_all {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e]
  simp

private theorem aw_conc {Q P I : Cx R} (μ : Pair Q P I) {X : Spc} {m n : ℤ} (h : m + 1 = n)
    (A : Cochain ((chains R).obj X) Q m) (B : Cochain ((chains R).obj X) P 1)
    (γ : Cochain ((chains R).obj X) I n) (hγ : μ.IsAW h A B γ)
    (hB : ∀ (p : ℕ) s hs U x, ev (R := R) B (p + 1) s hs U x = 0)
    (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + n = w) (U : Scheme.{0}) (x : Sx X N U) :
    ev (R := R) γ N w hw U x = (N : ℤ).negOnePow • μ.mul U (w + -1) 1 w (by omega) (ev (R := R) A N (w + -1) (by omega) U x)
      (ev (R := R) B 0 1 (by simp) U (x.sub N 0 (by omega))) := by
  have term : ∀ (r l : ℕ) (hrl : r + l = N) (t u : ℤ) (ht : -(r : ℤ) + m = t) (hu : -(l : ℤ) + 1 = u) (hw' : t + u = w),
      μ.mul U t u w hw' (ev (R := R) A r t ht U (x.sub 0 r (by omega))) (ev (R := R) B l u hu U (x.sub r l (by omega))) =
        if l = 0 then μ.mul U (w + -1) 1 w (by omega) (ev (R := R) A N (w + -1) (by omega) U x)
          (ev (R := R) B 0 1 (by simp) U (x.sub N 0 (by omega))) else 0 := by
    intro r l hrl t u ht hu hw'
    rcases l with _ | l
    · obtain rfl : r = N := by omega
      obtain rfl : u = 1 := by simpa using hu.symm
      obtain rfl : t = w + -1 := by omega
      simp only [if_true]
      rw [sub_self_all]
    · rw [hB]
      simp
  rw [hγ N w hw U x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · rw [term _ _ (by simp) _ _ rfl rfl]
    simp
  · intro i _
    rw [term _ _ (by simp <;> omega) _ _ rfl rfl, if_neg (by simp <;> omega)]
    simp

end UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem ev_rightShift {E : Spc} {Q : Cx R} {m n : ℤ} (h : m + 1 = n)
    (α : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    (ev (R := R) (α.rightShift (-1) n (by omega)).1 p s hs U x : Sec ((sh Q).X s) U) = (ev (R := R) α.1 p (s + -1) (by omega) U x : Sec (Q.X (s + -1)) U) := by
  have e : (α.rightShift (-1) n (by omega)).1.v (-(p : ℤ)) s hs =
      (show _ ⟶ (sh Q).X s from α.1.v (-(p : ℤ)) (s + -1) (by omega)) := by
    refine (Cochain.rightShift_v α.1 (-1) n (by omega) (-(p : ℤ)) s hs (s + -1) (by omega)).trans ?_
    simp [CochainComplex.shiftFunctorObjXIso]
  unfold ev
  rw [e]

private theorem ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (inL h α₁ α₂).1 p s hs U x =
      cc (ev (R := R) α₁.1 p s hs U x) (n.negOnePow • ev (R := R) α₂.1 p (s + -1) (by omega) U x) := by
  have b := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := LL I Q) (n := n)
  have e₁ : (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      ((n.negOnePow : ℤˣ) : ℤ) • (α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl
  rw [e₁, (b.1 _ _ p s hs U x).1, (b.1 ((α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n)) 0 p s hs U x).2.2.2,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.2 _ α₁.1 p s hs U x,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := sh Q) (n := n)).2.2.2.2 _ _ p s hs U x, ev_rightShift h α₂ p s hs U x]
  unfold cc
  congr 1
  rw [Units.smul_def]
  exact (map_zsmul ((((biprod.inr : sh Q ⟶ LL I Q).f s).hom.app (op U)).hom) _ _).symm

private theorem c₁_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₁ (ev (R := R) (inL h α₁ α₂).1 p s hs U x) = ev (R := R) α₁.1 p s hs U x := by
  rw [ev_inL, c₁_cc]

private theorem c₂_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₂ (ev (R := R) (inL h α₁ α₂).1 p s hs U x) = n.negOnePow • ev (R := R) α₂.1 p (s + -1) (by omega) U x := by
  rw [ev_inL, c₂_cc]

private theorem sub_map_sch {W : Scheme.{0}} {X : Spc} (f : X ⟶ sch.obj W) {p : ℕ} {T : Scheme.{0}} (y : Sx X p T)
    (h : p + 0 ≤ p) : (show T ⟶ W from (y.sub p 0 h).map f) = (show T ⟶ W from y.map f) := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval p 0 h).op) (op T)) y

private theorem psi_read (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) {T : Scheme.{0}} (s : ℤ)
    (f : T ⟶ W) (a : Sec ((LL I Q).X s) T) :
    Sec.res (prod.lift f (𝟙 T)) (psi W μ z T s a) =
      c₁ a + s.negOnePow • μ.mul T (s + -1) 1 s (by omega) (c₂ a) (Sec.res f z) := by
  change Sec.res (prod.lift f (𝟙 T)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) = _
  rw [res_add, res_units, μ.nat, res_res, res_res, res_res, prod.lift_snd, prod.lift_fst, res_id, res_id]

end UpperTheory.Kun

theorem UpperTheory.exteriorCup_cocycle_exists_of_pairing :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) {E : Spc} {m n : ℤ}
        (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n) (α₂ : Cocycle ((chains R).obj E) Q m)
        (β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n),
        (∀ (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
          ev (R := R) β.1 p s hs T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T))
            (psi W μ (sg κ) T s (ev (R := R) (inL h α₁ α₂).1 p s hs T (y.map prod.snd)))) →
        CohomologyClass.mk β = cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n (CohomologyClass.mk α₁) +
          μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m (CohomologyClass.mk α₂))
            (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
  intro R _ W I Q P μ κ E m n h α₁ α₂ β hβ
  have hS := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R W P 0 1 2 (by norm_num) (by norm_num)
  obtain ⟨z', hz0, hz1⟩ := hS.1 (sg κ) (hS.2 κ).1
  have hκ : CohomologyClass.mk κ = CohomologyClass.mk z' := by
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
    refine (hS.2 (κ - z')).2.2 ⟨0, ?_⟩
    have e : sg (κ - z') = 0 := by
      rw [sg_sub]
      have e' : sg z' = sg κ := by
        have := hz0 W (𝟙 W)
        rw [res_id] at this
        exact this
      rw [e', sub_self]
    exact (map_zero ((P.d 0 1).hom.app (op W)).hom).trans e.symm
  let A : Cocycle ((chains R).obj (sch.obj W ⨯ E)) Q m :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₂ (zero_add m)
  let B : Cocycle ((chains R).obj (sch.obj W ⨯ E)) P 1 :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _))) z' (zero_add 1)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).1 A B
  have hc := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).2 A B γ hγ
  have evA : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev (R := R) A.1 p s hs T y = ev (R := R) α₂.1 p s hs T (y.map prod.snd) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := Q) (n := m)).2.2.2.1 prod.snd α₂.1 p s hs T y
  have evB : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev (R := R) B.1 p s hs T y = ev (R := R) z'.1 p s hs T (y.map prod.fst) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W) (I := P) (n := 1)).2.2.2.1 prod.fst z'.1 p s hs T y
  have hβ' : β = zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ := by
    apply Cocycle.ext
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).2.2.1 _ _ fun p s hs T y => ?_
    have e₁ : (zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ).1 =
        (Cochain.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))).comp α₁.1 (zero_add n) + γ.1 := rfl
    rw [e₁, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).1 _ _ p s hs T y).1,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.1 prod.snd α₁.1 p s hs T y,
      hβ p s hs T y, psi_read, c₁_ev_inL, c₂_ev_inL,
      aw_conc μ h A.1 B.1 γ.1 hγ (fun p s hs U x => by rw [evB]; exact hz1 p s hs U _) p s hs T y,
      evA, evB]
    congr 1
    have e₂ : ev (R := R) z'.1 0 1 (by simp) T ((y.sub p 0 (by omega)).map prod.fst) = Sec.res (show T ⟶ W from y.map prod.fst) (sg κ) := by
      rw [← sub_map_sch prod.fst y (by omega)]
      exact hz0 T _
    rw [e₂]
    have hsign : s.negOnePow * n.negOnePow = (p : ℤ).negOnePow := by
      rw [← hs, Int.negOnePow_add, Int.negOnePow_neg, mul_assoc, Int.units_mul_self, mul_one]
    have key : ∀ (ε : ℤˣ) (a : Sec (Q.X (s + -1)) T) (b : Sec (P.X 1) T),
        μ.mul T (s + -1) 1 s (by omega) (ε • a) b = ε • μ.mul T (s + -1) 1 s (by omega) a b := by
      intro ε a b
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
    rw [key, smul_smul, hsign]
  rw [hκ, hβ', CohomologyClass.mk_add, cpre_mk, cpre_mk, cpre_mk]
  exact congrArg (fun c => _ + c) hc.symm
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.PsiCommDifferentialOfCocycle
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

private theorem map_units {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (ε : ℤˣ) (x : Sec F U) :
    Sec.map φ (ε • x) = ε • Sec.map φ x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

private theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y :=
  map_add _ _ _

private theorem mul_mid {R : Type} [CommRing R] {I Q P : Cx R} (μ : Pair Q P I) (U : Scheme.{0}) (k m m' w : ℤ) (e : m = m')
    (h : m + 1 = w) (h' : m' + 1 = w) (A : Sec (Q.X k) U) (B : Sec (P.X 1) U) :
    μ.mul U m 1 w h (Sec.map (Q.d k m) A) B = μ.mul U m' 1 w h' (Sec.map (Q.d k m') A) B := by
  subst e
  rfl

theorem UpperTheory.psi_comm_differential_of_cocycle :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W), Sec.map (P.d 1 2) z = 0 →
        ∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec ((LL I Q).X s) T),
          Sec.map (I.d s t) (psi W μ z T s a) = psi W μ z T t (Sec.map ((LL I Q).d s t) a) := by
  intro R _ W I Q P μ z hz T s t a
  by_cases hst : s + 1 = t
  · subst hst
    have hB : Sec.map (P.d 1 (1 + 1)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z) = 0 := by
      rw [← res_map]
      have h2 : Sec.map (P.d 1 (1 + 1)) z = 0 := hz
      rw [h2]
      exact map_zero _
    have hL := μ.leibniz (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a))
      (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [hB, map_zero, smul_zero, add_zero,
      mul_mid μ (W ⨯ T) (s + -1) (s + -1 + 1) (s + 1 + -1) (s + 1) (by omega) (by omega) (by omega)] at hL
    change Sec.map (I.d s (s + 1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
        s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
      Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ (Sec.map ((LL I Q).d s (s + 1)) a)) +
        (s + 1).negOnePow • μ.mul (W ⨯ T) (s + 1 + -1) 1 (s + 1) (by omega)
          (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ (Sec.map ((LL I Q).d s (s + 1)) a))) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [map_add', map_units, hL, c₁_d, c₂_d, res_map, Int.negOnePow_succ]
    congr 1
    have hn : Sec.res (prod.snd : W ⨯ T ⟶ T) (- Sec.map (Q.d (s + -1) (s + 1 + -1)) (c₂ a)) =
        - Sec.map (Q.d (s + -1) (s + 1 + -1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) := by
      rw [← res_map]
      exact map_neg _ _
    rw [hn, map_neg, LinearMap.neg_apply, smul_neg, Units.neg_smul, neg_neg]
  · have h1 : I.d s t = 0 := I.shape _ _ hst
    have h2 : (LL I Q).d s t = 0 := (LL I Q).shape _ _ hst
    rw [h1, h2, map_zeroS, map_zeroS, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCocycleProductEqPullAddCup
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

theorem UpperTheory.exists_cocycle_product_eq_pull_add_cup :
    ∀ (R : Type) [CommRing R] (W X : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I)
        (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) {m n : ℤ} (h : m + 1 = n)
        (α₁ : Cocycle ((chains R).obj (sch.obj X)) I n) (α₂ : Cocycle ((chains R).obj (sch.obj X)) Q m),
        ∃ β : Cocycle ((chains R).obj (sch.obj (W ⨯ X))) I n,
          CohomologyClass.mk β =
              cpull ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X))) I n (CohomologyClass.mk α₁) +
                μ.cup (sch.obj (W ⨯ X)) h
                  (cpull ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X))) Q m (CohomologyClass.mk α₂))
                  (cpull ((chains R).map (sch.map (prod.fst : W ⨯ X ⟶ W))) P 1 (CohomologyClass.mk κ)) ∧
            sg β = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₁) +
              μ.mul (W ⨯ X) m 1 n h (Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₂))
                (Sec.res (prod.fst : W ⨯ X ⟶ W) (sg κ)) := by
  intro R _ W X I Q P μ κ m n h α₁ α₂
  let A := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X)))) α₂ (zero_add m)
  let B := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.fst : W ⨯ X ⟶ W)))) κ (zero_add 1)
  let C := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X)))) α₁ (zero_add n)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).1 A B
  have hc := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).2 A B γ hγ
  refine ⟨C + γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_add, ← hc]
    rfl
  · have hadd : sg (C + γ) = sg C + sg γ :=
      ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj (W ⨯ X)) (I := I) (n := n)).1 C.1 γ.1 0 n (by simp) (W ⨯ X) (𝟙 _)).1
    have hC : sg C = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₁) := sg_pull _ α₁
    have hA : sg A = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₂) := sg_pull _ α₂
    have hB : sg B = Sec.res (prod.fst : W ⨯ X ⟶ W) (sg κ) := sg_pull _ κ
    have key : ∀ (d e : ℤ) (hd : -((0 : ℕ) : ℤ) + m = d) (he : -((0 : ℕ) : ℤ) + 1 = e) (hw : d + e = n),
        μ.mul (W ⨯ X) d e n hw (ev A.1 0 d hd (W ⨯ X) (𝟙 _)) (ev B.1 0 e he (W ⨯ X) (𝟙 _)) =
          μ.mul (W ⨯ X) m 1 n h (sg A) (sg B) := by
      intro d e hd he hw
      obtain rfl : m = d := by simpa using hd
      obtain rfl : (1 : ℤ) = e := by simpa using he
      rfl
    have hg : sg γ = μ.mul (W ⨯ X) m 1 n h (sg A) (sg B) := by
      have h0 := hγ 0 n (by simp) (W ⨯ X) (𝟙 _)
      rw [Fin.sum_univ_one] at h0
      refine h0.trans ?_
      have e : ((1 : ℤ) * (((0 : Fin 1) : ℕ) : ℤ)).negOnePow = 1 := by simp
      rw [e, one_smul]
      exact key _ _ rfl rfl _
    rw [hadd, hC, hg, hA, hB]
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem genK (W : Scheme.{0}) (I Q P : Cx R) [I.IsStrictlyGE 0] [Q.IsStrictlyGE 0]
    (hI : ∀ s, Injective (I.X s)) (hQ : ∀ s, Injective (Q.X s)) (μ : Pair Q P I)
    (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) (Z : Scheme.{0} → Prop) (hZ : ∀ {T' T : Scheme.{0}}, (T' ⟶ T) → Z T → Z T')
    (hS : ∀ (T : Scheme.{0}), Z T → ∀ (m n : ℤ) (h : m + 1 = n) (y : CohomologyClass ((chains R).obj (sch.obj (W ⨯ T))) I n),
      Loc T fun V g => ∃ (a : CohomologyClass ((chains R).obj (sch.obj V)) I n) (b : CohomologyClass ((chains R).obj (sch.obj V)) Q m),
        cpull ((chains R).map (sch.map (prod.snd : W ⨯ V ⟶ V))) I n a +
          μ.cup (sch.obj (W ⨯ V)) h (cpull ((chains R).map (sch.map (prod.snd : W ⨯ V ⟶ V))) Q m b)
            (cpull ((chains R).map (sch.map (prod.fst : W ⨯ V ⟶ W))) P 1 (CohomologyClass.mk κ)) =
        cpull ((chains R).map (sch.map (prod.map (𝟙 W) g))) I n y)
    (hJ : ∀ (T : Scheme.{0}), Z T → ∀ (m n : ℤ) (h : m + 1 = n) (a : CohomologyClass ((chains R).obj (sch.obj T)) I n)
      (b : CohomologyClass ((chains R).obj (sch.obj T)) Q m),
        cpull ((chains R).map (sch.map (prod.snd : W ⨯ T ⟶ T))) I n a +
          μ.cup (sch.obj (W ⨯ T)) h (cpull ((chains R).map (sch.map (prod.snd : W ⨯ T ⟶ T))) Q m b)
            (cpull ((chains R).map (sch.map (prod.fst : W ⨯ T ⟶ W))) P 1 (CohomologyClass.mk κ)) = 0 →
        Loc T fun V g => cpull ((chains R).map (sch.map g)) I n a = 0 ∧ cpull ((chains R).map (sch.map g)) Q m b = 0)
    (E : Spc) (hE : ∀ T : Scheme.{0}, Nonempty (Sx E 0 T) → Z T) (m n : ℤ) (h : m + 1 = n) :
    Function.Bijective fun p : CohomologyClass ((chains R).obj E) I n × CohomologyClass ((chains R).obj E) Q m =>
      cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n p.1 +
        μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m p.2)
          (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
  have hz : Sec.map (P.d 1 2) (sg κ) = 0 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R W P 0 1 2 (by omega) (by omega)).2 κ).1
  have hmono := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1
  haveI := LL_ge I Q
  have key : ∀ (T : Scheme.{0}) (n' : ℤ) (a₁ : Sec (I.X n') T) (a₂ : Sec (Q.X (n' + -1)) T),
      psi W μ (sg κ) T n' (cc a₁ (n'.negOnePow • a₂)) = Sec.res (prod.snd : W ⨯ T ⟶ T) a₁ +
        μ.mul (W ⨯ T) (n' + -1) 1 n' (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) a₂) (Sec.res (prod.fst : W ⨯ T ⟶ W) (sg κ)) := by
    intro T n' a₁ a₂
    change Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ (cc a₁ (n'.negOnePow • a₂))) + n'.negOnePow • μ.mul (W ⨯ T) (n' + -1) 1 n' (by omega)
      (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ (cc a₁ (n'.negOnePow • a₂)))) (Sec.res (prod.fst : W ⨯ T ⟶ W) (sg κ)) = _
    rw [c₁_cc, c₂_cc]
    generalize n'.negOnePow = ε
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  obtain ⟨Φ, hΦ, hΦv⟩ := UpperTheory.injectiveComplex_productSection_map_quasiIso R W (LL I Q) I (LL_inj hI hQ) hI (psi W μ (sg κ))
    (fun g s a => psi_nat W μ _ g s a) (fun T s t a => UpperTheory.psi_comm_differential_of_cocycle R W μ _ hz T s t a) Z hZ
    (by
      intro T hT n' b hb
      obtain ⟨y, hy0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (W ⨯ T) I (n' - 1) n' (n' + 1) (by omega) rfl).1 b hb
      have hsy : sg y = b := (hy0 _ (𝟙 _)).trans (res_id _)
      refine hmono _ _ _ (hS T hT (n' + -1) n' (by omega) (CohomologyClass.mk y)) ?_
      rintro V g ⟨a, b', e⟩
      obtain ⟨α₁, rfl⟩ := a.mk_surjective
      obtain ⟨α₂, rfl⟩ := b'.mk_surjective
      obtain ⟨β, hβ, hσ⟩ := UpperTheory.exists_cocycle_product_eq_pull_add_cup R W _ μ κ (by omega : n' + -1 + 1 = n') α₁ α₂
      have e2 : CohomologyClass.mk (β - zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.map (𝟙 W) g)))) y (zero_add n')) = 0 := by
        rw [CohomologyClass.mk_sub, hβ, e, sub_eq_zero]
        rfl
      obtain ⟨c, hc⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (W ⨯ V) I (n' - 1) n' (n' + 1) (by omega) rfl).2 _).2.1 e2
      refine ⟨cc (sg α₁) (n'.negOnePow • sg α₂), c, ?_, ?_⟩
      · apply LLsec_ext
        · rw [c₁_d, c₁_cc, map_zero]
          exact ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V I (n' - 1) n' (n' + 1) (by omega) rfl).2 α₁).1
        · rw [c₂_d, c₂_cc, map_zero]
          have h0 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V Q (n' + -1 - 1) (n' + -1) (n' + 1 + -1) (by omega) (by omega)).2 α₂).1
          generalize n'.negOnePow = ε
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [sg, h0]
      · rw [key, ← hσ]
        have h3 : sg (β - zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.map (𝟙 W) g)))) y (zero_add n')) = Sec.map (I.d (n' - 1) n') c := hc.symm
        rw [sg_sub, sg_pull, hsy] at h3
        rw [← h3]
        abel)
    (by
      rintro T hT n' a ha ⟨c, hc⟩
      have h1 : Sec.map (I.d n' (n' + 1)) (c₁ a) = 0 := by rw [← c₁_d, ha, map_zero]
      have h2 : Sec.map (Q.d (n' + -1) (n' + 1 + -1)) (c₂ a) = 0 := by
        have := c₂_d n' (n' + 1) a
        rw [ha, map_zero] at this
        exact neg_eq_zero.1 this.symm
      have h2' : Sec.map (Q.d (n' + -1) (n' + 1 + -1)) (n'.negOnePow • c₂ a) = 0 := by
        generalize n'.negOnePow = ε
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [h2]
      obtain ⟨α₁, hα₁, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R T I (n' - 1) n' (n' + 1) (by omega) rfl).1 _ h1
      obtain ⟨α₂, hα₂, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R T Q (n' + -1 - 1) (n' + -1) (n' + 1 + -1) (by omega) (by omega)).1 _ h2'
      have hs₁ : sg α₁ = c₁ a := (hα₁ _ (𝟙 _)).trans (res_id _)
      have hs₂ : sg α₂ = n'.negOnePow • c₂ a := (hα₂ _ (𝟙 _)).trans (res_id _)
      obtain ⟨β, hβ, hσ⟩ := UpperTheory.exists_cocycle_product_eq_pull_add_cup R W _ μ κ (by omega : n' + -1 + 1 = n') α₁ α₂
      have ha' : a = cc (sg α₁) (n'.negOnePow • sg α₂) := by
        apply LLsec_ext
        · rw [c₁_cc, hs₁]
        · rw [c₂_cc, hs₂]
          generalize n'.negOnePow = ε
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      have e0 : CohomologyClass.mk β = 0 := by
        refine ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (W ⨯ T) I (n' - 1) n' (n' + 1) (by omega) rfl).2 β).2.2 ⟨c, ?_⟩
        rw [← hc]
        change _ = sg β
        rw [hσ, ← key, ← ha']
      refine hmono _ _ _ (hJ T hT (n' + -1) n' (by omega) (CohomologyClass.mk α₁) (CohomologyClass.mk α₂) (by rw [← hβ, e0])) ?_
      rintro V g ⟨e₁, e₂⟩
      obtain ⟨y₁, hy₁⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V I (n' - 1) n' (n' + 1) (by omega) rfl).2
        (zcomp (Cocycle.ofHom ((chains R).map (sch.map g))) α₁ (zero_add n'))).2.1 e₁
      obtain ⟨y₂, hy₂⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V Q (n' - 1 + -1) (n' + -1) (n' + 1 + -1) (by omega) (by omega)).2
        (zcomp (Cocycle.ofHom ((chains R).map (sch.map g))) α₂ (zero_add (n' + -1)))).2.1 e₂
      change _ = sg _ at hy₁
      change _ = sg _ at hy₂
      rw [sg_pull, hs₁] at hy₁
      rw [sg_pull, hs₂] at hy₂
      refine ⟨cc y₁ (-(n'.negOnePow • y₂)), ?_⟩
      apply LLsec_ext
      · rw [c₁_d, c₁_cc, c₁_res, hy₁]
      · rw [c₂_d, c₂_cc, c₂_res]
        generalize n'.negOnePow = ε at hy₂ ⊢
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [hy₂])
    E hE
  have hf : ∀ (α₁ : Cocycle ((chains R).obj E) I n) (α₂ : Cocycle ((chains R).obj E) Q m),
      Φ n (CohomologyClass.mk (inL h α₁ α₂)) = cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n (CohomologyClass.mk α₁) +
        μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m (CohomologyClass.mk α₂))
          (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
    intro α₁ α₂
    obtain ⟨β, hβ, hv⟩ := hΦv n (inL h α₁ α₂)
    rw [hβ]
    exact UpperTheory.exteriorCup_cocycle_exists_of_pairing R W μ κ h α₁ α₂ β hv
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hpp
    obtain ⟨α₁, rfl⟩ := a.mk_surjective
    obtain ⟨α₂, rfl⟩ := b.mk_surjective
    obtain ⟨α₁', rfl⟩ := a'.mk_surjective
    obtain ⟨α₂', rfl⟩ := b'.mk_surjective
    have h0 : Φ n (CohomologyClass.mk (inL h (α₁ - α₁') (α₂ - α₂'))) = 0 := by
      rw [hf, CohomologyClass.mk_sub, CohomologyClass.mk_sub, map_sub, map_sub, map_sub, AddMonoidHom.sub_apply]
      beta_reduce at hpp
      rw [sub_add_sub_comm, hpp, sub_self]
    have h1 := (hΦ n).1 (h0.trans (map_zero _).symm)
    obtain ⟨e₁, e₂⟩ := (UpperTheory.cohomologyClass_inL_surjective_and_injective R h).2 _ _ h1
    rw [CohomologyClass.mk_sub, sub_eq_zero] at e₁ e₂
    rw [e₁, e₂]
  · intro y
    obtain ⟨x, rfl⟩ := (hΦ n).2 y
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨α₁, α₂, e⟩ := (UpperTheory.cohomologyClass_inL_surjective_and_injective R h).1 x
    exact ⟨(CohomologyClass.mk α₁, CohomologyClass.mk α₂), by rw [e]; exact (hf α₁ α₂).symm⟩

end UpperTheory.Kun

private theorem UpperTheory.Kun.main (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E) (m j : ℤ) :
    Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
        cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q)) := by
  obtain ⟨κ, hκ⟩ := (kappa q).mk_surjective
  have hr := fun i : ℤ => GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  haveI := (hr (j + 1)).2.2.1
  haveI := (hr j).2.2.1
  have hmono := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1
  have h := UpperTheory.Kun.genK (Gq q) (res _ (tw q (j + 1))) (res _ (tw q j)) (res _ (tw q 1)) (hr (j + 1)).2.1 (hr j).2.1
    (twPair q j 1) κ (fun T => IsUnit (q : Γ(T, ⊤)))
    (fun {T' T} f hT => by simpa using hT.map f.appTop.hom)
    (by
      intro T hT m' n' h' y
      subst h'
      refine hmono _ _ _ ((UpperTheory.locally_surjective_multiplicativeGroupKunnethMap q T hT m' j).1 y) ?_
      rintro V g ⟨p, e⟩
      exact ⟨p.1, p.2, by rw [hκ]; exact e⟩)
    (by
      intro T hT m' n' h' a b e
      subst h'
      exact (UpperTheory.locally_surjective_multiplicativeGroupKunnethMap q T hT m' j).2 (a, b) (by rw [hκ] at e; exact e))
    E hE m (m + 1) rfl
  rw [hκ] at h
  exact h

theorem UpperTheory.bijective_cohomology_gm_product_kummer_cup :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ n i : ℤ, Function.Bijective fun p : Ht q E n i × Ht q E (n - 1) (i - 1) =>
        pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
          ((cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q))).cast (by ring) (by ring) : Ht q (sch.obj (Gq q) ⨯ E) n i) := by
  intro q _ E hE n i
  have key : ∀ (m j n' i' : ℤ) (hn : m + 1 = n') (hi : j + 1 = i'), Function.Bijective fun p : Ht q E n' i' × Ht q E m j =>
      pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
        ((cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q))).cast hn hi : Ht q (sch.obj (Gq q) ⨯ E) n' i') := by
    intro m j n' i' hn hi
    subst hn hi
    exact UpperTheory.Kun.main q E hE m j
  exact key (n - 1) (i - 1) n i (by ring) (by ring)

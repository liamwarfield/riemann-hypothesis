module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleCochainPresheafIsSheaf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleCochainPresheafIsSheaf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC.CotSheaf

def evF (p : ℕ) (V : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p)) ⋙ (evaluation Scheme.{0}ᵒᵖ Type).obj (op V)

instance (A B : Spc) (p : ℕ) (V : Scheme.{0}) : PreservesLimit (pair A B) (evF p V) := by
  unfold evF; infer_instance

def prodEquiv (A B : Spc) (p : ℕ) (V : Scheme.{0}) : Sx (A ⨯ B) p V ≃ Sx A p V × Sx B p V :=
  ((PreservesLimitPair.iso (evF p V) A B) ≪≫ Types.binaryProductIso _ _).toEquiv

theorem prodEquiv_apply {A B : Spc} {p : ℕ} {V : Scheme.{0}} (y : Sx (A ⨯ B) p V) :
    prodEquiv A B p V y = (Sx.map prod.fst y, Sx.map prod.snd y) := by
  have e1 := ConcreteCategory.congr_hom (prodComparison_fst (evF p V) A B) y
  have e2 := ConcreteCategory.congr_hom (prodComparison_snd (evF p V) A B) y
  simp only [prodEquiv, Iso.toEquiv, Iso.trans_hom, PreservesLimitPair.iso_hom]
  ext
  · simp
    exact e1
  · simp
    exact e2

variable {p : ℕ}

theorem map_res' {E E' : Spc} (φ : E ⟶ E') {V W : Scheme.{0}} (k : W ⟶ V) (y : Sx E p V) :
    Sx.map φ (y.res k) = (Sx.map φ y).res k :=
  ConcreteCategory.congr_hom ((φ.app (op (SimplexCategory.mk p))).naturality k.op) y

theorem map_comp' {E E' E'' : Spc} (φ : E ⟶ E') (ψ : E' ⟶ E'') {V : Scheme.{0}} (y : Sx E p V) :
    Sx.map (φ ≫ ψ) y = Sx.map ψ (Sx.map φ y) := rfl

theorem res_res {E : Spc} {V W W' : Scheme.{0}} (k : W ⟶ V) (g : W' ⟶ W) (y : Sx E p V) :
    (y.res k).res g = y.res (g ≫ k) :=
  (ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_comp k.op g.op) y).symm

theorem res_id {E : Spc} {V : Scheme.{0}} (y : Sx E p V) : y.res (𝟙 V) = y :=
  ConcreteCategory.congr_hom ((E.obj (op (SimplexCategory.mk p))).map_id (op V)) y

theorem prod_ext {A B : Spc} {V : Scheme.{0}} {y y' : Sx (A ⨯ B) p V} (h1 : Sx.map prod.fst y = Sx.map prod.fst y')
    (h2 : Sx.map prod.snd y = Sx.map prod.snd y') : y = y' :=
  (prodEquiv A B p V).injective (by rw [prodEquiv_apply, prodEquiv_apply, h1, h2])

def mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx (A ⨯ B) p V := (prodEquiv A B p V).symm (a, b)

theorem fst_mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx.map prod.fst (mkS a b) = a := by
  have := (prodEquiv A B p V).apply_symm_apply (a, b)
  rw [prodEquiv_apply] at this
  exact congrArg Prod.fst this

theorem snd_mkS {A B : Spc} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx.map prod.snd (mkS a b) = b := by
  have := (prodEquiv A B p V).apply_symm_apply (a, b)
  rw [prodEquiv_apply] at this
  exact congrArg Prod.snd this

def mk1 {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : Sx (sch.obj W ⨯ F) p W := mkS (A := sch.obj W) (𝟙 W) z

theorem simplexImage_fst_schemeProductSimplexIdFirst {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : (Sx.map prod.fst (mk1 z) : W ⟶ W) = 𝟙 W :=
  fst_mkS (A := sch.obj W) _ _

theorem simplexImage_snd_schemeProductSimplexIdFirst {F : Spc} {W : Scheme.{0}} (z : Sx F p W) : Sx.map prod.snd (mk1 z) = z :=
  snd_mkS (A := sch.obj W) _ _

theorem fst_pm {F : Spc} {U U' V : Scheme.{0}} (f : U' ⟶ U) (y : Sx (sch.obj U' ⨯ F) p V) :
    (Sx.map prod.fst (Sx.map (prod.map (sch.map f) (𝟙 F)) y) : V ⟶ U) = (Sx.map prod.fst y : V ⟶ U') ≫ f := by
  rw [← map_comp', prod.map_fst, map_comp']
  rfl

theorem snd_pm {F : Spc} {U U' V : Scheme.{0}} (f : U' ⟶ U) (y : Sx (sch.obj U' ⨯ F) p V) :
    Sx.map prod.snd (Sx.map (prod.map (sch.map f) (𝟙 F)) y) = Sx.map prod.snd y := by
  rw [← map_comp', prod.map_snd, Category.comp_id]

theorem fst_res {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    (Sx.map prod.fst (y.res k) : W ⟶ U) = k ≫ (Sx.map prod.fst y : V ⟶ U) := by
  rw [map_res']
  rfl

theorem snd_res {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    Sx.map prod.snd (y.res k) = (Sx.map prod.snd y).res k :=
  map_res' _ _ _

theorem yres_eq {F : Spc} {U V W : Scheme.{0}} (k : W ⟶ V) (y : Sx (sch.obj U ⨯ F) p V) :
    y.res k = Sx.map (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 F)) (mk1 ((Sx.map prod.snd y).res k)) :=
  prod_ext (by rw [fst_pm, simplexImage_fst_schemeProductSimplexIdFirst, Category.id_comp, fst_res]) (by rw [snd_pm, simplexImage_snd_schemeProductSimplexIdFirst, snd_res])

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]
  have hQ : ∀ s, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).property)
  have sres_res : ∀ (s : ℤ) {V W W' : Scheme.{0}} (k : W ⟶ V) (g : W' ⟶ W) (v : Sec (I.X s) V),
      Sec.res g (Sec.res k v) = Sec.res (g ≫ k) v := fun s V W W' k g v =>
    (ConcreteCategory.congr_hom (((I.X s).obj).map_comp k.op g.op) v).symm
  have sres_id : ∀ (s : ℤ) {V : Scheme.{0}} (v : Sec (I.X s) V), Sec.res (𝟙 V) v = v := fun s V v =>
    ConcreteCategory.congr_hom (((I.X s).obj).map_id (op V)) v
  intro U S hS
  have hsep : Presieve.IsSeparatedFor (cotPre R q N I n ⋙ forget _) S.arrows := by
    intro x α β hα hβ
    have hc : ∀ (W : Scheme.{0}) (c : W ⟶ U), S.arrows c →
        (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) =
        (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp β (zero_add n) :=
      fun W c hc => (hα c hc).trans (hβ c hc).symm
    refine ev_ext _ _ fun p s h V y => ?_
    refine (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).isSeparatedFor.ext
      fun W k hk => ?_
    have e1 := ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) α p s h k y
    have e2 := ev_res (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) β p s h k y
    refine e1.trans (Eq.trans ?_ e2.symm)
    have e3 := ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) α
      p s h W (mk1 ((Sx.map prod.snd y).res k))
    have e4 := ev_pull (R := R) (I := I) (n := n) (prod.map (sch.map (k ≫ (Sx.map prod.fst y : V ⟶ U))) (𝟙 (fibQ q N))) β
      p s h W (mk1 ((Sx.map prod.snd y).res k))
    rw [yres_eq k y, ← e3, ← e4, hc _ _ hk]
  refine hsep.isSheafFor fun x hx => ?_
  have hx' := (Presieve.compatible_iff_sieveCompatible x).1 hx
  have evx : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c c' : W ⟶ U) (hc : S.arrows c)
      (hc' : S.arrows c') (w w' : Sx (sch.obj W ⨯ fibQ q N) p V), c = c' → w = w' →
        ev (x c hc) p s h V w = ev (x c' hc') p s h V w' := by
    rintro p s h V W c c' hc hc' w w' rfl rfl
    rfl
  have gen : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V W : Scheme.{0}} (c : W ⟶ U) (hc : S.arrows c)
      (w : Sx (sch.obj W ⨯ fibQ q N) p V), ev (x c hc) p s h V w =
        ev (x ((Sx.map prod.fst w : V ⟶ W) ≫ c) (S.downward_closed hc _)) p s h V (mk1 (Sx.map prod.snd w)) := by
    intro p s h V W c hc w
    have e2 := ev_pull (R := R) (I := I) (n := n) (E := sch.obj W ⨯ fibQ q N)
      (prod.map (sch.map (Sx.map prod.fst w : V ⟶ W)) (𝟙 (fibQ q N))) (x c hc) p s h V (mk1 (Sx.map prod.snd w))
    rw [hx' c (Sx.map prod.fst w : V ⟶ W) hc]
    refine Eq.trans ?_ e2.symm
    congr 1
    exact (prod_ext ((fst_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (by rw [simplexImage_fst_schemeProductSimplexIdFirst]; exact Category.id_comp _))
      ((snd_pm (Sx.map prod.fst w : V ⟶ W) (mk1 (Sx.map prod.snd w))).trans (simplexImage_snd_schemeProductSimplexIdFirst _))).symm
  let φ : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V),
      Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
        (S.pullback (Sx.map prod.fst y : V ⟶ U)).arrows :=
    fun p s h V y W k hk => ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k))
  have hφ : ∀ p s h V y, (φ p s h V y).Compatible := by
    intro p s h V y
    rw [Presieve.compatible_iff_sieveCompatible]
    intro W W' k g hk
    change ev (x (g ≫ k ≫ _) _) p s h W' (mk1 _) = Sec.res g (ev (x (k ≫ _) hk) p s h W (mk1 _))
    refine Eq.trans ?_ (ev_res (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) (n := n) (x (k ≫ _) hk) p s h g _).symm
    refine Eq.trans ?_ (gen p s h _ hk _).symm
    apply evx
    · rw [fst_res, simplexImage_fst_schemeProductSimplexIdFirst, Category.comp_id]
    · rw [snd_res, simplexImage_snd_schemeProductSimplexIdFirst, res_res]
  let val : ∀ (p : ℕ) (s : ℤ) (_ : -(p : ℤ) + n = s) (V : Scheme.{0}), Sx (sch.obj U ⨯ fibQ q N) p V → Sec (I.X s) V :=
    fun p s h V y => (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).amalgamate
      (φ p s h V y) (hφ p s h V y)
  have hval : ∀ p s h V y {W : Scheme.{0}} (k : W ⟶ V) (hk : S.arrows (k ≫ Sx.map prod.fst y)),
      Sec.res k (val p s h V y) = ev (x (k ≫ Sx.map prod.fst y) hk) p s h W (mk1 ((Sx.map prod.snd y).res k)) :=
    fun p s h V y W k hk =>
      (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst y : V ⟶ U) hS)).valid_glue (hφ p s h V y) k hk
  have hnat : ∀ p s h (V V' : Scheme.{0}) (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V),
      Sec.res g (val p s h V y) = val p s h V' (y.res g) := by
    intro p s h V V' g y
    refine (hQ s _ (Scheme.etaleTopology.pullback_stable (Sx.map prod.fst (y.res g) : V' ⟶ U) hS)).isSeparatedFor.ext
      fun W k hk => ?_
    change Sec.res k (Sec.res g _) = Sec.res k (val p s h V' (y.res g))
    have hk' : S.arrows ((k ≫ g) ≫ Sx.map prod.fst y) := by
      have : S.arrows (k ≫ Sx.map prod.fst (y.res g)) := hk
      rw [fst_res] at this
      convert this using 2
      exact Category.assoc _ _ _
    rw [sres_res, hval _ _ _ _ _ _ hk', hval _ _ _ _ _ _ hk]
    apply evx
    · rw [fst_res]
      exact Category.assoc _ _ _
    · rw [snd_res, res_res]
  obtain ⟨α, hα⟩ := ev_exists (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) val
    (fun p s h V' V g y => hnat p s h V V' g y)
  refine ⟨α, fun W c hc => ?_⟩
  change (Cochain.ofHom ((chains R).map (prod.map (sch.map c) (𝟙 (fibQ q N))))).comp α (zero_add n) = x c hc
  refine ev_ext _ _ fun p s h V w => ?_
  have h1 : S.arrows (𝟙 V ≫ Sx.map prod.fst (Sx.map (prod.map (sch.map c) (𝟙 (fibQ q N))) w)) := by
    have := S.downward_closed hc (Sx.map prod.fst w : V ⟶ W)
    convert this using 2
    exact (Category.id_comp _).trans (fst_pm c w)
  refine (ev_pull (R := R) (I := I) (n := n) (E := sch.obj U ⨯ fibQ q N) _ α p s h V w).trans ?_
  rw [hα]
  refine (sres_id s _).symm.trans ((hval _ _ _ _ _ _ h1).trans ?_)
  refine Eq.trans ?_ (gen p s h c hc w).symm
  apply evx
  · exact (Category.id_comp _).trans (fst_pm c w)
  · rw [res_id, snd_pm]

end GlobalTheory.EtC.CotSheaf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleCochainPresheafIsSheafStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projBundleCochainPresheaf_isSheaf : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ), Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  first | (exact @GlobalTheory.EtC.CotSheaf.cotPre_isSheaf) | (exact GlobalTheory.EtC.CotSheaf.cotPre_isSheaf) | (intros; apply GlobalTheory.EtC.CotSheaf.cotPre_isSheaf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibre
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

noncomputable section

namespace GlobalTheory.EtC.DiscCoch

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := GlobalTheory.T.projBundleCochainPresheaf_isSheaf R q N I n

theorem jsec_bij (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) (U : Scheme.{0}) :
    Function.Bijective (fun c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n =>
      (Jsec c : Sec ((Jcx R q N I).X n) U)) := by
  have := isIso_toSheafify Scheme.etaleTopology.{0} (cotPre_isSheaf R q N I n)
  have h2 : IsIso ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)) := inferInstance
  exact ConcreteCategory.bijective_of_isIso ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U))

theorem glue (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ)
    (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n)
    (hc : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c V (F.map g.op x) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) :
    ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)),
      (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) =
        c U x := GlobalTheory.T.unique_cochain_on_disc_product R q N I F n c hc

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {F : PSh}

theorem sec_map_at_zero {A B : Shv R} {U : Scheme.{0}} (φ : A ⟶ B) : Sec.map φ (0 : Sec A U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

theorem jsec_res {n : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec.res g (Jsec c) = Jsec ((Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp c (zero_add n)) :=
  (ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).naturality g.op) c).symm

theorem jsec_d {n m : ℤ} (hm : n + 1 = m) {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec.map ((Jcx R q N I).d n m) (Jsec c) = Jsec (δ n m c) := by
  subst hm
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (cotD R q N I n))) c
  have hd : (Jcx R q N I).d n (n + 1) = (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n) :=
    by simp only [Jcx, CochainComplex.of_d]
  rw [hd]
  exact h.symm

theorem jsec_add {n : ℤ} {U : Scheme.{0}} (a b : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    (Jsec (a + b) : Sec ((Jcx R q N I).X n) U) = Jsec a + Jsec b :=
  map_add ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom a b

theorem jsec_zero {n : ℤ} {U : Scheme.{0}} :
    (Jsec (0 : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) : Sec ((Jcx R q N I).X n) U) = 0 :=
  map_zero ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom

def ptFst {U : Scheme.{0}} (x : F.obj (op U)) : sch.obj U ⟶ disc.obj F := disc.map (yonedaEquiv.symm x)

theorem ptFst_res {V U : Scheme.{0}} (g : V ⟶ U) (x : F.obj (op U)) : ptFst (F.map g.op x) = sch.map g ≫ ptFst x := by
  have e : yonedaEquiv.symm (F.map g.op x) = yoneda.map g ≫ yonedaEquiv.symm x := yonedaEquiv_symm_map g.op x
  show disc.map (yonedaEquiv.symm (F.map g.op x)) = disc.map (yoneda.map g) ≫ disc.map (yonedaEquiv.symm x)
  exact (congrArg disc.map e).trans (disc.map_comp _ _)

def ptMap {U : Scheme.{0}} (x : F.obj (op U)) : sch.obj U ⨯ fibQ q N ⟶ disc.obj F ⨯ fibQ q N :=
  prod.map (ptFst x) (𝟙 (fibQ q N))

def ptPull {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {U : Scheme.{0}} (x : F.obj (op U)) :
    Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (Cochain.ofHom ((chains R).map (ptMap (q := q) (N := N) x))).comp γ (zero_add n)

theorem ptMap_res {V U : Scheme.{0}} (g : V ⟶ U) (x : F.obj (op U)) :
    (ptMap (F.map g.op x) : sch.obj V ⨯ fibQ q N ⟶ _) = prod.map (sch.map g) (𝟙 (fibQ q N)) ≫ ptMap x := by
  unfold ptMap
  rw [ptFst_res, prod.map_map, Category.comp_id]

theorem ptPull_res {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : F.obj (op U)) : ptPull γ (F.map g.op x) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (ptPull γ x) (zero_add n) := by
  unfold ptPull
  rw [ptMap_res (q := q) (N := N), Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem comp_δ {K L M : Cx R} {n m : ℤ} (hm : n + 1 = m) (f : K ⟶ L) (γ : Cochain L M n) :
    δ n m ((Cochain.ofHom f).comp γ (zero_add n)) = (Cochain.ofHom f).comp (δ n m γ) (zero_add m) := by
  rw [δ_zero_cochain_comp _ _ _ hm, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem ptPull_δ {n m : ℤ} (hm : n + 1 = m) (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n)
    {U : Scheme.{0}} (x : F.obj (op U)) : ptPull (δ n m γ) x = δ n m (ptPull γ x) :=
  (comp_δ hm _ γ).symm

theorem ptPull_add {n : ℤ} (a b : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {U : Scheme.{0}}
    (x : F.obj (op U)) : ptPull (a + b) x = ptPull a x + ptPull b x := Cochain.comp_add _ _ _ _

theorem ptPull_zero {n : ℤ} {U : Scheme.{0}} (x : F.obj (op U)) :
    ptPull (0 : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) x = 0 := Cochain.comp_zero _ _

theorem ev_zero_of_v {E : Spc} {L : Cx R} {n : ℤ} (β : Cochain ((chains R).obj E) L n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hβ : β.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : ev (R := R) β p s h U x = 0 := by
  unfold ev
  rw [hβ, comp_zero]
  rfl

theorem conc_δ {L : Cx R} {n m : ℤ} (hm : n + 1 = m) (β : Cochain ((chains R).obj (disc.obj F)) L n)
    (hβ : ∀ (p : ℕ) s h U x, ev (R := R) β (p + 1) s h U x = 0) :
    ∀ (p : ℕ) s h U x, ev (R := R) (δ n m β) (p + 1) s h U x = 0 := by
  have ev_def {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  have ev_δ_succ {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
      (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
      ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) α p t (by omega) U (x.face i) := by
    rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def,
      Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [freeGen_map]
    rfl
  intro p s h U x
  rw [ev_δ_succ hm β U p (s - m + n) s (by omega) h x, hβ, sec_map_at_zero, zero_add]
  cases p with
  | zero =>
    have hf : ∀ i, Sx.face x i = x := fun i => rfl
    simp [Fin.sum_univ_two, hf]
  | succ p => simp [hβ]

end GlobalTheory.EtC.DiscCoch

namespace GlobalTheory.EtC.DiscCoch

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {F : PSh}

def aS {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx (disc.obj F) p U → Sec ((Jcx R q N I).X s) U
  | 0, s, h, U, x => (show n = s by simpa using h) ▸ Jsec (ptPull γ (show F.obj (op U) from x))
  | _ + 1, _, _, _, _ => 0

theorem exS {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) n,
      (∀ (U : Scheme.{0}) (x : F.obj (op U)), ev (R := R) β 0 n (by simp) U x = Jsec (ptPull γ x)) ∧
      ∀ (p : ℕ) s h U x, ev (R := R) β (p + 1) s h U x = 0 := by
  have ev_exists {E : Spc} {I : Cx R} {n : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
      (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x := by
    have key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) =
          a p j (hp ▸ hij) U x := by
      intro i j hij
      by_cases hi : i ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
        refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
        obtain rfl : k = p := by omega
        rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
        exact hφ U x
      · exact ⟨0, fun p hp => by omega⟩
    choose φ hφ using key
    refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
    have := hφ _ _ h p rfl U x
    rw [eqToHom_refl, Category.id_comp] at this
    exact this
  obtain ⟨β, hβ⟩ := ev_exists (E := disc.obj F) (I := Jcx R q N I) (n := n) (aS γ) (by
    intro p s h V U g x
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      exact (jsec_res g _).trans (congrArg Jsec (ptPull_res γ g x).symm)
    | succ p => exact map_zero _)
  exact ⟨β, fun U x => hβ 0 n _ U x, fun p s h U x => hβ (p + 1) s h U x⟩

theorem model : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ), ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+ CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n) (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) → (∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ev (R := R) β.1 0 n (by simp) U x = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev (R := R) c k s hs V y = ev (R := R) γ.1 k s hs V (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) → e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  intro R _ q N I F n
  have ev_def {E : Spc} {J : Cx R} {m : ℤ} (α : Cochain ((chains R).obj E) J m)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + m = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  have ev_ext {E : Spc} {J : Cx R} {m : ℤ} (α β : Cochain ((chains R).obj E) J m)
      (h : ∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) : α = β := by
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact free_ext _ _ (fun U x => h k s hs U x)
    · exact (isZero_chains E p (by omega)).eq_of_src _ _
  have ev_res {E : Spc} {J : Cx R} {m : ℤ} (α : Cochain ((chains R).obj E) J m)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + m = s) {V U : Scheme.{0}} (g : V ⟶ U)
      (x : Sx E p U) : Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g) := by
    rw [ev_def, map_res, freeGen_res]
    rfl
  have ev_add {E : Spc} {J : Cx R} {m : ℤ} (a b : Cochain ((chains R).obj E) J m)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + m = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) (a + b) p s h U x = ev (R := R) a p s h U x + ev (R := R) b p s h U x := by
    simp [ev, Cochain.add_v]
  have ev_δ_zero {E : Spc} {J : Cx R} {n m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) J n) (U : Scheme.{0}) (s t : ℤ)
      (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t) (x : Sx E 0 U) :
      ev (R := R) (δ n m α) 0 t ht U x = Sec.map (J.d s t) (ev (R := R) α 0 s hs U x) := by
    rw [ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp),
      (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]
    rfl
  have ev_pull {E E' : Spc} {J : Cx R} {m : ℤ} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) J m)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + m = s) (U : Scheme.{0}) (x : Sx E' p U) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add m)) p s h U x = ev (R := R) α p s h U (x.map f) := by
    rw [ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [freeGen_map]
    rfl
  have ev_zero {E : Spc} {J : Cx R} {m : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + m = s)
      (U : Scheme.{0}) (x : Sx E p U) :
      ev (0 : Cochain ((chains R).obj E) J m) p s h U x = 0 := by
    rw [ev_def, Cochain.zero_v, comp_zero]
    rfl
  choose S hS0 hS1 using fun (m : ℤ) (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m) => exS γ
  have hSδ : ∀ (m m' : ℤ) (hm : m + 1 = m') (η : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m),
      S m' (δ m m' η) = δ m m' (S m η) := by
    intro m m' hm η
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : m' = s := by omega
      rw [hS0, ev_δ_zero hm (S m η) U m m' (by simp) h x, hS0, jsec_d hm, ptPull_δ hm]
    | succ p => rw [hS1, conc_δ hm _ (hS1 m η)]
  have hSadd : ∀ (γ γ' : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), S n (γ + γ') = S n γ + S n γ' := by
    intro γ γ'
    apply ev_ext
    intro p s h U x
    rw [ev_add]
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      rw [hS0, hS0, hS0, ptPull_add, jsec_add]
    | succ p => rw [hS1, hS1, hS1, add_zero]
  have hSzero : ∀ m : ℤ, S m 0 = 0 := by
    intro m
    apply ev_ext
    intro p s h U x
    rw [ev_zero]
    cases p with
    | zero =>
      obtain rfl : m = s := by omega
      rw [hS0, ptPull_zero, jsec_zero]
    | succ p => rw [hS1]
  have hScyc : ∀ γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, δ n (n + 1) (S n γ.1) = 0 := by
    intro γ
    rw [← hSδ n (n + 1) rfl, Cocycle.δ_eq_zero, hSzero]
  let Sc : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n →+
      CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n :=
    AddMonoidHom.mk' (fun γ => CohomologyClass.mk (Cocycle.mk (S n γ.1) (n + 1) rfl (hScyc γ))) (by
      intro a b
      rw [← CohomologyClass.mk_add]
      exact congrArg CohomologyClass.mk (Cocycle.ext (hSadd a.1 b.1)))
  have hcob : coboundaries ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n ≤ Sc.ker := by
    rintro ⟨γ, hγ⟩ ⟨n', hn', η, rfl⟩
    change CohomologyClass.mk _ = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', S n' η, (hSδ n' n hn' η).symm⟩
  let Φ := CohomologyClass.descAddMonoidHom Sc hcob
  have hnat : ∀ (m : ℤ) (b : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) m)
      (c' : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I m),
      (∀ U x, Jsec (c' U x) = ev (R := R) b 0 m (by simp) U x) →
      ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c' V (F.map g.op x) =
        (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c' U x) (zero_add m) := by
    intro m b c' hc' V U g x
    apply (jsec_bij R q N I m V).1
    change Jsec _ = Jsec _
    rw [hc', ← jsec_res, hc', ev_res]
    rfl
  have hΦinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨γ, rfl⟩ := c.mk_surjective
    change CohomologyClass.mk _ = 0 at hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc
    obtain ⟨n', hn', β', hβ'⟩ := hc
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n',
        Jsec c = ev (R := R) β' 0 n' (by simp) U x := fun U x => (jsec_bij R q N I n' U).2 _
    choose c' hc' using hc'
    obtain ⟨η, hη, -⟩ := glue R q N I F n' c' (hnat n' β' c' hc')
    have h2 : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ptPull (δ n' n η) x = ptPull γ.1 x := by
      intro U x
      have h1 : ptPull η x = c' U x := hη U x
      rw [ptPull_δ hn', h1]
      apply (jsec_bij R q N I n U).1
      change Jsec _ = Jsec _
      rw [← jsec_d hn', hc', ← ev_δ_zero hn' β' U n' n (by simp) (by simp) x]
      rw [hβ']
      exact hS0 n γ.1 U x
    have huniq := (glue R q N I F n (fun U x => ptPull γ.1 x) (fun V U g x => ptPull_res γ.1 g x)).unique
      (y₁ := γ.1) (y₂ := δ n' n η) (fun U x => rfl) h2
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', η, huniq.symm⟩
  have hΦsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨α, hαc, hα0⟩ := GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos R F (Jcx R q N I) n c
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
        Jsec c = ev (R := R) α.1 0 n (by simp) U x := fun U x => (jsec_bij R q N I n U).2 _
    choose c' hc' using hc'
    obtain ⟨γ, hγ, -⟩ := glue R q N I F n c' (hnat n α.1 c' hc')
    have hδ : δ n (n + 1) γ = 0 := by
      refine (glue R q N I F (n + 1) (fun U x => 0) (fun V U g x => (Cochain.comp_zero _ _).symm)).unique
        (fun U x => ?_) (fun U x => Cochain.comp_zero _ _)
      show ptPull (δ n (n + 1) γ) x = 0
      rw [ptPull_δ rfl, show ptPull γ x = c' U x from hγ U x]
      apply (jsec_bij R q N I (n + 1) U).1
      change Jsec _ = Jsec _
      rw [← jsec_d rfl, hc', ← ev_δ_zero rfl α.1 U n (n + 1) (by simp) (by simp) x, Cocycle.δ_eq_zero, ev_zero,
        jsec_zero]
    refine ⟨CohomologyClass.mk (Cocycle.mk γ (n + 1) rfl hδ), ?_⟩
    rw [← hαc]
    change CohomologyClass.mk _ = _
    congr 1
    apply Cocycle.ext
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      show ev (R := R) (S n γ) 0 n h U x = ev (R := R) α.1 0 n h U x
      rw [hS0, show ptPull γ x = c' U x from hγ U x, hc']
    | succ p =>
      show ev (R := R) (S n γ) (p + 1) s h U x = ev (R := R) α.1 (p + 1) s h U x
      rw [hS1, ev_zero_of_v _ _ _ _ (hα0 (p + 1) (by omega) s h)]
  refine ⟨(AddEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm, fun β γ hβ0 hβc => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  change CohomologyClass.mk β = CohomologyClass.mk _
  congr 1
  apply Cocycle.ext
  apply ev_ext
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : n = s := by omega
    obtain ⟨c, hc1, hc2⟩ := hβc U x
    show ev (R := R) β.1 0 n h U x = ev (R := R) (S n γ.1) 0 n h U x
    rw [hS0, hc1]
    congr 1
    apply ev_ext
    intro k s hs V y
    rw [hc2]
    exact (ev_pull _ γ.1 k s hs V y).symm
  | succ p =>
    show ev (R := R) β.1 (p + 1) s h U x = ev (R := R) (S n γ.1) (p + 1) s h U x
    rw [hS1, ev_zero_of_v _ _ _ _ (hβ0 (p + 1) (by omega) s h)]

end GlobalTheory.EtC.DiscCoch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibreStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open GlobalTheory.EtC.CupSpec GlobalTheory.EtC.DiscCoch in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre :
    ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ),
      ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+
          CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n,
        ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n)
          (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n),
          (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) →
          (∀ (U : Scheme.{0}) (x : F.obj (op U)),
            ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
              ev (R := R) β.1 0 n (by simp) U x = Jsec c ∧
              ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0})
                (y : Sx (sch.obj U ⨯ fibQ q N) k V),
                ev (R := R) c k s hs V y =
                  ev (R := R) γ.1 k s hs V
                    (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) →
          e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  intro R _ q N I F n
  -- Evaluate cochains on the free generators of the sheaves of chains.
  have ev_def {E : Spc} {L : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  have ev_ext {E : Spc} {L : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) L n)
      (h : ∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) : α = β := by
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact free_ext _ _ (fun U x => h k s hs U x)
    · exact (isZero_chains E p (by omega)).eq_of_src _ _
  have ev_exists {E : Spc} {L : Cx R} {n : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (L.X s) U)
      (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
      ∃ α : Cochain ((chains R).obj E) L n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x := by
    have key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ L.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) =
          a p j (hp ▸ hij) U x := by
      intro i j hij
      by_cases hi : i ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
        refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
        obtain rfl : k = p := by omega
        rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
        exact hφ U x
      · exact ⟨0, fun p hp => by omega⟩
    choose φ hφ using key
    refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
    have := hφ _ _ h p rfl U x
    rw [eqToHom_refl, Category.id_comp] at this
    exact this
  have ev_res {E : Spc} {L : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
      (x : Sx E p U) : Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g) := by
    rw [ev_def, map_res, freeGen_res]
    rfl
  have ev_add {E : Spc} {L : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) (a + b) p s h U x = ev (R := R) a p s h U x + ev (R := R) b p s h U x := by
    simp [_root_.GlobalTheory.EtC.ev, Cochain.add_v]
  let evHom {E : Spc} (I : Cx R) (n : ℤ) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
    AddMonoidHom.mk' (fun a => ev (R := R) a p s h U x) (fun a b => ev_add a b p s h U x)
  have ev_zero {E : Spc} {L : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) (0 : Cochain ((chains R).obj E) L n) p s h U x = 0 := map_zero (evHom L n p s h U x)
  have ev_pull {E : Spc} {L : Cx R} {n : ℤ} {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
      (U : Scheme.{0}) (x : Sx E' p U) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev (R := R) α p s h U (x.map f) := by
    rw [ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [freeGen_map]
    rfl
  have ev_δ_zero {E : Spc} {L : Cx R} {n : ℤ} {m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) L n) (U : Scheme.{0}) (s t : ℤ)
      (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t) (x : Sx E 0 U) :
      ev (R := R) (δ n m α) 0 t ht U x = Sec.map (L.d s t) (ev (R := R) α 0 s hs U x) := by
    rw [ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp),
      (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]
    rfl
  have ev_δ_succ {E : Spc} {L : Cx R} {n : ℤ} {m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) L n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
      (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
      ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (L.d s t) (ev (R := R) α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) α p t (by omega) U (x.face i) := by
    rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def,
      Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [freeGen_map]
    rfl
  have ev_zero_of_v {E : Spc} {L : Cx R} {n : ℤ} (β : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hβ : β.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : ev (R := R) β p s h U x = 0 := by
    rw [ev_def, hβ, comp_zero]
    rfl
  have conc_δ {L : Cx R} {n m : ℤ} (hm : n + 1 = m) (β : Cochain ((chains R).obj (disc.obj F)) L n)
    (hβ : ∀ (p : ℕ) s h U x, ev (R := R) β (p + 1) s h U x = 0) :
    ∀ (p : ℕ) s h U x, ev (R := R) (δ n m β) (p + 1) s h U x = 0 := by
    intro p s h U x
    rw [ev_δ_succ hm β U p (s - m + n) s (by omega) h x, hβ, sec_map_at_zero, zero_add]
    cases p with
    | zero =>
      have hf : ∀ i, Sx.face x i = x := fun i => rfl
      simp [Fin.sum_univ_two, hf]
    | succ p => simp [hβ]

  -- Lift the pullbacks to a cochain supported in simplicial degree zero.
  have exS {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) n,
      (∀ (U : Scheme.{0}) (x : F.obj (op U)), ev (R := R) β 0 n (by simp) U x = Jsec (ptPull γ x)) ∧
      ∀ (p : ℕ) s h U x, ev (R := R) β (p + 1) s h U x = 0 := by
    obtain ⟨β, hβ⟩ := ev_exists (E := disc.obj F) (L := Jcx R q N I) (n := n) (aS γ) (by
      intro p s h V U g x
      cases p with
      | zero =>
        obtain rfl : n = s := by omega
        exact (jsec_res g _).trans (congrArg Jsec (ptPull_res γ g x).symm)
      | succ p => exact map_zero _)
    exact ⟨β, fun U x => hβ 0 n _ U x, fun p s h U x => hβ (p + 1) s h U x⟩
  choose S hS0 hS1 using fun (m : ℤ) (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m) => exS γ
  have hSδ : ∀ (m m' : ℤ) (hm : m + 1 = m') (η : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m),
      S m' (δ m m' η) = δ m m' (S m η) := by
    intro m m' hm η
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : m' = s := by omega
      rw [hS0, ev_δ_zero hm (S m η) U m m' (by simp) h x, hS0, jsec_d hm, ptPull_δ hm]
    | succ p => rw [hS1, conc_δ hm _ (hS1 m η)]
  have hSadd : ∀ (γ γ' : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), S n (γ + γ') = S n γ + S n γ' := by
    intro γ γ'
    apply ev_ext
    intro p s h U x
    rw [ev_add]
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      rw [hS0, hS0, hS0, ptPull_add, jsec_add]
    | succ p => rw [hS1, hS1, hS1, add_zero]
  have hSzero : ∀ m : ℤ, S m 0 = 0 := by
    intro m
    apply ev_ext
    intro p s h U x
    rw [ev_zero]
    cases p with
    | zero =>
      obtain rfl : m = s := by omega
      rw [hS0, ptPull_zero, jsec_zero]
    | succ p => rw [hS1]
  have hScyc : ∀ γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, δ n (n + 1) (S n γ.1) = 0 := by
    intro γ
    rw [← hSδ n (n + 1) rfl, Cocycle.δ_eq_zero, hSzero]
  let Sc : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n →+
      CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n :=
    AddMonoidHom.mk' (fun γ => CohomologyClass.mk (Cocycle.mk (S n γ.1) (n + 1) rfl (hScyc γ))) (by
      intro a b
      rw [← CohomologyClass.mk_add]
      exact congrArg CohomologyClass.mk (Cocycle.ext (hSadd a.1 b.1)))
  have hcob : coboundaries ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n ≤ Sc.ker := by
    rintro ⟨γ, hγ⟩ ⟨n', hn', η, rfl⟩
    change CohomologyClass.mk _ = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', S n' η, (hSδ n' n hn' η).symm⟩
  let Φ := CohomologyClass.descAddMonoidHom Sc hcob
  have hnat : ∀ (m : ℤ) (b : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) m)
      (c' : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I m),
      (∀ U x, Jsec (c' U x) = ev (R := R) b 0 m (by simp) U x) →
      ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c' V (F.map g.op x) =
        (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c' U x) (zero_add m) := by
    intro m b c' hc' V U g x
    apply (jsec_bij R q N I m V).1
    change Jsec _ = Jsec _
    rw [hc', ← jsec_res, hc', ev_res]
    rfl
  have hΦinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨γ, rfl⟩ := c.mk_surjective
    change CohomologyClass.mk _ = 0 at hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc
    obtain ⟨n', hn', β', hβ'⟩ := hc
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n',
        Jsec c = ev (R := R) β' 0 n' (by simp) U x := fun U x => (jsec_bij R q N I n' U).2 _
    choose c' hc' using hc'
    obtain ⟨η, hη, -⟩ := glue R q N I F n' c' (hnat n' β' c' hc')
    have h2 : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ptPull (δ n' n η) x = ptPull γ.1 x := by
      intro U x
      have h1 : ptPull η x = c' U x := hη U x
      rw [ptPull_δ hn', h1]
      apply (jsec_bij R q N I n U).1
      change Jsec _ = Jsec _
      rw [← jsec_d hn', hc', ← ev_δ_zero hn' β' U n' n (by simp) (by simp) x]
      rw [hβ']
      exact hS0 n γ.1 U x
    have huniq := (glue R q N I F n (fun U x => ptPull γ.1 x) (fun V U g x => ptPull_res γ.1 g x)).unique
      (y₁ := γ.1) (y₂ := δ n' n η) (fun U x => rfl) h2
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', η, huniq.symm⟩
  have hΦsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨α, hαc, hα0⟩ := GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos R F (Jcx R q N I) n c
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
        Jsec c = ev (R := R) α.1 0 n (by simp) U x := fun U x => (jsec_bij R q N I n U).2 _
    choose c' hc' using hc'
    obtain ⟨γ, hγ, -⟩ := glue R q N I F n c' (hnat n α.1 c' hc')
    have hδ : δ n (n + 1) γ = 0 := by
      refine (glue R q N I F (n + 1) (fun U x => 0) (fun V U g x => (Cochain.comp_zero _ _).symm)).unique
        (fun U x => ?_) (fun U x => Cochain.comp_zero _ _)
      show ptPull (δ n (n + 1) γ) x = 0
      rw [ptPull_δ rfl, show ptPull γ x = c' U x from hγ U x]
      apply (jsec_bij R q N I (n + 1) U).1
      change Jsec _ = Jsec _
      rw [← jsec_d rfl, hc', ← ev_δ_zero rfl α.1 U n (n + 1) (by simp) (by simp) x, Cocycle.δ_eq_zero, ev_zero,
        jsec_zero]
    refine ⟨CohomologyClass.mk (Cocycle.mk γ (n + 1) rfl hδ), ?_⟩
    rw [← hαc]
    change CohomologyClass.mk _ = _
    congr 1
    apply Cocycle.ext
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      show ev (R := R) (S n γ) 0 n h U x = ev (R := R) α.1 0 n h U x
      rw [hS0, show ptPull γ x = c' U x from hγ U x, hc']
    | succ p =>
      show ev (R := R) (S n γ) (p + 1) s h U x = ev (R := R) α.1 (p + 1) s h U x
      rw [hS1, ev_zero_of_v _ _ _ _ (hα0 (p + 1) (by omega) s h)]
  refine ⟨(AddEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm, fun β γ hβ0 hβc => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  change CohomologyClass.mk β = CohomologyClass.mk _
  congr 1
  apply Cocycle.ext
  apply ev_ext
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : n = s := by omega
    obtain ⟨c, hc1, hc2⟩ := hβc U x
    show ev (R := R) β.1 0 n h U x = ev (R := R) (S n γ.1) 0 n h U x
    rw [hS0, hc1]
    congr 1
    apply ev_ext
    intro k s hs V y
    rw [hc2]
    exact (ev_pull _ γ.1 k s hs V y).symm
  | succ p =>
    show ev (R := R) β.1 (p + 1) s h U x = ev (R := R) (S n γ.1) (p + 1) s h U x
    rw [hS1, ev_zero_of_v _ _ _ _ (hβ0 (p + 1) (by omega) s h)]
end

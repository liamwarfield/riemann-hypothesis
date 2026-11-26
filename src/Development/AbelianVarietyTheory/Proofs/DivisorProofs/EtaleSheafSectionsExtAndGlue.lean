module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_ext_glue : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg := by
  intro R _ F U
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).2
  refine ⟨fun a b ⟨S, hS, h⟩ => ?_, fun S hS s hs => ?_⟩
  · exact (hF S hS).isSeparatedFor.ext fun V g hg => h V g hg
  · let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) S.arrows := fun V g hg => s V g hg
    have hx : x.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W g k hg
      exact (hs V W g k hg).symm
    obtain ⟨a, ha, -⟩ := hF S hS x hx
    exact ⟨a, fun V g hg => ha g hg⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_ext_and_glue : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg := by
  first | exact @GlobalTheory.EtC.sec_ext_glue | exact GlobalTheory.EtC.sec_ext_glue | (intros; apply GlobalTheory.EtC.sec_ext_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem loc_of_forall (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := hP
  obtain ⟨T, hT, hQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_pullback (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S.pullback k, Scheme.etaleTopology.pullback_stable k hS, fun V g hg => hP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hloc⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := fun {W W'} h hh k W'' k' => by
        simpa [Category.assoc] using hh W'' (k' ≫ k) }
  refine ⟨R, Scheme.etaleTopology.transitive hS R ?_, fun V g hg => by simpa using hg V (𝟙 V)⟩
  intro V g hg
  obtain ⟨T, hT, hP⟩ := hloc V g hg
  refine Scheme.etaleTopology.superset_covering ?_ hT
  intro W k hk W' k'
  have := hP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_top (U : Scheme.{0}) : Loc U fun _ _ => True :=
  loc_of_forall U _ fun _ _ => trivial

theorem loc_finset (U : Scheme.{0}) {ι : Type} (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_of_forall U _ fun V g i hi => absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  have := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U P h Finset.univ) fun V g hg i => hg i (Finset.mem_univ i)

theorem loc_of_isEmpty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) :
    Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

theorem loc_calculus :
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → Loc U P) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → (∀ V g, P V g → Q V g) → Loc U Q) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc U Q → Loc U fun V g => P V g ∧ Q V g) ∧
    (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc W fun V g => P V (g ≫ k)) ∧
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U (fun V g => Loc V fun W k => P W (k ≫ g)) → Loc U P) ∧
    (∀ (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i, Loc U (P i)) → Loc U fun V g => ∀ i, P i V g) ∧
    (∀ (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P) :=
  ⟨loc_of_forall, loc_mono, loc_and, loc_pullback, loc_trans, loc_finite, loc_of_isEmpty⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleLocal_property_calculus_rules : (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → Loc U P) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → (∀ V g, P V g → Q V g) → Loc U Q) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc U Q → Loc U fun V g => P V g ∧ Q V g) ∧ (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc W fun V g => P V (g ≫ k)) ∧ (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U (fun V g => Loc V fun W k => P W (k ≫ g)) → Loc U P) ∧ (∀ (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i, Loc U (P i)) → Loc U fun V g => ∀ i, P i V g) ∧ (∀ (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P) := by
  first | (exact @GlobalTheory.EtC.loc_calculus) | (exact GlobalTheory.EtC.loc_calculus) | (intros; apply GlobalTheory.EtC.loc_calculus  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicProperties
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ev_basic : ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ⟨CupSpec.ev_add α β p s h U x,
      map_sub (CupSpec.evHom I n p s h U x) α β, CupSpec.ev_zero p s h U x,
      fun c => CupSpec.ev_zsmul c α p s h U x⟩,
    fun α p s h V U g x => CupSpec.ev_res α p s h g x,
    fun α β H => CupSpec.ev_ext α β H,
    fun f α p s h U x => CupSpec.ev_pull f α p s h U x, ?_⟩
  intro J m α p s h U x
  rw [CupSpec.ev_def, CupSpec.ev_def, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ← Category.assoc]
  rfl

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  intro R _ E I n
  have ev_eq {F : Spc} {J : Cx R} (α : Cochain ((chains R).obj F) J n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx F p U) :
      ev α p s h U x = Sec.map ((chainsXIso R F p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α β p s h U x
    have hadd (a b : Cochain ((chains R).obj E) I n) :
        ev (a + b) p s h U x = ev a p s h U x + ev b p s h U x := by
      simp [ev, Cochain.add_v]
    let eval : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
      AddMonoidHom.mk' (fun a => ev a p s h U x) hadd
    exact ⟨hadd α β, map_sub eval α β, map_zero eval, fun c => map_zsmul eval c α⟩
  · intro α p s h V U g x
    rw [ev_eq, CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  · intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U x => H k s hs U x)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  · intro E' f α p s h U x
    rw [ev_eq, ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      ← Category.assoc, CupSpec.chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h)
      (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  · intro J m α p s h U x
    rw [ev_eq, ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      ← Category.assoc]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ResBasic

variable (R : Type) [CommRing R]

def resHom {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    congrArg (fun f => HomologicalComplex.Hom.f f 0)
      (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))⟩

theorem mono_ι_f_zero (F : Shv R) : Mono ((injectiveResolution F).ι.f 0) :=
  mono_of_isLimit_fork (injectiveResolution F).isLimitKernelFork

theorem mono_resι (F : Shv R) : Mono (resι R F) := by
  have h1 := mono_ι_f_zero R F
  change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0)
  rw [InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
  exact @mono_comp _ _ _ _ _ _ h1 _ inferInstance

theorem sglι_comp_single_map {F G : Shv R} (φ : F ⟶ G) :
    sglι F ≫ ((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0 = φ ≫ sglι G := by
  have := HomologicalComplex.single_map_f_self (V := Shv R) (ComplexShape.up ℤ) 0 φ
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ).f 0 = _
  rw [this, Iso.inv_hom_id_assoc]
  rfl

theorem res_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧
    resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧
      resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  intro R _ F
  have hinj : ∀ n, Injective ((res R F).X n) := fun n =>
    inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  have hge : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  have hq : QuasiIso (resAug F) := inferInstanceAs (QuasiIso (injectiveResolution F).ι')
  have hι : ∀ F : Shv R, sglι F ≫ (resAug F).f 0 = resι R F := fun _ => rfl
  have hcomm : ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G :=
    fun G φ => (resHom R φ).ι'_comp_hom'
  refine ⟨CochainComplex.isKInjective_of_injective _ 0, hinj, hge, hq, hι F, mono_resι R F, ?_,
    fun G φ => ⟨hcomm G φ, ?_⟩⟩
  · rw [← hι F, Category.assoc, (resAug F).comm 0 1]
    simp
  · rw [← hι F, Category.assoc, ← HomologicalComplex.comp_f, hcomm G φ, HomologicalComplex.comp_f, ← hι G,
      ← Category.assoc, sglι_comp_single_map, Category.assoc]

end GlobalTheory.EtC.ResBasic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧ (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧ resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G), resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧ resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  first | exact @GlobalTheory.EtC.ResBasic.res_basic | exact GlobalTheory.EtC.ResBasic.res_basic | (intros; apply GlobalTheory.EtC.ResBasic.res_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.loc_iff_etale_affine_points : ∀ (U : Scheme.{0})
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    (_root_.GlobalTheory.EtC.Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U),
      IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g) := by
  intro U P hP
  unfold _root_.GlobalTheory.EtC.Loc
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    haveI : Scheme.JointlySurjective (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) :=
      Scheme.instJointlySurjectivePrecoverage
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    let A := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := A.covers y
    have hE : Etale (𝒰.f i) := 𝒰.map_prop i
    refine ⟨A.X (A.idx y), A.f (A.idx y) ≫ 𝒰.f i, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hz]
    · exact hSP _ _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hV hE hx hPg using h
    let S : Sieve U :=
      { arrows := fun W f => P W f, downward_closed := fun hf k => hP _ _ _ k hf }
    refine ⟨S, ?_, fun W f hf => hf⟩
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V g (fun x => ?_) (fun x => hE x), ?_⟩
    · obtain ⟨y, hy⟩ := hx x
      exact ⟨x, y, hy⟩
    · rintro _ _ ⟨x⟩
      exact hPg x

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover : ∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) → (Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g) := by
  first | (exact @GlobalTheory.EtC.loc_iff_etale_affine_points) | (exact GlobalTheory.EtC.loc_iff_etale_affine_points) | (intros; apply GlobalTheory.EtC.loc_iff_etale_affine_points  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ShfLoc

instance wEqLB (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end GlobalTheory.EtC.ShfLoc


open GlobalTheory.EtC.ShfLoc in
theorem GlobalTheory.EtC.toSheafify_loc_bij_lift : ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ := by
  intro R _ P
  refine ⟨?_, ?_, ?_⟩
  · intro U y
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y,
      fun V g hg => hg⟩
  · intro U x hx
    have h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x =
        ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by rw [hx, map_zero]
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h,
      fun V g hg => ?_⟩
    have h' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    show (P.map g.op).hom x = 0
    rw [h', map_zero]
  · intro F φ
    refine ⟨⟨sheafifyLift Scheme.etaleTopology φ F.property⟩, toSheafify_sheafifyLift _ _ _, ?_⟩
    intro ψ hψ
    ext1
    exact sheafifyLift_unique _ _ _ _ hψ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift : ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ := by
  first | (exact @GlobalTheory.EtC.toSheafify_loc_bij_lift) | (exact GlobalTheory.EtC.toSheafify_loc_bij_lift) | (intros; apply GlobalTheory.EtC.toSheafify_loc_bij_lift  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem dual {k : Type} [Field k] [ValuativeRel k] {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k}
    {Y : Matrix (Fin n) (Fin d) k} (hY : Y ∉ latt ψ0 n d s) :
    ∃ l : Matrix (Fin n) (Fin d) k →ₗ[k] k, (∀ Z ∈ latt ψ0 n d s, ψ0 (l Z) = 1) ∧ ψ0 (l Y) ≠ 1 := by
  rw [mem_latt] at hY
  push_neg at hY
  obtain ⟨i, j, o, ho, h⟩ := hY
  let l : Matrix (Fin n) (Fin d) k →ₗ[k] k :=
    { toFun := fun Z => o * (s * Z i j)
      map_add' := fun a b => by simp only [Matrix.add_apply]; ring
      map_smul' := fun c a => by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  exact ⟨l, fun Z hZ => hZ i j o ho, h⟩

theorem cind_mem {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {L : AddSubgroup X}
    (ho : IsOpen (L : Set X)) (hc : IsCompact (L : Set X)) (y : X) : cind L y ∈ GlobalTheory.WeilM.SB X := by
  have hK : IsOpen {Z : X | Z - y ∈ L} := ho.preimage (continuous_sub_right y)
  have hKc : IsClosed {Z : X | Z - y ∈ L} := (AddSubgroup.isClosed_of_isOpen L ho).preimage (continuous_sub_right y)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro Y
    by_cases hY : Y - y ∈ L
    · exact ⟨_, hK, hY, fun Z hZ => by simp only [cind, if_pos (show Z - y ∈ L from hZ), if_pos hY]⟩
    · exact ⟨_, hKc.isOpen_compl, hY, fun Z hZ => by simp only [cind, if_neg (show Z - y ∉ L from hZ), if_neg hY]⟩
  · have himg : {Z : X | Z - y ∈ L} = (fun Z => Z + y) '' (L : Set X) := by
      ext Z
      constructor
      · intro h
        exact ⟨Z - y, h, sub_add_cancel Z y⟩
      · rintro ⟨W, hW, rfl⟩
        show W + y - y ∈ L
        rwa [add_sub_cancel_right]
    refine IsCompact.of_isClosed_subset (himg ▸ hc.image (continuous_add_const y)) (isClosed_tsupport _)
      (closure_minimal ?_ hKc)
    intro Z hZ
    by_contra h
    exact hZ (by simp only [cind, if_neg (show Z - y ∉ L from h)])

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have e := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

end GlobalTheory.LinSchur


open GlobalTheory.LinSchur in
theorem GlobalTheory.LinSchur.eq_smul_of_commute : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (ι₂ : Xt → Matrix (Fin n) (Fin d) k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → Xt → Xt) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n d Xt _ _ V ψ0 hcont hne ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  classical
  obtain ⟨hLoc, hBasis⟩ := GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis n d ψ0 hcont hne
  have inj : ∀ x ∈ V, ∀ y ∈ V, ι₁ x = ι₁ y → x = y := fun x hx y hy h => hbij.injOn hx hy h
  have surj : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∃ x, x ∈ V ∧ ι₁ x = f := fun f hf => hbij.surjOn hf
  have maps : ∀ x ∈ V, ι₁ x ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := fun x hx => hbij.mapsTo hx
  have h20 : ι₂ 0 = 0 := by
    have e := hlin 0 V.zero_mem 0 V.zero_mem 1
    simpa using e
  have hsmul : ∀ x ∈ V, ∀ c : ℂ, ι₂ (c • x) = c • ι₂ x := by
    intro x hx c
    have e := hlin x hx 0 V.zero_mem c
    rwa [add_zero, h20, add_zero] at e
  have hsum : ∀ (F : Finset (Matrix (Fin n) (Fin d) k)) (a : Matrix (Fin n) (Fin d) k → ℂ)
      (xs : Matrix (Fin n) (Fin d) k → Xt), (∀ y ∈ F, xs y ∈ V) →
      ι₂ (∑ y ∈ F, a y • xs y) = ∑ y ∈ F, a y • ι₂ (xs y) := by
    intro F a xs hxs
    induction F using Finset.induction_on with
    | empty => simpa using h20
    | insert y F hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy, hlin _ (hxs y (Finset.mem_insert_self _ _)) _
        (V.sum_mem fun z hz => V.smul_mem _ (hxs z (Finset.mem_insert_of_mem hz))),
        ih fun z hz => hxs z (Finset.mem_insert_of_mem hz)]
  have stepB : ∀ x ∈ V, ∀ C, (∀ Y, ι₁ x (Y + C) = ι₁ x Y) → ∀ Y, ι₂ x (Y + C) = ι₂ x Y := by
    intro x hx C hper Y
    obtain ⟨h1, h2, h3⟩ := hTr C x hx
    have e0 : Tr C x = x := inj _ h1 _ hx (by rw [h2]; funext Y; exact hper Y)
    have e := congrFun h3 Y
    rw [e0] at e
    exact e.symm
  have stepA : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ∀ Y, Y - y ∉ latt ψ0 n d s → ι₂ x Y = 0 := by
    intro s x hx y hxy Y hY
    obtain ⟨l, hl1, hl2⟩ := dual hY
    obtain ⟨m1, m2, m3⟩ := hMu l x hx
    have e1 : ι₁ (Mu l x) = ι₁ (ψ0 (l y) • x) := by
      rw [m2, map_smul, hxy]
      funext Z
      simp only [cind, Pi.smul_apply, smul_eq_mul]
      split_ifs with hZ
      · rw [mul_one, mul_one, show l Z = l (Z - y) + l y by rw [← map_add (f := _), sub_add_cancel],
          AddChar.map_add_eq_mul, hl1 _ hZ, one_mul]
      · simp
    have e2 : Mu l x = ψ0 (l y) • x := inj _ m1 _ (V.smul_mem _ hx) e1
    have e3 := congrFun m3 Y
    rw [e2, hsmul x hx] at e3
    simp only [Pi.smul_apply, smul_eq_mul] at e3
    have hYy : ψ0 (l Y) = ψ0 (l (Y - y)) * ψ0 (l y) := by
      rw [← AddChar.map_add_eq_mul, ← map_add (f := _), sub_add_cancel]
    rw [hYy] at e3
    have e4 : ψ0 (l y) * (1 - ψ0 (l (Y - y))) * ι₂ x Y = 0 := by linear_combination e3
    rcases mul_eq_zero.mp e4 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (addChar_ne_zero ψ0 _)
      · exact absurd (sub_eq_zero.mp h).symm hl2
    · exact h
  have stepC : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ι₂ x = ι₂ x y • ι₁ x := by
    intro s x hx y hxy
    funext Y
    rw [hxy]
    simp only [cind, Pi.smul_apply, smul_eq_mul]
    split_ifs with hY
    · rw [mul_one]
      have e := stepB x hx (Y - y) (fun Z => by
        rw [hxy]
        simp only [cind]
        rw [show Z + (Y - y) - y = (Z - y) + (Y - y) by abel, (latt ψ0 n d s).add_mem_cancel_right hY]) y
      rwa [add_sub_cancel] at e
    · rw [mul_zero]
      exact stepA s x hx y hxy Y hY
  have hcind : ∀ s : k, s ≠ 0 → ∀ y, cind (latt ψ0 n d s) y ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) :=
    fun s hs y => cind_mem (hLoc s hs).1 (hLoc s hs).2 y
  choose! xs hxsV hxs1 using fun s (hs : s ≠ 0) y => surj _ (hcind s hs y)
  have stepD : ∀ s : k, s ≠ 0 → ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx y hxy
    rw [stepC s x hx y hxy]
    congr 1
    obtain ⟨t1, t2, t3⟩ := hTr y x hx
    have e0 : Tr y x = xs s 0 := inj _ t1 _ (hxsV s hs 0) (by
      rw [t2, hxs1 s hs 0, hxy]
      funext Z
      simp only [cind, add_sub_cancel_right, sub_zero])
    have e := congrFun t3 0
    rw [e0, zero_add] at e
    exact e.symm
  have stepE : ∀ s : k, s ≠ 0 → ∀ x ∈ V, (∀ Y, ∀ C ∈ latt ψ0 n d s, ι₁ x (Y + C) = ι₁ x Y) →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx hper
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator _ (hLoc s hs).1 (ι₁ x) (maps x hx) hper
    have hxeq : x = ∑ y ∈ F, ι₁ x y • xs s y :=
      inj _ hx _ (V.sum_mem fun y _ => V.smul_mem _ (hxsV s hs y)) (by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul, hxs1 s hs]
        exact hF)
    calc ι₂ x = ι₂ (∑ y ∈ F, ι₁ x y • xs s y) := congrArg ι₂ hxeq
      _ = ∑ y ∈ F, ι₁ x y • ι₂ (xs s y) := hsum F _ _ (fun y _ => hxsV s hs y)
      _ = ∑ y ∈ F, ι₁ x y • (ι₂ (xs s 0) 0 • cind (latt ψ0 n d s) y) :=
          Finset.sum_congr rfl fun y _ => by
            rw [stepD s hs (xs s y) (hxsV s hs y) y (hxs1 s hs y), hxs1 s hs y]
      _ = ι₂ (xs s 0) 0 • ∑ y ∈ F, ι₁ x y • cind (latt ψ0 n d s) y := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _
      _ = ι₂ (xs s 0) 0 • ι₁ x := by rw [← hF]
  have stepF : ∀ s : k, s ≠ 0 → ∀ s' : k, s' ≠ 0 →
      (latt ψ0 n d s' : Set (Matrix (Fin n) (Fin d) k)) ⊆ latt ψ0 n d s →
      ι₂ (xs s 0) 0 = ι₂ (xs s' 0) 0 := by
    intro s hs s' hs' hsub
    have e0 := stepE s' hs' (xs s 0) (hxsV s hs 0) (fun Y C hC => by
      rw [hxs1 s hs 0]
      simp only [cind, sub_zero, (latt ψ0 n d s).add_mem_cancel_right (hsub hC)])
    have e := congrFun e0 0
    rw [hxs1 s hs 0] at e
    simpa [cind] using e
  refine ⟨ι₂ (xs 1 0) 0, fun x hx => ?_⟩
  obtain ⟨⟨s, hs⟩, hper⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : k // s ≠ 0} => latt ψ0 n d s) (fun s => (hLoc s.1 s.2).1)
    (fun W hW => by
      obtain ⟨s, hs, h⟩ := hBasis W hW
      exact ⟨⟨s, hs⟩, h⟩) (ι₁ x) (maps x hx)
  rw [stepE s hs x hx hper]
  congr 1
  obtain ⟨s'', hs'', hsub⟩ := hBasis ((latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∩ latt ψ0 n d 1)
    (inter_mem ((hLoc s hs).1.mem_nhds (latt ψ0 n d s).zero_mem) ((hLoc 1 one_ne_zero).1.mem_nhds (latt ψ0 n d 1).zero_mem))
  rw [stepF s hs s'' hs'' (fun z hz => (hsub hz).1), stepF 1 one_ne_zero s'' hs'' (fun z hz => (hsub hz).2)]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
open MeasureTheory Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (ι₂ : Xt → Matrix (Fin n) (Fin d) k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → Xt → Xt) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  first | exact @GlobalTheory.LinSchur.eq_smul_of_commute | exact GlobalTheory.LinSchur.eq_smul_of_commute | (intros; apply GlobalTheory.LinSchur.eq_smul_of_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.free_hom_sections : ∀ (R : Type) [CommRing R] (P : _root_.GlobalTheory.EtC.PSh)
    (F : _root_.GlobalTheory.EtC.Shv R),
    (∀ a : ∀ U : Scheme.{0}, P.obj (op U) → _root_.GlobalTheory.EtC.Sec F U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) x,
        _root_.GlobalTheory.EtC.Sec.res g (a U x) = a V (P.map g.op x)) →
      ∃ φ : (_root_.GlobalTheory.EtC.free R).obj P ⟶ F, ∀ U x,
        _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.freeGen R P U x) = a U x) ∧
    (∀ φ ψ : (_root_.GlobalTheory.EtC.free R).obj P ⟶ F,
      (∀ U x, _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.Sec.map ψ (_root_.GlobalTheory.EtC.freeGen R P U x)) → φ = ψ) ∧
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) x,
      _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.freeGen R P V (P.map g.op x)) ∧
    ∀ (Q : _root_.GlobalTheory.EtC.PSh) (f : P ⟶ Q) U x,
      _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.free R).map f)
          (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.freeGen R Q U (f.app (op U) x) := by
  intro R _ P F
  exact ⟨fun a ha => _root_.GlobalTheory.EtC.CupSpec.free_exists P F a ha,
    fun φ ψ h => _root_.GlobalTheory.EtC.CupSpec.free_ext φ ψ h,
    fun V U g x => _root_.GlobalTheory.EtC.CupSpec.freeGen_res P g x,
    fun Q f U x => _root_.GlobalTheory.EtC.CupSpec.freeGen_map f U x⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_sections_ext_res_map : ∀ (R : Type) [CommRing R] (P : PSh) (F : Shv R), (∀ a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) → ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x) ∧ (∀ φ ψ : (free R).obj P ⟶ F, (∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧ ∀ (Q : PSh) (f : P ⟶ Q) U x, Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  first | (exact @GlobalTheory.EtC.free_hom_sections) | (exact GlobalTheory.EtC.free_hom_sections) | (intros; apply GlobalTheory.EtC.free_hom_sections  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentVarUnit (A : Type) [CommRing A] : (LaurentPolynomial A)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← LaurentPolynomial.T_add]; simp

def laurentVar (A : Type) [CommRing A] : (Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.toMonoidHom (laurentVarUnit A)

namespace GmPhi

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

end GmPhi

def gmPhi (q : ℕ) (A : Type) [CommRing A] (i : ℤ) : Ht q (sp A) 0 (i - 1) →+ Ht q (sp (LaurentPolynomial A)) 1 i where
  toFun a := (cup q (pull _ (spMap (LaurentPolynomial.C : A →+* LaurentPolynomial A)) (tw q (i - 1)) 0 a)
    (kum q (laurentVar A))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add (f := _), AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
open GlobalTheory.WeilM Matrix

namespace GlobalTheory.RankChart

theorem exists_eq_stack (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T]
    [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k)
    (hrank : Y.rank ≤ Fintype.card R) (hdet : (Y.submatrix Sum.inl τ).det ≠ 0) :
    ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  classical
  set Y₁ := Y.toRows₁ with hY₁

  have hA : LinearIndependent k (fun i : R => fun j : R => Y (Sum.inl i) (τ j)) := by
    have hu : IsUnit (Y.submatrix Sum.inl τ) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
    exact Matrix.linearIndependent_rows_of_isUnit hu
  have hli : LinearIndependent k (fun i : R => Y₁ i) := by
    apply LinearIndependent.of_comp (LinearMap.funLeft k k τ)
    exact hA
  have hfin₁ : Module.finrank k (Submodule.span k (Set.range fun i : R => Y₁ i)) = Fintype.card R :=
    finrank_span_eq_card hli
  have hle : Submodule.span k (Set.range fun i : R => Y₁ i) ≤ Submodule.span k (Set.range Y.row) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  have heq : Submodule.span k (Set.range fun i : R => Y₁ i) = Submodule.span k (Set.range Y.row) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hfin₁, ← Matrix.rank_eq_finrank_span_row]
    exact hrank
  have hmem : ∀ t : T, ∃ c : R → k, ∑ i, c i • Y₁ i = Y (Sum.inr t) := by
    intro t
    have : Y (Sum.inr t) ∈ Submodule.span k (Set.range fun i : R => Y₁ i) := by
      rw [heq]; exact Submodule.subset_span ⟨Sum.inr t, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun k).1 this
  choose C hC using hmem
  refine ⟨Matrix.of fun t i => C t i, ?_⟩
  ext (i | t) j
  · simp [stack, hY₁]
  · have := congrFun (hC t) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [stack, fromRows_apply_inr, Matrix.mul_apply, Matrix.of_apply]
    rw [← this]

end GlobalTheory.RankChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecompositionStatement
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_chart_stack_decomposition : ∀ (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k), Y.rank ≤ Fintype.card R → (Y.submatrix Sum.inl τ).det ≠ 0 → ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  first | exact @GlobalTheory.RankChart.exists_eq_stack | exact GlobalTheory.RankChart.exists_eq_stack | (intros; apply GlobalTheory.RankChart.exists_eq_stack <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvariance
open GlobalTheory.WeilM Matrix

noncomputable section
open Filter
open scoped Topology

namespace GlobalTheory.RankChart

theorem sb_shear_invariant :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D],
      ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k),
        ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ f hf
  obtain ⟨Λ, hΛo, hΛ⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ f hf
  have hK : IsCompact (tsupport f) := hf.2
  have hc : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k =>
      fromRows (0 : Matrix R D k) (p.1 * p.2.toRows₁) := by
    have hm : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k => p.1 * p.2.toRows₁ :=
      continuous_fst.matrix_mul (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply (Sum.inl i) j).comp continuous_snd)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simp only [fromRows_apply_inr]
      exact (continuous_apply_apply i j).comp hm
  have hev : ∀ᶠ c in 𝓝 (0 : Matrix T R k), ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ :=
    hK.eventually_forall_of_forall_eventually fun Y _ => by
      have h0 : fromRows (0 : Matrix R D k) ((0 : Matrix T R k) * Y.toRows₁) ∈ Λ := by
        simp
      exact (hc.tendsto ((0 : Matrix T R k), Y)) (hΛo.mem_nhds h0)
  obtain ⟨b, hb⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset hev
  refine ⟨b, fun Y c hcb => ?_⟩
  have hZ : ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ := hb c hcb
  by_cases hY : Y ∈ tsupport f
  · rw [← hΛ Y _ (hZ Y hY), ← shear_sub_self, add_sub_cancel]
  by_cases hY' : shear c Y ∈ tsupport f
  · have h1 := hZ _ hY'
    rw [toRows₁_shear, ← shear_sub_self] at h1
    rw [← hΛ (shear c Y) _ (Λ.neg_mem h1), neg_sub, add_sub_cancel]
  · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']

end GlobalTheory.RankChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvarianceStatement
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_chart_shear_invariance : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D], ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k), ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  first | exact @GlobalTheory.RankChart.sb_shear_invariant | exact GlobalTheory.RankChart.sb_shear_invariant | (intros; apply GlobalTheory.RankChart.sb_shear_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def pbfMap (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (n i : ℤ)
    (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) : Ht q (pullback V (PGL.pr N)) n i :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def PBF (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : Prop :=
  ∀ n i : ℤ, Function.Bijective (pbfMap q V n i)

theorem projectiveBundleFormula_of_unitOnEtalePoints (h : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V) : D1 :=
  fun q _ _ _ V hq n i => h q V hq n i

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNatural
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cochain_ev_eq_of_natural :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
      (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) →
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x := by
  intro R _ E I n a ha
  have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ U x) = a p j (hp ▸ hij) U x := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U x
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
  have hEval := hφ _ _ h p rfl U x
  rw [eqToHom_refl, Category.id_comp] at hEval
  exact hEval

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

def HInv (q : ℕ) [NeZero q] (A : Type) [CommRing A] : Prop :=
  ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)

end GlobalTheory.EtC
end

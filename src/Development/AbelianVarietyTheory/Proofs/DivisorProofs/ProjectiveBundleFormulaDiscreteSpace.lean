module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaSuccOfForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBund

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyProjectiveBundleFormula
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (T : Scheme.{0}) [IsEmpty T] (a : Sec F T) : a = 0 :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1 a 0 ⟨⊥, Scheme.bot_mem_grothendieckTopology T, fun _ _ h => h.elim⟩

private theorem free_sec_zero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) (U : Scheme.{0})
    (y : Sec ((free R).obj P) U) : y = 0 := by
  obtain ⟨S, hS, h⟩ := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 y
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue R _ U).1 y 0 ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨c, hc⟩ := h V g hg
  have h0 : Sec.res g (0 : Sec ((free R).obj P) U) = 0 := map_zero (((free R).obj P).obj.map g.op).hom
  rw [h0]
  by_cases hV : IsEmpty V
  · exact sec_empty _ _ _
  · rw [hc]
    have : IsEmpty (P.obj (op V)) := ⟨fun x => hV (hP V ⟨x⟩)⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    simp [hc0]

private theorem free_isZero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) : IsZero ((free R).obj P) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext U y
  exact free_sec_zero R P hP U.unop y

private theorem sx_empty (E : Spc) (p : ℕ) (T : Scheme.{0})
    (x : Sx (pullback (triv E 0) (PGL.pr 0)) p T) : IsEmpty T := by
  have y : Sx (PGL 0) p T := Sx.map (pullback.snd (triv E 0) (PGL.pr 0)) x
  have v : Um 0 Γ(T, ⊤) := (show ComposableArrows (Um 0 Γ(T, ⊤)) p from y).obj 0
  have h : (⊥ : Ideal Γ(T, ⊤)) = ⊤ := by
    have := v.2
    rwa [Set.range_eq_empty, Ideal.span_empty] at this
  have hs : Subsingleton Γ(T, ⊤) := by
    rcases subsingleton_or_nontrivial Γ(T, ⊤) with hs | hn
    · exact hs
    · exact absurd h bot_ne_top
  refine ⟨fun t => ?_⟩
  have := (T.presheaf.germ ⊤ t trivial).hom.codomain_trivial
  exact not_subsingleton (T.presheaf.stalk t) this

private theorem chains_isZero (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (k : ℤ) :
    IsZero (((chains R).obj X).X k) := by
  by_cases hk : k ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact (free_isZero R _ (hX p)).of_iso (chainsXIso R X p)
  · refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat k fun i => ?_
    change -(i : ℤ) ≠ k
    omega

private theorem H_subsingleton (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (F : Shv R) (n : ℤ) :
    Subsingleton (H R X F n) := ⟨fun a b => by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  congr 1
  exact Cocycle.ext (Cochain.ext _ _ fun p q h => (chains_isZero R X hX p).eq_of_src _ _)⟩

theorem UpperTheory.projectiveBundleFormula_rank_zero :
    ∀ (q : ℕ) [NeZero q] (E : Spc), PBF q E 0 := by
  intro q _ E n i
  haveI : Subsingleton (Ht q (pullback (triv E 0) (PGL.pr 0)) n i) :=
    H_subsingleton _ _ (fun p T ⟨x⟩ => sx_empty E p T x) _ _
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun j => j.elim0, Subsingleton.elim _ _⟩⟩
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Pbf

private theorem functor_to_single_object_const {G : Type} [Monoid G] {n : ℕ} (y : Fin 1 ⥤ SingleObj G) (θ : Fin (n + 1) ⥤ Fin 1) :
    θ ⋙ y = (Functor.const _).obj (SingleObj.star G) := by
  have key : ∀ (a b : Fin 1) (g : a ⟶ b), y.map g = 𝟙 _ := by
    intro a b g
    obtain rfl : a = b := Subsingleton.elim _ _
    rw [Subsingleton.elim g (𝟙 a), y.map_id]
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  simp only [Functor.comp_map, Functor.const_obj_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact key _ _ _

private theorem eq_triv (U : Scheme.{0}) {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)) : V = triv (sch.obj U) N := by
  ext k T x
  let f : (Opposite.op (SimplexCategory.mk 0)) ⟶ k := (SimplexCategory.isTerminalZero.from k.unop).op
  have h := congrArg (fun φ => (ConcreteCategory.hom (NatTrans.app φ T)).toFun x) (V.naturality f)
  refine h.trans ?_
  exact functor_to_single_object_const _ _

private theorem pbf_all (q : ℕ) [NeZero q] (N : ℕ) : ∀ E : Spc, Inv q E → PBF q E N := by
  induction N with
  | zero => exact fun E _ => UpperTheory.projectiveBundleFormula_rank_zero q E
  | succ N ih =>
    rcases N with _ | _ | N
    · exact UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q
    · exact UpperTheory.projectiveBundleFormula_rank_two q
    · exact UpperTheory.projectiveBundleFormula_succ_of_forall q (N + 2) (by omega) ih

end UpperTheory.Pbf

theorem UpperTheory.Cb.etaleCohomology_projectiveBundle_formula :
    ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), ∀ {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)), Inv q (sch.obj U) → ∀ n i : ℤ, Function.Bijective fun a : ∀ j : Fin N, Ht q (sch.obj U) (n - 2 * (j : ℕ)) (i - (j : ℕ)) => ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j)) (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i) := by
  intro q _ U N V h n i
  obtain rfl := UpperTheory.Pbf.eq_triv U V
  exact UpperTheory.Pbf.pbf_all q N _ h n i
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProjectiveBundleFormula
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCohomology_projectiveBundle_formula : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), ∀ {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)), Inv q (sch.obj U) → ∀ n i : ℤ, Function.Bijective fun a : ∀ j : Fin N, Ht q (sch.obj U) (n - 2 * (j : ℕ)) (i - (j : ℕ)) => ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j)) (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i) :=
  @UpperTheory.Cb.etaleCohomology_projectiveBundle_formula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClasses
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SchLocExact

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map ψ (Sec.res g x) = Sec.res g (Sec.map ψ x) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => f.hom x) (ψ.hom.naturality g.op)

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res f x) = Sec.res (g ≫ f) x := by
  simp [Sec.res]

theorem res_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem subsingleton_of_homotopyEquiv {K L M : Cx R} (e : HomotopyEquiv K L) (n : ℤ)
    (h : Subsingleton (CohomologyClass L M n)) : Subsingleton (CohomologyClass K M n) := by
  suffices H : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (H x).trans (H y).symm⟩
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h0 : cpull e.inv M n (CohomologyClass.mk α) = 0 := Subsingleton.elim _ _
  have key : cpull e.hom M n (cpull e.inv M n (CohomologyClass.mk α)) = CohomologyClass.mk α := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom e.hom) (zcomp (Cocycle.ofHom e.inv) α (zero_add n)) (zero_add n)) =
      CohomologyClass.mk α
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨n.negOnePow • (Cochain.ofHomotopy e.homotopyHomInvId).comp α.1 (by omega), ?_⟩
    rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  rw [← key, h0, map_zero]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ m' hm] at h0
  exact h0

end GlobalTheory.EtC.SchLocExact


open GlobalTheory.EtC.SchLocExact in
theorem GlobalTheory.EtC.sch_loc_exact : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}),
    (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U),
    Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  intro R _ M U hU n b hb
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  have hs : Subsingleton (CohomologyClass (sgl ((free R).obj (yoneda.obj U))) M n) :=
    subsingleton_of_homotopyEquiv (e (yoneda.obj U)) n (hU n)
  obtain ⟨hex, -, -, -⟩ := GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X n)
  obtain ⟨φ, hφ⟩ := hex (fun V x => Sec.res x b) (fun V W g x => res_res g x b)
  have hφd : φ ≫ M.d n (n + 1) = 0 := by
    apply (GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X (n + 1))).2.1
    intro W x
    rw [map_comp, hφ, map_res, hb]
    simp [Sec.map, Sec.res]
  obtain ⟨ψ, hψ⟩ := lift_of_subsingleton (m' := n - 1) (by omega) hs φ hφd
  let a0 : Sec (M.X (n - 1)) U := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  have ha0 : Sec.map (M.d (n - 1) n) a0 = b := by
    simp only [a0]
    rw [← map_comp, hψ, hφ, res_id]
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a0, ?_⟩⟩
  rw [map_res, ha0]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClassesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}), (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U), Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.sch_loc_exact) | (exact GlobalTheory.EtC.sch_loc_exact) | (intros; apply GlobalTheory.EtC.sch_loc_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyI
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyI
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.cone_kinj_and_bijective_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ),
    D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) →
    (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R,
      ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  intro R _ D C f m hD hC iD iC
  refine ⟨?_, ?_⟩
  · haveI : ∀ n, Injective ((mappingCone f).X n) := fun n =>
      Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
        (@Injective.instBiprod _ _ _ _ _ _ (iD (n + 1)) (iC n))
    haveI : (mappingCone f).IsStrictlyGE (m - 1) := CochainComplex.isStrictlyGE_mappingCone f m m (m - 1) (by omega)
    exact isKInjective_of_injective _ (m - 1)
  · intro K
    have ex := fun n => GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f n
    constructor
    · intro hb n
      refine ⟨fun x y => ?_⟩
      have h0 : ∀ x : CohomologyClass K (mappingCone f) n, x = 0 := by
        intro x
        have h1 : cpush K f (n + 1) (cpost K (mappingCone.fst f) n (n + 1) rfl x) = 0 :=
          ((ex n).2.2 _).2 ⟨x, rfl⟩
        have h2 : cpost K (mappingCone.fst f) n (n + 1) rfl x = 0 :=
          (hb (n + 1)).1 (by rw [h1, map_zero])
        obtain ⟨y, rfl⟩ := ((ex n).2.1 x).1 h2
        obtain ⟨z, rfl⟩ := (hb n).2 y
        exact ((ex n).1 _).2 ⟨z, rfl⟩
      rw [h0 x, h0 y]
    · intro hs n
      refine ⟨?_, fun y => ?_⟩
      · rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by ring⟩
        obtain ⟨w, rfl⟩ := ((ex k).2.2 z).1 hz
        rw [Subsingleton.elim w 0, map_zero]
      · exact ((ex n).1 y).1 (Subsingleton.elim _ _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyIStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R, ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  first | (exact @GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (exact GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (intros; apply GlobalTheory.EtC.cone_kinj_and_bijective_iff  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClasses
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ShiftCocycle

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

def rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K L n →+ CohomologyClass K (L⟦a⟧) n' :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K (L⟦a⟧) n').comp (Cocycle.rightShiftAddEquiv n a n' h).toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + -a, by omega, a.negOnePow • β.rightShift a (m + -a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightShift β a (m + -a) n' (by omega) n h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

def runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K (L⟦a⟧) n' →+ CohomologyClass K L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K L n).comp (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm.toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + a, by omega, a.negOnePow • β.rightUnshift (m + a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightUnshift β (m + a) (by omega) n n' h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem runsh_rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    runsh K L a n n' h (rsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm_apply_apply x

theorem rsh_runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    rsh K L a n n' h (runsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).apply_symm_apply x

def sgn (d : ℤ) : ℤˣ := ((-d) * 0 + ((-d) * (-d - 1)) / 2).negOnePow

theorem zcomp_rightShift_homOf_leftShift {K L M : CochainComplex C ℤ} (d n : ℤ) (α : Cocycle K L (n - d)) (ψ : Cocycle L M d) :
    zcomp (sgn d • α.rightShift (-d) n (by omega)) (Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega))))
      (add_zero n) = zcomp α ψ (by omega) := by
  ext p q hpq
  have e1 : (↑(Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)))) : Cochain (L⟦-d⟧) M 0) =
      (ψ.leftShift (-d) 0 (by omega) : Cochain _ _ 0) := by
    rw [Cocycle.ofHom_coe, Cocycle.cochain_ofHom_homOf_eq_coe]
  simp only [zcomp, Cocycle.mk_coe, e1, Cocycle.coe_units_smul, Cochain.units_smul_comp,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q),
    Cochain.comp_v _ _ (show n - d + d = n by omega) p (p + (n - d)) q rfl (by omega),
    Cochain.units_smul_v, Cocycle.rightShift_coe, Cocycle.leftShift_coe,
    Cochain.rightShift_v _ (-d) n (show n + -d = n - d by omega) p q hpq (p + (n - d)) rfl,
    Cochain.leftShift_v _ (-d) 0 (show d + -d = 0 by omega) q q (add_zero q) (p + (n - d)) (by omega)]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Category.assoc, Iso.inv_hom_id_assoc]
  have hs : sgn d * (-d * 0 + -d * (-d - 1) / 2).negOnePow = 1 := Int.units_mul_self _
  rw [hs, one_smul]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem smul_mk {K L : CochainComplex C ℤ} {n : ℤ} (u : ℤˣ) (z : Cocycle K L n) :
    CohomologyClass.mk (u • z) = u • CohomologyClass.mk z := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, CohomologyClass.mk_neg]

theorem smul_smul_self {G : Type*} [AddCommGroup G] (u : ℤˣ) (x : G) : u • u • x = x := by
  rw [smul_smul, Int.units_mul_self, one_smul]

theorem map_units_smul' {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (u : ℤˣ) (x : G) :
    f (u • x) = u • f x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, map_neg]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC

open ShiftCocycle in
theorem cocycle_as_chainMap_of_shift : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d),
    ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧
      ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧
      ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n,
        ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  intro R _ L C d ψ
  refine ⟨L⟦-d⟧, Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)), ?_, ?_, ?_⟩
  · intro m hm
    exact L.isStrictlyGE_shift m (-d) (m + d) (by omega)
  · intro hI n
    exact Injective.of_iso (L.shiftFunctorObjXIso (-d) n (n + -d) rfl).symm (hI _)
  · intro K n
    refine ⟨{ toFun := fun x => sgn d • rsh K L (-d) (n - d) n (by omega) x
              invFun := fun y => sgn d • runsh K L (-d) (n - d) n (by omega) y
              left_inv := fun x => by
                simp only [map_units_smul', runsh_rsh, smul_smul_self]
              right_inv := fun y => by
                simp only [map_units_smul', rsh_runsh, smul_smul_self] }, ?_⟩
    intro a
    obtain ⟨α, rfl⟩ := a.mk_surjective
    show cpush K _ n (sgn d • CohomologyClass.mk (α.rightShift (-d) n (by omega))) = _
    rw [← smul_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (zcomp_rightShift_homOf_leftShift d n α ψ)

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClassesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d), ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧ ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n, ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  first | (exact @GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (exact GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (intros; apply GlobalTheory.EtC.cocycle_as_chainMap_of_shift  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiproductChainMapOfInjectiveFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiproductChainMapOfInjectiveFamily
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.BiprodPush

variable {R : Type} [CommRing R]

theorem cpush_comp (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_add]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem cpush_zero (K : Cx R) {I J : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_zero]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_zero]

theorem cpush_id (K : Cx R) {I : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1
  ext1
  simp [zcomp]

def cpushHom (K : Cx R) (I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : (I ⟶ J) →+ CohomologyClass K J n where
  toFun f := cpush K f n x
  map_zero' := cpush_zero K n x
  map_add' f g := cpush_add K f g n x

theorem cpush_sum (K : Cx R) {I J : Cx R} {ι : Type} (s : Finset ι) (f : ι → (I ⟶ J)) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (∑ j ∈ s, f j) n x = ∑ j ∈ s, cpush K (f j) n x :=
  map_sum (cpushHom K I J n x) f s

end GlobalTheory.BiprodPush

end

noncomputable section

namespace GlobalTheory.BiprodPush

theorem injective_of_retracts {C : Type*} [Category C] [Preadditive C] {ι : Type} [Fintype ι] {X : C} (Y : ι → C)
    [∀ j, Injective (Y j)] (p : ∀ j, X ⟶ Y j) (i : ∀ j, Y j ⟶ X) (h : ∑ j, p j ≫ i j = 𝟙 X) : Injective X := by
  refine ⟨fun {A B} g m _ => ⟨∑ j, Injective.factorThru (g ≫ p j) m ≫ i j, ?_⟩⟩
  rw [Preadditive.comp_sum]
  simp_rw [← Category.assoc, Injective.comp_factorThru, Category.assoc, ← Preadditive.comp_sum, h, Category.comp_id]

theorem biproduct_push : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (g : ∀ j, L j ⟶ C) (m : ℤ), (∀ j, (L j).IsStrictlyGE m) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) n) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpush K (g j) n (a j) := by
  intro R _ ι _ L C g m hL hI
  classical
  haveI : HasFiniteBiproducts (Cx R) := HasFiniteBiproducts.of_hasFiniteProducts
  have htot : ∀ n, ∑ j, (biproduct.π L j).f n ≫ (biproduct.ι L j).f n = 𝟙 ((⨁ L).X n) := by
    intro n
    have := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_sum (fun j => biproduct.π L j ≫ biproduct.ι L j) Finset.univ
    rw [biproduct.total] at this
    simp only [Functor.map_id, Functor.map_comp, HomologicalComplex.eval_map] at this
    exact this.symm
  refine ⟨⨁ L, biproduct.desc g, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero, ← htot i]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : IsZero ((L j).X i) := (L j).isZero_of_isStrictlyGE m i hi
    rw [show (biproduct.π L j).f i = 0 from this.eq_of_tgt _ _, zero_comp]
  · intro n
    exact injective_of_retracts (fun j => (L j).X n) (fun j => (biproduct.π L j).f n) (fun j => (biproduct.ι L j).f n) (htot n)
  · intro K n
    refine ⟨{ toFun := fun a => ∑ j, cpush K (biproduct.ι L j) n (a j)
              invFun := fun b j => cpush K (biproduct.π L j) n b
              left_inv := ?_
              right_inv := ?_ }, ?_⟩
    · intro a
      funext k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, ← cpush_comp]
      rw [Finset.sum_eq_single k]
      · rw [biproduct.ι_π_self, cpush_id]
      · intro j _ hj
        rw [biproduct.ι_π_ne _ hj, cpush_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro b
      simp only [← cpush_comp]
      rw [← cpush_sum, biproduct.total, cpush_id]
    · intro a
      change cpush K (biproduct.desc g) n (∑ j, cpush K (biproduct.ι L j) n (a j)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [← cpush_comp, biproduct.ι_desc]

end GlobalTheory.BiprodPush

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiproductChainMapOfInjectiveFamilyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biproduct_chainMap_of_injective_family : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (g : ∀ j, L j ⟶ C) (m : ℤ), (∀ j, (L j).IsStrictlyGE m) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) n) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpush K (g j) n (a j) := by
  first | (exact @GlobalTheory.BiprodPush.biproduct_push) | (exact GlobalTheory.BiprodPush.biproduct_push) | (intros; apply GlobalTheory.BiprodPush.biproduct_push  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemes
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscSupp

theorem assemble : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) (n - d j)) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j) := by
  intro R _ ι _ L C d ψ m₀ hL hLi
  choose L' g hb hi he using fun j => GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes R (L j) C (d j) (ψ j)
  choose e he using he
  have hm : ∀ j, (L' j).IsStrictlyGE (m₀ - ∑ k, |d k|) := fun j => by
    haveI := hb j m₀ (hL j)
    refine isStrictlyGE_of_ge (L' j) _ (m₀ + d j) ?_
    have h1 : |d j| ≤ ∑ k, |d k| := Finset.single_le_sum (f := fun k => |d k|) (fun k _ => abs_nonneg (d k)) (Finset.mem_univ j)
    have h2 := neg_abs_le (d j)
    omega
  obtain ⟨D, f, hD, hDi, hs⟩ := GlobalTheory.T.exists_biproduct_chainMap_of_injective_family R L' C g (m₀ - ∑ k, |d k|) hm (fun j => hi j (hLi j))
  refine ⟨D, f, _, hD, hDi, fun K n => ?_⟩
  obtain ⟨e', he'⟩ := hs K n
  refine ⟨(Equiv.piCongrRight fun j => e j K n).trans e', fun a => ?_⟩
  simp only [Equiv.trans_apply, Equiv.piCongrRight_apply, he']
  exact Finset.sum_congr rfl fun j _ => he j K n (a j)

theorem bijective_disc : ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] (L : ι → Cx (ZMod q)) (C : Cx (ZMod q)) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → C.IsStrictlyGE m₀ → (∀ j n, CategoryTheory.Injective ((L j).X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (sch.obj U)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j)) → ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j) := by
  intro q _ ι _ L C d ψ m₀ hL hC hLi hCi hU F hF
  obtain ⟨D, f, m, hD, hDi, he⟩ := assemble (ZMod q) L C d ψ m₀ hL hLi
  have hD' : D.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge D _ _ (min_le_left _ _)
  have hC' : C.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge C _ _ (min_le_right _ _)
  obtain ⟨hKI, hcone⟩ := GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff (ZMod q) f (min m m₀) hD' hC' hDi hCi
  have key : ∀ K : Cx (ZMod q), (∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass K (L j) (n - d j) =>
      ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n) := by
    intro K
    rw [← hcone K]
    refine forall_congr' fun n => ?_
    obtain ⟨e, he'⟩ := he K n
    have : (fun a : ∀ j, CohomologyClass K (L j) (n - d j) => ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) =
        (cpush K f n) ∘ e := funext fun a => (he' a).symm
    rw [this]
    exact Function.Bijective.of_comp_iff _ e.bijective
  refine (key _).mpr ?_
  exact GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support (ZMod q) (disc.obj F) (mappingCone f) (fun U hU' n b hb =>
    GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes (ZMod q) (mappingCone f) U ((key _).mp (hU U (hF U hU'))) n b hb)

end GlobalTheory.EtC.DiscSupp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injectiveComplexMap_quasiIso_of_unit_schemes : ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] (L : ι → Cx (ZMod q)) (C : Cx (ZMod q)) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → C.IsStrictlyGE m₀ → (∀ j n, CategoryTheory.Injective ((L j).X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (sch.obj U)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j)) → ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j) := by
  first | (exact @GlobalTheory.EtC.DiscSupp.bijective_disc) | (exact GlobalTheory.EtC.DiscSupp.bijective_disc) | (intros; apply GlobalTheory.EtC.DiscSupp.bijective_disc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundle
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem disc_eq_trivV (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)) : V = trivV N (disc.obj F) := by
  ext n U x
  have h := congrArg
    (fun φ : (disc.obj F).obj (op (SimplexCategory.mk 0)) ⟶ (ofCat (glCat N)).obj n =>
      ConcreteCategory.hom (φ.app U) x)
    (V.naturality (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op)
  simp at h
  show (ConcreteCategory.hom ((V.app n).app U)) x = _
  rw [h]
  generalize (ConcreteCategory.hom ((V.app (op (SimplexCategory.mk 0))).app U)) x = y
  refine CategoryTheory.Functor.ext (fun i => rfl) ?_
  intro i j f
  change (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)).map (𝟙 (0 : Fin 1)) = _
  refine (CategoryTheory.Functor.map_id (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)) 0).trans ?_
  change 𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) =
    eqToHom (rfl : SingleObj.star (GL (Fin N) (Scheme.Γ.obj U)) = _) ≫
      𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) ≫ eqToHom rfl
  erw [Category.id_comp, Category.id_comp]
  exact (eqToHom_refl _ _).symm

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle : ∀ (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), V = trivV N (disc.obj F) := by
  first | (exact @GlobalTheory.EtC.disc_eq_trivV) | (exact GlobalTheory.EtC.disc_eq_trivV) | (intros; apply GlobalTheory.EtC.disc_eq_trivV  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaDiscreteSpace
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem inv_sch (q : ℕ) (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Inv q (sch.obj U) := by
  intro U' ⟨f⟩
  simpa using hU.map f.appTop.hom

theorem pbf_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)),
    Inv q (disc.obj F) → PBF q V := by
  intro q _ N F V hF n i
  obtain ⟨J, ψ, hJ, hinj, he⟩ := GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle q N i
  have key := GlobalTheory.T.injectiveComplexMap_quasiIso_of_unit_schemes q (fun j : Fin N => res (ZMod q) (tw q (i - (j : ℕ)))) J (fun j => 2 * ((j : ℕ) : ℤ)) ψ 0
    (fun j => inferInstanceAs ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.IsStrictlyGE 0)) hJ
    (fun j m => inferInstanceAs (Injective ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.X m))) hinj
    (by
      intro U hU m
      obtain ⟨e, he'⟩ := he (yoneda.obj U) (inv_sch q U hU) m
      have hs := GlobalTheory.T.etaleCohomology_projectiveBundle_formula q U (trivV N (sch.obj U)) (inv_sch q U hU) m i
      have hcomp : (fun a : ∀ j : Fin N, Ht q (sch.obj U) (m - 2 * (j : ℕ)) (i - (j : ℕ)) =>
          ∑ j : Fin N, ((cup q (pull _ (pullback.fst (trivV N (sch.obj U)) (PGL.pr N)) _ _ (a j))
            (cpow q (c1 q (pullback.snd (trivV N (sch.obj U)) (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) :
              Ht q _ m i)) = e ∘ (fun a => ∑ j, cpost _ (ψ j) (m - 2 * (j : ℕ)) m (by omega) (a j)) :=
        funext fun a => (he' a).symm
      rw [hcomp] at hs
      exact (Function.Bijective.of_comp_iff' e.bijective _).1 hs)
    F hF n
  obtain ⟨e, he'⟩ := he F hF n
  rw [GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle N F V]
  have hcomp : pbfMap q (trivV N (disc.obj F)) n i =
      e ∘ (fun a => ∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) :=
    funext fun a => (he' a).symm
  rw [hcomp]
  exact e.bijective.comp key

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaDiscreteSpaceStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
theorem _root_.GlobalTheory.T.projectiveBundleFormula_discrete_space : ∀ (q : ℕ) [NeZero q] (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V :=
  @GlobalTheory.EtC.pbf_disc
end

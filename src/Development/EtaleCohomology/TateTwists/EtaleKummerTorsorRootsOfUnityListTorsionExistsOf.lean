module

public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
public import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistExtendsThroughMonoToResolutionZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def EtaleKummerSectionsIntoTwistEmbeddingExist : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

def EtaleTwistExtendsThroughMonoToResolutionZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j →
    ∃ e : M ⟶ (res _ (tw q 1)).X 0, j ≫ e = resι _ (tw q 1)

theorem etale_kummer_torsor_class_exists_of_tors_and_ext (h1 : EtaleKummerSectionsIntoTwistEmbeddingExist) (h2 : EtaleTwistExtendsThroughMonoToResolutionZero) : EtaleKummerTriangleExists := by
  intro q _
  apply pick_spec
  obtain ⟨M, j, hj, s, hs1, hs2⟩ := h1 q
  obtain ⟨e, he⟩ := h2 q M j hj
  refine ⟨fun U v => Sec.map e (s U v), ?_, ?_⟩
  · intro V U g v hq
    show Sec.res g (Sec.map e (s U v)) = Sec.map e (s V _)
    rw [← hs1 V U g v hq]
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality g.op)) (s U v)).symm
  · intro U ζ v w h
    show Sec.map e (s U w) = Sec.map e (s U v) + _
    rw [hs2 U ζ v w h]
    show (e.hom.app (op U)).hom (_ + _) = _
    rw [map_add (f := _)]
    congr 1
    unfold resGen
    rw [← he]
    rfl
end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotien
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def twGenR {q : ℕ} (A : CommRingCat.{0}) (ζ : Prim q A) : (twF q 1).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ 1)

def ExistsEtaleMonoMuTwistKillingRootRelations : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) ∧
    ∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0

def EtaleMuTwistMonoExtendsToTorsorSheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) →
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

theorem exists_etale_mono_muTwist_into_torsorSheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : EtaleMuTwistMonoExtendsToTorsorSheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist := by
  intro q _
  obtain ⟨T, τ, hm, hl⟩ := h1 q
  exact h2 q T τ hm hl
end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotientAndPreshe
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

theorem kt_mono_sh (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G)
    (hι : ∀ A, Function.Injective (ι.app A).hom) :
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι)) := by
  have : ∀ U, Mono ((Functor.whiskerLeft Scheme.Γ ι).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).2 (hι _)
  have : Mono (Functor.whiskerLeft Scheme.Γ ι) := NatTrans.mono_of_mono_app _
  infer_instance

theorem kt_res_sec (q : ℕ) (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : G.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec (R := ZMod q) G U x) = ofRings.sec (R := ZMod q) G V ((G.map g.appTop).hom x) := by
  unfold Sec.res ofRings.sec ofRings
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ G)).naturality g.op)
  exact this.symm

theorem kt_map_sec (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G) (U : Scheme.{0})
    (x : T.obj Γ(U, ⊤)) :
    Sec.map ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι))
      (ofRings.sec (R := ZMod q) T U x) = ofRings.sec (R := ZMod q) G U ((ι.app _).hom x) := by
  unfold Sec.map ofRings.sec
  have := congrArg (fun f => (ModuleCat.Hom.hom (NatTrans.app f (op U))) x)
    (toSheafify_naturality Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ ι))
  exact this.symm

def MuTwistQuotientEmbedsInUnitTorsorPresheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G),
      (∀ A, Function.Injective (ι.app A).hom) ∧
      ∃ s : ∀ A : CommRingCat.{0}, Aˣ → G.obj A,
        (∀ (A B : CommRingCat.{0}) (f : A ⟶ B) (v : Aˣ), (G.map f).hom (s A v) = s B (Units.map f.hom.toMonoidHom v)) ∧
        ∀ (A : CommRingCat.{0}) (ζ : Prim q A) (v w : Aˣ), (w : A) = ζ.1 * v →
          s A w = s A v + (ι.app A).hom ((τ.app A).hom (twGenR A ζ))

theorem etale_mu_twist_mono_extends_of_presheaf_torsor_embedding (hpre : MuTwistQuotientEmbedsInUnitTorsorPresheaf) : EtaleMuTwistMonoExtendsToTorsorSheaf := by
  intro q _ T τ hm hl
  obtain ⟨G, ι, hι, s, hs, hr⟩ := hpre q T τ hl
  have hmι := kt_mono_sh q T G ι hι
  refine ⟨ofRings (ZMod q) G, (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ) ≫
    (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι), @mono_comp _ _ _ _ _ _ hm _ hmι,
    fun U v => ofRings.sec (R := ZMod q) G U (s _ v), ?_, ?_⟩
  · intro V U g v _
    rw [kt_res_sec]
    exact congrArg _ (hs _ _ g.appTop v)
  · intro U ζ v w h
    beta_reduce
    rw [hr _ ζ v w h]
    rw [show ofRings.sec (R := ZMod q) G U (s _ v + (ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) =
      ofRings.sec (R := ZMod q) G U (s _ v) + ofRings.sec (R := ZMod q) G U ((ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) by
        unfold ofRings.sec
        exact map_add _ _ _]
    congr 1
    exact ((kt_map_sec q T G ι U _).symm.trans (congrArg _ (kt_map_sec q (twF q 1) T τ U (twGenR _ ζ)).symm))

theorem exists_etale_mono_mu_twist_into_torsor_sheaf_of_presheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : MuTwistQuotientEmbedsInUnitTorsorPresheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist :=
  exists_etale_mono_muTwist_into_torsorSheaf h1 (etale_mu_twist_mono_extends_of_presheaf_torsor_embedding h2)
end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfRootListsLocally
section -- merged from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def muK (q : ℕ) (A : CommRingCat.{0}) : Submodule (ULift.{1} (ZMod q)) ((twF q 1).obj A) :=
  Submodule.span _ {x | ∃ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 ∧
    x = (l.map fun ζ => twGenR A ζ).sum}

theorem muK_gen_map (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (ζ.map f.hom) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem muK_le (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    muK q A ≤ (muK q B).comap ((twF q 1).map f).hom := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨l, hl, rfl⟩
  refine Submodule.subset_span ⟨l.map (Prim.map f.hom), ?_, ?_⟩
  · have : ((l.map fun ζ => ζ.1).map f.hom).prod = f.hom 1 := by rw [← map_list_prod, hl]
    rw [map_one] at this
    rw [← this, List.map_map, List.map_map]
    rfl
  · rw [map_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ζ _
    exact muK_gen_map q f ζ

noncomputable def muT (q : ℕ) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ ((twF q 1).obj A ⧸ muK q A)
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ ((twF q 1).map f).hom (muK_le q f))
  map_id A := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (𝟙 A)).hom x) = Submodule.Quotient.mk x
    rw [(twF q 1).map_id]; rfl
  map_comp f g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (f ≫ g)).hom x) =
      Submodule.Quotient.mk (((twF q 1).map g).hom (((twF q 1).map f).hom x))
    rw [(twF q 1).map_comp]; rfl

noncomputable def muτ (q : ℕ) : twF q 1 ⟶ muT q where
  app A := ModuleCat.ofHom (muK q A).mkQ
  naturality A B f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl

theorem muτ_list (q : ℕ) (A : CommRingCat.{0}) (l : List (Prim q A)) (hl : (l.map fun ζ => ζ.1).prod = 1) :
    (l.map fun ζ => ((muτ q).app A).hom (twGenR A ζ)).sum = 0 := by
  have h : (l.map fun ζ => twGenR A ζ).sum ∈ muK q A := Submodule.subset_span ⟨l, hl, rfl⟩
  have := (Submodule.Quotient.mk_eq_zero (muK q A)).2 h
  refine Eq.trans ?_ this
  change _ = ((muτ q).app A).hom (List.map (fun ζ => twGenR A ζ) l).sum
  rw [map_list_sum, List.map_map]
  rfl

def EtaleSheafifyMonoOfKernelLocallyZeroCriterion : Prop :=
  ∀ (q : ℕ) (P Q : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : P ⟶ Q),
    (∀ (U : Scheme.{0}) (x : P.obj Γ(U, ⊤)), (τ.app _).hom x = 0 → Loc U fun _ g => (P.map g.appTop).hom x = 0) →
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ))

def MuRootRelationSubmoduleEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (x : (twF q 1).obj Γ(U, ⊤)), x ∈ muK q Γ(U, ⊤) →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom x = 0

theorem etale_sheafify_mono_of_kernel_locally_zero : EtaleSheafifyMonoOfKernelLocallyZeroCriterion := by
  intro q P Q τ h
  have hli : Presheaf.IsLocallyInjective Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ τ) := by
    refine ⟨fun {X} x y hxy => ?_⟩
    let x' : P.obj Γ(X.unop, ⊤) := x
    let y' : P.obj Γ(X.unop, ⊤) := y
    have hxy' : (τ.app _).hom x' = (τ.app _).hom y' := hxy
    obtain ⟨S, hS, hSP⟩ := h X.unop (x' - y') (by rw [map_sub, hxy', sub_self])
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    have h2 : (P.map g.appTop).hom (x' - y') = 0 := hSP V g hg
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have : Sheaf.IsLocallyInjective ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 hli
  exact Sheaf.mono_of_isLocallyInjective _

theorem exists_etale_mono_muTwist_quotient_of_locally_zero (h1 : EtaleSheafifyMonoOfKernelLocallyZeroCriterion) (h2 : MuRootRelationSubmoduleEtaleLocallyZero) :
    ExistsEtaleMonoMuTwistKillingRootRelations := by
  intro q _
  refine ⟨muT q, muτ q, h1 q _ _ (muτ q) fun U x hx => h2 q U x ?_, muτ_list q⟩
  exact (Submodule.Quotient.mk_eq_zero (muK q _)).1 hx

end LateralTheory.EtaleFoundations
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def MuRootListProductOneSumEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (l : List (Prim q Γ(U, ⊤))), (l.map fun ζ => ζ.1).prod = 1 →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0

theorem mu_root_relation_submodule_etale_locally_zero_of_root_lists (h : MuRootListProductOneSumEtaleLocallyZero) : MuRootRelationSubmoduleEtaleLocallyZero := by
  intro q _ U x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact h q U l hl
  | zero => exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨S, hS, hSa⟩ := ha
    obtain ⟨T, hT, hTb⟩ := hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg.1
    have h2 : ((twF q 1).map g.appTop).hom b = 0 := hTb V g hg.2
    show ((twF q 1).map g.appTop).hom (a + b) = 0
    rw [map_add (f := _), h1, h2, add_zero]
  | smul c a _ ha =>
    obtain ⟨S, hS, hSa⟩ := ha
    exact ⟨S, hS, fun V g hg => by
      have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg
      show ((twF q 1).map g.appTop).hom (c • a) = 0
      rw [map_smul, h1, smul_zero]⟩

theorem exists_etale_mono_mu_twist_quotient_of_root_lists_locally_zero (h : MuRootListProductOneSumEtaleLocallyZero) : ExistsEtaleMonoMuTwistKillingRootRelations :=
  exists_etale_mono_muTwist_quotient_of_locally_zero etale_sheafify_mono_of_kernel_locally_zero (mu_root_relation_submodule_etale_locally_zero_of_root_lists h)

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.MuRootListProductOneSumEtaleLocallyZero
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyPrimaryLocalization
namespace LateralTheory.Fin.EtalePrimitiveRootsExistLocally
theorem etale_locally_exists_primitive_root_of_unity : LateralTheory.EtaleFoundations.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  apply LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order
theorem etale_torsion_cohomology_primary_localization_kummer : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  apply LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order
theorem etale_torsion_cohomology_primary_localization : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := by
  apply LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer <;> first | exact etale_locally_exists_primitive_root_of_unity | exact etale_torsion_cohomology_primary_localization_kummer
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := etale_torsion_cohomology_primary_localization
end LateralTheory.Fin.EtalePrimitiveRootsExistLocally
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyPrimaryPartBasic
namespace LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
theorem etale_torsion_cohomology_primary_part_basic : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  apply LateralTheory.EtaleFoundations.PrimPf.cyclotomic_primitive_root_product_identities_of_adjoin_root
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := etale_torsion_cohomology_primary_part_basic
end LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MuListPf

theorem ulift_natCast (q : ℕ) [NeZero q] (a : ZMod q) :
    ((a.val : ℕ) : ULift.{1} (ZMod q)) = ULift.up a := by
  apply ULift.ext
  show ((a.val : ℕ) : ULift.{1} (ZMod q)).down = a
  rw [ULift.down_natCast]
  exact ZMod.natCast_zmod_val a

theorem twGen_rel (q : ℕ) [NeZero q] (B : CommRingCat.{0}) (ζ ξ : Prim q B) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGenR B ξ = (a : ZMod q).val • twGenR B ζ := by
  have hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) -
      Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 B :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have h2 := (Submodule.Quotient.eq (twRel q 1 B)).2 hm
  simp only [zpow_one] at h2
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ulift_natCast]
  change Submodule.Quotient.mk _ = _
  rw [h2]
  change _ = (ULift.up (a : ZMod q) : ULift.{1} (ZMod q)) •
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 1 B)
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single]
  congr 2
  exact (mul_one _).symm

theorem dvd_of_pow (q : ℕ) [NeZero q] (B : Type) [CommRing B] [Nontrivial B] (ζ : Prim q B) (n : ℕ)
    (h : ζ.1 ^ n = 1) : q ∣ n := by
  obtain ⟨-, -, h3, -, -, -⟩ := LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities.intersectionNumber_baseChange q B
  by_contra hn
  have := h3 ζ n 0 (by rwa [Nat.modEq_zero_iff_dvd])
  rw [h, pow_zero, sub_self] at this
  exact not_isUnit_zero this

theorem sum_eq (q : ℕ) [NeZero q] (B : CommRingCat.{0}) (ζ : Prim q B) : ∀ (l : List (Prim q B)),
    (∀ ξ ∈ l, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) →
    ∃ n : ℕ, (l.map fun ξ => ξ.1).prod = ζ.1 ^ n ∧ (l.map fun ξ => twGenR B ξ).sum = n • twGenR B ζ := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, by simp, by simp⟩
  | cons ξ l ih =>
    intro h
    obtain ⟨n, h1, h2⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨a, ha⟩ := h ξ List.mem_cons_self
    refine ⟨(a : ZMod q).val + n, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, h1, ha, pow_add]
    · simp only [List.map_cons, List.sum_cons, h2, twGen_rel q B ζ ξ a ha, add_smul]

theorem nontriv (V : Scheme.{0}) (x : V) : Nontrivial Γ(V, ⊤) :=
  (V.presheaf.germ ⊤ x trivial).hom.domain_nontrivial

theorem zero_of_dvd (q : ℕ) [NeZero q] (M : Type*) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (n : ℕ) (hn : q ∣ n) (x : M) : n • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((n : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    rw [ULift.down_natCast]
    exact (ZMod.natCast_eq_zero_iff n q).2 hn
  rw [this, zero_smul]

end LateralTheory.EtaleFoundations.MuListPf

namespace LateralTheory.EtaleFoundations
open MuListPf

theorem mu_root_list_product_one_sum_etale_locally_zero : MuRootListProductOneSumEtaleLocallyZero := by
  intro q _ U l hl
  obtain ⟨hL1, hL2, -, -, hL5, hL6, hL7⟩ := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  have stab : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
      ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 →
      ((twF q 1).map (k ≫ g).appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 := by
    intro V W g k h
    rw [Scheme.Hom.comp_appTop, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h, map_zero]
  cases l with
  | nil => exact hL1 _ _ fun V g => by simp
  | cons ζ l' =>
    have hloc : Loc U fun V g => ∀ ξ ∈ ζ :: l', ∃ a : (ZMod q)ˣ,
        g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
      have := hL6 U (Fin (ζ :: l').length) (fun i V g => ∃ a : (ZMod q)ˣ,
          g.appTop.hom ((ζ :: l').get i).1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val)
        (fun i => ((LateralTheory.Fin.EtalePrimitiveRootsExistLocally.intersectionNumber_baseChange q U).2.1 ζ ((ζ :: l').get i)))
      refine hL2 _ _ _ this fun V g h ξ hξ => ?_
      obtain ⟨i, rfl⟩ := List.get_of_mem hξ
      exact h i
    refine hL5 U _ (hL2 _ _ _ hloc fun V g h => ?_)
    by_cases hV : IsEmpty V
    · exact hL7 V _
    · rw [not_isEmpty_iff] at hV
      obtain ⟨x⟩ := hV
      have := nontriv V x
      have key : ((twF q 1).map g.appTop).hom ((ζ :: l').map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 := by
        rw [map_list_sum, List.map_map]
        have e : ((fun y => ((twF q 1).map g.appTop).hom y) ∘ fun ζ => twGenR Γ(U, ⊤) ζ) =
            (fun ξ => twGenR Γ(V, ⊤) ξ) ∘ Prim.map g.appTop.hom := by
          funext ξ; exact muK_gen_map q g.appTop ξ
        rw [e, ← List.map_map]
        obtain ⟨n, h1, h2⟩ := sum_eq q Γ(V, ⊤) (ζ.map g.appTop.hom) ((ζ :: l').map (Prim.map g.appTop.hom))
          (by
            intro ξ' hξ'
            obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.1 hξ'
            exact h ξ hξ)
        rw [h2]
        apply zero_of_dvd q
        apply dvd_of_pow q Γ(V, ⊤) (ζ.map g.appTop.hom) n
        rw [← h1]
        refine Eq.trans ?_ ((congrArg g.appTop.hom hl).trans (map_one _))
        rw [map_list_prod, List.map_map, List.map_map]
        rfl
      exact hL1 _ _ fun W k => stab V W g k key

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.MuTwistQuotientEmbedsInUnitTorsorPresheaf
open CategoryTheory GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations.KTP

theorem twGenR_nat {q : ℕ} (A B : CommRingCat.{0}) (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (Prim.map f.hom ζ) := by
  change Submodule.Quotient.mk (Finsupp.lmapDomain _ _ _ (Finsupp.single ζ 1)) = _
  simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.1 h

theorem list_pow {q : ℕ} {A : Type} [CommRing A] (l : List (Prim q A)) : ((l.map fun ζ => ζ.1).prod) ^ q = 1 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [mul_pow, prim_pow, ih]

theorem q_smul {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext; simp
  rw [this, zero_smul]

variable {q : ℕ} {A : Type} [CommRing A] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]

theorem sum_eq_of_prod_eq [NeZero q] (τ' : Prim q A → M)
    (hl : ∀ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 → (l.map τ').sum = 0)
    (l1 l2 : List (Prim q A)) (h : (l1.map fun ζ => ζ.1).prod = (l2.map fun ζ => ζ.1).prod) :
    (l1.map τ').sum = (l2.map τ').sum := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have := hl (l1 ++ (List.replicate (q - 1) l2).flatten) (by
    simp only [List.map_append, List.prod_append, List.map_flatten, List.map_replicate, List.prod_flatten,
      List.prod_replicate, h, ← pow_succ']
    rw [Nat.sub_add_cancel hq, list_pow])
  simp only [List.map_append, List.sum_append, List.map_flatten, List.map_replicate, List.sum_flatten,
    List.sum_replicate] at this
  have h2 := q_smul (q := q) (l2.map τ').sum
  have h3 : q • (l2.map τ').sum = (q - 1) • (l2.map τ').sum + (l2.map τ').sum := by
    rw [← succ_nsmul, Nat.sub_add_cancel hq]
  rw [h3] at h2
  have := this.trans h2.symm
  rw [add_comm ((q-1) • _) _] at this
  exact add_left_cancel (a := (q-1) • (l2.map τ').sum) (by rw [add_comm _ (List.sum _), this, add_comm])

def rel (q : ℕ) [NeZero q] (A : Type) [CommRing A] : Setoid Aˣ where
  r x y := ∃ l : List (Prim q A), (y : A) = (l.map fun ζ => ζ.1).prod * x
  iseqv := by
    refine ⟨fun x => ⟨[], by simp⟩, ?_, ?_⟩
    · rintro x y ⟨l, hl⟩
      refine ⟨(List.replicate (q - 1) l).flatten, ?_⟩
      have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
      simp only [List.map_flatten, List.map_replicate, List.prod_flatten, List.prod_replicate, hl, ← mul_assoc,
        ← pow_succ]
      rw [Nat.sub_add_cancel hq, list_pow, one_mul]
    · rintro x y z ⟨l, hl⟩ ⟨m, hm⟩
      exact ⟨m ++ l, by simp [hm, hl, mul_assoc]⟩

theorem exists_chi [NeZero q] (τ' : Prim q A → M)
    (hl : ∀ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 → (l.map τ').sum = 0) :
    ∃ χ : Aˣ → M, ∀ (ζ : Prim q A) (v w : Aˣ), (w : A) = ζ.1 * v → χ w = χ v + τ' ζ := by
  classical
  let S := rel q A
  let r : Aˣ → Aˣ := fun x => Quotient.out (s := S) (Quotient.mk S x)
  have hr : ∀ x, S.r (r x) x := fun x => Quotient.exact (s := S) (Quotient.out_eq (s := S) (Quotient.mk S x))
  let L : Aˣ → List (Prim q A) := fun x => Classical.choose (hr x)
  have hL : ∀ x : Aˣ, (x : A) = ((L x).map fun ζ => ζ.1).prod * (r x : A) := fun x => Classical.choose_spec (hr x)
  refine ⟨fun x => ((L x).map τ').sum, ?_⟩
  intro ζ v w h
  have hvw : S.r v w := ⟨[ζ], by simp [h]⟩
  have hrr : r w = r v := by
    show Quotient.out (s := S) (Quotient.mk S w) = Quotient.out (s := S) (Quotient.mk S v)
    rw [Quotient.sound (s := S) (S.iseqv.symm hvw)]
  have key : ((L w).map fun ζ => ζ.1).prod = ((ζ :: L v).map fun ζ => ζ.1).prod := by
    have e1 := hL w
    rw [h, hL v, hrr, ← mul_assoc] at e1
    simp only [List.map_cons, List.prod_cons]
    exact ((Units.isUnit (r v)).mul_left_inj).1 e1.symm
  show ((L w).map τ').sum = ((L v).map τ').sum + τ' ζ
  rw [sum_eq_of_prod_eq τ' hl _ _ key]
  simp [add_comm]

noncomputable section Cons
variable (q : ℕ) (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T)

abbrev R := ULift.{1} (ZMod q)

abbrev Mo (A : CommRingCat.{0}) := (T.obj A) × ((A : Type)ˣ →₀ R q)

def Idx (A : CommRingCat.{0}) := {p : Prim q A × (A : Type)ˣ × (A : Type)ˣ // ((p.2.2 : (A : Type))) = p.1.1 * p.2.1}

def relv (A : CommRingCat.{0}) (p : Idx q A) : Mo q T A :=
  (-(τ.app A).hom (twGenR A p.1.1), Finsupp.single p.1.2.2 1 - Finsupp.single p.1.2.1 1)

def N (A : CommRingCat.{0}) : Submodule (R q) (Mo q T A) := Submodule.span (R q) (Set.range (relv q T τ A))

def Gm {A B : CommRingCat.{0}} (f : A ⟶ B) : Mo q T A →ₗ[R q] Mo q T B :=
  (T.map f).hom.prodMap (Finsupp.lmapDomain (R q) (R q) (Units.map f.hom.toMonoidHom))

theorem tau_nat {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    (τ.app B).hom (twGenR B (Prim.map f.hom ζ)) = (T.map f).hom ((τ.app A).hom (twGenR A ζ)) := by
  rw [← twGenR_nat]
  exact congrArg (fun g => ModuleCat.Hom.hom g (twGenR A ζ)) (τ.naturality f)

theorem N_le {A B : CommRingCat.{0}} (f : A ⟶ B) : N q T τ A ≤ (N q T τ B).comap (Gm q T f) := by
  rw [N, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨(Prim.map f.hom p.1.1, Units.map f.hom.toMonoidHom p.1.2.1, Units.map f.hom.toMonoidHom p.1.2.2), ?_⟩, ?_⟩
  · simp [Units.coe_map, p.2, Prim.map]
  · simp [relv, Gm, tau_nat, Finsupp.mapDomain_sub, Finsupp.mapDomain_single]

def Gf : CommRingCat.{0} ⥤ ModuleCat.{1} (R q) where
  obj A := ModuleCat.of (R q) (Mo q T A ⧸ N q T τ A)
  map f := ModuleCat.ofHom ((N q T τ _).mapQ (N q T τ _) (Gm q T f) (N_le q T τ f))
  map_id A := by
    ext x <;> simp [Gm]
  map_comp f g := by
    ext x <;> (simp [Gm]; try rfl)

def iota : T ⟶ Gf q T τ where
  app A := ModuleCat.ofHom ((N q T τ A).mkQ ∘ₗ LinearMap.inl (R q) _ _)
  naturality A B f := by
    ext x
    change (Submodule.Quotient.mk ((T.map f).hom x, (0 : (B : Type)ˣ →₀ R q)) : Mo q T B ⧸ N q T τ B) =
      Submodule.Quotient.mk (Gm q T f (x, 0))
    simp [Gm]

def sec (A : CommRingCat.{0}) (v : (A : Type)ˣ) : (Gf q T τ).obj A :=
  Submodule.Quotient.mk (p := N q T τ A) ((0 : T.obj A), Finsupp.single v 1)

theorem sec_nat (A B : CommRingCat.{0}) (f : A ⟶ B) (v : (A : Type)ˣ) :
    ((Gf q T τ).map f).hom (sec q T τ A v) = sec q T τ B (Units.map f.hom.toMonoidHom v) := by
  show (Submodule.Quotient.mk (Gm q T f (0, Finsupp.single v 1)) : Mo q T B ⧸ N q T τ B) =
    Submodule.Quotient.mk (0, Finsupp.single _ 1)
  simp [Gm, Finsupp.mapDomain_single]

theorem sec_rel (A : CommRingCat.{0}) (ζ : Prim q A) (v w : (A : Type)ˣ) (h : (w : (A : Type)) = ζ.1 * v) :
    sec q T τ A w = sec q T τ A v + ((iota q T τ).app A).hom ((τ.app A).hom (twGenR A ζ)) := by
  have hm : relv q T τ A ⟨(ζ, v, w), h⟩ ∈ N q T τ A := Submodule.subset_span ⟨_, rfl⟩
  have key : (Submodule.Quotient.mk (0, Finsupp.single w 1) : Mo q T A ⧸ N q T τ A) =
      Submodule.Quotient.mk (0, Finsupp.single v 1) + Submodule.Quotient.mk ((τ.app A).hom (twGenR A ζ), 0) := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    convert hm using 1
    ext <;> simp [relv]
  exact key

theorem iota_inj [NeZero q]
    (hl : ∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) (A : CommRingCat.{0}) :
    Function.Injective ((iota q T τ).app A).hom := by
  obtain ⟨χ, hχ⟩ := exists_chi (M := T.obj A) (fun ζ => (τ.app A).hom (twGenR A ζ)) (hl A)
  let φ : Mo q T A →ₗ[R q] T.obj A :=
    LinearMap.fst _ _ _ + (Finsupp.linearCombination (R q) χ) ∘ₗ LinearMap.snd _ _ _
  have hN : N q T τ A ≤ LinearMap.ker φ := by
    rw [N, Submodule.span_le]
    rintro _ ⟨⟨⟨ζ, v, w⟩, h⟩, rfl⟩
    simp [φ, relv, hχ ζ v w h]
  intro a b hab
  have hab' : (Submodule.Quotient.mk (a, 0) : Mo q T A ⧸ N q T τ A) = Submodule.Quotient.mk (b, 0) := hab
  rw [Submodule.Quotient.eq] at hab'
  have := hN hab'
  simpa [φ, sub_eq_zero] using this

end Cons

theorem main : MuTwistQuotientEmbedsInUnitTorsorPresheaf := by
  intro q _ T τ hl
  exact ⟨Gf q T τ, iota q T τ, iota_inj q T τ hl, sec q T τ, sec_nat q T τ, sec_rel q T τ⟩
end LateralTheory.EtaleFoundations.KTP

namespace LateralTheory.EtaleFoundations
theorem mu_twist_quotient_embeds_in_unit_torsor_presheaf : MuTwistQuotientEmbedsInUnitTorsorPresheaf := KTP.main
end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionDegreeZeroInjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

theorem etale_injective_resolution_degree_zero_injective (q : ℕ) (F : Shv (ZMod q)) : Injective ((res _ F).X 0) := by
  unfold res
  exact inferInstance

theorem etale_twist_extends_through_mono_to_resolution_holds : EtaleTwistExtendsThroughMonoToResolutionZero := by
  intro q _ M j hj
  have := etale_injective_resolution_degree_zero_injective q (tw q 1)
  exact ⟨Injective.factorThru (resι _ (tw q 1)) j, Injective.comp_factorThru _ _⟩

end LateralTheory.EtaleFoundations
end

namespace LateralTheory.Fin.EtaleKummerTriangleExists
theorem etale_kummer_torsor_roots_of_unity_list_torsion_exists_of_components : LateralTheory.EtaleFoundations.MuRootListProductOneSumEtaleLocallyZero := by
  apply LateralTheory.EtaleFoundations.mu_root_list_product_one_sum_etale_locally_zero
theorem etale_kummer_torsor_roots_of_unity_torsion_exists_of_components : LateralTheory.EtaleFoundations.ExistsEtaleMonoMuTwistKillingRootRelations := by
  apply LateralTheory.EtaleFoundations.exists_etale_mono_mu_twist_quotient_of_root_lists_locally_zero <;> first | exact etale_kummer_torsor_roots_of_unity_list_torsion_exists_of_components
theorem etale_kummer_torsor_torsion_preimage_exists_of_components : LateralTheory.EtaleFoundations.MuTwistQuotientEmbedsInUnitTorsorPresheaf := by
  apply LateralTheory.EtaleFoundations.mu_twist_quotient_embeds_in_unit_torsor_presheaf
theorem etale_kummer_torsor_torsion_exists_of_components : LateralTheory.EtaleFoundations.EtaleKummerSectionsIntoTwistEmbeddingExist := by
  apply LateralTheory.EtaleFoundations.exists_etale_mono_mu_twist_into_torsor_sheaf_of_presheaf <;> first | exact etale_kummer_torsor_roots_of_unity_torsion_exists_of_components | exact etale_kummer_torsor_torsion_preimage_exists_of_components
theorem etale_kummer_torsor_extension_exists_of_components : LateralTheory.EtaleFoundations.EtaleTwistExtendsThroughMonoToResolutionZero := by
  apply LateralTheory.EtaleFoundations.etale_twist_extends_through_mono_to_resolution_holds
theorem etale_kummer_torsor_exists_of_components : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := by
  apply LateralTheory.EtaleFoundations.etale_kummer_torsor_class_exists_of_tors_and_ext <;> first | exact etale_kummer_torsor_torsion_exists_of_components | exact etale_kummer_torsor_extension_exists_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := etale_kummer_torsor_exists_of_components
end LateralTheory.Fin.EtaleKummerTriangleExists

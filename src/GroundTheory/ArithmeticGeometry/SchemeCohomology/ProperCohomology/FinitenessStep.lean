module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafHOver
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ExistsChow

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelativeSerre
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AcyclicLeray
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SheafHEquiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian TopologicalSpace AlgebraicGeometry

universe w' v u

noncomputable section

section Congr

variable {C D : Type v} [SmallCategory C] [SmallCategory D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  {T : C} (hT : IsTerminal T)

abbrev sheafCongrAb : Sheaf J AddCommGrpCat.{v} ≌ Sheaf K AddCommGrpCat.{v} :=
  e.sheafCongr J K AddCommGrpCat.{v}

def sheafCongrSectionsIso :
    (sheafCongrAb J K e).inverse ⋙ (sheafSections J AddCommGrpCat.{v}).obj (op T) ≅
      (sheafSections K AddCommGrpCat.{v}).obj (op (e.functor.obj T)) :=
  Iso.refl _

def constantSheafCongrIso :
    constantSheaf J AddCommGrpCat.{v} ⋙ (sheafCongrAb J K e).functor ≅
      constantSheaf K AddCommGrpCat.{v} :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj J AddCommGrpCat.{v} hT).comp (sheafCongrAb J K e).toAdjunction).ofNatIsoRight
      (sheafCongrSectionsIso J K e))
    (constantSheafAdj K AddCommGrpCat.{v} (hT.isTerminalObj e.functor))

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]

instance sheafCongrAb_functor_additive : (sheafCongrAb J K e).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance sheafCongrAb_functor_preservesInjectiveObjects :
    (sheafCongrAb J K e).functor.PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafCongrAb J K e).symm.toAdjunction

def sheafHCongr [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] (G : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} ((sheafCongrAb J K e).functor.obj G) n :=
  (AddEquiv.ofBijective _ ((sheafCongrAb J K e).functor.mapExt_bijective_of_preservesInjectiveObjects
      _ G n)).trans
    (extAddEquivOfIsoLeft ((constantSheafCongrIso J K e hT).app _) _ n)

end Congr

section Scheme

variable {X : Scheme.{u}} (U : X.Opens)

instance isDenseSubsite_overEquivalence_inverse :
    U.overEquivalence.inverse.IsDenseSubsite (Opens.grothendieckTopology U.toScheme.toTopCat)
      ((Opens.grothendieckTopology X.toTopCat).over U) :=
  U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence


set_option maxHeartbeats 4000000 in
def restrictAbIso (F : X.Modules) :
    (sheafCongrAb ((Opens.grothendieckTopology X.toTopCat).over U)
      (Opens.grothendieckTopology U.toScheme.toTopCat) U.overEquivalence).functor.obj
      ((modulesAb F).over U) ≅ modulesAb (F.restrict U.ι) :=
  (SheafOfModules.toSheaf _).mapIso ((Scheme.Modules.overFunctorEquiv U).app F)

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology U.toScheme.toTopCat) AddCommGrpCat.{u})]

def cohomologyPresheafAddEquivRestrict (F : X.Modules) (n : ℕ) :
    (modulesAb F).H' n U ≃+ Sheaf.H.{w'} (modulesAb (F.restrict U.ι)) n :=
  (cohomologyPresheafOverAddEquivOfSmall _ U (modulesAb F) n).trans
    ((sheafHCongr ((Opens.grothendieckTopology X.toTopCat).over U)
      (Opens.grothendieckTopology U.toScheme.toTopCat) U.overEquivalence Over.mkIdTerminal
      ((modulesAb F).over U) n).trans
      ((Sheaf.functorH _ n).mapIso (restrictAbIso U F)).addCommGroupIsoToAddEquiv)

lemma subsingleton_H'_of_restrict (F : X.Modules) (n : ℕ)
    [h : Subsingleton (Sheaf.H.{w'} (modulesAb (F.restrict U.ι)) n)] :
    Subsingleton ((modulesAb F).H' n U) :=
  (cohomologyPresheafAddEquivRestrict.{w'} U F n).toEquiv.subsingleton

end Scheme

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

noncomputable section

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry

universe w w' u

section Top

variable {X : TopCat.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → Opens X)

def HAcyclicOn (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ {n : ℕ} (i : Fin (n + 1) → ι) (q : ℕ), Subsingleton (G.H' (q + 1) (inter U i))

variable {U}

lemma surjective_app_of_subsingleton_H'
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (V : Opens X) [Subsingleton (S.X₁.H' 1 V)] : Function.Surjective (S.g.hom.app (op V)) := by
  intro y
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    ((H'.equiv₀ S.X₃ V).symm y) rfl (Subsingleton.elim (α := S.X₁.H' 1 V) _ _)
  have key : H'.equiv₀ S.X₃ V (x.comp (Ext.mk₀ S.g) (add_zero 0)) =
      S.g.hom.app (op V) (H'.equiv₀ S.X₂ V x) := H'.equiv₀_naturality S.g V x
  exact ⟨H'.equiv₀ S.X₂ V x, by rw [← key, hx, AddEquiv.apply_symm_apply]⟩

lemma subsingleton_H'_of_injective
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    [Injective S.X₂] (V : Opens X) (q : ℕ) [Subsingleton (S.X₁.H' (q + 2) V)] :
    Subsingleton (S.X₃.H' (q + 1) V) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    y rfl (Subsingleton.elim (α := S.X₁.H' (q + 2) V) _ _)
  have : Subsingleton (S.X₂.H' (q + 1) V) := H'.subsingleton_of_injective S.X₂ q V
  have hx0 : x = 0 := Subsingleton.elim (α := S.X₂.H' (q + 1) V) _ _
  rw [← hx, hx0, Ext.zero_comp]
  rfl

variable (U)

lemma injectiveSequence_isCechShortExact_of_acyclic
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    IsCechShortExact U (injectiveSequence G).f.hom (injectiveSequence G).g.hom :=
  isCechShortExact_of_surjective (injectiveSequence_shortExact G) U fun i =>
    have : Subsingleton ((injectiveSequence G).X₁.H' 1 (inter U i)) := hG i 0
    surjective_app_of_subsingleton_H'.{w'} (injectiveSequence_shortExact G) _

lemma injectiveSequence_hAcyclicOn
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    HAcyclicOn.{w, w'} U (injectiveSequence G).X₃ := fun i q =>
  have : Subsingleton ((injectiveSequence G).X₁.H' (q + 2) (inter U i)) := hG i (q + 1)
  have : Injective (injectiveSequence G).X₂ := inferInstanceAs (Injective (Injective.under G))
  subsingleton_H'_of_injective (injectiveSequence_shortExact G) _ q

variable (hU : iSup U = ⊤)

def cechHEquivOfAcyclic : ∀ (n : ℕ) (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
    HAcyclicOn.{w, w'} U G → (cechH G.obj U n ≃+ Sheaf.H.{w'} G n)
  | 0, G, _ => cechHZeroEquivH G U hU
  | 1, G, hG => cechHOneEquiv (S := injectiveSequence G) U hU (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U)
  | m + 2, G, hG => cechHEquivStep (S := injectiveSequence G) U (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U) m
      (cechHEquivOfAcyclic (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))

theorem cechHEquivOfAcyclic_naturality : ∀ (n : ℕ)
    {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hG : HAcyclicOn.{w, w'} U G) (hG' : HAcyclicOn.{w, w'} U G') (φ : G ⟶ G')
    (x : cechH G.obj U n),
    cechHEquivOfAcyclic U hU n G' hG' (cechHMap U φ.hom n x) =
      Sheaf.H.map.{w'} φ n (cechHEquivOfAcyclic U hU n G hG x)
  | 0, _, _, _, _, φ, x => cechHZeroEquivH_naturality U φ hU x
  | 1, G, G', hG, hG', φ, x =>
      cechHOneEquiv_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U hU
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) x
  | m + 2, G, G', hG, hG', φ, x =>
      cechHEquivStep_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) m
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G' hG'))
        (fun y => cechHEquivOfAcyclic_naturality (m + 1) (injectiveSequence_hAcyclicOn U G hG)
          (injectiveSequence_hAcyclicOn U G' hG') (injectiveSequenceMap φ).τ₃ y) x

end Top

section Scheme

variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → X.Opens) (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def cechHLinearEquivHOfAcyclic (hU : iSup U = ⊤) (F : X.Modules)
    (hF : HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F)) (n : ℕ) :
    cechH (modulesAb F).obj U n ≃ₗ[A] Sheaf.H.{w'} (modulesAb F) n :=
  (cechHEquivOfAcyclic (X := X.toTopCat) U hU n (modulesAb F) hF).toLinearEquiv fun a x =>
    cechHEquivOfAcyclic_naturality (X := X.toTopCat) U hU n hF hF
      (modulesAbMap (smulHom F (algebraMap A Γ(X, ⊤) a))) x

variable [∀ V : X.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]

lemma hAcyclicOn_of_restrict (F : X.Modules)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (F.restrict (⨅ a, U (i a)).ι)) (q + 1))) :
    HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F) := fun {n} i q => by
  have := h n i q
  rw [inter_eq_iInf]
  exact subsingleton_H'_of_restrict.{w'} (⨅ a, U (i a)) F (q + 1)

end Scheme

section Pushforward

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) (A : Type u) [CommRing A] [X.Over (Spec (.of A))]
  [X'.Over (Spec (.of A))] [ψ.IsOver (Spec (.of A))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u})]
  [∀ V : X'.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X'.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X'.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (V : ι → X.Opens) (hV : iSup V = ⊤)
  (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, V (i a)))

attribute [local instance] algebraOfOver

def HLinearEquivPushforwardOfAcyclic (G : X'.Modules)
    [((Scheme.Modules.pushforward ψ).obj G).IsQuasicoherent]
    (hG : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (G.restrict (ψ ⁻¹ᵁ ⨅ a, V (i a)).ι)) (q + 1)))
    (p : ℕ) :
    Sheaf.H.{w'} (modulesAb G) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward ψ).obj G)) p :=
  have hV' : iSup (fun j => ψ ⁻¹ᵁ V j) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]
    rfl
  have hG' : HAcyclicOn.{w, w'} (X := X'.toTopCat) (fun j => ψ ⁻¹ᵁ V j) (modulesAb G) :=
    hAcyclicOn_of_restrict _ G fun n i q => by
      have e := preimage_inter ψ V i
      rw [inter_eq_iInf, inter_eq_iInf] at e
      have h1 := hG n i q
      rw [e] at h1
      exact h1
  (cechHLinearEquivHOfAcyclic (fun j => ψ ⁻¹ᵁ V j) A hV' G hG' p).symm ≪≫ₗ
    (cechHPushforwardLinearEquiv ψ A G V p).symm ≪≫ₗ cechHLinearEquivH V hV hVaff A _ p

end Pushforward

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

attribute [local instance] algebraOfOver

namespace ProjScheme

theorem exists_relativeSerre {A : Type u} [CommRing A] [IsNoetherianRing A] {X X' : Scheme.{u}}
    [X.Over (Spec (.of A))] [X'.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [CompactSpace X] [IsLocallyNoetherian X] {N : ℕ} (i : X' ⟶ projectiveSpace A N)
    [IsClosedImmersion i] [i.IsOver (Spec (.of A))] (ψ : X' ⟶ X) [ψ.IsOver (Spec (.of A))]
    (G : X'.Modules) (hG : IsCoherent G) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsCoherent ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)) ∧
      ∀ p : ℕ, Nonempty (Sheaf.H.{u} (modulesAb (ProjScheme.twist i G n)) p ≃ₗ[A]
        Sheaf.H.{u} (modulesAb ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n))) p) := by
  classical
  have h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) := by
    rw [CategoryTheory.comp_over ψ (Spec (.of A))]
    exact CategoryTheory.comp_over i (Spec (.of A))
  have : X.IsSeparated := ⟨by
    rw [show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  have : QuasiCompact (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ (X ↘ Spec (.of A))
  have : QuasiSeparated (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiSeparated ψ := QuasiSeparated.of_comp ψ (X ↘ Spec (.of A))

  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun U : X.affineOpens => (U : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨U, hU⟩ := Opens.mem_iSup.1
        (show x ∈ ⨆ U : X.affineOpens, (U : X.Opens) by rw [iSup_affineOpens_eq_top X]; trivial)
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  let ι := { U // U ∈ t }
  let V : ι → X.Opens := fun a => a.1.1
  have hVaff1 : ∀ a, IsAffineOpen (V a) := fun a => a.1.2
  have hV : iSup V = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hUt, hxU⟩ := Set.mem_iUnion.1 hU
    exact Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

  let W : Finset ι → X.Opens := fun S => ⨅ a : S, V a
  have hWaff : ∀ S : Finset ι, S.Nonempty → IsAffineOpen (W S) := fun S hS => by
    have : Nonempty S := hS.to_subtype
    exact IsAffineOpen.iInf fun a => hVaff1 a
  have hWtuple : ∀ (m : ℕ) (s : Fin (m + 1) → ι),
      (⨅ a, V (s a)) = W (Finset.univ.image s) := fun m s => by
    apply le_antisymm
    · exact le_iInf fun b => by
        obtain ⟨a, -, ha⟩ := Finset.mem_image.1 b.2
        exact (iInf_le _ a).trans (le_of_eq (congrArg V ha))
    · exact le_iInf fun a => iInf_le (fun b : (Finset.univ.image s : Finset ι) => V b)
        ⟨s a, Finset.mem_image_of_mem s (Finset.mem_univ a)⟩
  have hWsingle : ∀ a : ι, W {a} = V a := fun a => by
    apply le_antisymm
    · exact iInf_le (fun b : ({a} : Finset ι) => V b) ⟨a, Finset.mem_singleton_self a⟩
    · exact le_iInf fun b => le_of_eq (congrArg V (Finset.mem_singleton.1 b.2).symm)

  have key : ∀ S : Finset ι, ∃ n₁ : ℕ, S.Nonempty → ∀ n : ℕ, n₁ ≤ n →
      (∀ q : ℕ, Subsingleton (Sheaf.H.{u}
        (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ W S).ι)) (q + 1))) ∧
      Module.Finite Γ(X, W S) Γ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n), W S) := by
    intro S
    by_cases hS : S.Nonempty
    · have hA := hWaff S hS
      have : IsNoetherianRing Γ(X, W S) := IsLocallyNoetherian.component_noetherian ⟨_, hA⟩
      obtain ⟨n₁, hn₁⟩ := RelSerre.exists_vanishing_finite i ψ h hA G hG
      exact ⟨n₁, fun _ n hn => ⟨(hn₁ n hn).1,
        RelSerre.finite_sections_pushforward i ψ h hA _ (hn₁ n hn).2⟩⟩
    · exact ⟨0, fun h' => absurd h' hS⟩
  choose nS hnS using key
  refine ⟨Finset.univ.sup nS, fun n hn => ?_⟩
  have hle : ∀ S, nS S ≤ n := fun S => (Finset.le_sup (Finset.mem_univ S)).trans hn
  have : G.IsQuasicoherent := hG.1
  have : ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs ψ _
  refine ⟨?_, fun p => ?_⟩
  · refine isCoherent_of_affineCover _ V hVaff1 hV fun a => ?_
    have hfin := (hnS {a} (Finset.singleton_nonempty a) n (hle _)).2
    rw [hWsingle] at hfin
    exact hfin
  · have hVaff : ∀ (m : ℕ) (s : Fin (m + 1) → ι), IsAffineOpen (⨅ a, V (s a)) := fun m s =>
      IsAffineOpen.iInf fun a => hVaff1 (s a)
    refine ⟨HLinearEquivPushforwardOfAcyclic ψ A V hV hVaff (ProjScheme.twist i G n)
      ?_ p⟩
    intro m s q
    have h1 := (hnS (Finset.univ.image s) (Finset.univ_nonempty.image s) n (hle _)).1 q
    rw [← hWtuple] at h1
    exact h1

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma IsBasisOn.isUnit_smul {P : PMod X} {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    {a : ringOn X U} (ha : IsUnit a) : IsBasisOn P U (a • s) := by
  intro V h
  have e : resM P h (a • s) = resR h a • resM P h s := resM_smul P h a s
  have hu : IsUnit (resR h a) := ha.map _
  have : (fun r : ringOn X V => r • resM P h (a • s)) =
      (fun r : ringOn X V => r • resM P h s) ∘ (fun r => r * resR h a) := by
    funext r
    simp only [Function.comp_apply, e, mul_smul]
  rw [this]
  refine (hs V h).comp ⟨fun r r' hrr => hu.mul_left_injective hrr, fun r => ⟨r * hu.unit⁻¹, ?_⟩⟩
  change r * ↑hu.unit⁻¹ * resR h a = r
  rw [mul_assoc, hu.val_inv_mul, mul_one]

theorem exists_isBasisOn_generatingSection (L : X.Modules) [L.IsQuasicoherent]
    (hL : IsInvertibleSheaf L) (σ : L.GeneratingSections) [σ.IsFiniteType] (x : X) :
    ∃ (k : σ.I) (W : X.Opens), x ∈ W ∧
      IsBasisOn ((preMod X).obj L) W
        (resM ((preMod X).obj L) le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤))) := by
  classical
  set P := (preMod X).obj L
  obtain ⟨U, hxU, e, he⟩ := hL x
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  replace hVU : V ≤ U := hVU
  have hb : IsBasisOn P V (resM P hVU e) := he.restrict hVU
  let φ : ringOn X V ≃ₗ[ringOn X V] P.obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM P hVU e))
      (by
        have h := hb V le_rfl
        rwa [show resM P (le_refl V) (resM P hVU e) = resM P hVU e by
          rw [resM_resM]] at h)
  let g : σ.I → P.obj (op V) := fun k => resM P le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤))
  let a : σ.I → ringOn X V := fun k => φ.symm (g k)
  have hga : ∀ k, g k = a k • resM P hVU e := fun k => by
    change g k = φ (a k)
    simp [a]
  have hspan : Submodule.span (ringOn X V) (Set.range g) = ⊤ :=
    span_eq_top_of_generatingSections L σ hVaff
  have hIdeal : Ideal.span (Set.range a) = ⊤ := by
    have h2 : Submodule.map φ.symm.toLinearMap (Submodule.span (ringOn X V) (Set.range g)) = ⊤ := by
      rw [hspan, Submodule.map_top,
        LinearMap.range_eq_top]
      exact φ.symm.surjective
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hxcov : V ≤ ⨆ k, X.basicOpen (a k) := by
    have := (hVaff.self_le_iSup_basicOpen_iff (s := Set.range a)).2 hIdeal
    intro y hy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := Opens.mem_iSup.1 (this hy)
    exact Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hxcov hxV)
  have hWV : X.basicOpen (a k) ≤ V := X.basicOpen_le _
  refine ⟨k, X.basicOpen (a k), hk, ?_⟩
  have hu : IsUnit (resR hWV (a k)) := X.toRingedSpace.isUnit_res_basicOpen (a k)
  have key : resM P le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤)) =
      resR hWV (a k) • resM P hWV (resM P hVU e) := by
    have h1 : resM P hWV (g k) = resM P (hWV.trans le_top) _ := resM_resM P le_top hWV _
    rw [hga k, resM_smul] at h1
    exact h1.symm
  rw [key]
  exact (hb.restrict hWV).isUnit_smul hu

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionTensor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma bijective_app_of_factor {A B : X.Modules} (φ : A ⟶ B) {P : PMod X}
    (p : (preMod X).obj A ⟶ P) (q : P ⟶ (preMod X).obj B)
    (hq : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj q)
    (hφ : (preMod X).map φ = p ≫ q) {W : X.Opens}
    (hp : ∀ V ≤ W, Function.Bijective (p.app (op V))) :
    ∀ V ≤ W, Function.Bijective (φ.app V) := by
  obtain ⟨hq₁, hq₂⟩ := (ModulesTensor.W_toPresheaf_iff q).1 hq
  have hφapp : ∀ (V : X.Opens) (a : Γ(A, V)), φ.app V a = q.app (op V) (p.app (op V) a) :=
    fun V a => congrArg (fun g => g.app (op V) a) hφ |>.trans rfl
  have nat : ∀ {V V' : X.Opens} (i : V' ≤ V) (σ : Γ(A, V)),
      φ.app V' (A.presheaf.map (homOfLE i).op σ) = B.presheaf.map (homOfLE i).op (φ.app V σ) :=
    fun i σ => NatTrans.naturality_apply φ.mapPresheaf (homOfLE i).op σ
  have inj : ∀ V ≤ W, Function.Injective (φ.app V) := by
    intro V hV
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hφapp] at ha
    have hS := hq₁ (op V) _ ha
    rw [Opens.mem_grothendieckTopology] at hS
    apply sheaf_eq_of_locally ⟨A.presheaf, A.isSheaf⟩ (V := V)
    intro x hx
    obtain ⟨V', i, hi, hxV'⟩ := hS x hx
    refine ⟨V', i.le, hxV', ?_⟩
    have h0 : p.app (op V') (A.presheaf.map (homOfLE i.le).op a) = 0 := by
      have := PresheafOfModules.naturality_apply p (homOfLE i.le).op a
      exact this.trans hi
    apply (hp V' (i.le.trans hV)).1
    exact h0.trans (map_zero _).symm |>.trans (congrArg _ (map_zero _).symm)
  intro V hV
  refine ⟨inj V hV, fun b => ?_⟩
  have hS := hq₂ (op V) b
  rw [Opens.mem_grothendieckTopology] at hS
  choose V' i hi hxV' using hS
  choose w hw using hi
  choose a₀ ha using fun x (hx : x ∈ V) => (hp (V' x hx) ((i x hx).le.trans hV)).2 (w x hx)
  let a : ∀ x (hx : x ∈ V), Γ(A, V' x hx) := fun x hx => a₀ x hx
  have key : ∀ x hx, φ.app (V' x hx) (a x hx) = B.presheaf.map (homOfLE (i x hx).le).op b :=
    fun x hx => (hφapp _ (a x hx)).trans ((congrArg _ (ha x hx)).trans (hw x hx))
  obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨A.presheaf, A.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
    (fun c => V' c.1 c.2) (fun c => (i c.1 c.2).le) (fun x hx => ⟨⟨x, hx⟩, hxV' x hx⟩)
    (fun c => a c.1 c.2) (by
      intro c d
      apply inj _ (inf_le_left.trans ((i c.1 c.2).le.trans hV))
      change φ.app _ (A.presheaf.map _ (a c.1 c.2)) = φ.app _ (A.presheaf.map _ (a d.1 d.2))
      rw [nat, nat, key, key]
      change ((B.presheaf.map _ ≫ B.presheaf.map _) b) = ((B.presheaf.map _ ≫ B.presheaf.map _) b)
      rw [← B.presheaf.map_comp, ← B.presheaf.map_comp]
      rfl)
  refine ⟨g, ?_⟩
  apply sheaf_eq_of_locally ⟨B.presheaf, B.isSheaf⟩ (V := V)
  intro x hx
  refine ⟨V' x hx, (i x hx).le, hxV' x hx, ?_⟩
  change B.presheaf.map _ (φ.app V g) = _
  rw [← nat]
  have := hg ⟨x, hx⟩
  simp only at this
  rw [this]
  exact key x hx

def homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) : M ⟶ S :=
  inv ((sheafifyModAdj X).counit.app M) ≫ ((sheafifyModAdj X).homEquiv _ _).symm g

lemma preMod_map_homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) :
    (preMod X).map (homOfPreMod g) = g := by
  have h1 : (preMod X).map (inv ((sheafifyModAdj X).counit.app M)) =
      (sheafifyModAdj X).unit.app ((preMod X).obj M) := by
    rw [Functor.map_inv]
    exact (IsIso.eq_inv_of_inv_hom_id ((sheafifyModAdj X).right_triangle_components M)).symm
  rw [homOfPreMod, Functor.map_comp, h1, Adjunction.homEquiv_counit, Functor.map_comp,
    ← Category.assoc]
  erw [← (sheafifyModAdj X).unit.naturality g]
  rw [Category.assoc]
  erw [(sheafifyModAdj X).right_triangle_components S]
  exact Category.comp_id g

variable (M L : X.Modules) (s : Γ(L, ⊤))

def tensorSection : (preMod X).obj M ⟶ (preMod X).obj M ⊗ (preMod X).obj L :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun m => (m : ((preMod X).obj M).obj U) ⊗ₜ
            resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s
          map_zero' := zero_tmul _ _
          map_add' := fun a b => add_tmul _ _ _ }
      naturality := fun U V g => by
        ext m
        change (((preMod X).obj M).map g m) ⊗ₜ resM ((preMod X).obj L) (le_top : V.unop ≤ ⊤) s =
          (((preMod X).obj M).map g m) ⊗ₜ ((preMod X).obj L).map g
            (resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s)
        congr 1
        change ((preMod X).obj L).map (homOfLE (le_top : V.unop ≤ ⊤)).op s =
          ((preMod X).obj L).map g (((preMod X).obj L).map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
        exact PresheafOfModules.map_comp_apply ((preMod X).obj L) (homOfLE (le_top : U.unop ≤ ⊤)).op g s }
    (fun _ _ _ => rfl)

def mulSection : M ⟶ M ⊗ L :=
  homOfPreMod (tensorSection M L s ≫ tensorToSheaf M L)

lemma preMod_map_mulSection :
    (preMod X).map (mulSection M L s) = tensorSection M L s ≫ tensorToSheaf M L :=
  preMod_map_homOfPreMod _

theorem bijective_mulSection_app {W : X.Opens}
    (hs : IsBasisOn ((preMod X).obj L) W (resM ((preMod X).obj L) le_top s)) :
    ∀ V ≤ W, Function.Bijective ((mulSection M L s).app V) := by
  refine bijective_app_of_factor _ (tensorSection M L s) (tensorToSheaf M L) (W_tensorToSheaf M L)
    (preMod_map_mulSection M L s) ?_
  intro V hV
  have e0 : resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s) =
      resM ((preMod X).obj L) (le_top : V ≤ ⊤) s := resM_resM _ le_top hV s
  let R := X.sheaf.obj.obj (op V)
  let e : R ≃ₗ[R] ((preMod X).obj L).obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _
      (resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s))) (hs V hV)
  let E := (TensorProduct.rid R (((preMod X).obj M).obj (op V))).symm ≪≫ₗ
    e.lTensor (((preMod X).obj M).obj (op V))
  have hE : ∀ m, E m = (tensorSection M L s).app (op V) m := by
    intro m
    change m ⊗ₜ e 1 = m ⊗ₜ resM ((preMod X).obj L) (le_top : V ≤ ⊤) s
    congr 1
    exact (one_smul R _).trans e0
  have : ⇑((tensorSection M L s).app (op V)) = E := funext fun m => (hE m).symm
  rw [this]
  exact E.bijective

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.IrreducibleImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

lemma isIso_opens_ι_restrict {Z : Scheme.{u}} (O : Z.Opens) : IsIso (O.ι ∣_ O) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply le_antisymm le_top
  intro x _
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change O.ι x ∈ O
    exact x.2
  · apply Subtype.ext
    exact morphismRestrict_base_coe O.ι O ⟨x, _⟩

theorem exists_irreducible_isIso_restrict (Z : Scheme.{u}) [IsNoetherian Z] [Nonempty Z] :
    ∃ (Z₁ : Scheme.{u}) (c : Z₁ ⟶ Z) (O : Z.Opens), IsClosedImmersion c ∧ IrreducibleSpace Z₁ ∧
      (O : Set Z).Nonempty ∧ IsIso (c ∣_ O) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hC := irreducibleComponent_mem_irreducibleComponents z
  set C := irreducibleComponent z
  set O := Z.irreducibleComponentOpen C
  refine ⟨Z.irreducibleComponent C hC, Z.irreducibleComponentι C hC, O, inferInstance,
    inferInstance, ?_, ?_⟩
  · obtain ⟨o, ho, hne, hoC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC

    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents C hC
    have : (O : Set Z) = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ := rfl
    rw [this, Set.compl_empty_iff] at h
    rw [h, Set.compl_univ, closure_empty] at hcl
    exact hC.1.nonempty.ne_empty hcl.symm
  · have hI := Z.irreducibleComponentIdeal_def C hC
    have : IsIso (O.ι ∣_ O) := isIso_opens_ι_restrict O
    have key := SchemeImage.imageRestrictLift_fac O.ι O
    change IsIso ((Z.irreducibleComponentIdeal C hC).subschemeι ∣_ O)
    rw [hI]
    change IsIso (O.ι.imageι ∣_ O)
    rw [← key]
    infer_instance

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory

universe u

noncomputable section

attribute [local instance] algebraOfOver

lemma isClosedImmersion_of_isIso' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f :=
  inferInstance

theorem isCoherent_unit (X : Scheme.{u}) : IsCoherent (𝟙_ X.Modules) := by
  refine ⟨isQuasicoherent_unit X, fun U _ => ?_⟩
  let one : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))
  refine ⟨⟨{one}, ?_⟩⟩
  rw [eq_top_iff]
  intro m _
  have hm : m = (show Γ(X, U) from m) • one := (mul_one (show Γ(X, U) from m)).symm
  rw [hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_singleton_self _)))

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

theorem finiteH_step
    (X : Scheme.{u}) [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))]
    (T : Set X) (hT : IsClosed T)
    (IH : ∀ T' : Set X, IsClosed T' → T' ⊂ T → ∀ F : X.Modules, IsCoherent F →
      Scheme.Modules.SupportedIn F T' → FiniteH.{u} A F)
    (F : X.Modules) (hF : IsCoherent F) (hFT : Scheme.Modules.SupportedIn F T) :
    FiniteH.{u} A F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := hF.1
  obtain ⟨I, hIT, G, hG, ⟨e⟩⟩ := exists_pushforward_iso_of_supportedIn F hF hT hFT
  have hFI : Scheme.Modules.SupportedIn F (I.support : Set X) := by
    have h := (Scheme.Modules.SupportedIn.univ G).pushforward I.subschemeι
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h
    exact h.of_iso e
  by_cases hST : (I.support : Set X) = T
  swap
  · exact IH _ I.support.isClosed (lt_of_le_of_ne hIT hST) F hF hFI
  rcases isEmpty_or_nonempty I.subscheme with hZ | hZ
  · have h0 : (I.support : Set X) = ∅ := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.range_eq_empty _
    exact FiniteH.of_isZero A (Scheme.Modules.SupportedIn.isZero_of_empty (h0 ▸ hFI))
  set Z := I.subscheme
  set j : Z ⟶ X := I.subschemeι
  let _ : Z.Over (Spec (.of A)) := ⟨j ≫ (X ↘ Spec (.of A))⟩
  have : IsProper (Z ↘ Spec (.of A)) := (inferInstance : IsProper (j ≫ (X ↘ Spec (.of A))))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of A))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of A))
  have : IsNoetherian Z := ⟨⟩
  obtain ⟨Z₁, c, O, hc, hirr, hOne, hcO⟩ := exists_irreducible_isIso_restrict Z
  let _ : Z₁.Over (Spec (.of A)) := ⟨c ≫ (Z ↘ Spec (.of A))⟩
  have : IsProper (Z₁ ↘ Spec (.of A)) := (inferInstance : IsProper (c ≫ (Z ↘ Spec (.of A))))
  obtain ⟨N, Z', i, π, U₁, hi, hiπ, hU₁, hπU⟩ := exists_chow (A := A) Z₁
  set ψ : Z' ⟶ X := π ≫ c ≫ j with hψ
  let _ : Z'.Over (Spec (.of A)) := ⟨ψ ≫ (X ↘ Spec (.of A))⟩
  have : ψ.IsOver (Spec (.of A)) := ⟨rfl⟩
  have : i.IsOver (Spec (.of A)) := ⟨by
    change i ≫ ProjSpace.toSpecBase A N = (π ≫ c ≫ j) ≫ (X ↘ Spec (.of A))
    rw [hiπ]
    simp only [Category.assoc]
    rfl⟩
  have hZ'p : IsProper (ψ ≫ (X ↘ Spec (.of A))) := by
    have h : ψ ≫ (X ↘ Spec (.of A)) = i ≫ ProjSpace.toSpecBase A N :=
      (CategoryTheory.comp_over i (Spec (.of A))).symm
    rw [h]
    infer_instance
  have : IsProper ψ := IsProper.of_comp ψ (X ↘ Spec (.of A))
  have : IsClosedImmersion (c ≫ j) := inferInstance

  have hG' : IsCoherent ((Scheme.Modules.pullback ψ).obj F) := isCoherent_pullback ψ hF
  set G' := (Scheme.Modules.pullback ψ).obj F
  obtain ⟨n₀, hn₀⟩ := ProjScheme.exists_relativeSerre i ψ G' hG'
  letI : (𝟙_ Z'.Modules).IsQuasicoherent := isQuasicoherent_unit Z'
  obtain ⟨n₁, hn₁⟩ := ProjScheme.exists_generatingSections_twist i (𝟙_ Z'.Modules)
    (isCoherent_unit Z')
  set n := max n₀ n₁
  obtain ⟨σ, hσ⟩ := hn₁ n (le_max_right _ _)
  set L := ProjScheme.twistingSheaf i (n : ℤ)
  have eL : ProjScheme.twist i (𝟙_ Z'.Modules) (n : ℤ) ≅ L := λ_ L
  obtain ⟨σL, hσL⟩ := exists_generatingSections_of_iso eL ⟨σ, hσ⟩
  have : L.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z'.ringCatSheaf).prop_of_iso eL
      (ProjScheme.isQuasicoherent_twist i (𝟙_ Z'.Modules) (n : ℤ))
  have hL : IsInvertibleSheaf L := ProjScheme.isInvertibleSheaf_twistingSheaf i (n : ℤ)

  have hcO' : ((c ⁻¹ᵁ O : Z₁.Opens) : Set Z₁).Nonempty := by
    obtain ⟨o, ho⟩ := hOne
    obtain ⟨z, hz, -⟩ := exists_preimage_of_isIso_morphismRestrict c ho
    exact ⟨z, hz⟩
  obtain ⟨z, hzU, hzO⟩ := nonempty_preirreducible_inter U₁.isOpen (c ⁻¹ᵁ O).isOpen hU₁ hcO'
  obtain ⟨y, hyU, hyz⟩ := exists_preimage_of_isIso_morphismRestrict π hzU
  obtain ⟨k, W', hyW', hbasis⟩ := exists_isBasisOn_generatingSection L hL σL y
  set s : Γ(L, ⊤) := (σL.s k).val (op ⊤)
  set Φ := (Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G' n)
  let α : F ⟶ Φ := (Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app F ≫
    (Scheme.Modules.pushforward ψ).map (mulSection G' L s)

  set Wg : Z'.Opens := W' ⊓ π ⁻¹ᵁ (U₁ ⊓ c ⁻¹ᵁ O)
  set Bad : Set X := ψ.base '' (Wg : Set Z')ᶜ ∪ j.base '' (O : Set Z)ᶜ ∪
    (c ≫ j).base '' (U₁ : Set Z₁)ᶜ
  have hBad : IsClosed Bad :=
    ((ψ.isClosedMap _ Wg.isOpen.isClosed_compl).union
      (j.isClosedMap _ O.isOpen.isClosed_compl)).union
      ((c ≫ j).isClosedMap _ U₁.isOpen.isClosed_compl)
  obtain ⟨W, hWdef⟩ : ∃ W : X.Opens, (W : Set X) = Badᶜ := ⟨⟨Badᶜ, hBad.isOpen_compl⟩, rfl⟩
  have hcjinj : Function.Injective (c ≫ j).base := (c ≫ j).isClosedEmbedding.injective
  have hjinj : Function.Injective j.base := j.isClosedEmbedding.injective
  have hψy : ψ.base y = (c ≫ j).base (π.base y) := rfl
  have hyWg : y ∈ Wg := ⟨hyW', by
    change π.base y ∈ U₁ ⊓ c ⁻¹ᵁ O
    rw [hyz]
    exact ⟨hzU, hzO⟩⟩
  have hxW : ψ.base y ∈ W := by
    change ψ.base y ∈ (W : Set X)
    rw [hWdef]
    rintro ((⟨y', hy', hyy'⟩ | ⟨o, ho, hoy⟩) | ⟨z', hz', hzy⟩)
    · have h1 : π.base y' = π.base y := hcjinj hyy'
      have hy'U : y' ∈ π ⁻¹ᵁ U₁ := by
        change π.base y' ∈ U₁
        rw [h1, hyz]
        exact hzU
      exact hy' (injOn_of_isIso_morphismRestrict π hy'U hyU h1 ▸ hyWg)
    · have h1 : o = c.base (π.base y) := hjinj hoy
      apply ho
      rw [h1, hyz]
      exact hzO
    · have h1 : z' = π.base y := hcjinj hzy
      apply hz'
      rw [h1, hyz]
      exact hzU
  have hψW : ψ ⁻¹ᵁ W ≤ Wg := fun y' hy' => by
    have hy' : ψ.base y' ∈ (W : Set X) := hy'
    rw [hWdef] at hy'
    by_contra h
    exact hy' (Or.inl (Or.inl ⟨y', h, rfl⟩))
  have hjW : j ⁻¹ᵁ W ≤ O := fun z' hz' => by
    have hz' : j.base z' ∈ (W : Set X) := hz'
    rw [hWdef] at hz'
    by_contra h
    exact hz' (Or.inl (Or.inr ⟨z', h, rfl⟩))
  have hcjW : (c ≫ j) ⁻¹ᵁ W ≤ U₁ := fun z' hz' => by
    have hz' : (c ≫ j).base z' ∈ (W : Set X) := hz'
    rw [hWdef] at hz'
    by_contra h
    exact hz' (Or.inr ⟨z', h, rfl⟩)

  have hπW : IsIso (π ∣_ ((c ≫ j) ⁻¹ᵁ W)) := isIso_morphismRestrict_of_le π hcjW
  have : IsClosedImmersion (ψ ∣_ W) := by
    have h1 : IsClosedImmersion (π ∣_ ((c ≫ j) ⁻¹ᵁ W)) :=
      @isClosedImmersion_of_isIso' _ _ _ hπW
    have h2 : IsClosedImmersion ((c ≫ j) ∣_ W) := inferInstance
    rw [show ψ = π ≫ (c ≫ j) from rfl, morphismRestrict_comp]
    exact @IsClosedImmersion.comp _ _ _ _ _ h1 h2

  have hkill : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → ∀ a : Γ(X, V), ψ.app V a = 0 →
      ∀ m : Γ(F, V), a • m = 0 := by
    intro V _ hVW a ha m
    have hVc : (c ≫ j) ⁻¹ᵁ V ≤ U₁ := (Scheme.Hom.preimage_mono _ hVW).trans hcjW
    have hVj : j ⁻¹ᵁ V ≤ O := (Scheme.Hom.preimage_mono _ hVW).trans hjW
    have hπinj := (bijective_app_of_isIso_morphismRestrict π hVc).1
    have hcinj := (bijective_app_of_isIso_morphismRestrict c hVj).1
    have hja : j.app V a = 0 := by
      apply hcinj
      apply hπinj
      calc _ = (ψ.app V) a := rfl
        _ = 0 := ha
        _ = _ := by rw [map_zero]; exact (map_zero _).symm
    obtain ⟨m', rfl⟩ : ∃ m', e.hom.app V m' = m :=
      ⟨e.inv.app V m, by rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
        e.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]⟩
    have h0 : a • m' = 0 := by
      rw [smul_pushforward, hja, zero_smul]
      rfl
    rw [← Scheme.Modules.Hom.app_smul, h0, map_zero]
  have hunit := bijective_unit_app_of_le ψ F W hkill
  have hmul := bijective_mulSection_app G' L s hbasis
  have hα : ∀ V : X.Opens, V ≤ W → Function.Bijective (α.app V) := fun V hV =>
    (hmul (ψ ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hV).trans (hψW.trans inf_le_left))).comp
      (hunit V hV)

  obtain ⟨hΦcoh, hΦiso⟩ := hn₀ n (le_max_left _ _)
  have hΦ : FiniteH.{u} A Φ := fun p => by
    obtain ⟨e'⟩ := hΦiso p
    have := ProjScheme.finite_H.{u} i (ProjScheme.twist i G' n)
      (isCoherent_tensor_of_invertible hG' hL) p
    exact Module.Finite.equiv e'

  have hxT : ψ.base y ∈ T := by
    rw [← hST, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨c.base (π.base y), rfl⟩
  have hT' : IsClosed (T ∩ (W : Set X)ᶜ) := hT.inter W.isOpen.isClosed_compl
  have hT'T : T ∩ (W : Set X)ᶜ ⊂ T :=
    ⟨Set.inter_subset_left, fun h => (h hxT).2 hxW⟩
  have hK : FiniteH.{u} A (kernel α) :=
    have := hΦcoh.1
    IH _ hT' hT'T (kernel α) (isCoherent_kernel α hF)
      ((hFT.of_mono (kernel.ι α)).inter (kernel_supportedIn α W hα) hT W.isOpen.isClosed_compl)
  have hΦT : Scheme.Modules.SupportedIn Φ T := by
    refine ((Scheme.Modules.SupportedIn.univ _).pushforward ψ).mono ?_
    rintro _ ⟨y', -, rfl⟩
    rw [← hST, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨c.base (π.base y'), rfl⟩
  have hC : FiniteH.{u} A (cokernel α) :=
    IH _ hT' hT'T (cokernel α) (isCoherent_cokernel α hΦcoh)
      ((hΦT.of_epi (cokernel.π α)).inter (cokernel_supportedIn α W hα) hT
        W.isOpen.isClosed_compl)
  exact FiniteH.of_shortExact₂ (kerCoimSC_shortExact α) hK
    (FiniteH.of_shortExact₁ (coimCokSC_shortExact α) hΦ hC)

theorem finiteH_of_supportedIn
    (X : Scheme.{u}) [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (T : Closeds X) :
    ∀ F : X.Modules, IsCoherent F → Scheme.Modules.SupportedIn F T → FiniteH.{u} A F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have : IsNoetherian X := ⟨⟩
  induction T using WellFoundedLT.induction with
  | _ T IH =>
    intro F hF hFT
    refine finiteH_step X T T.isClosed (fun T' hT' hlt F' hF' hF'T' => ?_) F hF hFT
    exact IH ⟨T', hT'⟩ hlt F' hF' hF'T'

end

end GroundTheory.Arith.SchemeCoh

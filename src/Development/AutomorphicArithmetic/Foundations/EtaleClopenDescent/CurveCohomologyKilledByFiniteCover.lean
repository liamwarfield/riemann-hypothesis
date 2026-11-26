module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteSurjectiveCurveCoverOfFunctionFieldE

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMayerVietorisPreimageOfRestrictionsVanish
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsCoveringPairOfIsOpenImmersionOfJointlySurjecti
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace UpperTheory.CoverSieveFree

private def coverSieve {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) (x : T ⟶ Y) : Sieve T where
  arrows V g := (∃ u : V ⟶ A, u ≫ a = g ≫ x) ∨ ∃ v : V ⟶ B, v ≫ b = g ≫ x
  downward_closed := by
    rintro V W g (⟨u, hu⟩ | ⟨v, hv⟩) h
    · exact Or.inl ⟨h ≫ u, by simp [hu]⟩
    · exact Or.inr ⟨h ≫ v, by simp [hv]⟩

private theorem coverSieve_mem {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) [IsOpenImmersion a]
    [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) (x : T ⟶ Y) :
    coverSieve a b x ∈ Scheme.etaleTopology.{0} T := by
  let Xs : Bool → Scheme.{0} := fun i => Bool.casesOn i B A
  let fs : ∀ i, Xs i ⟶ Y := fun i => Bool.casesOn (motive := fun i => Xs i ⟶ Y) i b a
  have hmem : Presieve.ofArrows Xs fs ∈ Scheme.precoverage @Etale Y := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun y => ?_, fun i => ?_⟩
    · rcases hc y with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · cases i <;> dsimp [fs] <;> infer_instance
  have hS := Precoverage.generate_mem_toGrothendieck hmem
  refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.pullback_stable x hS)
  rintro V g ⟨W, h, k, hk, e⟩
  rcases hk with ⟨i⟩
  cases i
  · exact Or.inr ⟨h, e⟩
  · exact Or.inl ⟨h, e⟩

private theorem free_hom_ext (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b)
    {G : Shv R} (φ ψ : (free R).obj (yoneda.obj Y) ⟶ G)
    (ha : (free R).map (yoneda.map a) ≫ φ = (free R).map (yoneda.map a) ≫ ψ)
    (hb : (free R).map (yoneda.map b) ≫ φ = (free R).map (yoneda.map b) ≫ ψ) : φ = ψ := by
  apply free_ext
  intro U x
  refine G.isSeparated _ (coverSieve a b x) (coverSieve_mem a b hc x) _ _ ?_
  intro V g hg
  change Sec.res g (Sec.map φ _) = Sec.res g (Sec.map ψ _)
  rw [map_res, map_res, freeGen_res]
  rcases hg with ⟨u, hu⟩ | ⟨v, hv⟩
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map a).app (op V))) u := hu.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map a) ≫ φ) _ = Sec.map ((free R).map (yoneda.map a) ≫ ψ) _
    rw [ha]
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map b).app (op V))) v := hv.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map b) ≫ φ) _ = Sec.map ((free R).map (yoneda.map b) ≫ ψ) _
    rw [hb]

end UpperTheory.CoverSieveFree

open UpperTheory.CoverSieveFree in
theorem UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective :
    ∀ (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y), IsOpenImmersion a → IsOpenImmersion b →
       (∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) → Cover2 R (sch.map a) (sch.map b) := by
  intro R _ Y A B a b ha hb hc
  have hy : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) [Mono f], Mono (sch.map f) := by
    intro Z f _
    have h1 : ∀ X, Mono ((yoneda.map f).app X) := fun X =>
      (mono_iff_injective _).2 (fun g h e => (cancel_mono f).1 (by simpa using e))
    have h2 : Mono (yoneda.map f) := NatTrans.mono_of_mono_app _
    have h3 : ∀ n, Mono ((sch.map f).app n) := fun n => h2
    exact NatTrans.mono_of_mono_app _
  refine ⟨hy a, hy b, fun n => ⟨fun {G} φ ψ h => ?_⟩⟩
  apply free_hom_ext R a b hc φ ψ
  · have e := congrArg (fun k => biprod.inl ≫ k) h
    simp only [biprod.inl_desc_assoc] at e
    exact e
  · have e := congrArg (fun k => biprod.inr ≫ k) h
    simp only [biprod.inr_desc_assoc] at e
    exact e
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.SchemePresentationCover

private theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

private theorem pb {Y : Scheme.{0}} {A B C D : Y.Opens} (hC : C = A ⊓ B) (hCA : C ≤ A) (hCB : C ≤ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    IsPullback (Y.homOfLE hCA) (Y.homOfLE hCB) (Y.homOfLE hA) (Y.homOfLE hB) := by
  subst hC
  exact isPullback_opens_inf_le hA hB

private theorem cov (R : Type) [CommRing R] {Y : Scheme.{0}} {A B D : Y.Opens} (hD : D = A ⊔ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    Cover2 R (sch.map (Y.homOfLE hA)) (sch.map (Y.homOfLE hB)) := by
  subst hD
  apply UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective
  · infer_instance
  · infer_instance
  · intro y
    have hy : (y.1 : Y) ∈ A ⊔ B := y.2
    rcases (by simpa using hy : (y.1 : Y) ∈ A ∨ (y.1 : Y) ∈ B) with h | h
    · exact Or.inl ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩
    · exact Or.inr ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩

end UpperTheory.SchemePresentationCover

private theorem sq_lemma' {T S : Scheme.{0}} (f : T ⟶ S) {P Q : S.Opens} (h : P ≤ Q) (h' : f ⁻¹ᵁ P ≤ f ⁻¹ᵁ Q) :
    T.homOfLE h' ≫ f ∣_ Q = f ∣_ P ≫ S.homOfLE h := by
  rw [← cancel_mono Q.ι]
  simp [morphismRestrict_ι]

open UpperTheory.SchemePresentationCover in
theorem UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish :
    ∀ (R : Type) [CommRing R] (F : Shv R) {S : Scheme.{0}} (U V : S.Opens) (n : ℤ)
        (x : H R (sch.obj (U ⊔ V).toScheme) F (n + 1)),
        pull R (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) F (n + 1) x = 0 →
        pull R (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V))) F (n + 1) x = 0 →
        ∃ y : H R (sch.obj (U ⊓ V).toScheme) F n,
          ∀ {T : Scheme.{0}} (f : T ⟶ S) (a : H R (sch.obj (f ⁻¹ᵁ U).toScheme) F n)
            (b : H R (sch.obj (f ⁻¹ᵁ V).toScheme) F n),
            pull R (sch.map (f ∣_ (U ⊓ V))) F n y =
              pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_left))) F n a -
                pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_right))) F n b →
            pull R (sch.map (f ∣_ (U ⊔ V))) F (n + 1) x = 0 := by
  intro R _ F S U V n x hx1 hx2
  obtain ⟨d, hd, hnat⟩ := mayerVietoris R F
  haveI := sch_pres
  have hc := cov R (rfl : U ⊔ V = U ⊔ V) le_sup_left le_sup_right
  obtain ⟨c, hc'⟩ := ((hd _ _ hc n).2.2 x).1 ⟨hx1, hx2⟩
  have P := (pb (rfl : U ⊓ V = U ⊓ V) inf_le_left inf_le_right
    (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
  intro T f a b hab
  have hD : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := by
    ext; simp
  have hC : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := by
    ext; simp
  have hcT := cov R hD (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)
  have PT := (pb hC (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
    (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)).map sch
  have hu : sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ U) ≫ sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have hv : sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ V) ≫ sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have key := hnat (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))))
    (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    (sch.map (f ∣_ (U ⊔ V))) (sch.map (f ∣_ U)) (sch.map (f ∣_ V)) hu hv hcT hc n c
  rw [← hc', key, ((hd (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V)))) hcT n).2.1)]
  refine ⟨a, b, ?_⟩
  have inj : Function.Injective (pull R PT.isoPullback.hom F n) := by
    intro z w h
    have h2 := congrArg (pull R PT.isoPullback.inv F n) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h2
  apply inj
  rw [map_sub, ← pull_comp, ← pull_comp, ← pull_comp, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd, ← hab, ← pull_comp]
  refine congrArg (fun φ => pull R φ F n c) ?_
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
      IsPullback.isoPullback_hom_snd, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteExtPullbackIntegralClosureEqZero
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.PullbackAlongInclusion

section
variable (A K L : Type) [CommRing A] [Field K] [Algebra A K] [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]

private abbrev Idx : Type := {E : IntermediateField K L // FiniteDimensional K E}

omit [Algebra A K] in
private theorem idx_directed : IsDirected (Idx K L) (· ≤ ·) :=
  ⟨fun a b => by
    haveI := a.2
    haveI := b.2
    exact ⟨⟨a.1 ⊔ b.1, inferInstance⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

private noncomputable def incl {E F : IntermediateField K L} (h : E ≤ F) :
    integralClosure A E →ₐ[A] integralClosure A F :=
  ((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure

private noncomputable def toL (E : IntermediateField K L) :
    integralClosure A E →ₐ[A] integralClosure A L :=
  (E.val.restrictScalars A).mapIntegralClosure

private noncomputable def ringD : Idx K L ⥤ CommRingCat.{0} where
  obj E := CommRingCat.of (integralClosure A E.1)
  map f := CommRingCat.ofHom (incl A K L (leOfHom f)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private noncomputable def ringC : Cocone (ringD A K L) where
  pt := CommRingCat.of (integralClosure A L)
  ι := { app := fun E => CommRingCat.ofHom (toL A K L E.1).toRingHom
         naturality := fun _ _ _ => by ext; rfl }

private theorem ringC_isColimit [Algebra.IsAlgebraic K L] : Nonempty (IsColimit (ringC A K L)) := by
  haveI := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := inferInstance
  haveI : ReflectsColimitsOfShape (Idx K L) (forget CommRingCat) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    have hx : IsIntegral K (x.1 : L) := Algebra.IsIntegral.isIntegral _
    let E : Idx K L := ⟨IntermediateField.adjoin K {x.1}, IntermediateField.adjoin.finiteDimensional hx⟩
    have hm : x.1 ∈ E.1 := IntermediateField.mem_adjoin_simple_self K x.1
    have hi : IsIntegral A (⟨x.1, hm⟩ : E.1) :=
      (isIntegral_algHom_iff (E.1.val.restrictScalars A) E.1.val.toRingHom.injective).1 x.2
    exact ⟨E, ⟨⟨x.1, hm⟩, hi⟩, rfl⟩
  · intro a b xa xb h
    haveI := a.2
    haveI := b.2
    refine ⟨⟨a.1 ⊔ b.1, inferInstance⟩, homOfLE (le_sup_left (a := a.1)),
      homOfLE (le_sup_right (b := b.1)), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : integralClosure A L => (z : L)) h

omit [Algebra A K] [IsScalarTower A K L] [Field K] [Algebra K L] in
private theorem aic [IsAlgClosed L] : AIC (integralClosure A L) := by
  intro p hp hdeg
  have hd : (p.map (algebraMap (integralClosure A L) L)).degree ≠ 0 := by
    rw [hp.degree_map]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral (integralClosure A L) a := ⟨p, hp, by rw [← Polynomial.eval_map]; exact ha⟩
  have hA : IsIntegral A a := isIntegral_trans a hint
  refine ⟨⟨a, hA⟩, ?_⟩
  have h2 : algebraMap (integralClosure A L) L (Polynomial.eval ⟨a, hA⟩ p) = 0 := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact ha
  exact Subtype.ext h2

end

private theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

private theorem pull_of_comp (q : ℕ) (m i : ℤ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (e : g.comp f = h) (x : Ht q (sp R) m i) :
    pull _ (spMap g) _ m (pull _ (spMap f) _ m x) = pull _ (spMap h) _ m x := by
  rw [← pull_comp, spMap_comp, e]

end UpperTheory.PullbackAlongInclusion

open UpperTheory.PullbackAlongInclusion in
theorem UpperTheory.exists_finite_ext_pullback_integralClosure_eq_zero :
    Hyps → ∀ (q : ℕ) [NeZero q] (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
        [IsFractionRing A K], IsUnit (q : A) → ∀ (m i : ℤ), 0 < m → ∀ x : Ht q (sp A) m i,
        ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F) (_ : IsScalarTower A K F) (_ : FiniteDimensional K F),
          pull _ (spMap (algebraMap A (integralClosure A F))) _ m x = 0 := by
  intro h q _ A K _ _ _ _ _ hq m i hm x
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hB1, -, -, -, hB5, -⟩ := h
  let L := AlgebraicClosure K
  haveI : IsDirected (Idx K L) (· ≤ ·) := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := isFiltered_of_directed_le_nonempty _
  obtain ⟨hc⟩ := ringC_isColimit A K L
  let j0 : Idx K L := ⟨⊥, inferInstance⟩
  have hqE : ∀ E : IntermediateField K L, IsUnit ((q : integralClosure A E)) := fun E => by
    simpa using hq.map (algebraMap A (integralClosure A E))
  have hqL : IsUnit ((q : integralClosure A L)) := by
    simpa using hq.map (algebraMap A (integralClosure A L))
  have e1 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1)) (toL A K L j0.1).toRingHom
    (algebraMap A (integralClosure A L)) (toL A K L j0.1).comp_algebraMap x
  haveI := hB5 q (integralClosure A L) (aic A L) hqL m i hm
  have hzero : pull _ (spMap ((ringC A K L).ι.app j0).hom) _ m
      (pull _ (spMap (algebraMap A (integralClosure A j0.1))) _ m x) = 0 :=
    e1.trans (Subsingleton.elim _ _)
  obtain ⟨k, f, hk⟩ := (hB1 q (ringD A K L) (ringC A K L) hc m i).2 j0 _ (hqE _) hzero
  refine ⟨k.1, inferInstance, inferInstance, inferInstance, inferInstance, k.2, ?_⟩
  have e2 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1))
    (incl A K L (leOfHom f)).toRingHom (algebraMap A (integralClosure A k.1))
    (incl A K L (leOfHom f)).comp_algebraMap x
  exact e2.symm.trans hk
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.curve_cohomology_killed_by_finite_cover

inductive AffU {C : Scheme.{0}} : ℕ → C.Opens → Prop
  | one (U : C.Opens) : IsAffineOpen U → Nonempty U → AffU 0 U
  | succ {k : ℕ} {W : C.Opens} (U : C.Opens) : AffU k W → IsAffineOpen U → Nonempty U → AffU (k + 1) (W ⊔ U)

theorem AffU.pre {C C' : Scheme.{0}} (γ : C' ⟶ C) [IsFinite γ] [Surjective γ] {k : ℕ} {W : C.Opens}
    (h : AffU k W) : AffU k (γ ⁻¹ᵁ W) := by
  induction h with
  | one U hU hn =>
    refine AffU.one _ (hU.preimage γ) ?_
    obtain ⟨⟨x, hx⟩⟩ := hn
    obtain ⟨y, rfl⟩ := Surjective.surj (f := γ) x
    exact ⟨⟨y, hx⟩⟩
  | @succ k W U h hU hn ih =>
    have e : γ ⁻¹ᵁ (W ⊔ U) = γ ⁻¹ᵁ W ⊔ γ ⁻¹ᵁ U := by
      ext x
      simp
    rw [e]
    refine AffU.succ _ ih (hU.preimage γ) ?_
    obtain ⟨⟨x, hx⟩⟩ := hn
    obtain ⟨y, rfl⟩ := Surjective.surj (f := γ) x
    exact ⟨⟨y, hx⟩⟩

theorem AffU.inter {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) {k : ℕ} {W V : C.Opens}
    (h : AffU k W) (hV : IsAffineOpen V) (hn : Nonempty V) : AffU k (W ⊓ V) := by
  induction h with
  | one U hU hn' =>
    refine AffU.one _ (CurveCut.CoverPf.inf_affine c hc hU hV) ?_
    obtain ⟨⟨a, ha⟩⟩ := hn'
    obtain ⟨⟨b, hb⟩⟩ := hn
    obtain ⟨x, hx⟩ := CurveCut.CoverPf.inf_nonempty c hc (U := U) (V := V) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨x, hx⟩⟩
  | @succ k W U h hU hn' ih =>
    rw [inf_sup_right]
    refine AffU.succ _ ih (CurveCut.CoverPf.inf_affine c hc hU hV) ?_
    obtain ⟨⟨a, ha⟩⟩ := hn'
    obtain ⟨⟨b, hb⟩⟩ := hn
    obtain ⟨x, hx⟩ := CurveCut.CoverPf.inf_nonempty c hc (U := U) (V := V) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨x, hx⟩⟩

theorem exists_affU {C : Scheme.{0}} [CompactSpace C] [Nonempty C] : ∃ k, AffU k (⊤ : C.Opens) := by
  classical
  let U : C → C.Opens := fun x => (C.affineCover.f (C.affineCover.idx x)).opensRange
  have hU : ∀ x, IsAffineOpen (U x) := fun x => isAffineOpen_opensRange _
  have hx : ∀ x, x ∈ U x := fun x => C.affineCover.covers x
  have hne : ∀ x, Nonempty (U x) := fun x => ⟨⟨x, hx x⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set C))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  have key : ∀ s : Finset C, s.Nonempty → ∃ k, AffU k (s.sup U) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨0, ?_⟩
      rw [Finset.sup_singleton]
      exact AffU.one _ (hU a) (hne a)
    | cons a s ha hs ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [Finset.sup_cons, sup_comm]
      exact AffU.succ _ hk (hU a) (hne a)
  obtain ⟨x0⟩ := ‹Nonempty C›
  have htne : t.Nonempty := by
    have := ht (Set.mem_univ x0)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, _⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := key t htne
  have htop : t.sup U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hy⟩ := this
    exact (Finset.le_sup (f := U) hi) hy
  exact ⟨k, htop ▸ hk⟩

theorem pl_eq_zero_of_iso (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (e : Y ⟶ X) [IsIso e] (m : ℤ)
    (x : Ht q (sch.obj X) m i) (h : pl q i e m x = 0) : x = 0 := by
  have h2 := pl_comp q i (inv e) e m x
  rw [h, map_zero, IsIso.inv_hom_id] at h2
  simpa [pl, pull_id] using h2

theorem AffU.nonempty {C : Scheme.{0}} {k : ℕ} {W : C.Opens} (h : AffU k W) : Nonempty W := by
  induction h with
  | one U _ hn => exact hn
  | @succ k W U h hU hn ih =>
    obtain ⟨⟨x, hx⟩⟩ := ih
    exact ⟨⟨x, (le_sup_left : W ≤ W ⊔ U) hx⟩⟩

theorem res_sq {T S : Scheme.{0}} (f : T ⟶ S) {A B : S.Opens} (h : A ≤ B) (h' : f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B) :
    T.homOfLE h' ≫ (f ∣_ B) = (f ∣_ A) ≫ S.homOfLE h := by
  rw [← cancel_mono B.ι]
  simp [morphismRestrict_ι]

theorem pl_res_sq (q : ℕ) (i m : ℤ) {T S : Scheme.{0}} (f : T ⟶ S) {A B : S.Opens} (h : A ≤ B) (h' : f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B)
    (x : Ht q (sch.obj B.toScheme) m i) :
    pl q i (T.homOfLE h') m (pl q i (f ∣_ B) m x) = pl q i (f ∣_ A) m (pl q i (S.homOfLE h) m x) := by
  rw [← pl_comp, ← pl_comp, res_sq f h h']

theorem killAff (hy : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω))
    {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) (U : C.Opens) (hU : IsAffineOpen U) (hn : Nonempty U)
    (m i : ℤ) (hm : 0 < m) (x : Ht q (sch.obj U.toScheme) m i) :
    ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧ pl q i (γ ∣_ U) m x = 0 := by
  haveI : IsIntegral C := hc.1
  haveI : Nonempty U := hn
  haveI := functionField_isFractionRing_of_isAffineOpen C U hU
  have hqU : IsUnit (q : Γ(C, U)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ c.appLE ⊤ U (by simp)).hom
    simpa using this
  set x0 : Ht q (sp Γ(C, U)) m i := pl q i hU.isoSpec.inv m x with hx0
  obtain ⟨F, _, _, _, hST, hFD, hF⟩ := UpperTheory.exists_finite_ext_pullback_integralClosure_eq_zero hy q Γ(C, U) C.functionField hqU m i hm x0
  obtain ⟨C', γ, hγc, hγs, hγf, hγ⟩ := UpperTheory.exists_finite_surjective_curve_cover_of_functionField_extension Ω c hc hc.1 F
  obtain ⟨e, he⟩ := hγ U hU hn inferInstance hST
  refine ⟨C', γ, hγc, hγs, hγf, ?_⟩
  have hx : x = pl q i hU.isoSpec.hom m x0 := by
    rw [hx0, ← pl_comp, Iso.hom_inv_id]
    simp [pl, pull_id]
  have h0 : pl q i (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)))) m x0 = 0 := hF
  rw [hx, ← pl_comp, he, pl_comp, h0, map_zero]

set_option maxHeartbeats 1000000 in
theorem kill (hy : Hyps) (hH0 : H0TwistOverClosedField) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω)) (k : ℕ) :
    ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ W : C.Opens, AffU k W → ∀ m i : ℤ, 0 < m →
    ∀ x : Ht q (sch.obj W.toScheme) m i,
    ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧ pl q i (γ ∣_ W) m x = 0 := by
  have pm : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens}, A ≤ B → f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B :=
    fun f _ _ h _ hy => h hy
  induction k with
  | zero =>
    intro C c hc W hW m i hm x
    cases hW with
    | one _ hU hn => exact killAff hy q Ω hq c hc _ hU hn m i hm x
  | succ k ih =>
    intro C c hc W' hW' m i hm x
    cases hW' with
    | @succ _ W U hW hU hn =>
      obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
      obtain ⟨C1, γ1, hc1, hs1, hf1, h1⟩ := ih c hc W hW (n + 1) i hm
        (pl q i (C.homOfLE (le_sup_left : W ≤ W ⊔ U)) (n + 1) x)
      haveI := hs1
      haveI := hf1
      obtain ⟨C2, γ2, hc2, hs2, hf2, h2⟩ := killAff hy q Ω hq (γ1 ≫ c) hc1 (γ1 ⁻¹ᵁ U) (hU.preimage γ1)
        (AffU.nonempty (AffU.pre γ1 (AffU.one U hU hn))) (n + 1) i hm
        (pl q i (C1.homOfLE (pm γ1 (le_sup_right : U ≤ W ⊔ U))) (n + 1) (pl q i (γ1 ∣_ (W ⊔ U)) (n + 1) x))
      haveI := hs2
      haveI := hf2
      have hcγ : IsCurve ((γ2 ≫ γ1) ≫ c) := by simpa only [Category.assoc] using hc2
      have hW2 : AffU k ((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U) := AffU.pre (γ2 ≫ γ1) (AffU.inter c hc hW hU hn)
      have hA : pl q i (C2.homOfLE (pm (γ2 ≫ γ1) (le_sup_left : W ≤ W ⊔ U))) (n + 1)
          (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 := by
        have e2 := pl_res_sq q i (n + 1) (γ2 ≫ γ1) (le_sup_left : W ≤ W ⊔ U) (pm _ le_sup_left) x
        have e3 := pl_comp q i (γ2 ∣_ (γ1 ⁻¹ᵁ W)) (γ1 ∣_ W) (n + 1)
          (pl q i (C.homOfLE (le_sup_left : W ≤ W ⊔ U)) (n + 1) x)
        rw [h1, map_zero, ← morphismRestrict_comp] at e3
        exact e2.trans e3
      have hB : pl q i (C2.homOfLE (pm (γ2 ≫ γ1) (le_sup_right : U ≤ W ⊔ U))) (n + 1)
          (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 := by
        have e1 := pl_res_sq q i (n + 1) γ2 (pm γ1 (le_sup_right : U ≤ W ⊔ U)) (pm γ2 (pm γ1 le_sup_right))
          (pl q i (γ1 ∣_ (W ⊔ U)) (n + 1) x)
        rw [h2, ← pl_comp q i (γ2 ∣_ (γ1 ⁻¹ᵁ (W ⊔ U))) (γ1 ∣_ (W ⊔ U)), ← morphismRestrict_comp] at e1
        exact e1
      obtain ⟨y, hyv⟩ := UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish (ZMod q) (tw q i) ((γ2 ≫ γ1) ⁻¹ᵁ W) ((γ2 ≫ γ1) ⁻¹ᵁ U) n
        (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) hA hB
      have fin : ∀ (C3 : Scheme.{0}) (f : C3 ⟶ C2), IsCurve (f ≫ (γ2 ≫ γ1) ≫ c) → Surjective f → IsFinite f →
          pl q i (f ∣_ ((γ2 ≫ γ1) ⁻¹ᵁ W ⊔ (γ2 ≫ γ1) ⁻¹ᵁ U)) (n + 1)
            (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 →
          ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧
            pl q i (γ ∣_ (W ⊔ U)) (n + 1) x = 0 := by
        intro C3 f hc3 hs3 hf3 h3
        haveI := hs3
        haveI := hf3
        refine ⟨C3, f ≫ γ2 ≫ γ1, by simpa only [Category.assoc] using hc3, inferInstance, inferInstance, ?_⟩
        rw [morphismRestrict_comp f (γ2 ≫ γ1) (W ⊔ U)]
        exact (pl_comp q i (f ∣_ ((γ2 ≫ γ1) ⁻¹ᵁ (W ⊔ U))) ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x).trans h3
      rcases (show (0 : ℤ) < n ∨ n = 0 by omega) with hn0 | rfl
      · obtain ⟨C3, f, hc3, hs3, hf3, h3⟩ := ih ((γ2 ≫ γ1) ≫ c) hcγ _ hW2 n i hn0 y
        refine fin C3 f (by simpa only [Category.assoc] using hc3) hs3 hf3 ?_
        exact hyv f 0 0 (by rw [map_zero, map_zero, sub_zero]; exact h3)
      · haveI : IsIntegral C2 := hc2.1
        haveI : Nonempty (((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U : C2.Opens)) := AffU.nonempty hW2
        obtain ⟨z, hz⟩ := ((hH0 hy q Ω hq i).2
          (X := ((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U : C2.Opens).toScheme)
          (Scheme.Opens.ι _ ≫ (γ2 ≫ γ1) ≫ c)).2 y
        refine fin C2 (𝟙 C2) (by rw [Category.id_comp]; exact hcγ) inferInstance inferInstance ?_
        refine hyv (𝟙 C2) (pl q i ((𝟙 C2 ⁻¹ᵁ ((γ2 ≫ γ1) ⁻¹ᵁ W)).ι ≫ (γ2 ≫ γ1) ≫ c) 0 z) 0 ?_
        rw [map_zero, sub_zero, ← hz]
        change pl q i _ 0 (pl q i _ 0 z) = pl q i _ 0 (pl q i _ 0 z)
        rw [← pl_comp, ← pl_comp, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, Category.id_comp]

end UpperTheory.curve_cohomology_killed_by_finite_cover

theorem UpperTheory.Cb.curve_cohomology_killed_by_finite_cover :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.LeafKillCut.LeafOne := by
  intro hH0 hy q _ Ω _ _ hq C c hc m i hm x
  have hI := hc.1
  have hP := hc.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨k, hk⟩ := UpperTheory.curve_cohomology_killed_by_finite_cover.exists_affU (C := C)
  obtain ⟨C', γ, h1, h2, h3, h4⟩ := UpperTheory.curve_cohomology_killed_by_finite_cover.kill hy hH0 q Ω hq k c hc ⊤ hk m i hm (pl q i (⊤ : C.Opens).ι m x)
  refine ⟨C', γ, h1, h2, ?_⟩
  rw [← pl_comp] at h4
  rw [morphismRestrict_ι, pl_comp] at h4
  have hι : ∀ V : C'.Opens, V = ⊤ → IsIso V.ι := by
    rintro _ rfl
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI := hι (γ ⁻¹ᵁ (⊤ : C.Opens)) rfl
  exact UpperTheory.curve_cohomology_killed_by_finite_cover.pl_eq_zero_of_iso q i ((γ ⁻¹ᵁ (⊤ : C.Opens)).ι) m _ h4

end

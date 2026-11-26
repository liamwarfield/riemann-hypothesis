module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFrameSpansGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFrameSpansGeneric
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem finrank_lieModel_of_algebra (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] [Algebra A K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (MV : LieModel G (spMap (algebraMap A K) ≫ x) V) : Module.finrank K V = Module.finrank A E₀ := by
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x = spMap (algebraMap A K) ≫ x := rfl
  have hsm : ∀ (a : A) (t : V), a • t = algebraMap A K a • t := fun a t => by
    rw [algebraMap_smul]
  have halg : (dualMap (algebraMap A K)).comp (algebraMap A (DualNumber A)) =
      (algebraMap K (DualNumber K)).comp (algebraMap A K) := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let b : epsAt (spMap (algebraMap A K) ≫ x) ⟶ epsAt x :=
    Over.homMk (spMap (dualMap (algebraMap A K))) (by
      change spMap (dualMap (algebraMap A K)) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap (algebraMap A K) ≫ x
      simp only [spMap]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg])
  have htan (e : E₀) : IsTanAt G (spMap (algebraMap A K) ≫ x) (b ≫ M₀.pt e) := by
    have h1 : (Over.homMk (spMap (algebraMap A K)) rfl : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) = 1 := MonObj.comp_one _
    have h2 : spMap (algebraMap A K) ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ G).left := by rw [← h1]; rfl
    have hv := M₀.tan e
    unfold IsTanAt at hv ⊢
    rw [← h2, ← hv]
    change Spec.map _ ≫ spMap (dualMap (algebraMap A K)) ≫ (M₀.pt e).left = spMap (algebraMap A K) ≫ Spec.map _ ≫ (M₀.pt e).left
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    congr 1
    exact RingHom.ext fun a => by simp [dualMap]
  have ex : ∀ e, ∃ t, MV.pt t = b ≫ M₀.pt e :=
    fun e => MV.onto _ (htan e)
  choose f hf using ex
  let j : E₀ →ₗ[A] V :=
    { toFun := f
      map_add' := fun a b => MV.inj (by rw [MV.add, hf, hf, hf, M₀.add, comp_mul])
      map_smul' := fun c e => MV.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc]
        have hb : b ≫ LieTangent.epsScale x c =
            LieTangent.epsScale (spMap (algebraMap A K) ≫ x) (algebraMap A K c) ≫ b := by
          apply Over.OverMorphism.ext
          change spMap (dualMap (algebraMap A K)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) =
            Spec.map (CommRingCat.ofHom (epsMul (algebraMap A K c))) ≫ spMap (dualMap (algebraMap A K))
          simp only [spMap]
          rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
          congr 1
          congr 1
          refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_smul]
        rw [hb, Category.assoc]) }

  have hl : ∀ e, ((MV.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A K)) ≫ (M₀.pt e).left) := fun e => by
    change (MV.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf, Category.comp_id]
    rfl
  have hbc : IsBaseChange K j := GlobalTheory.T.lie_model_isBaseChange X G A K x E₀ V M₀ MV j hl
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.lie_model_finite_projective X G A x E₀ M₀
  haveI : Module.Free A E₀ := Module.free_of_flat_of_isLocalRing
  rw [← LinearEquiv.finrank_eq hbc.equiv, Module.finrank_baseChange]

theorem finrank_lieModel_eq (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] (c : A →+* K) (y : Sp K ⟶ X) (hy : Spec.map (CommRingCat.ofHom c) ≫ x = y) (V : Type) [AddCommGroup V]
    [Module K V] (MV : LieModel G y V) : Module.finrank K V = Module.finrank A E₀ := by
  subst hy
  letI : Algebra A K := c.toAlgebra
  letI mR : Module A V := Module.compHom V c
  haveI tower : IsScalarTower A K V := ⟨fun a b t => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact finrank_lieModel_of_algebra X G A x E₀ M₀ K V MV

theorem lieModel_transport {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X} {Li : Type}
    [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) {L : Type} [Field L] {z z' : Sp L ⟶ X} (hz : z' = z)
    {T : Type} [AddCommGroup T] [Module L T] (TL : LieModel G z T) :
    ∃ MC : LieModel G z' T,
      (∀ t, (MC.pt t).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap L L))) ≫ (TL.pt t).left) ∧
      ∀ e t, M.ValAt z' e (MC.pt t) → M.ValAt z e (TL.pt t) := by
  subst hz
  have hd : dualMap (algebraMap L L) = RingHom.id _ := RingHom.ext fun a =>
    by ext <;> simp [dualMap]
  exact ⟨TL, fun t => by rw [hd, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp], fun _ _ h => h⟩

theorem lieModel_valFrame : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M L _ zL T _ _ TL h Ix _ f hξ hli hsp hlat
  have ex : ∀ i, ∃ w, M.ValAt zL (f i) (TL.pt w) := fun i => by
    have hm : f i ∈ M.lat ⟨centre zL, h⟩ := by
      rw [hlat]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := (M.exists_valAt_iff zL (f i)).2 ⟨h, hm⟩
    obtain ⟨t, rfl⟩ := TL.onto v hv.isTanAt
    exact ⟨t, hv⟩
  choose w hw using ex
  have key : ∀ (A : Set Ix) (e : Li), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) →
      ∃ u ∈ Submodule.span L (w '' A), M.ValAt zL e (TL.pt u) := by
    intro A e he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨i, hi, rfl⟩ := he
      exact ⟨w i, Submodule.subset_span ⟨i, hi, rfl⟩, hw i⟩
    | zero => exact ⟨0, zero_mem _, by rw [TL.pt_zero]; exact M.valAt_zero h⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨u', hu', hv'⟩ := hb
      exact ⟨u + u', add_mem hu hu', by rw [TL.add]; exact hv.add hv'⟩
    | smul c a _ ha =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨_, s, rfl⟩ := c
      refine ⟨(Scheme.stalkClosedPointTo zL).hom s • u, Submodule.smul_mem _ _ hu, ?_⟩
      rw [TL.pt_smul]
      exact hv.smul h s
  have hz : Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL = zL := by
    have e : CommRingCat.ofHom (algebraMap L L) = 𝟙 (CommRingCat.of L) := rfl
    rw [e, Spec.map_id, Category.id_comp]
  obtain ⟨MC, h1, h2⟩ := lieModel_transport M hz TL
  have hc : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL) :=
    (congrArg centre hz).symm ▸ h
  have hspan : ⊤ ≤ Submodule.span L (Set.range w) := by
    intro t _
    have ht : t ∈ M.fibAt M.lat zL MC :=
      (GlobalTheory.T.lie_lattice_eval_fraction_field X G Ω ξ Li M L zL L T MC hξ inferInstance h hc t).2 ⟨TL.pt t, TL.tan t, h1 t⟩
    refine (Submodule.span_le.2 ?_ : M.fibAt M.lat zL MC ≤ _) ht
    rintro w' ⟨h', e, he, hv⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' Set.univ) := by
      rw [Set.image_univ, ← hlat]
      exact he
    obtain ⟨u, hu, hv'⟩ := key _ _ he'
    have := TL.inj ((h2 _ _ hv).unique hξ hv')
    rw [this]
    rwa [Set.image_univ] at hu
  obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre zL)) (X.fromSpecStalk (centre zL))
  have c1 := finrank_lieModel_eq X G _ _ E₀ M₀ Ω (genMap ξ ⟨centre zL, h⟩) ξ (LieTangent.spec_genMap ξ ⟨centre zL, h⟩) Li M
  have c2 := finrank_lieModel_eq X G _ _ E₀ M₀ L (Scheme.stalkClosedPointTo zL).hom zL (LieTangent.spec_centre zL) T TL
  have card : Fintype.card Ix = Module.finrank L T := by
    rw [c2, ← c1, Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)]
  refine ⟨w, hw, linearIndependent_of_top_le_span_of_card_eq_finrank hspan card, top_le_iff.1 hspan, ?_⟩
  intro A e u he hv
  obtain ⟨u', hu', hv'⟩ := key A e he
  rw [TL.inj (hv.unique hξ hv')]
  exact hu'

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFrameSpansGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_frame_spans_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | exact GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlagBasisAtStalk
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlagBasisAtStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFrames

theorem mem_of_sum_mem {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {O : Type} [CommRing O] (ρ : O →+* Module.End Ω Li) {I : Type} [DecidableEq I] (σ : I → (O →+* Ω))
    (Λ : Submodule R Li) (hst : ∀ a, ∀ e ∈ Λ, ρ a e ∈ Λ) (hval : ∀ s a, σ s a ∈ R)
    (hinv : ∀ s s' a, σ s a ≠ σ s' a → (σ s a - σ s' a)⁻¹ ∈ R)
    (hsep : ∀ s s', s ≠ s' → ∃ a, σ s a ≠ σ s' a) (T : Finset I) :
    ∀ x : I → Li, (∀ t, x t ∈ eigSp ρ (σ t)) → ∑ t ∈ T, x t ∈ Λ → ∀ t ∈ T, x t ∈ Λ := by
  have hact : ∀ (t : I) (a : O) (e : Li), e ∈ eigSp ρ (σ t) → ρ a e = σ t a • e := by
    intro t a e he
    have := (Submodule.mem_iInf _).1 he a
    simpa [sub_eq_zero] using this
  have hRs : ∀ (r : Ω), r ∈ R → ∀ e ∈ Λ, r • e ∈ Λ := fun r hr e he => Λ.smul_mem ⟨r, hr⟩ he
  induction T using Finset.induction_on with
  | empty => simp
  | insert u T hu ih =>
    intro x hx hs
    rw [Finset.sum_insert hu] at hs
    have hT : ∀ t ∈ T, x t ∈ Λ := by
      intro t ht
      have hne : t ≠ u := fun h => hu (h ▸ ht)
      obtain ⟨a, ha⟩ := hsep t u hne
      have h1 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) ∈ Λ :=
        Λ.sub_mem (hst a _ hs) (hRs _ (hval u a) _ hs)
      have h2 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) =
          ∑ t ∈ T, (σ t a - σ u a) • x t := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), map_sum, hact u a _ (hx u), smul_add, Finset.smul_sum]
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hact t a _ (hx t), sub_smul]
      rw [h2] at h1
      have h3 := ih (fun t => (σ t a - σ u a) • x t)
        (fun t => (eigSp ρ (σ t)).smul_mem _ (hx t)) h1 t ht
      have h4 := hRs _ (hinv t u a ha) _ h3
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 ha), one_smul] at h4
    have hu' : x u ∈ Λ := by
      have := Λ.sub_mem hs (Λ.sum_mem hT)
      simpa using this
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hu'
    · exact hT t ht

theorem eq_span_sigma {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {O : Type} [CommRing O] (ρ : O →+* Module.End Ω Li) {I : Type} [DecidableEq I] (σ : I → (O →+* Ω))
    (Λ : Submodule R Li) (hst : ∀ a, ∀ e ∈ Λ, ρ a e ∈ Λ) (hval : ∀ s a, σ s a ∈ R)
    (hinv : ∀ s s' a, σ s a ≠ σ s' a → (σ s a - σ s' a)⁻¹ ∈ R)
    (hsep : ∀ s s', s ≠ s' → ∃ a, σ s a ≠ σ s' a)
    (hspan : ⨆ s, eigSp ρ (σ s) = ⊤) {r : I → ℕ} (b : ∀ s, Fin (r s) → Li)
    (hb : ∀ s, Λ ⊓ (eigSp ρ (σ s)).restrictScalars R = Submodule.span R (Set.range (b s))) :
    Λ = Submodule.span R (Set.range fun q : Σ s, Fin (r s) => b q.1 q.2) := by
  apply le_antisymm
  · intro e he
    have hm : e ∈ ⨆ s, eigSp ρ (σ s) := hspan ▸ Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hm
    refine Submodule.sum_mem _ fun t ht => ?_
    have h1 := mem_of_sum_mem R ρ σ Λ hst hval hinv hsep f.support f hf he t ht
    have h2 : f t ∈ Submodule.span R (Set.range (b t)) := by
      rw [← hb t]
      exact ⟨h1, hf t⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨t, k⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨s, k⟩, rfl⟩
    have : b s k ∈ Λ ⊓ (eigSp ρ (σ s)).restrictScalars R := by
      rw [hb s]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact this.1

theorem mem_span_image_of_mem_flagStep {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li]
    [Module Ω Li] {r : ℕ} (b : Fin r → Li) (hli : LinearIndependent Ω b) (i : ℕ) {e : Li}
    (h1 : e ∈ flagStep Ω b i) (h2 : e ∈ Submodule.span R (Set.range b)) :
    e ∈ Submodule.span R (b '' {k | (k : ℕ) < i}) := by
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
  have hc : l = Finsupp.equivFunOnFinite.symm (fun k => (w k : Ω)) := by
    apply hli
    rw [hle, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    exact Finset.sum_congr rfl fun k _ => rfl
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : (k : ℕ) < i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · have h0 : l k = 0 := by
      by_contra h
      exact hk (hl (Finsupp.mem_support_iff.2 h))
    have hw : w k = 0 := by
      rw [hc] at h0
      exact Subtype.ext h0
    rw [hw, zero_smul]
    exact Submodule.zero_mem _

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_natCast [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : X.presheaf.stalk p.1))) (n : ℕ) (hn : n ≠ 0) : unitAt ξ p (n : Ω) := by
  obtain ⟨u, hu⟩ := hu n hn
  have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨h0, RingHom.mem_range.2 ⟨u, h1⟩, RingHom.mem_range.2 ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩⟩
  have h2 : genMap ξ p (↑u⁻¹ : X.presheaf.stalk p.1) * (n : Ω) = 1 := by
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h2

theorem not_inFibre [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : X.presheaf.stalk p.1))) (n : ℕ) (hn : n ≠ 0) : ¬ InFibre ξ n p :=
  not_not.2 (unitAt_natCast ξ p hu n hn)

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]


open LieTangent in
theorem lat_stable (M : LieModel G ξ Li) (p : Cpt ξ) (f : G ⟶ G) [IsMonHom f] (A : Li →ₗ[Ω] Li)
    (hA : M.IsDiffOf f A) (e : Li) (he : e ∈ M.lat p) : A e ∈ M.lat p := by
  obtain ⟨v, hv⟩ := (M.mem_lat_iff p e).1 he
  refine (M.mem_lat_iff p _).2 ⟨v ≫ f, ?_⟩
  rw [LieModel.extends_iff] at hv ⊢
  refine ⟨?_, ?_⟩
  · have h := hv.1
    rw [isTanAt_iff] at h ⊢
    rw [← Category.assoc, h, one_comp]
  · rw [hA e, hv.2, Category.assoc]

end Geo


open HodgeCpt in
theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ b : ∀ s, Fin (labelRk D s) → 𝔐.Li, (∀ s (i : ℕ), flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) ∧ (∀ s (i : ℕ), ∀ e ∈ flagStep Ω (b s) i, e ∈ 𝔐.M.lat p → e ∈ Submodule.span (regAt 𝔐.ξ p) (b s '' {k | (k : ℕ) < i})) ∧ LinearIndependent Ω (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ Submodule.span Ω (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) = ⊤ ∧ 𝔐.M.lat p = Submodule.span (regAt 𝔐.ξ p) (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl p hu
  classical
  haveI : CharZero c.F := charZero_of_injective_algebraMap (algebraMap ℚ c.F).injective
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective

  have hVd : ∀ s, 𝔐.V s p = 𝔐.dR s p := fun s =>
    Lat.patch_of_not S _ _ fun n hn => not_inFibre 𝔐.ξ p hu n (𝔐.S_prime n hn).ne_zero
  choose U hU b hflag hfr using fun s => Fl.sub s p (Set.mem_univ p)
  have hF : ∀ s, (𝔐.V s).IsFrameAt (b s) p := fun s => hfr s p (Set.mem_univ p) (hU s)
  have hli : ∀ s, LinearIndependent Ω (b s) := fun s => (hF s).1
  have hst : ∀ s, 𝔐.M.lat p ⊓ (eigSp 𝔐.ρ (𝔐.emb s)).restrictScalars (regAt 𝔐.ξ p) =
      Submodule.span (regAt 𝔐.ξ p) (Set.range (b s)) := fun s => (hVd s).symm.trans (hF s).2

  have hΩ : ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
    intro s
    obtain ⟨U', hU', b', hb', hfr'⟩ := 𝔐.vb s p (Set.mem_univ p)
    have h' : 𝔐.V s p = Submodule.span (regAt 𝔐.ξ p) (Set.range b') := (hfr' p (Set.mem_univ p) hU').2
    have e1 := Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range (b s))
    have e2 := Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range b')
    rw [← e1, ← (hF s).2, h', e2]
    exact hb'

  have hlab := GlobalTheory.CompanionTheory.Ar.LabelCount.labels_injective_card E H l c Ω 𝔐.cst
  have hinj : Function.Injective 𝔐.emb := hlab.1
  have hint : DirectSum.IsInternal fun s => eigSp 𝔐.ρ (𝔐.emb s) :=
    GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hlab.2
  let v : ∀ s, Module.Basis (Fin (labelRk D s)) Ω (eigSp 𝔐.ρ (𝔐.emb s)) := fun s =>
    (Module.Basis.span (hli s)).map (LinearEquiv.ofEq _ _ (hΩ s))
  have hB : ⇑(hint.collectedBasis v) = fun q : Σ s, Fin (labelRk D s) => b q.1 q.2 := by
    rw [hint.collectedBasis_coe]
    funext q
    simp [v, Module.Basis.span_apply]

  obtain ⟨g₀, hg₀⟩ := GlobalTheory.CompanionTheory.Ar.Flat.KonstReg.exists_const_stalk E H D l Xo c Y S Ω K J y 𝔐 p hu
  have hcst : ∀ x : c.F, 𝔐.cst x ∈ regAt 𝔐.ξ p := fun x =>
    RingHom.mem_range.2 ⟨g₀ x, by rw [← hg₀]; rfl⟩
  have hval : ∀ s a, 𝔐.emb s a ∈ regAt 𝔐.ξ p := fun s a => hcst _
  have hinv : ∀ s s' a, 𝔐.emb s a ≠ 𝔐.emb s' a → (𝔐.emb s a - 𝔐.emb s' a)⁻¹ ∈ regAt 𝔐.ξ p := by
    intro s s' a _
    have : (𝔐.emb s a - 𝔐.emb s' a)⁻¹ = 𝔐.cst (labelEmb c s a - labelEmb c s' a)⁻¹ := by
      rw [map_inv₀, map_sub]; rfl
    rw [this]
    exact hcst _
  have hsep : ∀ s s', s ≠ s' → ∃ a, 𝔐.emb s a ≠ 𝔐.emb s' a := by
    intro s s' h
    by_contra hc
    push_neg at hc
    exact h (hinj (RingHom.ext hc))
  have hstab : ∀ a, ∀ e ∈ 𝔐.M.lat p, 𝔐.ρ a e ∈ 𝔐.M.lat p := fun a e he =>
    haveI := 𝔐.t.act.hom a
    lat_stable 𝔐.M p (𝔐.t.act.act a) (𝔐.ρ a) (𝔐.act a) e he
  refine ⟨b, fun s i => hflag s i, ?_, ?_, ?_, ?_, hΩ⟩
  · intro s i e he hl
    refine mem_span_image_of_mem_flagStep _ (b s) (hli s) i he ?_
    rw [← hst s]
    refine ⟨hl, ?_⟩
    have h1 : flagStep Ω (b s) i ≤ Submodule.span Ω (Set.range (b s)) :=
      Submodule.span_mono (Set.image_subset_range _ _)
    have h2 := h1 he
    rw [hΩ s] at h2
    exact h2
  · rw [← hB]
    exact (hint.collectedBasis v).linearIndependent
  · rw [← hB]
    exact (hint.collectedBasis v).span_eq
  · exact eq_span_sigma (regAt 𝔐.ξ p) 𝔐.ρ 𝔐.emb (𝔐.M.lat p) hstab hval hinv hsep
      hint.submodule_iSup_eq_top b hst

end GlobalTheory.CompanionTheory.Ar.FlagFrames
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlagBasisAtStalkStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_basis_at_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ b : ∀ s, Fin (labelRk D s) → 𝔐.Li, (∀ s (i : ℕ), flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) ∧ (∀ s (i : ℕ), ∀ e ∈ flagStep Ω (b s) i, e ∈ 𝔐.M.lat p → e ∈ Submodule.span (regAt 𝔐.ξ p) (b s '' {k | (k : ℕ) < i})) ∧ LinearIndependent Ω (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ Submodule.span Ω (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) = ⊤ ∧ 𝔐.M.lat p = Submodule.span (regAt 𝔐.ξ p) (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames | exact GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelProjectiveGenericFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelProjectiveGenericFibre
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Alg

variable {A K V T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup V] [Module A V] [AddCommGroup T] [Module K T] [Module A T] [IsScalarTower A K T]

theorem finrank_eq_of_isLocalized (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Module K T]
    [IsScalarTower A K T] (j : V →ₗ[A] T) [IsLocalizedModule (nonZeroDivisors A) j] :
    Module.finrank A V = Module.finrank K T := by
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors A) j le_rfl
  have h2 : Module.finrank K T = Module.finrank A T :=
    congrArg Cardinal.toNat (IsLocalization.rank_eq K (N := T) (nonZeroDivisors A) le_rfl)
  exact h1.symm.trans h2.symm

theorem injective_of_isLocalized [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] : Function.Injective j := by
  intro x y h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors A) j).1 h
  exact smul_right_injective V (nonZeroDivisors.ne_zero c.2) hc

def resMap (j : V →ₗ[A] T) (W : Submodule K T) : (W.restrictScalars A).comap j →ₗ[A] W where
  toFun x := ⟨j x, x.2⟩
  map_add' x y := Subtype.ext (map_add j _ _)
  map_smul' c x := Subtype.ext (map_smul j c _)

theorem isLocalized_resMap [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    IsLocalizedModule (nonZeroDivisors A) (resMap j W) := by
  constructor
  · intro a
    have hk : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have key : ∀ w : W, algebraMap A (Module.End A W) a w = algebraMap A K a • w := fun w => by
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    refine (Module.End.isUnit_iff _).2 ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A K a)⁻¹ • w, ?_⟩⟩
    · rw [key, key] at h
      exact smul_right_injective W hk h
    · rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  · intro w
    obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors A) j (w : T)
    have h' : (a : A) • (w : T) = j y := h
    have hy : j y ∈ W := by
      rw [← h', ← algebraMap_smul K (a : A) (w : T)]
      exact W.smul_mem _ w.2
    exact ⟨(⟨y, hy⟩, a), Subtype.ext h⟩
  · intro x y h
    refine ⟨1, ?_⟩
    rw [one_smul, one_smul]
    exact Subtype.ext (injective_of_isLocalized j (congrArg Subtype.val h))

theorem finrank_comap_eq [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    Module.finrank A ((W.restrictScalars A).comap j) = Module.finrank K W := by
  haveI := isLocalized_resMap j W
  exact finrank_eq_of_isLocalized K (resMap j W)

theorem exists_smul_mem (j : V →ₗ[A] T) (S : Submodule A V) (B : Set T)
    (hB : ∀ w ∈ B, ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y) {w : T} (hw : w ∈ Submodule.span K B) :
    ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hB w hw
  | zero => exact ⟨1, one_ne_zero, 0, S.zero_mem, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, hb, y', hy', e'⟩ := hv
    refine ⟨a * b, mul_ne_zero ha hb, b • y + a • y', S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hy'), ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm a b, mul_comm b a,
      mul_comm a b]
  | smul c u _ hu =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hk : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    refine ⟨d * a, mul_ne_zero hd0 ha, b • y, S.smul_mem _ hy, ?_⟩
    rw [map_smul, ← e, ← algebraMap_smul K (d * a), ← algebraMap_smul K b, ← algebraMap_smul K a, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp

end Alg

section Num

variable {L V T : Type} [Field L] [NumberField L] [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup T]
  [Module (𝓞 L) T]

theorem exists_nat_smul (j : V →ₗ[𝓞 L] T) [IsLocalizedModule (nonZeroDivisors (𝓞 L)) j] (w : T) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ y : V, (n : 𝓞 L) • w = j y := by
  obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) j w
  have ha : (a : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero a.2
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {(a : 𝓞 L)}))
  refine ⟨Ideal.absNorm (Ideal.span {(a : 𝓞 L)}), ?_, b • y, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  · have h' : (a : 𝓞 L) • w = j y := h
    rw [← hb, mul_smul, map_smul, ← h']

end Num

section Geo

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li]
  [Module Ω Li] {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
  [Module (𝓞 L) V] {T : Type} [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T]

theorem eq_pt_of_lifts {MB : LieModel G z V} {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T}
    {j : V →ₗ[𝓞 L] T} (hl : ∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) {x : V}
    {v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G} (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) :
    v = TL.pt (j x) := by
  have e : v.left ≫ 𝟙 G.left = (TL.pt (j x)).left ≫ 𝟙 G.left := h.trans (hl x).symm
  rw [Category.comp_id, Category.comp_id] at e
  exact Over.OverMorphism.ext e

theorem mem_subGens_of_nat {M : LieModel G ξ Li} {U : Submodule Ω Li} {MB : LieModel G z V}
    {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T} {j : V →ₗ[𝓞 L] T}
    (hl : ∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) {e : Li} (he : e ∈ U) {w : T}
    (hv : M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)) (n : ℕ) {y : V} (hy : (n : 𝓞 L) • w = j y) :
    y ∈ subGens M U z MB := by
  obtain ⟨h1, -⟩ := id hv
  have key := hv.smul h1 (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
  have e1 : (Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom
      (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z))) = (n : L) := map_natCast _ n
  rw [map_natCast, e1, ← TL.pt_smul] at key
  have e2 : (n : L) • w = j y := by
    rw [← hy, ← algebraMap_smul L (n : 𝓞 L) w, map_natCast]
  rw [e2] at key
  exact ⟨_, U.smul_mem _ he, _, key, hl y⟩

end Geo

theorem finrank_subFib : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  intro X G _ Ω _ ξ Li _ _ M L _ _ z V _ _ _ _ MB T _ _ _ _ TL j U _ hl hj
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L j).2 hj
  refine ⟨finrank_eq_of_isLocalized L j, ?_⟩
  set B : Set T := {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)} with hBdef
  have hinj : Function.Injective j := injective_of_isLocalized j
  have hS : ∀ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), j y ∈ Submodule.span L B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, v, hv, hlift⟩ := hy
      have hv' := eq_pt_of_lifts hl hlift
      exact Submodule.subset_span ⟨e, he, hv' ▸ hv⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← algebraMap_smul L c (j a)]
      exact Submodule.smul_mem _ _ ha
  have hB : ∀ w ∈ B, ∃ a : 𝓞 L, a ≠ 0 ∧ ∃ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), a • w = j y := by
    rintro w ⟨e, he, hv⟩
    obtain ⟨n, hn, y, hy⟩ := exists_nat_smul j w
    exact ⟨n, Nat.cast_ne_zero.2 hn, y, Submodule.subset_span (mem_subGens_of_nat hl he hv n hy), hy⟩
  have e : subFib M U z MB = ((Submodule.span L B).restrictScalars (𝓞 L)).comap j := by
    ext x
    rw [mem_subFib]
    constructor
    · rintro ⟨a, ha, hx⟩
      have h1 := hS _ hx
      rw [map_smul, ← algebraMap_smul L a (j x)] at h1
      have hk : algebraMap (𝓞 L) L a ≠ 0 := fun h0 => ha (by simpa using h0)
      exact (Submodule.smul_mem_iff (Submodule.span L B) hk).1 h1
    · intro hx
      obtain ⟨a, ha, y, hy, h⟩ := exists_smul_mem j _ B hB (K := L) hx
      refine ⟨a, ha, ?_⟩
      rwa [hinj (by rw [map_smul]; exact h : j (a • x) = j y)]
  rw [e]
  exact finrank_comap_eq j _

end GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelProjectiveGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_projective_generic_fibre : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | exact GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegree
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem flagStep_mono' {Ω E' : Type} [Field Ω] [AddCommGroup E'] [Module Ω E'] {r : ℕ} (b : Fin r → E') {i i' : ℕ} (h : i ≤ i') :
    flagStep Ω b i ≤ flagStep Ω b i' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem exists_satFlag {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L] (M : LieModel G ξ Li)
    (z : Sp (𝓞 L) ⟶ X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) {r : ℕ}
    (b : Fin r → Li) (hr : ∀ i : ℕ, i ≤ r → Module.finrank (𝓞 L) (subFib M (flagStep Ω b i) z MB) = i) :
    ∃ A : SatFlag B r, ∀ i, A.F i = subFib M (flagStep Ω b i.val) z MB :=
  ⟨{ F := fun i => subFib M (flagStep Ω b i.val) z MB
     mono := fun _ _ hi => subFib_mono M (flagStep_mono' b (Fin.le_def.1 hi)) z MB
     sat := fun _ => subFib_saturated M _ z B MB
     rank := fun i => hr i.val (Nat.lt_succ_iff.1 i.2) }, fun _ => rfl⟩

theorem rank_fib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier),
    Fintype.card (CMType H) * (D.p + D.q) = Module.finrank (𝓞 L) B.carrier ∧
    (∀ s (i : ℕ), i ≤ labelRk D s → Module.finrank (𝓞 L) (subFib 𝔐.M (flagStep Ω (Fl.b s) i) z MB) = i) ∧
    ∀ s (i : ℕ), flagStep Ω (Fl.b s) i ≤ 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl L _ _ z B MB
  classical
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hs : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  have hu := fun n hn => isUnit_natCast_stalk 𝔐.X L (spMap (algebraMap (𝓞 L) L) ≫ z) n hn
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5, hb6⟩ := GlobalTheory.T.exists_flag_basis_at_stalk E H D l Xo c Y S Ω K J y 𝔐 Fl ⟨_, hs⟩ hu
  obtain ⟨T, _, _, _, _, TL, j, hj, hbc⟩ := GlobalTheory.T.exists_lie_model_base_change 𝔐.X 𝔐.t.G (𝓞 L) L z B.carrier MB
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := GlobalTheory.T.lie_model_frame_spans_generic 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L _ T TL hs
    (Σ s, Fin (labelRk D s)) _ hgen hb3 hb4 hb5
  have hbr := fun U => GlobalTheory.T.lie_model_projective_generic_fibre 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L z B.carrier MB T TL j U hgen hj hbc
  refine ⟨?_, ?_, ?_⟩
  · rw [(hbr ⊥).1]
    have e1 := finrank_span_eq_card hw2
    rw [hw3, finrank_top] at e1
    rw [e1, Fintype.card_sigma, Fintype.sum_sum_type]
    have a1 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inl τ))) = D.p := fun _ => Fintype.card_fin _
    have a2 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inr τ))) = D.q := fun _ => Fintype.card_fin _
    simp only [a1, a2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  · intro s i hi
    rw [(hbr _).2]
    let g : Fin i → Σ s, Fin (labelRk D s) := fun k => ⟨s, ⟨k.1, lt_of_lt_of_le k.2 hi⟩⟩
    have hg : Function.Injective g := by
      intro a b' hab
      simp only [g, Sigma.mk.injEq, heq_eq_eq, true_and, Fin.mk.injEq] at hab
      exact Fin.ext hab
    have himg : (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) '' Set.range g = b s '' {k | (k : ℕ) < i} := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨k.1, lt_of_lt_of_le k.2 hi⟩, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨_, ⟨⟨k.1, hk⟩, rfl⟩, rfl⟩
    have hspan : Submodule.span L {w' | ∃ e ∈ flagStep Ω (Fl.b s) i, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w')} =
        Submodule.span L (Set.range (w ∘ g)) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w' ⟨e, he, hv⟩
        obtain ⟨h', hl⟩ := (LieModel.exists_valAt_iff 𝔐.M _ e).1 ⟨_, hv⟩
        have h2 := hb2 s i e (by rw [hb1]; exact he) hl
        rw [← himg] at h2
        have := hw4 (Set.range g) e w' h2 hv
        rwa [← Set.range_comp] at this
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        refine Submodule.subset_span ⟨b s ⟨k.1, lt_of_lt_of_le k.2 hi⟩, ?_, hw1 (g k)⟩
        rw [← hb1]
        exact Submodule.subset_span ⟨_, k.2, rfl⟩
    rw [hspan, finrank_span_eq_card (hw2.comp g hg), Fintype.card_fin]
  · intro s i
    rw [← hb1, ← hb6]
    exact Submodule.span_mono (Set.image_subset_range _ _)

theorem flag_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 _ Fl h hO L _ _ z B MB hF
  obtain ⟨h1, h2, h3⟩ := rank_fib E H D l Xo c Y S Ω K J y 𝔐 Fl L z B MB
  have ho := GlobalTheory.T.orthogonal_metric_hermitian_bundle E H D l Xo c Y S Ω K J y 𝔐 h hO L z B MB hF
  have hex : ∀ s, ∃ A : SatFlag B (labelRk D s), ∀ i, A.F i = subFib 𝔐.M (flagStep Ω (Fl.b s) i.val) z MB := by
    intro s
    exact exists_satFlag 𝔐.M z B MB (Fl.b s) (h2 s)
  choose A hA using hex
  have hW : ∀ (τ : CMType H) (i : Fin (D.p + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A (.inl τ)).F i) := by
    intro τ i
    rw [hA (.inl τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hS : ∀ (τ : CMType H) (i : Fin (D.q + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A (.inr τ)).F i) := by
    intro τ i
    rw [hA (.inr τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hpart : ∀ s, FlagPair.part (⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩ : FlagPair B (CMType H) D.p D.q) s =
      subFib 𝔐.M (flagStep Ω (Fl.b s) (labelRk D s)) z MB := by
    rintro (τ | τ)
    · exact hA (.inl τ) (Fin.last _)
    · exact hA (.inr τ) (Fin.last _)
  refine ⟨⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩, ⟨?_, h1⟩, hW, hS⟩
  intro a b hab
  rw [hpart, hpart]
  exact ho a b hab _ _ (h3 a _) (h3 b _)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_metric_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre | exact GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre <;> assumption)
end

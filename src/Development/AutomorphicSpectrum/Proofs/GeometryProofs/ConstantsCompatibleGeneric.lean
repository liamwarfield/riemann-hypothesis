module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcLie

theorem mem_eigSp_iff {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {O : Type} [CommRing O]
    (ρ : O →+* Module.End R V) (σ : O →+* R) (e : V) :
    e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_lie_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → 𝔐.ξ₀ = y₁ ≫ Y.j → 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) → 𝔐.fn.comp cst₀ = 𝔐.cst → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ (a : 𝔐.Ω₀) e, j (a • e) = 𝔐.fn a • j e) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (∀ s, LinearIndependent 𝔐.Ω₀ (b s) ∧ Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s) ∧ (∀ s, LinearIndependent Ω fun k => j (b s k)) ∧ ∀ s, Submodule.span Ω (Set.range fun k => j (b s k)) = 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J y 𝔐 y₀ cst₀ y₁ hy hy₁ hs₀ hcst
  classical
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).2 inferInstance
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀
  obtain ⟨ρ₀, hρ₀, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀ Li₀ M₀ (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  obtain ⟨j, hj, hsl, hli, -, -⟩ := GlobalTheory.T.lie_model_dominant_hodge E H Y.X Y.t 𝔐.X 𝔐.t 𝔐.f 𝔐.m 𝔐.Ω₀ Ω 𝔐.ξ₀ 𝔐.ξ 𝔐.fn Li₀ 𝔐.Li M₀ 𝔐.M
    𝔐.gen₀ 𝔐.tie.gen 𝔐.fn_over
  obtain ⟨m₀, -⟩ := GlobalTheory.CompanionTheory.Ar.exists_sabMap_id E H Y.X Y.t
  obtain ⟨hfd₀, hrk₀⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y Y.X 𝔐.Ω₀ 𝔐.ξ₀ (𝟙 _) y₁ Y.t m₀ Li₀ M₀ ρ₀ cst₀
    (by rw [Category.comp_id]; exact hy₁) (by rw [Category.id_comp]; exact hs₀) hρ₀
  obtain ⟨hfd, hrk⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y 𝔐.X Ω 𝔐.ξ 𝔐.f y₀ 𝔐.t 𝔐.m 𝔐.Li 𝔐.M 𝔐.ρ 𝔐.cst hy 𝔐.cst_over 𝔐.act
  have hρj : ∀ (a : 𝓞 E) e, j (ρ₀ a e) = 𝔐.ρ a (j e) := by
    intro a e
    apply 𝔐.M.inj
    refine Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ?_)
    · rw [hj, hρ₀ a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc,
        ← Category.assoc (𝔐.M.pt (j e)).left]
      exact congrArg (· ≫ (Y.t.act.act a).left) (hj e).symm
    · rw [Over.w, Over.w]
  have hinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun v hv => by_contra fun h0 => ?_
    exact (hli 1 (fun _ => v) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hv
  have hσ : ∀ s (a : 𝓞 E), 𝔐.fn ((cst₀.comp (labelEmb c s)) a) = 𝔐.emb s a := by
    intro s a
    show (𝔐.fn.comp cst₀) (labelEmb c s a) = 𝔐.cst (labelEmb c s a)
    rw [hcst]
  let V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀ := fun s => eigSp ρ₀ (cst₀.comp (labelEmb c s))
  have hV : ∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s := by
    intro s e
    show e ∈ eigSp ρ₀ _ ↔ j e ∈ eigSp 𝔐.ρ _
    rw [mem_eigSp_iff, mem_eigSp_iff]
    refine forall_congr' fun a => ?_
    rw [← hρj, ← hσ, ← hsl]
    exact hinj.eq_iff.symm
  let B : ∀ s, Module.Basis (Fin (labelRk D s)) 𝔐.Ω₀ (V₀ s) := fun s => Module.finBasisOfFinrankEq _ _ (hrk₀ s)
  let b : ∀ s, Fin (labelRk D s) → Li₀ := fun s k => (B s k : Li₀)
  have hbli : ∀ s, LinearIndependent 𝔐.Ω₀ (b s) := fun s =>
    (B s).linearIndependent.map' (V₀ s).subtype (Submodule.ker_subtype _)
  have hbsp : ∀ s, Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s := by
    intro s
    have h : Set.range (b s) = (V₀ s).subtype '' Set.range (B s) := by
      rw [← Set.range_comp]
      rfl
    rw [h, ← Submodule.map_span, (B s).span_eq, Submodule.map_top, Submodule.range_subtype]
  have hjli : ∀ s, LinearIndependent Ω fun k => j (b s k) := fun s => hli _ _ (hbli s)
  refine ⟨Li₀, inferInstance, inferInstance, M₀, j, V₀, b, hj, hsl, hV, fun s => ⟨hbli s, hbsp s⟩, hjli, fun s => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (hV s _).1 ((hbsp s) ▸ Submodule.subset_span ⟨k, rfl⟩)
  · rw [finrank_span_eq_card (hjli s), Fintype.card_fin]
    exact (hrk s).symm

end GlobalTheory.CompanionTheory.Ar.HcLie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constants_compatible_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → 𝔐.ξ₀ = y₁ ≫ Y.j → 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) → 𝔐.fn.comp cst₀ = 𝔐.cst → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ (a : 𝔐.Ω₀) e, j (a • e) = 𝔐.fn a • j e) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (∀ s, LinearIndependent 𝔐.Ω₀ (b s) ∧ Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s) ∧ (∀ s, LinearIndependent Ω fun k => j (b s k)) ∧ ∀ s, Submodule.span Ω (Set.range fun k => j (b s k)) = 𝔐.Vgen s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcLie.exists_lie_eig | exact GlobalTheory.CompanionTheory.Ar.HcLie.exists_lie_eig | (intros; apply GlobalTheory.CompanionTheory.Ar.HcLie.exists_lie_eig <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB


open scoped ComplexOrder in
theorem core_gram_det_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).det ≠ 0 := by
  letI : NormedAddCommGroup V := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := (Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv).det_pos
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp.ne'

theorem isTanAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {e : Li} {w : epsAt z ⟶ G} (h : M.ValAt z e w) : IsTanAt G z w := by
  obtain ⟨hz, v, ⟨hv, -⟩, hw⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo z).hom)) =
      Spec.map (Scheme.stalkClosedPointTo z) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z))).toRingHom) := by
    have a : CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo z).hom) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z)) (X.presheaf.stalk (centre z))).toRingHom ≫
          Scheme.stalkClosedPointTo z := by
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      show TrivSqZeroExt.fst (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo z).hom x) = (Scheme.stalkClosedPointTo z).hom (TrivSqZeroExt.fst x)
      simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map a).trans (Spec.map_comp _ _))
  let f : Over.mk z ⟶ Over.mk (X.fromSpecStalk (centre z)) :=
    Over.homMk (Spec.map (Scheme.stalkClosedPointTo z)) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)
  have e2 : f ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) = 1 := MonObj.comp_one f
  unfold IsTanAt at hv ⊢
  rw [hw]
  refine (Category.assoc _ _ _).symm.trans ((e1 =≫ v.left).trans ((Category.assoc _ _ _).trans ?_))
  refine (congrArg (fun k => Spec.map (Scheme.stalkClosedPointTo z) ≫ k) hv).trans ?_
  exact congrArg (fun k => k.left) e2

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB


open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB in
theorem GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (n : ℕ) (ix : Fin n → Fin r), Function.Injective ix → (gramAt h z fun l => B (ix l)).det ≠ 0 := by
  intro X Ω _ ξ K J y G _ _ _ Li _ _ M h z hz r b π B hξ hπ hreg hB n ix hix
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ z
  have htan : ∀ j, IsTanAt G z (B j) := fun j => isTanAt_of_valAt (hB j)
  choose β hβ using fun j => MR.onto (B j) (htan j)
  choose g hg using fun j => GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M ℂ z hz Vz MR (π j) hξ (hreg j)
  have hd : ∀ j l, g j (β l) = if j = l then 1 else 0 := by
    intro j l
    refine hg j (b l) (β l) _ (by rw [hβ]; exact hB l) ?_
    rw [hπ j l]
    split_ifs
    · exact val_one hz
    · exact val_zero hz
  have hli : LinearIndependent ℂ β := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := congrArg (g j) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hd] using this
  obtain ⟨core, hcore⟩ := h.herm z Vz MR
  have key := core_gram_det_ne_zero core (β ∘ ix) (hli.comp ix hix)
  have hm : (gramAt h z fun l => B (ix l)) = Matrix.of fun a b => core.inner ((β ∘ ix) a) ((β ∘ ix) b) := by
    ext a c
    simp [gramAt, hcore, hβ]
  rw [hm]
  exact key
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (n : ℕ) (ix : Fin n → Fin r), Function.Injective ix → (gramAt h z fun l => B (ix l)).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualBC
noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie
open GlobalTheory.CompanionTheory.Ar.HTChart (dual_comp snd_epsMul)

section Alg

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {L₀ : Type} [AddCommGroup L₀] [Module A L₀]

theorem clear_denom [Module.Finite A L₀] (hinj : Function.Injective (algebraMap A Ω)) (B : Subring Ω)
    (hB : ∀ b ∈ B, ∃ u a : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      algebraMap A Ω u * b = algebraMap A Ω a)
    (w : L₀ →ₗ[A] Ω) (hw : ∀ b, w b ∈ B) :
    ∃ (u : A) (w₀ : Module.Dual A L₀), algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b, algebraMap A Ω (w₀ b) = algebraMap A Ω u * w b := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L₀)
  have key : ∀ s : Finset L₀, ∃ u : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b ∈ s, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp, by simp⟩
    | insert b s _ ih =>
      obtain ⟨u, h1, h2, h3⟩ := ih
      obtain ⟨u', a, h1', h2', h3'⟩ := hB _ (hw b)
      refine ⟨u * u', by rw [map_mul]; exact mul_ne_zero h1 h1', by rw [map_mul, mul_inv]; exact mul_mem h2 h2',
        fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨u * a, by rw [map_mul, map_mul, ← h3']; ring⟩
      · obtain ⟨a', ha'⟩ := h3 c hc
        exact ⟨u' * a', by rw [map_mul, map_mul, ha']; ring⟩
  obtain ⟨u, h1, h2, h3⟩ := key s
  have hall : ∀ b, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set L₀) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc => exact h3 c hc
    | zero => exact ⟨0, by simp⟩
    | add c d _ _ hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨a', ha'⟩ := hd
      exact ⟨a + a', by rw [map_add (f := _), map_add (f := _), ha, ha', mul_add]⟩
    | smul r c _ hc =>
      obtain ⟨a, ha⟩ := hc
      exact ⟨r * a, by rw [map_mul, map_smul, ha, Algebra.smul_def]; ring⟩
  choose w₀ hw₀ using hall
  refine ⟨u, ⟨⟨w₀, fun a b => hinj ?_⟩, fun r a => hinj ?_⟩, h1, h2, hw₀⟩
  · rw [map_add (f := _), hw₀, hw₀, hw₀, map_add (f := _), mul_add]
  · show algebraMap A Ω (w₀ (r • a)) = algebraMap A Ω (r * w₀ a)
    rw [map_mul, hw₀, hw₀, map_smul, Algebra.smul_def]; ring

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] [Module A Li] [IsScalarTower A Ω Li]

theorem exists_dualBC [IsDomain A] [IsFractionRing A Ω] [Module.Finite A L₀] (j₀ : L₀ →ₗ[A] Li)
    (hj₀ : IsBaseChange Ω j₀) :
    ∃ j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li, IsBaseChange Ω j ∧
      ∀ w b, j w (j₀ b) = algebraMap A Ω (w b) := by
  have hinj := IsFractionRing.injective A Ω
  let J : Module.Dual A L₀ → Module.Dual Ω Li := fun w => hj₀.lift (Algebra.linearMap A Ω ∘ₗ w)
  have hJ : ∀ w b, J w (j₀ b) = algebraMap A Ω (w b) := fun w b => hj₀.lift_eq _ b
  have hext : ∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w' := fun w w' h => hj₀.algHom_ext _ _ h
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li) e, (a • w) e = algebraMap A Ω a * w e := fun a w e => by
    rw [← algebraMap_smul Ω a w]; rfl
  let j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li :=
    { toFun := J
      map_add' := fun w w' => hext _ _ fun b => by simp [hJ]
      map_smul' := fun a w => hext _ _ fun b => by simp [hJ, hsm] }
  refine ⟨j, (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) Ω j).1 ⟨fun s => ?_, fun w => ?_, ?_⟩, hJ⟩
  · have hs : algebraMap A Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A Ω s)⁻¹ • w, ?_⟩⟩
    · have h' : (s : A) • w = (s : A) • w' := h
      rw [← algebraMap_smul Ω, ← algebraMap_smul Ω (s : A) w'] at h'
      exact smul_right_injective _ hs h'
    · show (s : A) • ((algebraMap A Ω s)⁻¹ • w) = w
      rw [← algebraMap_smul Ω, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · obtain ⟨u, w₀, h1, -, h3⟩ := clear_denom hinj ⊤ (fun b _ => by
      obtain ⟨a, u, hu, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hu
      exact ⟨u, a, this, trivial, by field_simp⟩) ((w.restrictScalars A) ∘ₗ j₀) (fun _ => trivial)
    refine ⟨⟨w₀, ⟨u, mem_nonZeroDivisors_of_ne_zero fun h => h1 (by rw [h, map_zero])⟩⟩, hext _ _ fun b => ?_⟩
    show ((u : A) • w) (j₀ b) = J w₀ (j₀ b)
    rw [hsm, hJ, h3]; rfl
  · intro w w' h
    refine ⟨1, ?_⟩
    have : w = w' := LinearMap.ext fun b => hinj (by rw [← hJ, ← hJ]; exact LinearMap.congr_fun h _)
    rw [this]

end Alg

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {A : Type} [CommRing A] [Algebra A Ω] {x : Spec (CommRingCat.of A) ⟶ X}

theorem regAt_frac (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (p : PrimeSpectrum A) (q : Cpt ξ) (hp : x p = q.1)
    (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    (∀ u ∉ p.asIdeal, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ regAt ξ q) ∧
      ∀ b ∈ regAt ξ q, ∃ u a : A, u ∉ p.asIdeal ∧ algebraMap A Ω u * b = algebraMap A Ω a := by
  obtain ⟨_, hS, -, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hg' : ∀ a, genMap ξ q (algebraMap A _ a) = algebraMap A Ω a := RingHom.congr_fun hg
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (IsLocalization.map_units (X.presheaf.stalk q.1)
      (⟨u, hu⟩ : p.asIdeal.primeCompl)).exists_right_inv
    have h1 : algebraMap A Ω u * genMap ξ q t = 1 := by rw [← hg', ← map_mul, ht, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h1, t, (eq_inv_of_mul_eq_one_right h1)⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl c
    exact ⟨s, a, s.2, by rw [← hg', ← hg', ← h, map_mul, mul_comm]⟩

variable {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  (M : LieModel G ξ Li) {L₀ : Type} [AddCommGroup L₀] [Module A L₀] (M₀ : LieModel G x L₀)

omit [IsCommMonObj G] in
theorem exists_lieBC (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) [Module A Li]
    [IsScalarTower A Ω Li] : ∃ j₀ : L₀ →ₗ[A] Li, IsBaseChange Ω j₀ ∧ ∀ v, (M.pt (j₀ v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left := by
  subst hx
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G A Ω (algebraMap A Ω) x L₀ Li M₀ M
  have hj' : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left :=
    fun v => (Category.comp_id _).symm.trans (hj v)
  let j₀ : L₀ →ₗ[A] Li :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a v => by rw [j.map_smulₛₗ, algebraMap_smul]; rfl }
  exact ⟨j₀, (lie_proj X G A x L₀ M₀).2.2 Ω Li M j₀ hj', hj'⟩

omit [IsCommMonObj G] [Smooth G.hom] in
theorem tan_ext {O : Type} [CommRing O] [Algebra A O] {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (b : L₀) : ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧
      (M.pt (j₀ b)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left := by
  let ψ := LieCarrier.epsHom (algebraMap A O) x _ hzs
  have hleft : (ψ ≫ M₀.pt b).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A O))) ≫ (M₀.pt b).left := rfl
  refine ⟨ψ ≫ M₀.pt b, ?_, ?_⟩
  · have t : _ ≫ (M₀.pt b).left = _ := M₀.tan b
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt b).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp only [Over.mk_hom]
    rw [← Category.assoc, hzs]
  · rw [hleft, hj, ← Category.assoc, ← spec_comp, dual_comp, hg]

theorem tan_denom {O : Type} [CommRing O] [Algebra A O] (S : Submonoid A) [IsLocalization S O]
    {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (e : Li) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he' : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ u ∈ S, ∃ b, algebraMap A Ω u • e = j₀ b := by
  obtain ⟨u, hu, b, hub⟩ := exists_denom lie_proj G S x M₀ hzs v hv
  have hgu : g (algebraMap A O u) = algebraMap A Ω u := RingHom.congr_fun hg u
  refine ⟨u, hu, b, hgu ▸ M.inj (Over.OverMorphism.ext ?_)⟩
  rw [M.smul, he', hj, ← hg, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc,
    ← spec_comp, ← spec_comp, dual_eps]

theorem mem_omLat_iff (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) (w : Module.Dual Ω Li) :
    w ∈ M.omLat q ↔ ∀ b, w (j₀ b) ∈ regAt ξ q := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum A, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hlat := (lieLat_carrier X G Ω ξ Li M q).1
  refine ⟨fun h b => h _ ((hlat _).2 ?_), fun h e he => ?_⟩
  · exact tan_ext M M₀ hzs (genMap ξ q) hg j₀ hj b
  · obtain ⟨v, hv, he'⟩ := (hlat e).1 he
    obtain ⟨u, hu, b, hje⟩ := tan_denom M M₀ p.asIdeal.primeCompl hzs (genMap ξ q) hg j₀ hj e v hv he'
    obtain ⟨h1, h2⟩ := (regAt_frac hξ hk hx p q hp hsub).1 u hu
    have : w e = (algebraMap A Ω u)⁻¹ * w (j₀ b) := by
      rw [← hje, map_smul, smul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (h b)

end Geo

end GlobalTheory.CompanionTheory.HtLink
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeModel

section Normal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_div_of_tie {κ : Type} {x : κ → Ω} (ht : CoordTie ℤ ξ x) {c : κ} {q : Cpt ξ} (hc : InChart ξ x c q)
    (a : Ω) : ∃ u ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ v ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), v ≠ 0 ∧ a = u / v := by
  have hg : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc.1, fun c' => (RegAtMono.regAt_mono X Ω ξ q (TieArith.genCpt ξ) q.2).1 (hc.2 c')⟩
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ ht c (TieArith.genCpt ξ) hg a).1
    (TieArith.mem_regAt_genCpt ξ ht.gen a)
  exact ⟨s * a, hsa, s, hs, hu.1, by field_simp [hu.1]⟩

variable [CharZero Ω]

theorem exists_trdeg_eq {κ : Type} [Finite κ] {x : κ → Ω} (ht : CoordTie ℤ ξ x) :
    ∃ d : ℕ, Algebra.trdeg ℤ Ω = d := by
  obtain ⟨c, hc⟩ := ht.cover (TieArith.genCpt ξ)
  set s : Set Ω := Set.range fun j => x j / x c with hs
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℤ s) Ω := by
    refine ⟨fun a => ?_⟩
    obtain ⟨u, hu, v, hv, hv0, rfl⟩ := exists_div_of_tie ht hc a
    have h1 : IsAlgebraic (Algebra.adjoin ℤ s) u := isAlgebraic_algebraMap (⟨u, hu⟩ : Algebra.adjoin ℤ s)
    have h2 : IsAlgebraic (Algebra.adjoin ℤ s) v := isAlgebraic_algebraMap (⟨v, hv⟩ : Algebra.adjoin ℤ s)
    rw [div_eq_mul_inv]
    exact h1.mul h2.inv
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := ℤ) s
  have hfin : t.Finite := (Set.finite_range _).subset hts
  haveI := hfin.to_subtype
  haveI := Fintype.ofFinite t
  exact ⟨Fintype.card t, by rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype]⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem mem_regAt_of_isIntegral (ht : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hs : SmoothGenericFibreM y) (q : Cpt ξ) (hq : q ∈ genFib ξ) (a : Ω)
    (ha : IsIntegral (regAt ξ q) a) : a ∈ regAt ξ q := by
  classical
  obtain ⟨c, hc⟩ := ht.cover q
  have hne : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc.1) k (Finset.mem_univ k)
  set A : Subalgebra ℚ Ω := Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) with hA
  haveI : Algebra.Smooth ℚ A := hs c hne
  let R : Subalgebra ℚ Ω :=
    { (regAt ξ q) with
      algebraMap_mem' := fun r => by
        have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : ℕ) : Ω)⁻¹ := by
          rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
        rw [e]
        exact mul_mem (intCast_mem _ _) (hq r.den r.den_pos).2.2 }
  have hAR : ∀ b ∈ A, b ∈ regAt ξ q := by
    have : A ≤ R := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨⟨k, j⟩, rfl⟩
      exact Lat.block_ratio_mem hc k j
    exact fun b hb => this hb
  have hBA : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩), b ∈ A := by
    intro b hb
    have : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ A.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ A
      rw [← Finset.prod_div_distrib]
      exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    exact this hb
  have hfr : ∀ r ∈ regAt ξ q, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ regAt ξ q ∧ r = u / v := by
    intro r hr
    obtain ⟨s, hsB, hsu, hsr⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ ht c q hc r).1 hr
    refine ⟨s * r, hBA _ hsr, s, hBA _ hsB, hsu.1, hsu.2.2, ?_⟩
    field_simp [hsu.1]
  obtain ⟨v, hvA, hv0, hvR, hint⟩ :=
    GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral A (regAt ξ q) hAR hfr a ha
  haveI : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z => by
    obtain ⟨u, hu, w, hw, -, rfl⟩ := exists_div_of_tie ht hc z
    exact ⟨⟨u, hBA u hu⟩, ⟨w, hBA w hw⟩, rfl⟩
  haveI : IsIntegrallyClosed A := by
    have h1 : IsIntegrallyClosed (A ⧸ (⊥ : Ideal A)) :=
      GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth ℚ A ⊥ (by
        rw [IsDomain.minimalPrimes_eq_singleton_bot]; rfl)
    exact IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot A)
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have e : a = b * v⁻¹ := by
    have : (b : Ω) = v * a := hb
    rw [this]; field_simp [hv0]
  rw [e]
  exact mul_mem (hAR _ b.2) hvR

end Normal

section Blocks

variable {K : Type} {κ : Type} (J : K → Type)

def joinEquiv : ((k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k) ≃ ((k : K) → J k) × κ where
  toFun c := (fun k => c (.inl k), c (.inr ()))
  invFun t := fun k => match k with
    | .inl k => t.1 k
    | .inr () => t.2
  left_inv c := by funext k; rcases k with k | _ <;> rfl
  right_inv t := rfl

variable {J} [Fintype K] {Ω : Type} [Field Ω]

theorem segre_joinVec (x : (Σ k, J k) → Ω) (v : (Σ _ : Unit, κ) → Ω)
    (c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k) :
    ∏ k, Cmp.joinVec x v ⟨k, c k⟩ = (∏ k, x ⟨k, (joinEquiv J c).1 k⟩) * v ⟨(), (joinEquiv J c).2⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rfl

theorem tie_joinVec {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type} [CommRing o] [Algebra o Ω]
    (x : (Σ k, J k) → Ω) (v : (Σ _ : Unit, κ) → Ω)
    (h : CoordTie o ξ (fun q : ((k : K) → J k) × κ => (∏ k, x ⟨k, q.1 k⟩) * v ⟨(), q.2⟩)) :
    CoordTie o ξ (fun c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k => ∏ k, Cmp.joinVec x v ⟨k, c k⟩) := by
  have e : (fun c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k => ∏ k, Cmp.joinVec x v ⟨k, c k⟩) =
      fun c => (fun q : ((k : K) → J k) × κ => (∏ k, x ⟨k, q.1 k⟩) * v ⟨(), q.2⟩) (joinEquiv J c) :=
    funext fun c => segre_joinVec x v c
  rw [e]
  exact ExtraBlocks.coordTie_equiv (joinEquiv J) h

end Blocks

end GlobalTheory.CompanionTheory.Ar.ChangeModel

namespace GlobalTheory.CompanionTheory.Ar.ChangeModel

theorem dominates_comp {X₁ X₂ X₃ : Scheme.{0}} {Ω₁ Ω₂ Ω₃ : Type} [Field Ω₁] [Field Ω₂] [Field Ω₃]
    {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂} {ξ₃ : Spec (CommRingCat.of Ω₃) ⟶ X₃}
    {f : X₂ ⟶ X₁} {g : X₃ ⟶ X₂} {i : Ω₁ →+* Ω₂} {j : Ω₂ →+* Ω₃}
    (hf : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ f i) (hg : GlobalTheory.CompanionTheory.Ar.Dominates ξ₃ ξ₂ g j) :
    GlobalTheory.CompanionTheory.Ar.Dominates ξ₃ ξ₁ (g ≫ f) (j.comp i) := by
  unfold GlobalTheory.CompanionTheory.Ar.Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem closure_eq_top_of_basis {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    ∃ (n : ℕ) (w : Option (Fin n) → Ω), w none ≠ 0 ∧
      Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ := by
  letI := i.toAlgebra
  haveI := hfin
  let b := Module.finBasis Ω₁ Ω
  refine ⟨_, fun l => l.elim 1 b, one_ne_zero, ?_⟩
  rw [eq_top_iff]
  intro a _
  rw [← b.sum_repr a]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  refine mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨some j, none, ?_⟩))
  simp

theorem exists_normal_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] [CharZero Ω] (i : Ω₁ →+* Ω) (y : (Σ k, J k) → Ω₁) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (M : PModel ℤ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩)) (h : M.X ⟶ X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ h i ∧ Flat.NormalCpt M.ξ ∧ SmoothGenericFibreM y' := by
  intro hRes K _ J _ Ω₁ Ω _ _ _ i y X ξ hfin hall htie
  classical

  let M₀ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) :=
    { X := X, ξ := ξ, s := specZIsTerminal.from X, hover := specZIsTerminal.hom_ext _ _, all := hall, tie := htie }

  obtain ⟨n, w, hw0, hclo⟩ := closure_eq_top_of_basis i hfin
  obtain ⟨M₁, f₁, hf₁⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω₁ _ _ M₀ Ω i (Option (Fin n)) w (fun a => by simp) ⟨none, hw0⟩ hclo
  let y₁ : (Σ k, Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k) → Ω :=
    Cmp.joinVec (fun p => i (y p)) (fun p : Σ _ : Unit, Option (Fin n) => w p.2)
  have ht₁ : CoordTie ℤ M₁.ξ (fun c' : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k =>
      ∏ k, y₁ ⟨k, c' k⟩) := by
    refine tie_joinVec _ _ ?_
    have e : (fun q : ((k : K) → J k) × Option (Fin n) => (∏ k, i (y ⟨k, q.1 k⟩)) * w q.2) =
        joinCo i (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) w := by
      funext q
      simp [joinCo, map_prod]
    show CoordTie ℤ M₁.ξ (fun q : ((k : K) → J k) × Option (Fin n) => (∏ k, i (y ⟨k, q.1 k⟩)) * w q.2)
    rw [e]
    exact M₁.tie

  obtain ⟨d, hd⟩ := exists_trdeg_eq ht₁
  obtain ⟨-, hAr⟩ := GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar M₁.X Ω M₁.ξ (K ⊕ Unit) _ y₁ d ht₁ hd
  obtain ⟨m, y₂, Jb, ⟨l₀, hl₀⟩, -, -, -, hsnc, -⟩ := SncRes.exists_snc_model hRes (K ⊕ Unit) _ Ω y₁ d 1 0 hAr
    (by intro a ha k; simp [MvPolynomial.support_one] at ha; simp [ha])
    (by
      intro h
      have : mConeMap y₁ 1 = 0 := h
      simp at this)

  let M₁' : PModel ℤ (fun c' : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k => ∏ k, y₁ ⟨k, c' k⟩) :=
    { X := M₁.X, ξ := M₁.ξ, s := M₁.s, hover := M₁.hover, all := M₁.all, tie := ht₁ }
  have hclo₂ : Subfield.closure (Set.range (RingHom.id Ω) ∪ {a | ∃ l l', a = y₂ ⟨(), l⟩ / y₂ ⟨(), l'⟩}) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  obtain ⟨M₂, f₂, hf₂⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω _ _ M₁' Ω (RingHom.id Ω) (Fin m) (fun l => y₂ ⟨(), l⟩)
    (fun a => rfl) ⟨l₀, hl₀⟩ hclo₂
  let z := Cmp.joinVec y₁ y₂
  have ht₂ : CoordTie ℤ M₂.ξ (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k =>
      ∏ k, z ⟨k, c' k⟩) := tie_joinVec _ _ M₂.tie
  have hsm : SmoothGenericFibreM z := GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel _ _ Ω z d Jb hsnc
  let M₂' : PModel ℤ (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k => ∏ k, z ⟨k, c' k⟩) :=
    { X := M₂.X, ξ := M₂.ξ, s := M₂.s, hover := M₂.hover, all := M₂.all, tie := ht₂ }

  obtain ⟨κ₃, _, y₃, M₃, f₃, hf₃, hN, -, hNorm⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω _ _ M₂' Ω
  have hf₃' : GlobalTheory.CompanionTheory.Ar.Dominates M₃.ξ M₂.ξ f₃ (RingHom.id Ω) := hf₃
  have hchart : ∀ p : Cpt M₃.ξ, ∃ c₀, InChart M₃.ξ
      (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k => ∏ k, z ⟨k, c' k⟩) c₀ p := by
    intro p
    obtain ⟨h, hreg, -⟩ := RegAtDom.regAt_dominates M₂.X Ω M₂.ξ M₃.X Ω M₃.ξ f₃ _ hf₃' p
    obtain ⟨c, hc⟩ := ht₂.cover ⟨f₃ p.1, h⟩
    exact ⟨c, hc.1, fun c' => hreg _ (hc.2 c')⟩

  obtain ⟨K', _, J', _, y', bk, bx, -, hinj, heq, ht', -⟩ := ExtraBlocks.exists_blocks_of_lines ℤ Ω _ y₃ M₃ _ _ z Empty
    (fun a => a.elim) hchart (fun a => a.elim)
  have hsm' : SmoothGenericFibreM y' :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω _ _ z K' J' y' M₂.X M₃.X M₂.ξ M₃.ξ f₃ M₂.all M₃.all ht₂ ht' hf₃' hsm fun q hq =>
      GlobalTheory.T.normal_iso_of_integrally_closed M₂.X Ω M₂.ξ M₃.X M₃.ξ f₃ q (hNorm q) (mem_regAt_of_isIntegral ht₂ hsm q hq)
  refine ⟨K', inferInstance, J', inferInstance, y', fun k => bk (.inl (.inl k)), fun k => bx (.inl (.inl k)),
    { X := M₃.X, ξ := M₃.ξ, s := M₃.s, hover := M₃.hover, all := M₃.all, tie := ht' },
    f₃ ≫ f₂ ≫ f₁, fun a b e => ?_, fun k a => heq (.inl (.inl k)) a, ?_, hN, hsm'⟩
  · simpa using hinj e
  · have h1 := dominates_comp (dominates_comp hf₁ hf₂) hf₃'
    exact h1

end GlobalTheory.CompanionTheory.Ar.ChangeModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_after_finite_extension : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] [CharZero Ω] (i : Ω₁ →+* Ω) (y : (Σ k, J k) → Ω₁) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (M : PModel ℤ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩)) (h : M.X ⟶ X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ h i ∧ Flat.NormalCpt M.ξ ∧ SmoothGenericFibreM y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model | exact GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProjectiveCoordModel
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProjectiveCoordModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem mem_of_isIntegral_of_isLocAt {Ω : Type} [Field Ω] [CharZero Ω] (R : Subring Ω) [IsFractionRing R Ω]
    (A : Subalgebra ℚ Ω) (hs : Algebra.Smooth ℚ A) (q : Ideal A) (hq : q.IsPrime) (h : IsLocAt A q R)
    (a : Ω) (ha : IsIntegral R a) : a ∈ R := by
  have hAR : ∀ b : A, (b : Ω) ∈ R := fun b =>
    (h b).2 ⟨1, fun h1 => hq.ne_top ((Ideal.eq_top_iff_one q).2 h1), by simp⟩
  letI : Algebra A R := (RingHom.codRestrict A.val.toRingHom R hAR).toAlgebra
  have hmap : ∀ b : A, ((algebraMap A R b : R) : Ω) = b := fun _ => rfl
  have hne : ∀ s : A, s ∉ q → (s : Ω) ≠ 0 := fun s hs0 h0 =>
    hs0 (by rw [show s = 0 from Subtype.ext h0]; exact q.zero_mem)
  haveI : IsLocalization.AtPrime R q :=
    { map_units := by
        rintro ⟨s, hs0⟩
        have hs1 : s ∉ q := hs0
        refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, (h _).2 ⟨s, hs1, ?_⟩⟩ : R) (Subtype.ext ?_)
        · rw [mul_inv_cancel₀ (hne s hs1)]; exact A.one_mem
        · simp [hmap, mul_inv_cancel₀ (hne s hs1)]
      surj := by
        rintro ⟨r, hr⟩
        obtain ⟨s, hs1, hsr⟩ := (h r).1 hr
        exact ⟨⟨⟨_, hsr⟩, ⟨s, hs1⟩⟩, Subtype.ext (by simp [hmap, mul_comm])⟩
      exists_of_eq := by
        intro x y hxy
        exact ⟨1, by
          have : (x : Ω) = y := by simpa [hmap] using congrArg (Subtype.val) hxy
          rw [Subtype.ext this]⟩ }
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  obtain ⟨r, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := Ω)).1 ha
  exact r.2

end GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ X ξ N x e Ab hall htie hsnc
  let M0 : PModel ℤ x :=
    { X := X, ξ := ξ, s := specZIsTerminal.from X, hover := specZIsTerminal.hom_ext _ _, all := hall, tie := htie }
  obtain ⟨κ', _, y, M', f, hdom, hnorm, -, hat⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω (Fin (N + 1)) x M0 Ω
  have hdom' : GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ ξ f (RingHom.id Ω) := hdom
  have hiso : ∀ q ∈ genFib ξ, IsoAt M'.ξ f (RingHom.id Ω) q := by
    intro q hq
    have hc : Char0 ξ q := fun r hr hf => hf (hq r hr.pos)
    obtain ⟨A, z, n, P, hp, hP, hloc⟩ := hsnc q hc
    haveI := (GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ htie.gen q).1
    exact GlobalTheory.T.normal_iso_of_integrally_closed X Ω ξ M'.X M'.ξ f q (hat q)
      (fun a ha => mem_of_isIntegral_of_isLocAt _ A hp.smooth P hP hloc a ha)
  obtain ⟨N', x', hx'⟩ := GlobalTheory.T.coord_over_int_of_finite_order M'.X Ω M'.ξ ℤ κ' y M'.tie
  have hone := GlobalTheory.T.coords_single_block_segre M'.X Ω M'.ξ N' x' hx'
  have hsnc' := GlobalTheory.T.snc_points_transfer_dominating Ω (Fin (N + 1)) _ x _ X M'.X ξ M'.ξ f e Ab hall M'.all htie hone hdom' hiso hsnc
  exact ⟨Unit, inferInstance, fun _ => Fin (N' + 1), fun _ => inferInstance, fun p => x' p.2,
    { X := M'.X, ξ := M'.ξ, s := M'.s, hover := M'.hover, all := M'.all, tie := hone }, f,
    inferInstance, hdom', hnorm, hsnc'⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProjectiveCoordModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_coord_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model | exact GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model <;> assumption)
end
end

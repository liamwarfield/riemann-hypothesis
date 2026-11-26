module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsBasisTangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTangentModuleAbelianSchemeOfRelDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTangentModuleAbelianSchemeOfRelDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBasisDim


open ReciprocityTheory.ChartRestriction.G.PullbackSections in
theorem basis_tanM_of_dim {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (d : ℕ) (hG : SmoothOfRelativeDimension d G.hom) :
    Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  have hS := isGrpPullback_pullback G (𝟙 (Sp R))
  have hsm : SmoothOfRelativeDimension d ((Over.pullback (𝟙 (Sp R))).obj G).hom := by
    show SmoothOfRelativeDimension d (pullback.snd _ _)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis ((Over.pullback (𝟙 (Sp R))).obj G) hsm
  let b : Fin d → TanM (𝟙 (Sp R)) G := fun i =>
    mkT (pushHom hS (epsR R) (v i)) ((isTangent_iff hS _).1 (hv.1 i))
  have hb : ∀ m : TanM (𝟙 (Sp R)) G, ∃! a : Fin d → R, m = ∑ i, a i • b i := fun m => by
    obtain ⟨w', hw'⟩ := push_surj hS (tv m)
    have htan : IsTangent w' := (isTangent_iff hS w').2 (by rw [hw']; exact tv_mem m)
    have key : ∀ a : Fin d → R, IsLieComb a v w' ↔ m = ∑ i, a i • b i := by
      intro a
      rw [isLieComb_iff hS, hw']
      constructor
      · intro h
        apply tanM_ext
        rw [h, GlobalTheory.RayBasis.tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
      · intro h
        rw [h, GlobalTheory.RayBasis.tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
    obtain ⟨C, hC, hCu⟩ := hv.2 w' htan
    exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩
  refine ⟨Module.Basis.mk (v := b) ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun ((hb 0).unique hg.symm (y₂ := 0) (by simp)) i
  · intro m _
    obtain ⟨a, ha, -⟩ := hb m
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem basis_tanM_abelian : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (d : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension d G.hom → Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  intro R _ _ _ G _ _ d _ hG
  exact basis_tanM_of_dim G d hG

end GlobalTheory.TanBasisDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTangentModuleAbelianSchemeOfRelDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_tangentModule_abelianScheme_of_relDim : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (d : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension d G.hom → Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  first | exact @GlobalTheory.TanBasisDim.basis_tanM_abelian | exact GlobalTheory.TanBasisDim.basis_tanM_abelian | (intros; apply GlobalTheory.TanBasisDim.basis_tanM_abelian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubfamilyUniqueReprOfSpanningLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubfamilyUniqueReprOfSpanningLocalRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_subfamily_unique_repr_of_spanning_localRing
    (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M] (d g : ℕ) :
    Nonempty (Module.Basis (Fin d) R M) → ∀ w : Fin g → M,
      (∀ u : M, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) →
      ∃ e : Fin d → Fin g, ∀ u : M, ∃! cf : Fin d → R, u = ∑ a, cf a • w (e a) := by
  rintro ⟨b⟩ w hw
  haveI : Module.Finite R M := Module.Finite.of_basis b
  let V := IsLocalRing.ResidueField R ⊗[R] M
  let v : Fin g → V := fun a => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] w a
  have hsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c m =>
      obtain ⟨cf, rfl⟩ := hw m
      have : c ⊗ₜ[R] (∑ a, cf a • w a) = c • ∑ a, cf a • v a := by
        simp only [v, TensorProduct.tmul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          TensorProduct.smul_tmul', smul_comm c (cf a) (1 : IsLocalRing.ResidueField R),
          smul_eq_mul, _root_.mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  obtain ⟨κ, a, ha, hspa, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField R) v
  let bk : Module.Basis κ (IsLocalRing.ResidueField R) V :=
    Module.Basis.mk hli (by rw [hspa, hsp])
  let bV : Module.Basis (Fin d) (IsLocalRing.ResidueField R) V :=
    Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b
  let eq : Fin d ≃ κ := bV.indexEquiv bk
  refine ⟨a ∘ eq, ?_⟩
  have hspR : Submodule.span R (Set.range (w ∘ a ∘ eq)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (w ∘ a ∘ eq) (bk.reindex eq.symm) (fun i => by
      simp [bk, v])
  let f : (Fin d → R) →ₗ[R] M := Fintype.linearCombination R (w ∘ a ∘ eq)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspR
  have hfi : Function.Injective f :=
    OrzechProperty.injective_of_surjective_of_injective b.equivFun.symm.toLinearMap f
      b.equivFun.symm.injective hf
  intro u
  obtain ⟨cf, hcf⟩ := hf u
  refine ⟨cf, ?_, ?_⟩
  · rw [← hcf]; simp [f, Fintype.linearCombination_apply]
  · intro cf' hcf'
    apply hfi
    rw [hcf]; simp [f, Fintype.linearCombination_apply, hcf']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubfamilyUniqueReprOfSpanningLocalRingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subfamily_unique_repr_of_spanning_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M] (d g : ℕ), Nonempty (Module.Basis (Fin d) R M) → ∀ w : Fin g → M, (∀ u : M, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∃ e : Fin d → Fin g, ∀ u : M, ∃! cf : Fin d → R, u = ∑ a, cf a • w (e a) := by
  first | exact @GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing | exact GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing | (intros; apply GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechOneCocycleOnAffineCoverMixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechOneCocycleOnAffineCoverMixed
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

namespace GlobalTheory.CechMixed
open GlobalTheory.KS

theorem coc_on {X : Scheme.{0}} {J : Type} {V : J → X.Opens} {z : C1 V} (hz : IsCoc V z) (i j l : J)
    {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hl : W ≤ V l) :
    rsT (z i j) W + rsT (z j l) W = rsT (z i l) W := by
  have e : W ≤ V i ⊓ V j ⊓ V l := le_inf (le_inf hi hj) hl
  have h := congrArg (fun s => rsT s W) (hz i j l)
  simp only [rsT_add] at h
  rwa [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e] at h

theorem le_iSup_inf {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) (O : X.Opens) :
    O ≤ ⨆ i, V i ⊓ O := by
  rw [← iSup_inf_eq, hV, top_inf_eq]

theorem exists_split {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) {O : X.Opens}
    (hO : IsAffineOpen O) {z : C1 V} (hz : IsCoc V z) :
    ∃ b : ∀ i, Γ(X, V i ⊓ O), ∀ i i' (W : X.Opens), W ≤ V i → W ≤ V i' → W ≤ O →
      rsT (z i i') W = rsT (b i) W - rsT (b i') W := by
  have hs : ⨆ i, V i ⊓ O = O := by rw [← iSup_inf_eq, hV, top_inf_eq]
  have hle : ∀ i j, V i ⊓ O ⊓ (V j ⊓ O) ≤ V i ⊓ V j := fun i j => inf_le_inf inf_le_left inf_le_left
  obtain ⟨y, hy⟩ := isCob_of_isAffineOpen X J (fun i => V i ⊓ O)
    (fun i j => rsT (z i j) (V i ⊓ O ⊓ (V j ⊓ O))) (hs.symm ▸ hO) (by
      intro i j l
      dsimp only
      rw [rsT_rsT (hle i j) inf_le_left,
        rsT_rsT (hle j l) (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
        rsT_rsT (hle i l) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
      exact coc_on hz i j l ((inf_le_left.trans inf_le_left).trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans inf_le_left) (inf_le_right.trans inf_le_left))
  refine ⟨fun i => - y i, fun i i' W h h' hW => ?_⟩
  have e : W ≤ V i ⊓ O ⊓ (V i' ⊓ O) := le_inf (le_inf h hW) (le_inf h' hW)
  have k := congrArg (fun s => rsT s W) (hy i i')
  simp only [rsT_sub] at k
  rw [rsT_rsT (hle i i') e, rsT_rsT inf_le_right e, rsT_rsT inf_le_left e] at k
  simp only [rsT_neg]
  rw [k]; ring

theorem exists_cocycle_on_affine : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ i, V i = ⊤ → (∀ k, IsAffineOpen (U k)) → ∀ z : C1 V, IsCoc V z → ∃ (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), IsCoc U z' ∧ (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) ∧ ∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k') := by
  intro X J K V U hV hU z hz
  choose b hb using fun k => exists_split hV (hU k) hz
  have glue : ∀ k k', ∃ t : Γ(X, U k ⊓ U k'), ∀ i, rsT t (V i ⊓ (U k ⊓ U k')) =
      rsT (b k' i) (V i ⊓ (U k ⊓ U k')) - rsT (b k i) (V i ⊓ (U k ⊓ U k')) := by
    intro k k'
    refine exists_rsT_eq (fun i => V i ⊓ (U k ⊓ U k')) (fun i => inf_le_right)
      (le_iSup_inf hV _) _ fun i j => ?_
    simp only [rsT_sub]
    rw [rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_right,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_right]
    have hi : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V i := inf_le_left.trans inf_le_left
    have hj : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V j := inf_le_right.trans inf_le_left
    have hk : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ U k ⊓ U k' := inf_le_right.trans inf_le_right
    have h1 := hb k i j _ hi hj (hk.trans inf_le_left)
    have h2 := hb k' i j _ hi hj (hk.trans inf_le_right)
    linear_combination h1 - h2
  choose t ht using glue
  have ht' : ∀ k k' i (W : X.Opens), W ≤ V i → W ≤ U k → W ≤ U k' →
      rsT (t k k') W = rsT (b k' i) W - rsT (b k i) W := by
    intro k k' i W hi hk hk'
    have e : W ≤ V i ⊓ (U k ⊓ U k') := le_inf hi (le_inf hk hk')
    have h := congrArg (fun s => rsT s W) (ht k k' i)
    simp only [rsT_sub] at h
    rwa [rsT_rsT inf_le_right e, rsT_rsT (inf_le_inf_left _ inf_le_right) e,
      rsT_rsT (inf_le_inf_left _ inf_le_left) e] at h
  refine ⟨t, fun i k => b k i, fun k k' k'' => ?_, fun i i' k => hb k i i' _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right,
    fun i k k' => ht' k k' i _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      inf_le_right⟩
  refine eq_of_rsT_eq (fun i => V i ⊓ (U k ⊓ U k' ⊓ U k'')) (fun i => inf_le_right)
    (le_iSup_inf hV _) _ _ fun i => ?_
  have e : V i ⊓ (U k ⊓ U k' ⊓ U k'') ≤ U k ⊓ U k' ⊓ U k'' := inf_le_right
  have e1 := (e.trans inf_le_left).trans inf_le_left
  have e2 := (e.trans inf_le_left).trans inf_le_right
  have e3 := e.trans inf_le_right
  simp only [rsT_add]
  rw [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e,
    ht' k k' i _ inf_le_left e1 e2, ht' k' k'' i _ inf_le_left e2 e3, ht' k k'' i _ inf_le_left e1 e3]
  ring

end GlobalTheory.CechMixed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechOneCocycleOnAffineCoverMixedStatement
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechOneCocycle_on_affine_cover_mixed : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ i, V i = ⊤ → (∀ k, IsAffineOpen (U k)) → ∀ z : C1 V, IsCoc V z → ∃ (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), IsCoc U z' ∧ (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) ∧ ∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k') := by
  first | exact @GlobalTheory.CechMixed.exists_cocycle_on_affine | exact GlobalTheory.CechMixed.exists_cocycle_on_affine | (intros; apply GlobalTheory.CechMixed.exists_cocycle_on_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldsCechH1Relation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverRefinementPullback

theorem resG_resG' {X : Scheme.{0}} {O₀ O₁ O₂ : X.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(X, O₀)) :
    resG X h' (resG X h s) = resG X (h'.trans h) s := by
  simp only [resG]; rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem pbT_id' {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT; rw [dite_eq_left (show O ≤ (𝟙 X) ⁻¹ᵁ O₀ from h)]; simp [Scheme.Hom.appLE, resG, Category.id_comp]; rfl

theorem dlg_res' {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, pbT_id' _ le_rfl, pbT_id' _ le_rfl, ← hδ.2.2 _ _ hT le_top, resG_resG', resG_resG']
  rfl

theorem dlg_tri {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j k : L.ι) {T : B.left.Opens} (h₁ : T ≤ L.U i ⊓ L.U j)
    (h₂ : T ≤ L.U j ⊓ L.U k) (h₃ : T ≤ L.U i ⊓ L.U k) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T + rsT (dlg B (𝟙 _) L δ j k (L.U j ⊓ L.U k)) T =
      rsT (dlg B (𝟙 _) L δ i k (L.U i ⊓ L.U k)) T := by
  rw [dlg_res' B L δ hδ i j h₁, dlg_res' B L δ hδ j k h₂, dlg_res' B L δ hδ i k h₃,
    ← FinAffineCharts.cocycle_on hL i j k h₁ h₂ h₃]
  set u := res h₁ (L.g i j)
  set w := res h₂ (L.g j k)
  rw [mul_inv, Units.val_mul, hδ.2.1 _ le_top, Units.val_mul]
  have hu : (u : Γ(B.left, _)) * (u⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv u
  have hw : (w : Γ(B.left, _)) * (w⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv w
  linear_combination (-(δ _ w.val * (w⁻¹).val)) * hu + (-(δ _ u.val * (u⁻¹).val)) * hw

theorem dlg_refine {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) {κ : Type} (W : κ → B.left.Opens) (c : κ → L.ι) (h : ∀ a, W a ≤ L.U (c a))
    (a b : κ) {T : B.left.Opens} (hT : T ≤ W a ⊓ W b) :
    rsT (dlg B (𝟙 _) (FinAffineCharts.refineLB L W c h) δ a b (W a ⊓ W b)) T =
      rsT (dlg B (𝟙 _) L δ (c a) (c b) (L.U (c a) ⊓ L.U (c b))) T := by
  refine (dlg_res' B (FinAffineCharts.refineLB L W c h) δ hδ a b hT).trans ?_
  rw [dlg_res' B L δ hδ (c a) (c b) (hT.trans (inf_le_inf (h a) (h b)))]
  have e : res hT ((FinAffineCharts.refineLB L W c h).g a b) =
      res (hT.trans (inf_le_inf (h a) (h b))) (L.g (c a) (c b)) := FinAffineCharts.res_res _ _ _
  exact congrArg (fun u : Γ(B.left, T)ˣ => δ T u.val * (u⁻¹).val) e

theorem rsT_cmul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) {O₀ : Y.Opens} (r : R) (s : Γ(Y, O₀))
    (O : Y.Opens) : rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  by_cases h : O ≤ O₀
  · rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn q h]
  · unfold rsT; simp [h]

theorem sum_reindex {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) {d g : ℕ}
    (cc : Fin d → R) (e : Fin d → Fin g) (X : Fin g → Γ(Y, O)) :
    ∑ a, constFn q O (∑ b, if e b = a then cc b else 0) * X a = ∑ b, constFn q O (cc b) * X (e b) := by
  have h0 : ∀ a, constFn q O (∑ b, if e b = a then cc b else 0) = ∑ b, if e b = a then constFn q O (cc b) else 0 := by
    intro a; simp only [constFn, map_sum]; refine Finset.sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  simp only [h0, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := by
  intro R _ _ _ _ _ _ Dd g w dd' hinv hspan J V j hV hVj z hz
  have hab : IsAbelianScheme Dd.toPre.P.A := Dd.toPre.P.isAb
  haveI : CompactSpace Dd.toPre.P.A.left := by
    have := hab.proper; exact QuasiCompact.compactSpace_of_compactSpace Dd.toPre.P.A.hom
  obtain ⟨κ, hκ, W, c, hWa, hWc, hWcov⟩ :=
    FinAffineCharts.exists_finite_affine_cover Dd.toPre.P.L Dd.toPre.P.isLB
  have hL' := FinAffineCharts.refineLB_isLB Dd.toPre.P.isLB W c hWc hWcov
  have hiso := FinAffineCharts.iso_refineLB Dd.toPre.P.isLB W c hWc
  have hK' := MulDescent.kTriv_of_lbIso Dd.toPre.P.isLB hL' hiso Dd.toPre.P.ktriv
  have hA' : RelAmple Dd.toPre.P.A (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) := by
    obtain ⟨w0, hw0⟩ : LBIso (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc)
        (Dd.toPre.P.L.pull (𝟙 Dd.toPre.P.A.left)) :=
      hiso.symm.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Dd.toPre.P.L (𝟙 _) (𝟙 _) rfl)
    exact relAmple_pull IsPullback.of_id_fst Dd.toPre.P.isLB hL' ((isGen_iff w0).1 hw0) ⊤
      (isAffineOpen_top _) (fun _ => trivial) Dd.toPre.P.ample
  obtain ⟨bs⟩ := GlobalTheory.T.basis_tangentModule_abelianScheme_of_relDim R Dd.toPre.P.A Dd.toPre.P.g hab Dd.toPre.P.smoothDim
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_subfamily_unique_repr_of_spanning_of_local R _ Dd.toPre.P.g g ⟨bs⟩ w hspan
  have hI := GlobalTheory.T.invariant_vector_fields_basis_tangent R Dd.toPre.P.A Dd.toPre.P.g _ hab Dd.toPre.P.smoothDim hL' hA' hK' hWa hκ
    (fun a => w (e a)) (fun a => dd' (e a)) (fun a => hinv (e a)) he
  obtain ⟨z', b, hz'c, hR1, hR2⟩ := GlobalTheory.T.exists_cechOneCocycle_on_affine_cover_mixed _ J κ V W hV hWa z hz
  obtain ⟨cc, ⟨y', hy'⟩, -⟩ := hI z' hz'c

  obtain ⟨φV, hφV⟩ : ∃ φV : Fin g → C1 V, φV = fun a i i' => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a)
      (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') := ⟨_, rfl⟩
  obtain ⟨φU, hφU⟩ : ∃ φU : Fin g → C1 W, φU = fun a k k' => dlg Dd.toPre.P.A (𝟙 _)
      (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) (dd' a) k k' (W k ⊓ W k') := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin g → ∀ i k, Γ(Dd.toPre.P.A.left, V i ⊓ W k), β = fun a i k =>
      rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (c k)
        (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (c k))) (V i ⊓ W k) := ⟨_, rfl⟩

  have hm1 : ∀ a i i' k, rsT (φV a i i') (V i ⊓ V i' ⊓ W k) =
      rsT (β a i k) (V i ⊓ V i' ⊓ W k) - rsT (β a i' k) (V i ⊓ V i' ⊓ W k) := by
    intro a i i' k
    subst hφV hβ
    have t1 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ V i' := inf_le_left
    have t2 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ W k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have t3 : V i ⊓ V i' ⊓ W k ≤ V i' ⊓ W k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    simp only
    rw [GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hVj i')) t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i') (hWc k)) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (j i') (c k)
        (t1.trans (inf_le_inf (hVj i) (hVj i'))) (t3.trans (inf_le_inf (hVj i') (hWc k)))
        (t2.trans (inf_le_inf (hVj i) (hWc k)))]
    abel
  have hm2 : ∀ a i k k', rsT (φU a k k') (V i ⊓ W k ⊓ W k') =
      rsT (β a i k') (V i ⊓ W k ⊓ W k') - rsT (β a i k) (V i ⊓ W k ⊓ W k') := by
    intro a i k k'
    subst hφU hβ
    have t1 : V i ⊓ W k ⊓ W k' ≤ W k ⊓ W k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have t2 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k := inf_le_left
    have t3 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    simp only
    rw [dlg_refine _ _ (dd' a) (hinv a).1 W c hWc k k' t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k')) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (c k) (c k')
        (t2.trans (inf_le_inf (hVj i) (hWc k))) (t1.trans (inf_le_inf (hWc k) (hWc k')))
        (t3.trans (inf_le_inf (hVj i) (hWc k')))]
    abel

  set q := Dd.toPre.P.A.hom
  have hmix := GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps _ J κ V W hWcov
    (fun i i' => z i i' - ∑ a, constFn q _ (cc a) * φV (e a) i i')
    (fun k k' => z' k k' - ∑ a, constFn q _ (cc a) * φU (e a) k k')
    (fun i k => b i k - ∑ a, constFn q _ (cc a) * β (e a) i k)
    (fun i i' k => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR1, hm1, mul_sub, Finset.sum_sub_distrib]; abel)
    (fun i k k' => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR2, hm2, mul_sub, Finset.sum_sub_distrib]; abel)
    ⟨y', fun k k' => by subst hφU; exact hy' k k'⟩
  obtain ⟨y, hy⟩ := hmix
  refine ⟨fun a => ∑ b, if e b = a then cc b else 0, y, fun i i' => ?_⟩
  have h := hy i i'
  rw [sum_reindex q _ cc e (fun a => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i')
    (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i'))]
  simp only at h
  rw [← h]
  subst hφV
  simp only
  abel

end GlobalTheory.CoverRefinementPullback
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldsCechH1RelationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_fields_cech_h1_relation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := by
  first | exact @GlobalTheory.CoverRefinementPullback.main | exact GlobalTheory.CoverRefinementPullback.main | (intros; apply GlobalTheory.CoverRefinementPullback.main <;> assumption)
end

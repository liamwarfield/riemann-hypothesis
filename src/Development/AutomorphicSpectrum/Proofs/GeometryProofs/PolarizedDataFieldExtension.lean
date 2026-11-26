module

public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomain
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjoint

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.BaseExt

section Bundle

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

theorem normDegree_top_eq (M : HermitianBundle.{0} K) (M' : HermitianBundle.{0} L)
    (j : M.carrier → M'.carrier) (Φ : 𝓞 L ⊗[𝓞 K] M.carrier ≃ₗ[𝓞 L] M'.carrier)
    (hΦ : ∀ x, Φ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] x) = j x)
    (hm : ∀ (τ : L →+* ℂ) (x y : M.carrier),
      (M'.metric.form τ).inner ((1 : ComplexAt τ) ⊗ₜ[𝓞 L] j x) ((1 : ComplexAt τ) ⊗ₜ[𝓞 L] j y) =
        (M.metric.form (τ.comp (algebraMap K L))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 K] x) ((1 : ComplexAt _) ⊗ₜ[𝓞 K] y)) :
    M'.normDegree ⊤ = M.normDegree ⊤ := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have ht : LinearIndependent (𝓞 L) (fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) :=
    Module.Flat.linearIndependent_one_tmul (S := 𝓞 L) hs
  have hrank : Module.finrank (𝓞 L) (𝓞 L ⊗[𝓞 K] M.carrier) = Module.finrank (𝓞 K) M.carrier :=
    (TensorProduct.isBaseChange (𝓞 K) M.carrier (𝓞 L)).finrank_eq
  have hcomp : (Φ.toLinearMap ∘ fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) = fun i => j (s i) := by
    funext i
    simp [hΦ]
  have hs' : LinearIndependent (𝓞 L) (fun i => j (s i)) := by
    rw [← hcomp]
    exact ht.map' Φ.toLinearMap (LinearEquiv.ker Φ)
  have e1 : arithDegree M'.metric = arithDegree (M.metric.baseChange L) := by
    rw [arithDegree_eq M'.metric hs' (by rw [Fintype.card_fin, ← Φ.finrank_eq, hrank]),
      arithDegree_eq (M.metric.baseChange L) ht (by rw [Fintype.card_fin]; exact hrank.symm)]
    have hmap : (Submodule.span (𝓞 L) (Set.range fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)).map Φ.toLinearMap =
        Submodule.span (𝓞 L) (Set.range fun i => j (s i)) := by
      rw [Submodule.map_span, ← Set.range_comp, hcomp]
    have hg : ∀ τ : L →+* ℂ, gramDet M'.metric τ (fun i => j (s i)) =
        gramDet (M.metric.baseChange L) τ (fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) := by
      intro τ
      rw [LatticeLemmas.gramDet_baseChange]
      simp only [gramDet]
      congr 2
      ext a b
      simp only [Matrix.gram_apply]
      rw [fibreVec, fibreVec, fibreVec, fibreVec, FibreSpace.inner_equiv, FibreSpace.inner_equiv]
      exact hm τ _ _
    simp only [degreeWith, hg]
    rw [Nat.card_congr (Submodule.Quotient.equiv _ _ Φ hmap).toEquiv]
  have e2 := LatticeLemmas.BaseChange.proof K L M
  have e3 : M'.normDegree ⊤ = (M.baseChange L).deg := by
    rw [HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.deg]
    exact congrArg (· / (Module.finrank ℚ L : ℝ)) e1
  rw [e3, e2, HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.deg]

end Bundle

def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x x' : Sp R ⟶ S}
    (h : x = x') {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∃ M' : LieModel G x' V, ∀ e, lf (M'.pt e) = lf (M.pt e) := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    (dualMap c).comp (dualMap d) = dualMap (c.comp d) := by
  apply RingHom.ext
  intro x
  ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨P, h⟩ := GlobalTheory.SabBaseChange.exists_prescribed f t
  obtain ⟨c, s, a, p, m, -⟩ := GlobalTheory.SabBaseChange.exists_pullback_prescribed f t P h
  exact ⟨_, ⟨m⟩⟩

variable {L : Type} [Field L] [NumberField L] {L' : Type} [Field L'] [NumberField L'] [Algebra L L']

theorem algebraMap_square :
    (algebraMap (𝓞 L') L').comp (algebraMap (𝓞 L) (𝓞 L')) = (algebraMap L L').comp (algebraMap (𝓞 L) L) := by
  ext x
  rfl

theorem exists_ext (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] :
    Nonempty (Σ D' : PPData H L', D.Ext D') := by
  obtain ⟨t', ⟨m₁⟩⟩ := exists_pull (spMap (algebraMap (𝓞 L) (𝓞 L'))) D.t
  obtain ⟨tK', ⟨m₂⟩⟩ := exists_pull (spMap (algebraMap (𝓞 L') L')) t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ D.t t' tK' _ _ m₁ m₂
  have hsq : spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) =
      spMap (algebraMap L L') ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp, spMap_comp, algebraMap_square]
  obtain ⟨m₃, -⟩ := sabCancel pullCubCancel E H _ _ _ D.t D.tK tK' _ (spMap (algebraMap L L')) D.m (hsq ▸ n)
  have pr : IsPrincipal tK' := (GlobalTheory.T.isPrincipal_base_change_iff E H L L' (algebraMap L L') D.tK tK' m₃).2 D.princ
  obtain ⟨B, MB, fib⟩ := GlobalTheory.T.principal_hermitian_fibre E H L' t' tK' m₂ pr
  exact ⟨⟨⟨t', tK', m₂, pr, B, MB, fib⟩, m₁⟩⟩

theorem ext_props (D : PPData H L) (D' : PPData H L') (m : D.Ext D') :
    D'.g = D.g ∧ D'.hp = D.hp ∧ ∃ io : D.B.carrier →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] D'.B.carrier,
      Function.Injective io ∧ Submodule.span (𝓞 L') (Set.range io) = ⊤ ∧
      ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier),
        ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) =
          ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x)
            ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  haveI : Smooth D'.t.G.hom := D'.t.semi.smooth
  obtain ⟨Mp, hMp⟩ := (LiePull.lieModel_pullback _ _ D.t.G D'.t.G (spMap (algebraMap (𝓞 L) (𝓞 L'))) m.φ m.cart (𝓞 L')
    (𝟙 _) D'.B.carrier).2 D'.MB
  obtain ⟨Mq, hMq⟩ := exists_transport
    (show 𝟙 _ ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) = spMap (algebraMap (𝓞 L) (𝓞 L')) ≫ 𝟙 _ by simp) Mp
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts _ D.t.G _ _ (algebraMap (𝓞 L) (𝓞 L')) (𝟙 _) _ _ D.MB Mq
  have hj' : ∀ e, (D'.MB.pt (j e)).left ≫ m.φ =
      spMap (dualMap (algebraMap (𝓞 L) (𝓞 L'))) ≫ (D.MB.pt e).left := by
    intro e
    have h1 : lf (Mq.pt (j e)) = spMap (dualMap (algebraMap (𝓞 L) (𝓞 L'))) ≫ (D.MB.pt e).left :=
      (Category.comp_id _).symm.trans (hj e)
    rw [hMp, ← h1]
    exact (hMq _).symm
  letI : Module (𝓞 L) D'.B.carrier := Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))
  haveI : IsScalarTower (𝓞 L) (𝓞 L') D'.B.carrier := ⟨fun a b x => by
    change (a • b) • x = algebraMap (𝓞 L) (𝓞 L') a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let jl : D.B.carrier →ₗ[𝓞 L] D'.B.carrier :=
    { toFun := j, map_add' := j.map_add, map_smul' := fun r x => j.map_smulₛₗ r x }
  have hb : IsBaseChange (𝓞 L') jl := GlobalTheory.T.lie_model_isBaseChange _ D.t.G _ _ (𝟙 _) _ _ D.MB Mq jl hj
  have hΦ : ∀ x, hb.equiv ((1 : 𝓞 L') ⊗ₜ[𝓞 L] x) = j x := fun x => by
    rw [hb.equiv_tmul, one_smul]
    rfl
  have hmet : ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier),
      ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j y) : ℂ) =
        ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x)
          ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
    intro σ' x y
    obtain ⟨M₁, h₁⟩ := GlobalTheory.T.lie_model_complex_base_change _ D.t.G L (𝟙 _) D.B.carrier D.MB (σ'.comp (algebraMap L L'))
    obtain ⟨M₂, h₂⟩ := GlobalTheory.T.lie_model_complex_base_change _ D'.t.G L' (𝟙 _) D'.B.carrier D'.MB σ'
    have a := D.fib (σ'.comp (algebraMap L L')) x y _ _ (h₁ x) (h₁ y)
    have b := D'.fib σ' (j x) (j y) _ _ (h₂ (j x)) (h₂ (j y))
    have hring : (σ'.comp (algebraMap (𝓞 L') L')).comp (algebraMap (𝓞 L) (𝓞 L')) =
        (σ'.comp (algebraMap L L')).comp (algebraMap (𝓞 L) L) := by
      rw [RingHom.comp_assoc, algebraMap_square, RingHom.comp_assoc]
    have hz : spMap ((σ'.comp (algebraMap L L')).comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
        (spMap (σ'.comp (algebraMap (𝓞 L') L')) ≫ 𝟙 _) ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) := by
      rw [Category.comp_id, Category.comp_id, spMap_comp, hring]
    obtain ⟨M₃, h₃⟩ := exists_transport hz M₁
    have hv : ∀ e, (M₂.pt ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j e)).left ≫ m.φ =
        (M₃.pt ((1 : ComplexAt _) ⊗ₜ[𝓞 L] e)).left := by
      intro e
      have c₁ : lf (M₂.pt ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j e)) =
          spMap (dualMap (σ'.comp (algebraMap (𝓞 L') L'))) ≫ (D'.MB.pt (j e)).left :=
        (Category.comp_id _).symm.trans (h₂ (j e))
      have c₂ : lf (M₁.pt ((1 : ComplexAt _) ⊗ₜ[𝓞 L] e)) =
          spMap (dualMap ((σ'.comp (algebraMap L L')).comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt e).left :=
        (Category.comp_id _).symm.trans (h₁ e)
      change lf _ ≫ m.φ = lf _
      rw [h₃, c₁, c₂, Category.assoc, hj', ← Category.assoc, spMap_comp, dualMap_comp, hring]
    have T := GlobalTheory.T.hodge_inner_product_pullback_unique E H _ _ D'.t D.t _ m (spMap (σ'.comp (algebraMap (𝓞 L') L')) ≫ 𝟙 _) _ _ _ _ (hv x) (hv y)
    exact T.2 _ _ ((T.1 _).1 b) (hodge_congr _ hz (h₃ _).symm (h₃ _).symm a)
  refine ⟨hb.finrank_eq, ?_, j, ?_, ?_, hmet⟩
  · have := normDegree_top_eq D.B D'.B j hb.equiv hΦ hmet
    simp only [PPData.hp, this]
  · intro x y hxy
    have h1 : (1 : 𝓞 L') ⊗ₜ[𝓞 L] x = (1 : 𝓞 L') ⊗ₜ[𝓞 L] y := hb.equiv.injective (by rw [hΦ, hΦ, hxy])
    have hinj : Function.Injective ((Algebra.linearMap (𝓞 L) (𝓞 L')).rTensor D.B.carrier) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective _ _)
    have h2 : (1 : 𝓞 L) ⊗ₜ[𝓞 L] x = (1 : 𝓞 L) ⊗ₜ[𝓞 L] y := hinj (by simpa using h1)
    simpa using congrArg (TensorProduct.lid (𝓞 L) D.B.carrier) h2
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨t, rfl⟩ := hb.equiv.surjective y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [hb.equiv_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    | add a b ha hb' =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ ha hb'

end GlobalTheory.CompanionTheory.Ar.Sl.BaseExt


open GlobalTheory.CompanionTheory.Ar.Sl.BaseExt in
theorem GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'], Nonempty (Σ D' : PPData H L', D.Ext D') ∧ ∀ (D' : PPData H L') (_ : D.Ext D'), D'.g = D.g ∧ D'.hp = D.hp ∧ ∃ io : D.B.carrier →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] D'.B.carrier, Function.Injective io ∧ Submodule.span (𝓞 L') (Set.range io) = ⊤ ∧ ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier), ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) = ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
  intro E _ _ _ H L _ _ D L' _ _ _
  exact ⟨exists_ext D L', fun D' m => ext_props D D' m⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_data_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'], Nonempty (Σ D' : PPData H L', D.Ext D') ∧ ∀ (D' : PPData H L') (_ : D.Ext D'), D'.g = D.g ∧ D'.hp = D.hp ∧ ∃ io : D.B.carrier →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] D'.B.carrier, Function.Injective io ∧ Submodule.span (𝓞 L') (Set.range io) = ⊤ ∧ ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier), ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) = ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange | exact GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.ConstEmbedding

theorem exists_spMap {A : Type} [CommRing A] (x : Sp ℂ ⟶ Sp A) : ∃ ψ : A →+* ℂ, spMap ψ = x :=
  ⟨(Spec.preimage x).hom, by
    show Spec.map (CommRingCat.ofHom (Spec.preimage x).hom) = x
    simp⟩

theorem exists_extend (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* ℂ) :
    ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = ψ := by
  have hinj : Function.Injective ψ :=
    GlobalTheory.CompanionTheory.Ar.GrNorm.injective_of_algebraic (algebraMap (𝓞 F) F)
      (IsFractionRing.injective (𝓞 F) F) ψ
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun a => ?_⟩
  simp

theorem exists_embedding (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)) (hol : IsHolTo (Metric.ball 0 1) p) :
    ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  choose ψ hψ using fun u => exists_spMap (p u ≫ q)
  choose κ hκ using fun u => exists_extend F (ψ u)
  have hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) (Metric.ball 0 1) := by
    intro a
    have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hol q
    have h3 := (h2 ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv a)).2
    have hset : Metric.ball (0 : Fin n → ℂ) 1 ⊆ {b ∈ Metric.ball (0 : Fin n → ℂ) 1 | ⊤ ≤ (p b ≫ q) ⁻¹ᵁ ⊤} :=
      fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (a : F) = valAt' (p b ≫ q) ⊤ _
    rw [← hψ b, ← hκ b]
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 F) F)) a).symm
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  refine ⟨κ 0, fun u hu => ?_⟩
  have hc := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected (convex_ball (0 : Fin n → ℂ) 1).isPreconnected κ hd hu h0
  rw [← hc, hκ u, hψ u]

end GlobalTheory.CompanionTheory.Ar.ConstEmbedding
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_over_number_field_ring : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding | exact GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegree
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_change {E : Type} [AddCommGroup E] [Module Ω E] (L : Lat ξ E) {r : ℕ} {b b' : Fin r → E}
    {p : Cpt ξ} (hb : L.IsFrameAt b p) (hb' : L.IsFrameAt b' p) :
    ∃ T : Matrix (Fin r) (Fin r) (X.presheaf.stalk p.1), ∀ q, b' q = ∑ i, genMap ξ p (T i q) • b i := by
  have h : ∀ q, ∃ t : Fin r → X.presheaf.stalk p.1, b' q = ∑ i, genMap ξ p (t i) • b i := fun q => by
    have hm : b' q ∈ L p := by rw [hb'.2]; exact Submodule.subset_span ⟨q, rfl⟩
    rw [hb.2] at hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
    have h' : ∀ i, ∃ g, genMap ξ p g = (c i : Ω) := fun i => (c i).2
    choose t ht using h'
    exact ⟨t, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [ht]; rfl⟩
  choose T hT using h
  exact ⟨Matrix.of fun i q => T q i, hT⟩

theorem valAt_prod {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {A₀ : Type} (S : Finset A₀)
    {a : A₀ → Ω} {r : A₀ → ℂ} (h : ∀ i, ValAt ξ z (a i) (r i)) :
    ValAt ξ z (∏ i ∈ S, a i) (∏ i ∈ S, r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CxVal.one hz
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact CxVal.mul (h i) ih

theorem valAt_det {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {r : ℕ}
    (T : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z))) :
    ValAt ξ z (T.map (genMap ξ ⟨centre z, hz⟩)).det (T.map (Scheme.stalkClosedPointTo z).hom).det :=
  ⟨hz, T.det, RingHom.map_det _ _, RingHom.map_det _ _⟩

end General

section Quot

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

theorem quot_basis {N j : ℕ} (hj : j ≤ N) {b : Fin N → E} {F : Submodule Ω E} (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) (hF : Submodule.span Ω (Set.range (b ∘ headIdx hj)) = F) :
    LinearIndependent Ω (fun a => F.mkQ (b (tailIdx hj a))) ∧
      Submodule.span Ω (Set.range fun a => F.mkQ (b (tailIdx hj a))) = ⊤ := by
  have hinj : Function.Injective (tailIdx hj) := fun a a' h => by
    have := congrArg Fin.val h
    simp only [tailIdx] at this
    exact Fin.ext (by omega)
  constructor
  · have hd : Disjoint (Submodule.span Ω (Set.range (b ∘ tailIdx hj))) (LinearMap.ker F.mkQ) := by
      rw [Submodule.ker_mkQ, ← hF, Set.range_comp, Set.range_comp]
      refine hli.disjoint_span_image ?_
      rw [Set.disjoint_left]
      rintro _ ⟨a, rfl⟩ ⟨a', h⟩
      have := congrArg Fin.val h
      simp only [tailIdx, headIdx, Fin.val_castLE] at this
      have := a'.isLt
      omega
    exact (hli.comp _ hinj).map hd
  · rw [eq_top_iff]
    have hall : ∀ i, F.mkQ (b i) ∈ Submodule.span Ω (Set.range fun a => F.mkQ (b (tailIdx hj a))) := fun i => by
      by_cases hi : i.val < j
      · have : b i ∈ F := by
          rw [← hF]
          exact Submodule.subset_span ⟨⟨i.val, hi⟩, by simp [headIdx]⟩
        rw [(Submodule.Quotient.mk_eq_zero F).2 this |> fun h => (show F.mkQ (b i) = 0 from h)]
        exact zero_mem _
      · exact Submodule.subset_span ⟨⟨i.val - j, by have := i.isLt; omega⟩, by
          have : tailIdx hj ⟨i.val - j, by have := i.isLt; omega⟩ = i := Fin.ext (by simp [tailIdx]; omega)
          simp only [this]⟩
    rintro x -
    obtain ⟨e, rfl⟩ := F.mkQ_surjective x
    have he : e ∈ Submodule.span Ω (Set.range b) := by rw [hsp]; trivial
    induction he using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hall i
    | zero => simp
    | add _ _ _ _ h h' => rw [map_add]; exact add_mem h h'
    | smul a x _ h => rw [map_smul]; exact Submodule.smul_mem _ a h

end Quot

theorem sqrt_det_change {n : ℕ} {Γ Γ' Tz : Matrix (Fin n) (Fin n) ℂ} (hΓ : Γ.PosDef)
    (h : Γ' = Tz.conjTranspose * Γ * Tz) :
    Real.sqrt Γ'.det.re = ‖Tz.det‖ * Real.sqrt Γ.det.re := by
  obtain ⟨h0, h1⟩ := Complex.pos_iff.1 hΓ.det_pos
  have hg : Γ.det = ((Γ.det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using h1.symm)
  have e : Γ'.det = (((‖Tz.det‖ ^ 2 * Γ.det.re : ℝ)) : ℂ) := by
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hg]
    have : star Tz.det * Tz.det = ((‖Tz.det‖ ^ 2 : ℝ) : ℂ) := by
      simpa using Complex.conj_mul' Tz.det
    push_cast at this ⊢
    simp only [Complex.ofReal_re]
    linear_combination ((Γ.det.re : ℂ)) * this
  rw [e, Complex.ofReal_re, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem stalk_le_gen (𝔐 : HodgeCpt Y S₀ Dc.y) (t : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {x : 𝔐.Li}
    (hx : x ∈ 𝔐.V t p) : x ∈ 𝔐.Vgen t := by
  obtain ⟨U, hU, b, hs, hf⟩ := 𝔐.vb t p trivial
  have e : 𝔐.V t p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p trivial hU).2
  have hx' : x ∈ Submodule.span (regAt 𝔐.ξ p) (Set.range b) := e ▸ hx
  clear hx
  show x ∈ 𝔐.Vgen t
  have hs' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t := hs
  rw [← hs']
  induction hx' using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span h
  | zero => exact zero_mem _
  | add _ _ _ _ h h' => exact add_mem h h'
  | smul a x _ h => exact Submodule.smul_mem _ (a : Ω) h

theorem blocks_disjoint (Or : CptOrigin Y S₀ Dc Hd) (τ : CMType H) :
    Disjoint (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) := by
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S₀ Ω K J Dc.y Or.𝔐
    (FaithfulSMul.algebraMap_injective _ _)
  exact hind.pairwiseDisjoint (Or.bg_ne_sm τ τ)

theorem small_frame (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (d : MuFrameAt Hd w) {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li}
    (hs : Or.IsSmallPart d s) (τ : CMType H) (h : genPt Or.𝔐.ξ ⤳ centre z) :
    (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩ := by
  have hfr := GlobalTheory.T.component_data_hodge_second E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ d.c d.f (d.b τ) h hw (d.adapted τ).1 d.inDom
  exact (GlobalTheory.T.is_frame_at_tail_of_is_frame_at_comap_sup_lattice Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
    (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (d.b τ) (s τ) ⟨centre z, h⟩ (Or.i_inj τ)
    (Or.i_range τ) (blocks_disjoint Or τ) (fun _ hx => stalk_le_gen _ _ _ hx) (fun _ hx => stalk_le_gen _ _ _ hx) hfr
    (by rw [(d.adapted τ).2.2, Or.F_eq τ]) (hs τ)).1

theorem class_change (Or : CptOrigin Y S₀ Dc Hd) {w : (Σ k, J k) → ℂ} (d d' : MuFrameAt Hd w)
    {s s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s) (hs' : Or.IsSmallPart d' s')
    (τ : CMType H) (T : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω)
    (hT : ∀ q, s' τ q = ∑ p, T p q • s τ p) (q : Fin (Dc.N - Dc.j)) :
    (Hd.F τ).mkQ (d'.b τ (tailIdx Dc.j_le_N q)) =
      ∑ p, T p q • (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N p)) := by
  simp_rw [← map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  refine (Submodule.Quotient.eq (Hd.F τ)).2 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Or.F_eq τ, Submodule.mem_comap, map_sub, map_sum]
  have e : Or.i τ (d'.b τ (tailIdx Dc.j_le_N q)) - ∑ p, Or.i τ (T p q • d.b τ (tailIdx Dc.j_le_N p)) =
      (Or.i τ (d'.b τ (tailIdx Dc.j_le_N q)) - s' τ q) -
        ∑ p, T p q • (Or.i τ (d.b τ (tailIdx Dc.j_le_N p)) - s τ p) := by
    rw [hT q]
    simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [e]
  exact sub_mem (hs' τ q).2 (sum_mem fun p _ => Submodule.smul_mem _ _ (hs τ p).2)

end Main

theorem norm_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (d d' : MuFrameAt Hd w) (s s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (Γ Γ' : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → Or.IsSmallPart d s → Or.IsSmallPart d' s' → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s' τ) (Γ' τ)) → (∀ τ, (Γ τ).PosDef) → ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re = ‖valAt Dc.y d'.u w‖ * (∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ' τ).det.re := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w d d' s s' Γ Γ' hw hi hs hs' hg hg' hpd
  have : CharZero Ω := algebraRat.charZero Ω
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have htie : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi

  have hch : ∀ τ, ∃ T : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) (Or.𝔐.X.presheaf.stalk (centre z)),
      ∀ q, s' τ q = ∑ i, genMap Or.𝔐.ξ ⟨centre z, h⟩ (T i q) • s τ i := fun τ =>
    exists_change (Or.𝔐.V (Or.sm τ)) (small_frame Or hw d hs τ h) (small_frame Or hw d' hs' τ h)
  choose Ts hTs using hch
  let T : ∀ τ, Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω := fun τ => (Ts τ).map (genMap Or.𝔐.ξ ⟨centre z, h⟩)
  let Tz : ∀ τ, Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ :=
    fun τ => (Ts τ).map (Scheme.stalkClosedPointTo z).hom
  have hT : ∀ τ q, s' τ q = ∑ p, T τ p q • s τ p := hTs

  have hΓ : ∀ τ, Γ' τ = (Tz τ).conjTranspose * Γ τ * Tz τ := fun τ =>
    GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z _ (s τ) (s' τ) (Γ τ) (Γ' τ) (T τ) (Tz τ) hpol (hg τ) (hg' τ)
      (hT τ) fun p q => ⟨h, Ts τ p q, rfl, rfl⟩
  have hsq : ∀ τ, Real.sqrt (Γ' τ).det.re = ‖(Tz τ).det‖ * Real.sqrt (Γ τ).det.re := fun τ =>
    sqrt_det_change (hpd τ) (hΓ τ)

  have hΩ : d.u * chartMono Dc.y d.c Hd.aMu = d'.u * chartMono Dc.y d'.c Hd.aMu * ∏ τ, (T τ).det :=
    GlobalTheory.T.tensor_wedge_det_change (CMType H) Ω (fun τ => W τ ⧸ Hd.F τ) (Dc.N - Dc.j)
      (fun τ a => (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N a)))
      (fun τ a => (Hd.F τ).mkQ (d'.b τ (tailIdx Dc.j_le_N a))) T _ _
      (fun τ => (quot_basis Dc.j_le_N (b := d.b τ) (F := Hd.F τ)
        (d.adapted τ).1.2.2.2.1 (d.adapted τ).2.1 (d.adapted τ).2.2).1)
      (fun τ => (quot_basis Dc.j_le_N (b := d.b τ) (F := Hd.F τ)
        (d.adapted τ).1.2.2.2.1 (d.adapted τ).2.1 (d.adapted τ).2.2).2)
      (fun τ q => class_change Or d d' hs hs' τ (T τ) (hT τ) q)
      (d.eq.symm.trans d'.eq)

  have hc' : ∀ k, IsUnit (w ⟨k, d'.c k⟩) := fun k => IsUnit.mk0 _ (d'.inDom.1 k)
  have hy' : ∀ k, Dc.y ⟨k, d'.c k⟩ ≠ 0 := fun k => (hw.2 k _ (hc' k)).1
  have hr : ∀ k, ∃ r : ℂ, ValAt Or.𝔐.ξ z (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) r ∧
      w ⟨k, d.c k⟩ = r * w ⟨k, d'.c k⟩ := fun k => (hw.2 k _ (hc' k)).2 (d.c k)
  choose r hrv hrw using hr
  have hr0 : ∀ k, r k ≠ 0 := fun k h0 => d.inDom.1 k (by rw [hrw k, h0, zero_mul])
  have hmono : chartMono Dc.y d'.c Hd.aMu ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy' k)
  have hratio : d.u * ∏ k, (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) ^ Hd.aMu k = d'.u * ∏ τ, (T τ).det := by
    have e : ∏ k, (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) ^ Hd.aMu k =
        chartMono Dc.y d.c Hd.aMu / chartMono Dc.y d'.c Hd.aMu := by
      simp only [chartMono, div_zpow, Finset.prod_div_distrib]
    rw [e, ← mul_div_assoc, hΩ]
    field_simp

  have hu := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hu' := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d'.c d'.f d'.u htie h hw d'.inDom d'.unit
  have hL : ValAt Or.𝔐.ξ z (d.u * ∏ k, (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) ^ Hd.aMu k)
      (valAt Dc.y d.u w * ∏ k, r k ^ Hd.aMu k) :=
    CxVal.mul hu.2 (valAt_prod h _ fun k => CxVal.zpow (hrv k) (hr0 k) _)
  have hR : ValAt Or.𝔐.ξ z (d'.u * ∏ τ, (T τ).det) (valAt Dc.y d'.u w * ∏ τ, (Tz τ).det) :=
    CxVal.mul hu'.2 (valAt_prod h _ fun τ => valAt_det h (Ts τ))
  rw [hratio] at hL
  have hv := CxVal.unique hL hR
  have hn : ‖valAt Dc.y d.u w‖ * ∏ k, ‖r k‖ ^ Hd.aMu k = ‖valAt Dc.y d'.u w‖ * ∏ τ, ‖(Tz τ).det‖ := by
    have := congrArg norm hv
    simpa [norm_mul, norm_prod, norm_zpow] using this
  have hw' : ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k =
      (∏ k, ‖r k‖ ^ Hd.aMu k) * ∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, ← norm_mul, ← hrw k]
  simp_rw [hsq]
  rw [Finset.prod_mul_distrib, hw']
  calc _ = (‖valAt Dc.y d.u w‖ * ∏ k, ‖r k‖ ^ Hd.aMu k) * (∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k) *
        ∏ τ, Real.sqrt (Γ τ).det.re := by ring
    _ = _ := by rw [hn]; ring

end GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegreeStatement
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_hodge_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (d d' : MuFrameAt Hd w) (s s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (Γ Γ' : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → Or.IsSmallPart d s → Or.IsSmallPart d' s' → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s' τ) (Γ' τ)) → (∀ τ, (Γ τ).PosDef) → ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re = ‖valAt Dc.y d'.u w‖ * (∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ' τ).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep | exact GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourth
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourth
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree


open LieTangent in
theorem valAt_diff {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L] {M : LieModel G ξ L}
    {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f]
    {A : L →ₗ[Ω] L} (hA : M.IsDiffOf f A) {e : L} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨h1, v, hv, hw⟩ := h
  refine ⟨h1, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · change _ ≫ (v ≫ f).left = _
    simp only [Over.comp_left]
    rw [← Category.assoc, hv.1]
    exact congrArg CommaMorphism.left (one_comp f)
  · change (M.pt (A e)).left = _ ≫ (v ≫ f).left
    rw [hA e]
    simp only [Over.comp_left, ← Category.assoc, hv.2]
  · change (w ≫ f).left = _ ≫ (v ≫ f).left
    simp only [Over.comp_left, ← Category.assoc, hw]

theorem conj_ne_of_sq {x : ℂ} {d : ℕ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) : starRingEnd ℂ x ≠ x := by
  intro h
  have him : x.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re hx
  have : x = (x.re : ℂ) := Complex.ext rfl (by simpa using him)
  rw [this] at hre
  norm_cast at hre
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp at hre
  nlinarith [sq_nonneg x.re]

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  simp

theorem val_eig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hξ : IsCptGen 𝔐.ξ) (hg : genPt 𝔐.ξ ⤳ centre z)
    (s : CMType H ⊕ CMType H) (a : 𝓞 E) (t : 𝔐.X.presheaf.stalk (centre z))
    (ht : genMap 𝔐.ξ ⟨centre z, hg⟩ t = 𝔐.emb s a) {e : 𝔐.Li} (he : e ∈ 𝔐.Vgen s)
    {v : epsAt z ⟶ 𝔐.t.G} (hv : 𝔐.M.ValAt z e v) :
    v ≫ 𝔐.t.act.act a = LieTangent.epsScale z ((Scheme.stalkClosedPointTo z).hom t) ≫ v := by
  haveI := 𝔐.t.act.hom a
  have h1 := valAt_diff (𝔐.act a) hv
  have h2 := hv.smul hg t
  have e1 : 𝔐.ρ a e = genMap 𝔐.ξ ⟨centre z, hg⟩ t • e := by
    have h3 := (Submodule.mem_iInf _).1 he a
    rw [LinearMap.mem_ker] at h3
    rw [ht]
    simpa [sub_eq_zero] using h3
  rw [e1] at h1
  exact h1.unique hξ h2

theorem hodgeInnerProduct_blocks_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (e e' : Or.𝔐.Li) (v v' : epsAt z ⟶ Or.𝔐.t.G) (a : ℂ), Or.𝔐.Interior z → e ∈ Or.𝔐.Vgen (Or.bg τ) → e' ∈ Or.𝔐.Vgen (Or.sm τ) → Or.𝔐.M.ValAt z e v → Or.𝔐.M.ValAt z e' v' → HodgeIP Or.𝔐.t.G Or.𝔐.t.PP.L z v v' a → a = 0 := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ e e' v v' a hz he he' hv hv' hI
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, hc0, -, -, -, -, hreg⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S₀ Ω K J Dc.y Or.𝔐 hβ
  haveI := hc0
  have hP := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hz
  have hg : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have hξ : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists Or.𝔐.X Or.𝔐.t.G ℂ z
  obtain ⟨h, hHI, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H Or.𝔐.X Or.𝔐.t z Vz MR hP
  obtain ⟨g, hgen⟩ := hreg (Sum.inl τ) H.rt ⟨centre z, hg⟩
  set x : ℂ := (Scheme.stalkClosedPointTo z).hom g with hx
  have hsq : g ^ 2 = -(H.d : Or.𝔐.X.presheaf.stalk (centre z)) := by
    apply hξ.inj ⟨centre z, hg⟩
    rw [map_pow, hgen, map_neg, map_natCast, ← map_pow, H.rt_sq, map_neg, map_natCast]
  have hx2 : x ^ 2 = -(H.d : ℂ) := by
    rw [hx, ← map_pow, hsq, map_neg, map_natCast]
  have hne : starRingEnd ℂ x ≠ x := conj_ne_of_sq H.d_prime.pos hx2
  have hin : ∀ b, Or.𝔐.emb (Sum.inr τ) b = Or.𝔐.emb (Sum.inl τ) (H.bar b) := fun _ => rfl
  have key : ∃ b, v ≫ Or.𝔐.t.act.act b = LieTangent.epsScale z x ≫ v ∧
      v' ≫ Or.𝔐.t.act.act (H.bar b) = LieTangent.epsScale z x ≫ v' := by
    rcases Or.side with ⟨hb, hs, -⟩ | ⟨hb, hs, -⟩
    · rw [hb] at he
      rw [hs] at he'
      refine ⟨H.rt, val_eig Or.𝔐 hξ hg (Sum.inl τ) _ g hgen he hv,
        val_eig Or.𝔐 hξ hg (Sum.inr τ) _ g ?_ he' hv'⟩
      rw [hin, bar_bar, hgen]
    · rw [hb] at he
      rw [hs] at he'
      refine ⟨H.bar H.rt, val_eig Or.𝔐 hξ hg (Sum.inr τ) _ g ?_ he hv, ?_⟩
      · rw [hin, bar_bar, hgen]
      · rw [bar_bar]
        exact val_eig Or.𝔐 hξ hg (Sum.inl τ) _ g hgen he' hv'
  obtain ⟨b, A1, A2⟩ := key
  obtain ⟨p, rfl⟩ := MR.onto v hv.isTanAt
  obtain ⟨p', rfl⟩ := MR.onto v' hv'.isTanAt
  have ha : a = h p p' := (hHI _ _ _).1 hI
  have hadj := GlobalTheory.T.hodge_inner_product_adjoint E H Or.𝔐.X Or.𝔐.t z (MR.pt p) (MR.pt p') b (h (x • p) p') hP (MR.tan p) (MR.tan p')
  rw [A1, A2, ← MR.pt_smul, ← MR.pt_smul] at hadj
  have e1 : h (x • p) p' = h p (x • p') := (hHI _ _ _).1 (hadj.1 ((hHI _ _ _).2 rfl))
  rw [map_smulₛₗ, map_smul] at e1
  simp only [LinearMap.smul_apply, smul_eq_mul] at e1
  rw [ha]
  have e2 : (starRingEnd ℂ x - x) * h p p' = 0 := by
    rw [sub_mul, e1, sub_self]
  exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourthStatement
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (e e' : Or.𝔐.Li) (v v' : epsAt z ⟶ Or.𝔐.t.G) (a : ℂ), Or.𝔐.Interior z → e ∈ Or.𝔐.Vgen (Or.bg τ) → e' ∈ Or.𝔐.Vgen (Or.sm τ) → Or.𝔐.M.ValAt z e v → Or.𝔐.M.ValAt z e' v' → HodgeIP Or.𝔐.t.G Or.𝔐.t.PP.L z v v' a → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFifth
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFifth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open GlobalTheory.CompanionTheory.Ar.HodgeCpt (rootIdx rootSgn)

theorem isHodgeLine_pull_tensor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx hv r a a₀ e e₀ A₀ T
    hβ hcz hy hGen hNorm hVal hCoord hInt he hA hT hR hH z w hw hI t ν hg
  haveI := hcz
  subst hA
  have hsp : genPt 𝔐₀.ξ ⤳ centre (z ≫ h) := 𝔐₀.all _
  have hw₀ := hCoord z w hw
  have hI₀ := hInt z hI

  obtain ⟨t₀, ht₀⟩ := Flag.gr_gen_of_isFlagVBOn (Fl₀.sub (rootIdx D r).1)
    (p := ⟨centre (z ≫ h), 𝔐₀.all _⟩) (Set.mem_univ _) (rootIdx D r).2
  obtain ⟨ν₀, -, hn₀⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ Fl₀ hβ (z ≫ h) hI₀ _ _ t₀ ht₀
  have hgr₀ := (hn₀ t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀.1]; exact CxVal.one hsp, by simp⟩

  have ecp : pushCpt hd ⟨centre z, 𝔐.all _⟩ = ⟨centre (z ≫ h), 𝔐₀.all _⟩ := Subtype.ext (by
    show h (z _) = (z ≫ h) _
    exact (Scheme.Hom.comp_apply z h _).symm)
  have hgen := hGen ⟨centre z, 𝔐.all _⟩ (fun p hp => not_inFibre 𝔐.ξ z (𝔐.all _) hp) _ _ t₀ (ecp ▸ ht₀)
  obtain ⟨ν₁, -, hn₁⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S Ω K J y 𝔐 Fl hβ z hI _ _ (i t₀) hgen
  have hit : i t₀ ≠ 0 := hgen.1
  obtain ⟨u', -, hu', e'⟩ := (hn₁ _ _).1 (hNorm z _ _ t₀ ν₀ hgr₀)
  have hu1 : u' = 1 := CxVal.unique hu' (by rw [div_self hit]; exact CxVal.one (𝔐.all _))
  obtain ⟨u₁, hu₁0, hu₁, eν⟩ := (hn₁ _ _).1 hg
  rw [hu1, norm_one, _root_.one_mul] at e'
  subst e'

  have hsec := hH (z ≫ h) _ hw₀ hI₀ t₀ ν₀ hgr₀
  choose c₀ hc₀ using hw₀.1
  choose c hc using hw.1
  have hc₀' : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hc₀ k).ne_zero
  have hc' : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  obtain ⟨u₀, hu₀, en₀⟩ := hsec.2.2 c₀ hc₀'
  obtain ⟨u, -, hu, eT⟩ := hR z w hw c c₀ hc' hc₀'
  have ha : ((pullHerm hv A₀).tensor T).a = a := by
    show pullDeg bk A₀.a + T.a = a
    rw [hT]
    abel
  have hM₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k (c₀ k) (hc₀ k)).1
  have hM : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (hc k)).1
  have hm₀ : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) ≠ 0 :=
    (map_ne_zero i).2 (mul_ne_zero hM₀ hsec.1)
  refine (secNorm_iff_chart he hw c hc').2 ⟨u₁ ^ rootSgn D r * u₀ * u, ?_, ?_⟩
  · rw [ha]
    convert CxVal.mul (CxVal.mul (CxVal.zpow hu₁ hu₁0 (rootSgn D r)) (hVal z _ _ hu₀)) hu using 1
    rw [map_div₀, map_zpow₀, div_zpow]
    generalize i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) = m at hm₀
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) * e = n
    have hz : i t₀ ^ rootSgn D r ≠ 0 := zpow_ne_zero _ hit
    field_simp
  · rw [ha, eν]
    show (‖u₁‖ * ν₀) ^ rootSgn D r * (A₀.h (fun p => w (blkV bk bx p)) * T.h w) = _
    rw [mul_zpow, norm_mul, norm_mul, norm_zpow]
    linear_combination (‖u₁‖ ^ rootSgn D r * T.h w) * en₀ + (‖u₁‖ ^ rootSgn D r * ‖u₀‖) * eT

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFifthStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_fifth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor | exact GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor <;> assumption)
end
end

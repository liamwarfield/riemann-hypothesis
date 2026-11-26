module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistribution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWeilDatumTransportCmApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_vecEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Xo.XF c) :
    ∃ e : (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G) ≃ (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G),
      ∀ (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)),
        SameVecs Y x v (fun i => e (v i)) ∧ ∀ χ : 𝓞 E →+* R,
          IsEigBasisAt Xo.univ.t.act (x ≫ toX Xo c) χ v ↔
            IsEigBasisAt Y.t.act ((x ≫ Y.jQ) ≫ genι Y) χ (fun i => e (v i)) := by
  obtain ⟨e₀, he₀, hb₀⟩ := BdryUnit.exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act x (x ≫ toX Xo c) rfl
  obtain ⟨e, he, hb⟩ := BdryUnit.exists_eigEquiv Y.m.cart Y.m.act x ((x ≫ Y.jQ) ≫ genι Y) (Category.assoc _ _ _)
  refine ⟨e₀.symm.trans e, fun n v => ⟨fun i => ⟨e₀.symm (v i), ?_, (he _).symm⟩, fun χ => ?_⟩⟩
  · exact (he₀ _).symm.trans (congrArg (fun z => z.left) (e₀.apply_symm_apply (v i)))
  · have h := hb₀ χ n fun i => e₀.symm (v i)
    have hv : (fun i => e₀ (e₀.symm (v i))) = v := funext fun i => e₀.apply_symm_apply (v i)
    rw [hv] at h
    exact h.symm.trans (hb χ n fun i => e₀.symm (v i))

theorem frame_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c), (∀ v w, FrU Xo c U τ j x v w → ∃ vb wb, FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) ∧ (∀ (V : Set (gen Y)) vb wb, Set.range x ⊆ U → FrY Y V τ j (x ≫ Y.jQ) vb wb → ∃ v w, FrU Xo c U τ j x v w ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ R _ j x
  obtain ⟨e, he⟩ := exists_vecEquiv Y x
  have hs : (x ≫ Y.jQ) ≫ genStr Y = x ≫ toF Xo c := by
    rw [Category.assoc]
    exact congrArg (x ≫ ·) Y.jQ_over
  refine ⟨fun v w h => ⟨fun i => e (v i), fun i => e (w i),
    ⟨hs.trans h.1, ?_, ((he _ v).2 _).1 h.2.2.1, ((he _ w).2 _).1 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩,
    fun V vb wb hU h => ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact subset_closure ⟨x z, h.2.1 ⟨z, rfl⟩, by simp⟩
  · obtain ⟨v, rfl⟩ : ∃ v : Fin D.p → _, vb = fun i => e (v i) :=
      ⟨fun i => e.symm (vb i), funext fun i => (e.apply_symm_apply _).symm⟩
    obtain ⟨w, rfl⟩ : ∃ w : Fin D.q → _, wb = fun i => e (w i) :=
      ⟨fun i => e.symm (wb i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, w, ⟨hs.symm.trans h.1, hU, ((he _ v).2 _).2 h.2.2.1, ((he _ w).2 _).2 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩

end GlobalTheory.DetLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

open MonObj

theorem IsTranslate.fst_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ x → IsTanAtG t x v → IsTranslate t φ g₀ v w → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ := by
  intro E _ _ _ H X t R S _ _ φ x g₀ v w hg hv ⟨g', v', h₁, h₂, h₃⟩
  have e1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
  have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => by simp [dualMap]
  let r : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, e1, Category.id_comp])
  let q : Over.mk (g₀ ≫ t.G.hom) ⟶ Over.mk x := Over.homMk (spMap φ) hg.symm
  have hv1 : r ≫ v' = 1 := by
    rw [← MonObj.comp_one q]
    apply Over.OverMorphism.ext
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = spMap φ ≫ _
    rw [h₂, ← Category.assoc, e2, Category.assoc, hv.2]
  have h : (r ≫ (g' * v')).left = (r ≫ g').left := by
    rw [MonObj.comp_mul, hv1, _root_.mul_one]
  rw [← h₃]
  refine h.trans ?_
  show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ g'.left = g₀
  rw [h₁, ← Category.assoc, e1, Category.id_comp]

end GlobalTheory.LogKS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_eq_basePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ x → IsTanAtG t x v → IsTranslate t φ g₀ v w → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ := by
  first | exact @GlobalTheory.LogKS.IsTranslate.fst_comp | exact GlobalTheory.LogKS.IsTranslate.fst_comp | (intros; apply GlobalTheory.LogKS.IsTranslate.fst_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitary
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaRatPair

theorem det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]
    simp [Matrix.transpose_submatrix, Matrix.submatrix_map]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self] at this
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this
  exact pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm

theorem det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem thetaSum_om_rat : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine det_ne_zero_of_map W.J (B.emb w).1 fun h0 => det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ

end GlobalTheory.ThetaRatPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitaryStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSum_invariant_rational_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.ThetaRatPair.thetaSum_om_rat | exact GlobalTheory.ThetaRatPair.thetaSum_om_rat | (intros; apply GlobalTheory.ThetaRatPair.thetaSum_om_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.TransLift

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem lift_isTranslate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ X) (x' : Sp R' ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (u : Sp (DualNumber R) ⟶ t.G.left) (u' : Sp (DualNumber R') ⟶ t'.G.left), IsTanAtG t x u → IsTanAtG t' x' u' → u' ≫ m.φ = spMap (dualMap ψ) ≫ u → ∀ (S : Type) [CommRing S] (φS : R' →+* S) (g₀' : Sp S ⟶ t'.G.left), g₀' ≫ t'.G.hom = spMap φS ≫ x' → ∀ w : Sp (DualNumber S) ⟶ t.G.left, IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u w → ∃ w' : Sp (DualNumber S) ⟶ t'.G.left, w' ≫ m.φ = w ∧ IsTranslate t' φS g₀' u' w' := by
  intro E _ _ _ H X X' t t' j m R R' _ _ ψ x x' hx u u' hu hu' huu S _ φS g₀' hg₀' w hw
  obtain ⟨w', hw', -⟩ := existsUnique_isTranslate t' φS hg₀' hu'
  refine ⟨w', ?_, hw'⟩
  have hsq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  have hg : (g₀' ≫ m.φ) ≫ t.G.hom = spMap (φS.comp ψ) ≫ x := by
    rw [Category.assoc, hsq, ← Category.assoc, hg₀', Category.assoc, hx, ← Category.assoc, spMap_comp'']
  obtain ⟨g', v', h₁, h₂, h₃⟩ := hw'
  have ht : IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u (w' ≫ m.φ) := by
    let T : Over X' := tEpsG (g₀' ≫ t'.G.hom)
    have heq : (tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom)).hom = T.hom ≫ j := by
      show spMap _ ≫ (g₀' ≫ m.φ) ≫ t.G.hom = (spMap _ ≫ g₀' ≫ t'.G.hom) ≫ j
      rw [Category.assoc, Category.assoc, Category.assoc, hsq]
    let e : tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom) ⟶ Over.mk (T.hom ≫ j) :=
      Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact heq.symm)
    refine ⟨e ≫ pushHom m.cart T g', e ≫ pushHom m.cart T v', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ g'.left ≫ m.φ = _
      rw [Category.id_comp, h₁, Category.assoc]
    · show 𝟙 _ ≫ v'.left ≫ m.φ = _
      rw [Category.id_comp, h₂, Category.assoc, huu, ← Category.assoc, spMap_comp'', dualMap_comp'']
    · rw [← MonObj.comp_mul, ← map_mul]
      show 𝟙 _ ≫ (g' * v').left ≫ m.φ = _
      rw [Category.id_comp, h₃]
  exact (existsUnique_isTranslate t (φS.comp ψ) hg hu).unique ht hw

end GlobalTheory.TransLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMapStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentTranslate_lifts_semiAbelianTripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ X) (x' : Sp R' ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (u : Sp (DualNumber R) ⟶ t.G.left) (u' : Sp (DualNumber R') ⟶ t'.G.left), IsTanAtG t x u → IsTanAtG t' x' u' → u' ≫ m.φ = spMap (dualMap ψ) ≫ u → ∀ (S : Type) [CommRing S] (φS : R' →+* S) (g₀' : Sp S ⟶ t'.G.left), g₀' ≫ t'.G.hom = spMap φS ≫ x' → ∀ w : Sp (DualNumber S) ⟶ t.G.left, IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u w → ∃ w' : Sp (DualNumber S) ⟶ t'.G.left, w' ≫ m.φ = w ∧ IsTranslate t' φS g₀' u' w' := by
  first | exact @GlobalTheory.TransLift.lift_isTranslate | exact GlobalTheory.TransLift.lift_isTranslate | (intros; apply GlobalTheory.TransLift.lift_isTranslate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportWeilDatumCmExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportWeilDatumCmExtension
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.WeilContF

theorem continuous_transportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsContOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
  have hfin := GlobalTheory.T.exists_local_finiteDimensional_finite_parts_weil_transport F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hpt := GlobalTheory.T.continuous_weilDatum_transport_cm_apply F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hbd := GlobalTheory.T.weilDatumTransport_archimedeanSlice_schwartz_bounds F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hpres := (GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr).1
  refine GlobalTheory.WeilCont.isContOn_of_local F hfin (fun Φ hΦ y => ?_)
  choose s hs using fun p => GlobalTheory.WeilCont.exists_slice F (hpres p Φ hΦ) y
  refine ⟨s, continuous_iff_continuousAt.2 fun p0 => GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded s p0 (fun v => ?_) (fun k n => ?_), hs⟩
  · simp_rw [hs]
    exact (hpt Φ hΦ _).continuousAt
  · obtain ⟨C, hC⟩ := hbd Φ hΦ y p0 k n
    refine ⟨C, hC.mono fun p hp v => ?_⟩
    have e : (⇑(s p)) = fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y) := funext (hs p)
    rw [e]
    exact hp v

end GlobalTheory.WeilContF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportWeilDatumCmExtensionStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_transport_weil_datum_cm_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsContOn (adeleClass F) om := by
  first | exact @GlobalTheory.WeilContF.continuous_transportF | exact GlobalTheory.WeilContF.continuous_transportF | (intros; apply GlobalTheory.WeilContF.continuous_transportF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigFrameMatch
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.EigParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Generic

variable {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (x : Sp R ⟶ S) (χ : 𝓞 E → R)

def IsBasG {n : ℕ} (u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ (∀ i (a : 𝓞 E), u i ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ u i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x u a w

end Generic

variable {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S}

theorem comb_iff {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) (a : Fin n → R) (w : epsAt x ⟶ t.G) :
    IsCombAt x a v w ↔ IsCombAtG t x (fun i => (v i).left) a w.left :=
  exists_congr fun _ => and_congr Iff.rfl ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h.symm⟩

theorem basis_iff (χ : 𝓞 E →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) :
    IsEigBasisAt t.act x χ v ↔ IsBasG t x χ (fun i => (v i).left) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨Over.w (v i), (h1 i).1⟩, fun i a => (h1 i).2 a, fun w hw he => ?_⟩
    let w' : epsAt x ⟶ t.G := Over.homMk w hw.1
    exact (existsUnique_congr fun a => comb_iff v a w').1 (h2 w' ⟨hw.2, he⟩)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ⟨(h1 i).2, h2 i⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => comb_iff v a w).2 (h3 w.left ⟨Over.w w, hw.1⟩ hw.2)

theorem exists_over (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hu : IsBasG t x χ u) :
    ∃ v : Fin n → (epsAt x ⟶ t.G), IsEigBasisAt t.act x χ v ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => Over.homMk (u i) (hu.1 i).1, (basis_iff χ _).2 hu, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem exists_left (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) :
    ∃ u : Fin m → (Sp (DualNumber R) ⟶ t.G.left), IsBasG t x χ u ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => (v i).left, (basis_iff χ _).1 hv, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem eigFrame_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∀ (V : Set (gen Y)) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y), x ≫ genStr Y = spMap j → Set.range x ⊆ V → ∀ f : EigFrame Y j (x ≫ genι Y), (∃ v w, FrY Y V τ j x v w ∧ Match τ f v w) ∧ ∀ v w, FrY Y V τ j x v w → ∃ f' : EigFrame Y j (x ≫ genι Y), Match τ f' v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ hτ V R _ j x hx hV f
  have hp : D.mult τ = D.p := GlobalTheory.Harm.mult_of_mem D hτ
  have hq : D.mult (conjEmb τ) = D.q := GlobalTheory.Harm.mult_conjEmb_of_mem D hτ
  have hne : conjEmb τ ≠ τ := fun e => (GlobalTheory.Harm.not_mem_hostType_iff H τ).2 (by rw [e]; exact hτ) hτ
  have hf : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (f.v σ) :=
    fun σ => ⟨f.tan σ, f.eig σ, f.basis σ⟩
  refine ⟨?_, fun v w h => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := exists_over _ hp (hf τ)
    obtain ⟨w, hw, hw'⟩ := exists_over _ hq (hf (conjEmb τ))
    refine ⟨v, w, ⟨hx, hV, hv, ?_⟩, hv', hw'⟩
    rw [comp_chi_bar]
    exact hw
  · obtain ⟨-, -, hv, hw⟩ := h
    rw [comp_chi] at hv
    rw [comp_chi_bar] at hw
    obtain ⟨v₁, a, a'⟩ := exists_left _ hp hv
    obtain ⟨w₁, b, b'⟩ := exists_left _ hq hw
    classical
    let g := Function.update (Function.update f.v τ v₁) (conjEmb τ) w₁
    have g1 : g τ = v₁ := by
      simp only [g, Function.update_of_ne hne.symm, Function.update_self]
    have g2 : g (conjEmb τ) = w₁ := Function.update_self _ _ _
    have hg : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (g σ) := fun σ => by
      by_cases e2 : σ = conjEmb τ
      · rw [e2, g2]; exact b
      by_cases e1 : σ = τ
      · rw [e1, g1]; exact a
      have : g σ = f.v σ := by simp only [g, Function.update_of_ne e2, Function.update_of_ne e1]
      rw [this]; exact hf σ
    refine ⟨⟨g, fun σ => (hg σ).1, fun σ => (hg σ).2.1, fun σ => (hg σ).2.2⟩, fun i k e => ?_, fun i k e => ?_⟩
    · exact (a' i k e).trans (congrFun g1 k).symm
    · exact (b' i k e).trans (congrFun g2 k).symm

end GlobalTheory.DetLine.EigParts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadNonnegOfInt
open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

open Matrix in
private lemma exists_nat_mul_rat_eq_int' {s : ℕ} (q : Fin s → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ n : Fin s → ℤ, ∀ u, (N : ℚ) * q u = n u := by
  refine ⟨∏ v, (q v).den, Finset.prod_pos fun v _ => (q v).den_pos,
    fun u => (q u).num * ∏ v ∈ Finset.univ.erase u, ((q v).den : ℤ), fun u => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun v => (q v).den) (Finset.mem_univ u)]
  push_cast
  rw [← Rat.mul_den_eq_num (q u)]
  ring

open Matrix in
private lemma bilinForm_sum_zsmul_eq_sum_mul {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (y : Fin s → X) (n : Fin s → ℤ) :
    β (∑ u, n u • y u) (∑ v, n v • y v) = ∑ u, ∑ v, n u * n v * β (y u) (y v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

open Matrix in
private lemma gram_quadratic_real_nonneg {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, 0 ≤ β x x) (y : Fin s → X) (c : Fin s → ℝ) :
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ) := by
  have hdense : DenseRange (Pi.map fun _ : Fin s => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hdense.induction_on (p := fun c : Fin s → ℝ =>
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ)) c
    (isClosed_le continuous_const (by fun_prop)) fun q => ?_
  obtain ⟨N, hN, n, hn⟩ := exists_nat_mul_rat_eq_int' q
  have hnR : ∀ u, (N : ℝ) * (q u : ℝ) = (n u : ℝ) := fun u => by exact_mod_cast hn u
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have key : (N : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (q v : ℝ) * ((β (y u) (y v) : ℤ) : ℝ) =
      ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    rw [bilinForm_sum_zsmul_eq_sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hnR u, ← hnR v]
    ring
  have h0 : (0 : ℝ) ≤ ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    exact_mod_cast hpos _
  rw [← key] at h0
  exact (mul_nonneg_iff_of_pos_left hNpos).mp h0


open Matrix in
theorem _root_.GlobalTheory.Poinc.qW_nonneg_of_posW : ∀ {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ),
    _root_.GlobalTheory.Poinc.PosW W → ∀ {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ x, 0 ≤ β x x) →
    ∀ y : Fin s → X, 0 ≤ _root_.GlobalTheory.Poinc.qW W β y := by
  intro s W hW X _ β hsymm hpos y
  unfold _root_.GlobalTheory.Poinc.PosW at hW
  unfold _root_.GlobalTheory.Poinc.qW
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hW.posSemidef
  set S : ℤ := ∑ u, ∑ w, W u w * β (y u) (y w) with hS
  have hswap : ∑ u, ∑ w, W w u * β (y u) (y w) = S := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [hsymm]
  have htwo : ((2 * S : ℤ) : ℝ) = ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    have : (2 * S : ℤ) = ∑ u, ∑ w, (W u w + W w u) * β (y u) (y w) := by
      simp only [add_mul, Finset.sum_add_distrib, hswap, hS]
      ring
    rw [this]
    push_cast
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hnonneg : (0 : ℝ) ≤ ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    rw [hv]
    have e : ∀ u w, (∑ i, vecMulVec (v i) (star (v i))) u w * ((β (y u) (y w) : ℤ) : ℝ) =
        ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := by
      intro u w
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_mul]
    simp_rw [e]
    calc (0 : ℝ) ≤ ∑ i, ∑ u, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_nonneg fun i _ => gram_quadratic_real_nonneg β hpos y (v i)
      _ = ∑ u, ∑ i, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := Finset.sum_comm
      _ = ∑ u, ∑ w, ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
  rw [← htwo] at hnonneg
  have : (0 : ℝ) ≤ (S : ℝ) := by push_cast at hnonneg; linarith
  exact_mod_cast this

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
open GlobalTheory.SiegelTor Polynomial

namespace GlobalTheory.SiegelTor

theorem isPrimitiveRoot_zetaAway {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zetaAway N) N :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway N).subtype) (Complex.isPrimitiveRoot_exp N hN) Subtype.val_injective

theorem cycAway_hom_ext {N : ℕ} (hN : N ≠ 0) {R : Type*} [CommRing R] {β β' : cycAway N →+* R}
    (h : β (zetaAway N) = β' (zetaAway N)) : β = β' := by
  ext ⟨x, hx⟩
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
        Subtype.ext (by simpa using mul_inv_cancel₀ hN')
      have e₁ := congrArg β e
      have e₂ := congrArg β' e
      rw [map_mul, map_natCast, map_one] at e₁ e₂
      exact left_inv_eq_right_inv (by rw [mul_comm]; exact e₁) e₂
  | zero => exact (map_zero β).trans (map_zero β').symm
  | one => exact (map_one β).trans (map_one β').symm
  | add x y hx hy ihx ihy =>
    exact (map_add β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_add β' ⟨x, hx⟩ ⟨y, hy⟩).symm)
  | neg x hx ih => exact (map_neg β ⟨x, hx⟩).trans ((congrArg _ ih).trans (map_neg β' ⟨x, hx⟩).symm)
  | mul x y hx hy ihx ihy =>
    exact (map_mul β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_mul β' ⟨x, hx⟩ ⟨y, hy⟩).symm)

theorem exists_cycAway_hom_complex {N : ℕ} (hN : N ≠ 0) {μ : ℂ} (hμ : IsPrimitiveRoot μ N) :
    ∃ f : cycAway N →+* ℂ, f (zetaAway N) = μ := by
  have hp := Nat.pos_of_ne_zero hN
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  have hi : IsIntegral ℚ (zetaAway N : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway N : ℂ)}
  have hle : cycAway N ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K N)
  have hr : μ ∈ (minpoly ℚ (zetaAway N : ℂ)).aroots ℂ := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero N ℚ, ?_⟩
    rw [cyclotomic_eq_minpoly_rat hμ hp]
    exact minpoly.aeval ℚ μ
  let g : K →ₐ[ℚ] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨μ, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway N : ℂ)) = μ :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨μ, hr⟩
  exact ⟨g.toRingHom.comp (Subring.inclusion hle), hg⟩

theorem exists_cycAway_end {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ f : cycAway N →+* cycAway N, f (zetaAway N) = zetaAway N ^ m := by
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  obtain ⟨f, hf⟩ := exists_cycAway_hom_complex hN (hz.pow_of_coprime m hm)
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : ∀ x, f x ∈ cycAway N := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hf ▸ pow_mem (zetaAway N).2 m
      · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ hN')
        have e₁ := congrArg f e
        rw [map_mul, map_natCast, map_one] at e₁
        exact Set.mem_of_eq_of_mem (eq_inv_of_mul_eq_one_right e₁) (Subring.subset_closure (Or.inr rfl))
    | zero => exact Set.mem_of_eq_of_mem (map_zero f) (zero_mem (cycAway N))
    | one => exact Set.mem_of_eq_of_mem (map_one f) (one_mem (cycAway N))
    | add x y hx hy ihx ihy => exact (map_add f ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  exact ⟨f.codRestrict (cycAway N) hmem, Subtype.ext hf⟩

theorem exists_cycAway_aut {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m := by
  have hz := isPrimitiveRoot_zetaAway hN
  have : NeZero N := ⟨hN⟩
  obtain ⟨k, -, hk⟩ := (hz.pow_of_coprime m hm).eq_pow_of_pow_eq_one hz.pow_eq_one
  have hkc : k.Coprime N := by
    rw [← (hz.pow_of_coprime m hm).pow_iff_coprime (Nat.pos_of_ne_zero hN), hk]; exact hz
  obtain ⟨f, hf⟩ := exists_cycAway_end hN hm
  obtain ⟨g, hg⟩ := exists_cycAway_end hN hkc
  refine ⟨RingEquiv.ofRingHom f g (cycAway_hom_ext hN ?_) (cycAway_hom_ext hN ?_), hf⟩
  · rw [RingHom.comp_apply, hg, map_pow, hf, hk, RingHom.id_apply]
  · rw [RingHom.comp_apply, hf, map_pow, hg, ← pow_mul, mul_comm, pow_mul, hk, RingHom.id_apply]

theorem exists_pow_of_isLocalRing {N : ℕ} (hN : N ≠ 0) {R : Type} [CommRing R] [IsLocalRing R]
    (β β' : cycAway N →+* R) : ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m := by
  classical
  have hp := Nat.pos_of_ne_zero hN
  have : NeZero N := ⟨hN⟩
  have hz := isPrimitiveRoot_zetaAway hN
  have h₁ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β)
  have h₂ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β')
  obtain ⟨i, hi, he⟩ := h₁.eq_pow_of_pow_eq_one h₂.pow_eq_one
  refine ⟨i, by rw [← h₁.pow_iff_coprime hp, he]; exact h₂, ?_⟩
  have hprod : ∏ k ∈ Finset.range N, (β' (zetaAway N) - β (zetaAway N) ^ k) = 0 := by
    have e := congrArg (fun p => (p.map β).eval (β' (zetaAway N))) (X_pow_sub_C_eq_prod hz hp (one_pow N))
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, Polynomial.map_prod, eval_prod, eval_sub, eval_pow,
      eval_X, eval_C, mul_one, map_one, map_pow, Polynomial.map_one, eval_one] at e
    rw [← e, ← map_pow, hz.pow_eq_one, map_one, sub_self]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)] at hprod
  have hu : IsUnit (∏ k ∈ (Finset.range N).erase i, (β' (zetaAway N) - β (zetaAway N) ^ k)) := by
    refine IsUnit.prod_iff.2 fun k hk => ?_
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, sub_ne_zero]
    intro h
    obtain ⟨hki, hk⟩ := Finset.mem_erase.1 hk
    exact hki (h₁.pow_inj (Finset.mem_range.1 hk) hi (h.symm.trans he.symm))
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 hprod)

theorem cycAway_galois : ∀ N : ℕ, N ≠ 0 → (∀ m : ℕ, m.Coprime N → ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m) ∧ (∀ (R : Type) [CommRing R] (β β' : cycAway N →+* R), β (zetaAway N) = β' (zetaAway N) → β = β') ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β β' : cycAway N →+* R), ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m :=
  fun _ hN => ⟨fun _ hm => exists_cycAway_aut hN hm, fun _ _ _ _ h => cycAway_hom_ext hN h,
    fun _ _ _ β β' => exists_pow_of_isLocalRing hN β β'⟩

end GlobalTheory.SiegelTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexification
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.DefRead.Transport

section General

variable {Ks LL WL C : Type} [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Algebra Ks ℂ] [Algebra LL ℂ] [IsScalarTower Ks LL ℂ]

def phiBil (e : C →ₗ[Ks] WL) : ℂ →+ C →+ ℂ ⊗[LL] WL :=
  AddMonoidHom.mk' (fun z => ((TensorProduct.mk LL ℂ WL z).toAddMonoidHom.comp e.toAddMonoidHom))
    (fun a b => by ext f; exact TensorProduct.add_tmul a b (e f))

theorem phiBil_compat (e : C →ₗ[Ks] WL) (r : Ks) (z : ℂ) (f : C) :
    phiBil (LL := LL) e (r • z) f = phiBil (LL := LL) e z (r • f) := by
  show (r • z) ⊗ₜ[LL] e f = z ⊗ₜ[LL] e (r • f)
  rw [map_smul, ← algebraMap_smul LL r (e f), TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    algebraMap_smul LL r z]

def phi (e : C →ₗ[Ks] WL) : ℂ ⊗[Ks] C →ₗ[ℂ] ℂ ⊗[LL] WL where
  toFun := TensorProduct.liftAddHom (phiBil (LL := LL) e) (phiBil_compat e)
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z f =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show (c • z) ⊗ₜ[LL] e f = c • (z ⊗ₜ[LL] e f)
      rw [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

@[simp] theorem phi_tmul (e : C →ₗ[Ks] WL) (z : ℂ) (f : C) : phi e (z ⊗ₜ[Ks] f) = z ⊗ₜ[LL] e f :=
  TensorProduct.liftAddHom_tmul (phiBil (LL := LL) e) (phiBil_compat e) z f

theorem phi_comm (e : C →ₗ[Ks] WL) (a : C →ₗ[Ks] C) (r : WL →ₗ[LL] WL) (h : ∀ f, e (a f) = r (e f)) :
    phi e ∘ₗ a.baseChange ℂ = r.baseChange ℂ ∘ₗ phi e := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [h]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

theorem phi_bijective (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) :
    Function.Bijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap)) := by
  let bW : Module.Basis (Fin n) Ks (Submodule.span Ks (Set.range b)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) Ks WK := bW.map (LinearEquiv.ofEq _ _ hspK)
  let bC : Module.Basis (Fin n) Ks C := bK.map e.symm
  let bL : Module.Basis (Fin n) LL WL := Module.Basis.mk hliL (by rw [hspL])
  let cC := Algebra.TensorProduct.basis ℂ bC
  let cL := Algebra.TensorProduct.basis ℂ bL
  have key : phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) = (cC.equiv cL (Equiv.refl _)).toLinearMap := by
    refine cC.ext fun j => ?_
    show _ = (cC.equiv cL (Equiv.refl _)) (cC j)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [cC, cL, bC, bK, bW, bL, Module.Basis.span_apply]
  rw [key]
  exact (cC.equiv cL (Equiv.refl _)).bijective

theorem transport_general {H G X : Type} [Group G] [Group H] [DecidableEq X] [MulAction H X]
    (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) (ρ0 : G → (WL →ₗ[LL] WL))
    (act : G → C →ₗ[Ks] C) (he : ∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) (s : G → ℂ) (φ : H →* G)
    (A : X → Submodule ℂ (ℂ ⊗[Ks] C)) (hA : DirectSum.IsInternal A)
    (hinv : ∀ (h : H) (y : X), ∀ v ∈ A y, (act (φ h)).baseChange ℂ v ∈ A (h • y)) :
    ∃ A' : X → Submodule ℂ (ℂ ⊗[LL] WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, (s (φ h) • (ρ0 (φ h)).baseChange ℂ) v ∈ A' (h • y) := by
  let Ψ := LinearEquiv.ofBijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap))
    (phi_bijective WK n b hliK hspK hliL hspL e)
  let o := Submodule.orderIsoMapComap Ψ
  refine ⟨fun y => o (A y), ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
    refine ⟨iSupIndep.map_orderIso o hA.1, ?_⟩
    rw [← o.map_iSup, hA.2, o.map_top]
  · intro h y v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map).1 hv
    have hc := LinearMap.congr_fun (phi_comm (WK.subtype ∘ₗ e.toLinearMap) (act (φ h)) (ρ0 (φ h))
      (fun f => he _ f)) u
    refine Submodule.mem_map.2 ⟨s (φ h) • (act (φ h)).baseChange ℂ u, (A (h • y)).smul_mem _ (hinv h y u hu), ?_⟩
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.smul_apply, map_smul]
    show s (φ h) • phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) _ = s (φ h) • (ρ0 (φ h)).baseChange ℂ (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) u)
    rw [hc]

end General


open GlobalTheory.DefRead in
theorem transport : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  intro Ks LL WL C H G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ WK n b _ hliK hspK hliL hspL e ρ0 χ act he φ A hA hinv
  letI : Algebra Ks ℂ := (σ.comp (algebraMap Ks LL)).toAlgebra
  letI : Algebra LL ℂ := σ.toAlgebra
  haveI : IsScalarTower Ks LL ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨A', h1, h2⟩ := transport_general (X := X) WK n b hliK hspK hliL hspL e (fun g => ρ0 g) act he
    (fun g => σ (((χ g)⁻¹ : LLˣ) : LL)) φ A hA hinv
  exact ⟨A', h1, fun h y v hv => by rw [twBC_apply]; exact h2 h y v hv⟩

end GlobalTheory.DefRead.Transport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexificationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_permuted_directSum_complexification : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  first | exact @GlobalTheory.DefRead.Transport.transport | exact GlobalTheory.DefRead.Transport.transport | (intros; apply GlobalTheory.DefRead.Transport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {r m : ℕ}

theorem Supports.mul {d : ℕ} {γ : Fin r → LinearMap.BilinForm ℤ X} {a : Fin m → X} (h : Supports bar φ d γ a) {k : ℕ}
    (hk : 0 < k) : Supports bar φ (d * k) γ fun j : Fin (m * k) => a (finProdFinEquiv.symm j).1 := by
  have key : ∀ β : LinearMap.BilinForm ℤ X,
      (∑ j : Fin (m * k), β (a (finProdFinEquiv.symm j).1) (a (finProdFinEquiv.symm j).1) : ℤ) =
        k * ∑ i, β (a i) (a i) := fun β => by
    rw [finProdFinEquiv.symm.sum_comp (fun p : Fin m × Fin k => β (a p.1) (a p.1)), Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => h.only β hβ hp ?_⟩
  · rw [← h.span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨finProdFinEquiv (i, ⟨0, hk⟩), by simp⟩
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    have := h.le β hβ hp
    nlinarith
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← h.eq j]; ring
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast] at he
    have : (k : ℝ) * (d * φ.evalZ β) = k * (∑ i, β (a i) (a i) : ℤ) := by rw [← he]; ring
    exact mul_left_cancel₀ hk'.ne' this

theorem Supports.of_pull {d : ℕ} (e : X ≃ₗ[O] X₁) {γ : Fin r → LinearMap.BilinForm ℤ X₁} {a : Fin m → X}
    (h : Supports bar φ d (fun j => pull e.toLinearMap (γ j)) a) : Supports bar φ d γ fun i => e (a i) := by
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩
  · have h1 : Set.range (fun i => e (a i)) = e.toAddEquiv.toIntLinearEquiv.toLinearMap '' Set.range a := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h.span, Submodule.map_top, LinearMap.range_eq_top]
    exact e.toAddEquiv.toIntLinearEquiv.surjective
  · have := h.le _ (pull_mem e.toLinearMap hβ) fun y => hp _
    rwa [evalZ_pull φ e.surjective] at this
  · have := h.eq j
    rwa [evalZ_pull φ e.surjective] at this
  · have he' : d * φ.evalZ (pull e.toLinearMap β) = (∑ i, pull e.toLinearMap β (a i) (a i) : ℤ) := by
      rw [evalZ_pull φ e.surjective]; exact he
    obtain ⟨k, c, hk, hc⟩ := h.only _ (pull_mem e.toLinearMap hβ) (fun y => hp _) he'
    refine ⟨k, c, hk, LinearMap.ext₂ fun x y => ?_⟩
    have := LinearMap.congr_fun₂ hc (e.symm x) (e.symm y)
    simpa [LinearMap.sum_apply] using this

end Transport

theorem exists_common {ι : Type} [Finite ι] (P : ι → ℕ → Prop) (hmul : ∀ i d d', P i d → d ∣ d' → 0 < d' → P i d')
    (h : ∀ i, ∃ d, 1 ≤ d ∧ P i d) : ∃ d, 1 ≤ d ∧ ∀ i, P i d := by
  have := Fintype.ofFinite ι
  choose d hd hP using h
  have hpos : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  exact ⟨_, hpos, fun i => hmul i _ _ (hP i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hpos⟩

section Module

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}

theorem exists_common_module {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (hX : IsPolFanOn bar φ X)
    (hs : ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
      Supports bar φ d γ a) :
    ∃ d, 1 ≤ d ∧ ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → X),
      Supports bar φ d γ a := by
  obtain ⟨S, hS, hfin⟩ := hX.finite
  have := hS.to_subtype
  let N := Nat.card S
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Σ r : Fin (N + 1), (Fin r → S))
    (fun i d => IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) →
      ∃ (m : ℕ) (a : Fin m → X), Supports bar φ d (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) a)
    (fun i d d' h hdd hd' hc => by
      obtain ⟨m, a, ha⟩ := h hc
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun i => by
      by_cases hc : IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X))
      · obtain ⟨d, m, a, hd, ha⟩ := hs _ _ hc
        exact ⟨d, hd, fun _ => ⟨m, a, ha⟩⟩
      · exact ⟨1, le_rfl, fun h => (hc h).elim⟩)
  refine ⟨d, hd, fun r γ hγ => ?_⟩
  obtain ⟨e, he⟩ := hfin r γ hγ
  have hγ' := hγ.pull_equiv e
  have hr : r ≤ N := by
    have := Nat.card_le_card_of_injective (fun i : Fin r => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rwa [Nat.card_fin] at this
  obtain ⟨m, a, ha⟩ := hP ⟨⟨r, by omega⟩, fun i => ⟨_, he i⟩⟩ hγ'
  exact ⟨m, _, ha.of_pull e⟩

end Module

theorem exists_hasSupports : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O]
    [Finite (ClassGroup O)] (bar : O → O) (q : ℕ) (φ : InvFun O), IsPolFan bar q φ →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
        Supports bar φ d γ a) → ∃ d, 1 ≤ d ∧ HasSupports bar q φ d := by
  intro O _ _ _ _ _ bar q φ hpol hs
  obtain ⟨n, Y, hY⟩ := GlobalTheory.ProjModFinIso.exists_finite_reps (R := O) q
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Fin n)
    (fun k d => ∀ [Module.Finite O (Y k)] [Module.Projective O (Y k)], Module.finrank O (Y k) ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ (Y k)), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → Y k),
        Supports bar φ d γ a)
    (fun k d d' h hdd hd' _ _ hq r γ hγ => by
      obtain ⟨m, a, ha⟩ := h hq r γ hγ
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun k => by
      by_cases hk : Module.Finite O (Y k) ∧ Module.Projective O (Y k) ∧ Module.finrank O (Y k) ≤ q
      · obtain ⟨h1, h2, h3⟩ := hk
        obtain ⟨d, hd, h⟩ := exists_common_module (hpol _ h3) (hs _ h3)
        exact ⟨d, hd, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h3 => (hk ⟨‹_›, ‹_›, h3⟩).elim⟩)
  refine ⟨d, hd, fun X _ _ _ _ hX r γ hγ => ?_⟩
  obtain ⟨k, ⟨e⟩⟩ := hY X hX
  haveI := Module.Finite.equiv e
  haveI := Module.Projective.of_equiv e
  obtain ⟨m, a, ha⟩ := hP k (e.finrank_eq ▸ hX) r _ (hγ.pull_equiv e.symm)
  exact ⟨m, _, ha.of_pull e.symm⟩

end GlobalTheory.Poinc
end
end

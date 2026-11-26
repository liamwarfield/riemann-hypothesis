module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConsta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.RigAtOrigin

theorem frame_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left) (he : eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)
    (w : LB.Iso x.P.L (D.P.L.pull φ)), w.IsGen →
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
    ∀ (g : ℕ) (u : HolUnif x.P.A x.P.L g), u.IsRig x.rig → ∀ (k : x.P.L.ι) (j : D.P.L.ι),
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U k → ⊤ ≤ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U j →
      valAt' (u.ex 0).left _ (w.s (fun _ => j, k)).val * u.fr k 0 =
        valF (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)).val := by
  intro R _ _ _ D x φ he w _ hM g u hrig k j hk hj
  have hu0 : (u.ex 0).left = eSec x.P.A := by
    rw [(u.ker 0).2 u.Λ.zero_mem]
    change (toUnit _ ≫ η[x.P.A]).left = η[x.P.A].left
    rw [toUnit_unit, Category.id_comp]
  have hj' : ⊤ ≤ (𝟙 (Sp ℂ) ≫ eSec x.P.A ≫ φ) ⁻¹ᵁ D.P.L.U j := by
    rw [Category.id_comp, he]; exact hj
  have hk' : ⊤ ≤ (𝟙 (Sp ℂ) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U k := by
    rw [Category.id_comp, ← hu0]; exact hk
  have e := GlobalTheory.ArcThetaFib.maps_val' φ _ he D.P.L D.rig x.P.L w x.rig hM (𝟙 (Sp ℂ)) j k hj' hk'
  have hr := hrig (fun _ => k) (fun q hq => Set.mem_iInter.2 fun _ => hk' hq)
  rw [hu0, hr]
  simp only [Category.id_comp] at e
  exact e.symm

end GlobalTheory.RigAtOrigin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedFibre_frame_at_origin_eq_rigidification : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left) (he : eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)
    (w : LB.Iso x.P.L (D.P.L.pull φ)), w.IsGen →
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
    ∀ (g : ℕ) (u : HolUnif x.P.A x.P.L g), u.IsRig x.rig → ∀ (k : x.P.L.ι) (j : D.P.L.ι),
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U k → ⊤ ≤ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U j →
      valAt' (u.ex 0).left _ (w.s (fun _ => j, k)).val * u.fr k 0 =
        valF (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)).val := by
  first | exact @GlobalTheory.RigAtOrigin.frame_at_origin | exact GlobalTheory.RigAtOrigin.frame_at_origin | (intros; apply GlobalTheory.RigAtOrigin.frame_at_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFunctionValuesClassicalUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFunctionValuesClassicalUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.MBLow.Cl.HolB

variable {X Y : Scheme.{0}}

theorem valF_comp_app (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valF x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valF (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dite_eq_left h', dite_eq_left h]
    simp only [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dite_eq_right h', dite_eq_right h]

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := rfl

def psiB (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left)
    (hw : φ ≫ D.P.A.hom = x.P.A.hom ≫ spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) :
    x.P.A.left ⟶ (DegPre.BF D ℂ).left :=
  (lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
    (Over.homMk φ (by
      rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
      Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A)).left

theorem hol_ptB : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := by
  intro R _ _ _ D N ν g d x u φ hφ hE U f
  have hw := hφ.1.w
  have key : ∀ z, ptB ν d z = (u.ex z).left ≫ psiB R D x φ hw := by
    intro z
    have h0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := Over.w (u.ex z)
    let e : TF (R := R) ℂ ⟶ Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) :=
      Over.homMk (u.ex z).left (by simp only [Over.mk_hom]; rw [← Category.assoc, h0]; exact Category.id_comp _)
    have he : e ≫ lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
        (Over.homMk φ (by
          rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
          Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A) = lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) := by
      rw [comp_lift]
      congr 1
      · ext; simp [e, h0]
      · ext; simp [e, hE z]
    rw [ptB, ← he]
    rfl
  have hs : {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (psiB R D x φ hw ⁻¹ᵁ U)} := by
    ext z
    simp only [Set.mem_setOf_eq, key z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := u.hol (psiB R D x φ hw ⁻¹ᵁ U) ((psiB R D x φ hw).app U |>.hom f)
  rw [hs]
  refine ⟨ho, hd.congr fun z _ => ?_⟩
  rw [← valF_eq_valAt', valF_comp_app, key z]

end GlobalTheory.MBLow.Cl.HolB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFunctionValuesClassicalUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_functionValues_classicalUniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := by
  first | exact @GlobalTheory.MBLow.Cl.HolB.hol_ptB | exact GlobalTheory.MBLow.Cl.HolB.hol_ptB | (intros; apply GlobalTheory.MBLow.Cl.HolB.hol_ptB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicUniformizationComplexBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRComp
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ValuationCompositionDivisor

theorem valR_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y)
    (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  unfold valR
  rfl

end GlobalTheory.ValuationCompositionDivisor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicUniformizationComplexBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.UnifTan

theorem valR_comp_eq {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  first
  | exact @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | (apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp ..)

theorem valF_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF p U f = valAt' p U f := by
  unfold valF valAt' valAt
  split_ifs <;> rfl

theorem valR_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valR p U f = valAt' p U f := by
  unfold valR valAt' valAt
  split_ifs <;> rfl

theorem valAt'_comp_eq {X Y : Scheme.{0}} (p : Sp ℂ ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (p ≫ ψ) U f = valAt' p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  rw [← valR_eq_valAt', ← valR_eq_valAt', valR_comp_eq]

theorem prime_subsingleton : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
  constructor
  have key : ∀ (P : PrimeSpectrum (DualNumber ℂ)) (z : DualNumber ℂ), z ∈ P.asIdeal ↔ z.fst = 0 := by
    intro P z
    constructor
    · intro hz
      by_contra hne
      have hu : IsUnit z := (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (isUnit_iff_ne_zero.2 hne)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz hu)
    · intro hz
      have h2 : z * z = 0 := by
        ext <;> simp [hz]
      have : z * z ∈ P.asIdeal := by rw [h2]; exact P.asIdeal.zero_mem
      rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  intro P Q
  ext z
  rw [key P, key Q]

theorem top_le_of_red {X : Scheme.{0}} (p : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ (redE ℂ ≫ p) ⁻¹ᵁ U) :
    ⊤ ≤ p ⁻¹ᵁ U := by
  intro y _
  have hy : y = redE ℂ (IsLocalRing.closedPoint ℂ) := by
    haveI := prime_subsingleton
    exact Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
  have := h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [hy]
  exact this

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, Over.mk_hom, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    (u.ex 0).left = η[A].left := by
  have h1 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  rw [h1, Hom.one_def]
  simp

theorem isD_iff_isDiff : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (b' : epsR ℂ ⟶ x.P.A) (b : TE R ℂ ⟶ D.P.A), IsTangent b' → b'.left ≫ φ = b.left →
      ∀ W' : Fin g → ℂ, (IsD ν d W' b ↔ u.IsDiff W' b') := by
  intro R _ _ _ D N ν g d x u φ hφ hE b' b hb' hbb W'
  have hP : IsPullback x.P.A.hom φ (TF (R := R) ℂ).hom D.P.A.hom := by
    rw [tf_hom]; exact hφ.1.flip
  let e := hP.isoPullback
  let ψ : x.P.A.left ⟶ (DegPre.BF D ℂ).left := e.hom
  have hψi : ψ ≫ e.inv = 𝟙 _ := e.hom_inv_id
  have hpt : ∀ z, ptB ν d z = (u.ex z).left ≫ ψ := by
    intro z
    apply pullback.hom_ext
    · simp only [ptB, Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst]
      have := Over.w (u.ex z)
      simpa using this.symm
    · simp only [ptB, Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hE z
  have hb : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left = b'.left ≫ ψ := by
    apply pullback.hom_ext
    · simp only [Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst, Over.homMk_left]
      have := Over.w b'
      simpa using this.symm
    · simp only [Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hbb.symm
  have hred : redE ℂ ≫ b'.left = (u.ex 0).left := by
    rw [ex_zero]; exact hb'
  have back : ∀ {A : Type} [CommRing A] (p : Sp A ⟶ x.P.A.left) (U' : x.P.A.left.Opens) (f' : Γ(x.P.A.left, U')),
      valR (p ≫ ψ) (e.inv ⁻¹ᵁ U') ((e.inv.app U').hom f') = valR p U' f' := by
    intro A _ p U' f'
    rw [← valR_comp_eq, Category.assoc, hψi, Category.comp_id]
  have valB : ∀ (U' : x.P.A.left.Opens) (h : ⊤ ≤ b'.left ⁻¹ᵁ U') (f' : Γ(x.P.A.left, U')),
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((b'.left.appLE U' ⊤ h).hom f') = valR b'.left U' f' := by
    intro U' h f'
    unfold valR
    rw [dite_eq_left h]
  constructor
  · intro hD U' h f'
    have h0 : ⊤ ≤ ptB ν d 0 ⁻¹ᵁ (e.inv ⁻¹ᵁ U') := by
      have hc : (((u.ex 0).left ≫ ψ) ≫ e.inv) = redE ℂ ≫ b'.left := by
        rw [Category.assoc, hψi, Category.comp_id, hred]
      rw [hpt 0]
      show ⊤ ≤ (((u.ex 0).left ≫ ψ) ≫ e.inv) ⁻¹ᵁ U'
      rw [hc]
      exact fun y _ => h (Set.mem_univ ((redE ℂ) y))
    have k := hD _ ((e.inv.app U').hom f') h0
    simp only [hb, hpt, valF_eq_valAt', ← valR_eq_valAt', back] at k
    rw [valB U' h f', k]
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, valR_eq_valAt']
  · intro hI U f h0
    have h1 : ⊤ ≤ b'.left ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
      apply top_le_of_red
      rw [hred]
      rw [hpt] at h0
      exact h0
    have hs := hI (ψ ⁻¹ᵁ U) h1 ((ψ.app U).hom f)
    rw [valB] at hs
    simp only [hb, hpt, valR_comp_eq, valF_eq_valAt', valAt'_comp_eq]
    ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      rw [← hred, ← valR_eq_valAt', (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ _ h1).2]
      rfl
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact hs

end GlobalTheory.UnifTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicUniformizationComplexBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_uniformization_complex_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (b' : epsR ℂ ⟶ x.P.A) (b : TE R ℂ ⟶ D.P.A), IsTangent b' → b'.left ≫ φ = b.left →
      ∀ W' : Fin g → ℂ, (IsD ν d W' b ↔ u.IsDiff W' b') := by
  first | exact @GlobalTheory.UnifTan.isD_iff_isDiff | exact GlobalTheory.UnifTan.isD_iff_isDiff | (intros; apply GlobalTheory.UnifTan.isD_iff_isDiff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointOverOriginLiftsTangentVectorUniformised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointOverOriginLiftsTangentVectorUniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem tangent_lift_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left), IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ →
    eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A →
    ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left →
      ∃ b' : epsR ℂ ⟶ x.P.A, IsTangent b' ∧ b'.left ≫ φ = b.left := by
  intro R _ _ _ D x φ hφ he b hb
  have hTF : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    simp only [TF, Over.mk_hom, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hw : b.left ≫ D.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫
      spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    rw [Over.w b, ← hTF]; rfl
  let l := hφ.1.lift b.left (spMap (algebraMap ℂ (DualNumber ℂ))) hw
  have hl1 : l ≫ φ = b.left := hφ.1.lift_fst _ _ _
  have hl2 : l ≫ x.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := hφ.1.lift_snd _ _ _
  refine ⟨Over.homMk l hl2, ?_, hl1⟩
  show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ l = eSec x.P.A
  apply hφ.1.hom_ext
  · rw [Category.assoc, hl1, he]
    change redE ℂ ≫ b.left = _
    rw [hb, DegPre.zeroF, Over.comp_left, ← hTF]
    congr 1
  · rw [Category.assoc, hl2]
    have h1 : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := by
      simp only [eSec]
      rw [Over.w η[x.P.A]]; rfl
    rw [h1]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]; rfl

end GlobalTheory.MBLow.Cl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointOverOriginLiftsTangentVectorUniformisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualPointOverOrigin_lifts_tangentVector_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left), IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ →
    eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A →
    ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left →
      ∃ b' : epsR ℂ ⟶ x.P.A, IsTangent b' ∧ b'.left ≫ φ = b.left := by
  first | exact @GlobalTheory.MBLow.Cl.tangent_lift_of_pullback | exact GlobalTheory.MBLow.Cl.tangent_lift_of_pullback | (intros; apply GlobalTheory.MBLow.Cl.tangent_lift_of_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

def frW {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} (w : LB.Iso x.P.L (M.pull φ)) {g : ℕ}
    (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z).left)).val *
    u.fr (FrameValue.chartAt x.P.isLB (u.ex z).left) z

variable {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} {w : LB.Iso x.P.L (M.pull φ)} {g : ℕ}

theorem frW_eq (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (k : x.P.L.ι)
    (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U k) :
    frW w u j z = valAt' (u.ex z).left _ (w.s (fun _ => j, k)).val * u.fr k z := by
  unfold frW
  have hi := le_chartAt x.P.isLB (u.ex z).left
  rw [u.fr_compat _ k z ((le_preimage_inf _ _ _).2 ⟨hi, hk⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr k z) (GlobalTheory.Ex.Arch.FibEx.val_iso _ (pull_isLB hM φ) hw _ _ _
    ((le_preimage_wchart _ _ _ _).2 fun _ => hj) hi hk)

theorem frW_ne (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u j z ≠ 0 := by
  have hi := le_chartAt x.P.isLB (u.ex z).left
  exact mul_ne_zero (val_unit_ne_zero _ valueRules
    ((le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩) _) (u.fr_ne _ _ hi)

theorem frW_compat (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (i j : M.ι) (z : Fin g → ℂ)
    (hi : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U i) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u i z = valAt' ((u.ex z).left ≫ φ) (M.U i ⊓ M.U j) (M.g i j).val * frW w u j z := by
  unfold frW
  rw [← _root_.mul_assoc]
  exact congrArg (· * _) (GlobalTheory.Ex.Arch.val_iso_chart x.P.isLB hw _ i j _ hi hj (le_chartAt x.P.isLB (u.ex z).left))

theorem frW_hol (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) :
    DifferentiableOn ℂ (frW w u j) {z | ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j} := by
  intro z₀ hz₀
  have hk := le_chartAt x.P.isLB (u.ex z₀).left
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (((M.pull φ).div x.P.L).U (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hz₀, hk⟩
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₂.differentiableAt n₂).fun_mul ((u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds hk))
  refine (d.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  exact frW_eq hM hw u j z _ ((le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit) h₂

theorem valAt'_appLE_comp {X X' : Scheme.{0}} (p : Sp ℂ ⟶ X) (f : X ⟶ X') (U : X'.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (hV : ⊤ ≤ p ⁻¹ᵁ V) (s : Γ(X', U)) : valAt' p V ((f.appLE U V h).hom s) = valAt' (p ≫ f) U s := by
  show valAt' p V (resG X h ((f.app U).hom s)) = _
  rw [valAt'_res _ h _ hV, valAt'_comp]

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem eq_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (F : DualNumber A →+* DualNumber B)
    (h1 : ∀ a, F (algebraMap A _ a) = algebraMap B _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) : F = dualMap f := by
  refine RingHom.ext fun z => ?_
  have hz : z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz, map_add (f := _), map_mul, h1, h1, h2]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl, dualMap]

theorem eu_gen (x : KeyIn ℂ) (g : ℕ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) :
    ∀ w, IsTangent w → ∃! W, u.IsDiff W w := by
  subst hg
  exact (GlobalTheory.LamT.existsUnique_isDiff_and_linear x u).1

theorem one_left {S : Scheme.{0}} (X : Over S) [GrpObj X] : (1 : 𝟙_ (Over S) ⟶ X).left = eSec X := by
  have : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [this]; rfl

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue GlobalTheory.MBLow.Cl.GeoOne

theorem exists_ab_geo_of_nf : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  intro R _ _ _ _ D hψ hτ _ N ν y hyP hrig hth x hg hy u τ a b c W hpb hnf
  obtain ⟨P, gpos, rig, rig_gen, th, th_ne, v, basis⟩ := y
  subst hyP
  cases hrig
  obtain ⟨th', hth', hνth⟩ := hth
  cases hth'
  obtain ⟨φ, he, w, hg', F, hφ, hw, hrigm, hthm, hF1, hF2, hv⟩ := hpb
  have hnf' := hnf
  obtain ⟨hs, hp, ha, hb, hc, hΛ, hrigu, hfn, hdiff⟩ := hnf'
  obtain ⟨e, he'⟩ := LiePull.exists_pushEquiv hφ (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom
    (by rw [tf_hom]; exact (Category.id_comp _).symm)
  have hJ := ν.good
  have hex0 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h0 : (u.ex 0).left ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A := by rw [hex0, one_left]; exact he
  have hrg0 : frW w u (ν.J (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)) 0 = ν.rg := by
    unfold NumOf.rg vF
    rw [tf_hom]
    exact GlobalTheory.T.uniformisedFibre_frame_at_origin_eq_rigidification R D x φ he w hw hrigm _ u hrigu _ _ (le_chartAt _ _) (hJ _)
  have hrgne : ν.rg ≠ 0 := by
    rw [← hrg0]
    refine frW_ne u _ 0 ?_
    rw [h0]; exact hJ _
  have hthz : ∀ z, sF ν.th ((u.ex z).left ≫ φ) ν.J =
      c * thetaChar τ a b z * frW w u (ν.J ((u.ex z).left ≫ φ)) z := by
    intro z
    have hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := hJ _
    have hle : (D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) fun _ => ν.J ((u.ex z).left ≫ φ)) ≤
        D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := fun q hq => Set.mem_iInter.1 hq 0
    have e0 : sF ν.th ((u.ex z).left ≫ φ) ν.J = valAt' ((u.ex z).left ≫ φ) _ (resG _ hle (th.f (ν.J ((u.ex z).left ≫ φ)))) := by
      rw [← hνth _ hle]; rfl
    rw [e0, valAt'_res _ hle _ ((le_preimage_wchart _ _ _ _).2 fun _ => by rw [Category.comp_id]; exact hj)]
    have hk := le_chartAt x.P.isLB (u.ex z).left
    have hV : ((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓ x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left) ≤
        φ ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := inf_le_left.trans (LB.wchart_le _ _ _ PUnit.unit)
    have hpV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓
        x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left)) :=
      (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hk⟩
    have hm := congrArg (valAt' (u.ex z).left _) (hthm (fun _ => ν.J ((u.ex z).left ≫ φ)) _ hV)
    rw [valAt'_appLE_comp _ _ _ _ hV hpV, valAt'_mul, valAt'_res _ _ _ hpV, hfn _ z hk] at hm
    dsimp only at hm
    rw [hm]
    unfold frW
    have key : ∀ A B C E : ℂ, A = B → A * (C * E) = C * (B * E) := by intros; subst_vars; ring
    exact key _ _ _ _ rfl
  let d : AB N.toNumB D.P.g :=
    { τ := τ, a := a, b := b, c := c, symm := hs, pos := hp, ha := ha, hb := hb, hc := hc
      ex := fun z => ν.eA.symm (e (u.ex z))
      ex_add := fun z w => by simp only [u.ex_add, map_mul]
      onto := fun q => by
        obtain ⟨p, hp⟩ := e.surjective (ν.eA q)
        obtain ⟨z, rfl⟩ := u.ex_onto p
        exact ⟨z, show ν.eA.symm (e (u.ex z)) = q by rw [hp, MulEquiv.symm_apply_apply]⟩
      ker := fun z => by
        rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, u.ker, hΛ]
      fr := fun z => Units.mk0 (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) (div_ne_zero (frW_ne u _ z (hJ _)) hrgne)
      fr_zero := by
        ext
        rw [Units.val_mk0, Units.val_one, h0, hrg0, div_self hrgne]
      fr_per := fun M N z => by
        simp only [Units.val_mk0]
        have hl : u.ex (z + perV τ M N) = u.ex z := by
          rw [u.ex_add, (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩), _root_.mul_one]
        unfold frW
        rw [hl, frame_eq_autV_mul _ x hg u τ a b c W hnf M N _ z (le_chartAt _ _)]
        ring
      th := fun z => by
        have h1 := ν.th_eq (ν.eA.symm (e (u.ex z)))
        rw [MulEquiv.apply_symm_apply, he'] at h1
        change N.th _ * ν.rg = _ at h1
        rw [hthz z] at h1
        rw [Units.val_mk0]
        field_simp
        exact h1 }
  have hE : ∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ := fun z => by
    show (ν.eA (ν.eA.symm (e (u.ex z)))).left = _
    rw [MulEquiv.apply_symm_apply, he']
  refine ⟨d, ⟨fun i z => frW w u i z, GlobalTheory.T.holomorphic_functionValues_classicalUniformisation R D N ν _ d x u φ hφ hE, fun i => ?_, fun i j z h => ?_, fun z => ?_,
    fun bb hbb => ?_⟩, rfl, ?_⟩
  · simp only [hE]
    exact frW_hol D.P.isLB hw u i
  · rw [hE] at h ⊢
    exact frW_compat hw u i j z ((le_preimage_inf _ _ _).1 h).1 ((le_preimage_inf _ _ _).1 h).2
  · rw [hE]
    show (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) * ν.rg = _
    exact div_mul_cancel₀ _ hrgne
  · obtain ⟨b', hb't, hb'⟩ := GlobalTheory.T.dualPointOverOrigin_lifts_tangentVector_uniformised R D x φ hφ he bb hbb
    obtain ⟨W', hW', -⟩ := eu_gen x _ hg u b' hb't
    exact ⟨W', (GlobalTheory.T.holomorphic_uniformization_complex_base_change R D N ν _ d x u φ hφ hE b' bb hb't hb' W').2 hW'⟩
  · intro vB hvB i bb hbb W'
    have hvi : v i = vB i := by
      have := eq_of_heq (hvB i)
      rwa [Fin.cast_eq_self] at this
    have hF : F = dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := eq_dualMap _ F hF1 hF2
    have hb' : (x.v (i.cast hg.symm)).left ≫ φ = bb.left := by
      rw [hv, hbb, hF, ← hvi]
      rfl
    rw [GlobalTheory.T.holomorphic_uniformization_complex_base_change R D N ν _ d x u φ hφ hE _ bb (x.basis.1 _) hb' W']
    obtain ⟨W0, -, huniq⟩ := eu_gen x _ hg u _ (x.basis.1 (i.cast hg.symm))
    constructor
    · intro h
      exact (huniq _ h).trans (huniq _ (hdiff i)).symm
    · rintro rfl
      exact hdiff i

end GlobalTheory.MBLow.Cl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classical_abelianPart_values_of_normalForm : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  exact @GlobalTheory.MBLow.Cl.exists_ab_geo_of_nf
end

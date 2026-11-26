module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Famproj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsProductRefinement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnits
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchAtEachComponent
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSncModelOfPatches
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ObjAt

theorem exists_obj_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (f : X ⟶ Y.X) (t : SAB H X) (_ : SABMap t Y.t f) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (x : Sp Ω ⟶ Xo.XF c), ξ ≫ f = x ≫ Y.j → ∃ (s : Sp Ω ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), Nonempty (SABMap o.t t ξ) := by
  intro E _ _ _ H D l Xo c O _ β Y X f t h Ω _ ξ x hx
  obtain ⟨o, ⟨mP⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l)
    (RingHom.id _) _ _ _ (x ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) x rfl rfl (by rw [show spMap (RingHom.id (KA l)) = 𝟙 (Sp (KA l)) by simp [spMap], Category.comp_id]) Y.oF
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t o.t Y.j x Y.m mP.toSABMap
  have n' : SABMap o.t Y.t (ξ ≫ f) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n hx.symm
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t t o.t f ξ h n'
  exact ⟨_, o, ⟨k⟩⟩

end GlobalTheory.CompanionTheory.Ar.ObjAt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_point_object : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (f : X ⟶ Y.X) (t : SAB H X) (_ : SABMap t Y.t f) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (x : Sp Ω ⟶ Xo.XF c), ξ ≫ f = x ≫ Y.j → ∃ (s : Sp Ω ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), Nonempty (SABMap o.t t ξ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at | exact GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at | (intros; apply GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsAbLift {R : Type} [CommRing R] {t : SAB H (Sp R)} {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)}
    {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : FamExp t.G M B ψ) (b : Fin n → ℂ)
    (P : AbPart t (spMap (ψ b))) {A : Over (Sp ℂ)} [GrpObj A] (φ : A.left ⟶ P.tB.G.left) {Lb : LB A.left} {g' : ℕ}
    (u : HolUnif A Lb g') (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) : Prop :=
  ∀ (y : Fin g → ℂ) (s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G), s.left ≫ P.m.φ = (e.ex b y).left →
    (u.ex (ℓ y)).left ≫ φ = (s ≫ P.τ.q ≫ P.e.hom).left

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeUpper
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeUpper
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem family_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → HTFree 𝔐 p → (∀ s, Module.Projective (chartRing o (mseg y) s.1) (Dc s).om' ∧ ∀ σ : E →+* Ω, Module.Projective (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) ∧ (∀ σ : E →+* Ω, ∃ d : Ω, ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ ds : chartRing o (mseg y) s.1, (ds : Ω) = d ∧ GeneratesDiff σ ds) ∧ ∃ κ : Ω, IsCp p κ ∧ ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, κ ∈ chartRing o (mseg y) s.1 :=
  @PositivityTheory.HtPt.Famproj.family_proj

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeUpperStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_free_flag_lattice_upper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → HTFree 𝔐 p → (∀ s, Module.Projective (chartRing o (mseg y) s.1) (Dc s).om' ∧ ∀ σ : E →+* Ω, Module.Projective (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) ∧ (∀ σ : E →+* Ω, ∃ d : Ω, ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ ds : chartRing o (mseg y) s.1, (ds : Ω) = d ∧ GeneratesDiff σ ds) ∧ ∃ κ : Ω, IsCp p κ ∧ ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, κ ∈ chartRing o (mseg y) s.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.family_proj | exact GlobalTheory.CompanionTheory.Ar.HT.family_proj | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.family_proj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackIff
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgePullBack

theorem hodgeInnerProduct_iff_of_abelianSchemeMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0})
    (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (z : Sp ℂ ⟶ S') (v' w' : epsAt z ⟶ t'.G)
    (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v'.left ≫ m.φ = v.left → w'.left ≫ m.φ = w.left →
      (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) :=
  fun E _ _ _ H S S' t t' f m z v' w' v w c hv hw =>
    hodgeInnerProduct_tripleMap_iff E H S t S' t' f m z v' w' v w c hv.symm hw.symm

end GlobalTheory.CompanionTheory.Ar.HodgePullBack
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_pullback_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (z : Sp ℂ ⟶ S') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v'.left ≫ m.φ = v.left → w'.left ≫ m.φ = w.left → (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap | exact GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RiemGram

theorem hodgeForm_of_isHodgeGram {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {x : Sp ℂ ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} {Γ : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsLB) (hv : ∀ i, IsTanAt G x (v i))
    (h : Fl.IsHodgeGram G L x v Γ) (i j : Fin n) : HodgeForm G L x (v i) (v j) (Γ i j) := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := h
  have hM : (L.pull ψ).IsLB := LB.isLB_pull hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨hL, hv i, hv j, Q.A, inferInstance, ψ, Q.g, TorsionTauCompare.transport Q.isLB hM hw u, Hm, χ, v' i, v' j,
    W i, W j, hp, TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH, (hvW i).1, (hvW j).1, (hvW i).2, (hvW j).2,
    hΓ i j⟩

theorem isTanAt_value {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {Ei : Type} [AddCommGroup Ei] [Module R Ei]
    (M : LieModel G (𝟙 (Sp R)) Ei) (f : R →+* ℂ) (e : Ei) (v : epsAt (spMap f) ⟶ G)
    (hv : v.left = spMap (dualMap f) ≫ (M.pt e).left) : IsTanAt G (spMap f) v := by
  have ht := M.tan e
  unfold IsTanAt at ht ⊢
  have hsq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    simp [dualMap]
  rw [hv, ← Category.assoc, hsq, Category.assoc, ht]
  let F : Over.mk (spMap f) ⟶ Over.mk (𝟙 (Sp R)) := Over.homMk (spMap f) (by simp)
  have h1 : F ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := MonObj.comp_one _
  exact congrArg CommaMorphism.left h1

theorem exists_value {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {Ei : Type} [AddCommGroup Ei] [Module R Ei]
    (M : LieModel G (𝟙 (Sp R)) Ei) (f : R →+* ℂ) (e : Ei) :
    ∃ v : epsAt (spMap f) ⟶ G, v.left = spMap (dualMap f) ≫ (M.pt e).left := by
  have hsq : spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨Over.homMk (spMap (dualMap f) ≫ (M.pt e).left) ?_, rfl⟩
  have hw := Over.w (M.pt e)
  show (spMap (dualMap f) ≫ (M.pt e).left) ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap f
  rw [Category.assoc, hw, ← hsq]
  simp

theorem gramAt_of_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (h : Sp C.R ⟶ X) (m : SABMap C.t t h) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (N : ℕ) (b : Fin N → Li) (x : Fin N → Fin C.g → C.R) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (w : Fin N → (epsAt (spMap (C.ψ z) ≫ h) ⟶ t.G)), C.IsRiem z Hm → (∀ k, M.ValAt _ (b k) (w k)) → (∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ m.φ) → M.GramAt t.PP.L (spMap (C.ψ z) ≫ h) b (Matrix.of fun i j => (Real.pi : ℂ) * ((fun e => C.ψ z (x j e)) ⬝ᵥ Hm *ᵥ star (fun e => C.ψ z (x i e)))) := by
  intro E _ _ _ H D l Xo σ n a C X t h m Ω _ ξ Li _ _ M N b x z Hm w hR hval hw
  choose v hv using fun k => exists_value C.M (C.ψ z) (x k)
  have hG := (hR N x v (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (fun e => C.ψ z (x i e))
    (fun e => C.ψ z (x j e))) hv).2 fun _ _ => rfl
  have hF := hodgeForm_of_isHodgeGram C.t.PP.isLB (fun k => isTanAt_value C.M (C.ψ z) (x k) (v k) (hv k)) hG
  have e : ∀ k, (w k).left = (v k).left ≫ m.φ := fun k => by rw [hw k, hv k, Category.assoc]
  exact ⟨w, hval, fun p q => (GlobalTheory.T.hodge_inner_product_map_iff E H X t (Sp C.R) C.t h m (spMap (C.ψ z)) (v p) (v q) (w p) (w q) _
    (e p) (e q)).1 (hodgeInnerProduct_iff_hodgeForm.2 (hF q p))⟩

end GlobalTheory.CompanionTheory.Ar.RiemGram
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (h : Sp C.R ⟶ X) (m : SABMap C.t t h) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (N : ℕ) (b : Fin N → Li) (x : Fin N → Fin C.g → C.R) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (w : Fin N → (epsAt (spMap (C.ψ z) ≫ h) ⟶ t.G)), C.IsRiem z Hm → (∀ k, M.ValAt _ (b k) (w k)) → (∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ m.φ) → M.GramAt t.PP.L (spMap (C.ψ z) ≫ h) b (Matrix.of fun i j => (Real.pi : ℂ) * ((fun e => C.ψ z (x j e)) ⬝ᵥ Hm *ᵥ star (fun e => C.ψ z (x i e)))) := by
  intro E _ _ _ H D l Xo σ n a C X t h m Ω _ ξ Li _ _ M N b x z Hm w hR hval hw
  exact GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem E H D l Xo σ n a C X t h m Ω ξ Li M N b x z Hm w hR hval hw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothOpenImmersionRange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothOpenImmersionRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem smoothOfRelativeDimension_opensRange_ι_comp
    (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ)
    (h : SmoothOfRelativeDimension n (j ≫ g)) :
    SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  have e : j.opensRange.ι = j.isoOpensRange.inv ≫ j :=
    (Iso.eq_inv_comp _).mpr j.isoOpensRange_hom_ι
  rw [e, Category.assoc, ← zero_add n]
  exact smoothOfRelativeDimension_comp 0 n _ _

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothOpenImmersionRangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_open_immersion_range : ∀ (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ), SmoothOfRelativeDimension n (j ≫ g) → SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | exact GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_model_of_res (hRes : ResK.ResKStatement)
    (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (hp : IsProjOver s)
    (hn : Tor.IsNormalScheme P) (U : (pullback s (spMap (algebraMap (𝓞 F) F))).Opens) (hd : Dense (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))) (e : ℕ)
    (hU : SmoothOfRelativeDimension e (U.ι ≫ pullback.snd s (spMap (algebraMap (𝓞 F) F))))
    (Ab : Set P) (hAb : pullback.fst s (spMap (algebraMap (𝓞 F) F)) ⁻¹' Ab = U)
    (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P) (hξ₀ : IsCptGen ξ₀) :
    ∃ (N : ℕ) (x : Fin (N + 1) → Ω) (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (f : X ⟶ P)
      (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))),
      (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ x ∧ ξ ≫ f = ξ₀ ∧
      Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧
      ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w →
        (w ∈ mcPts bd ↔ f (centre z) ∉ Ab) := by
  obtain ⟨hred, hln, M, i, hi, his⟩ := GlobalTheory.T.generic_fibre_projective_embedding F P s hp hn
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre F P s Ω ξ₀ hξ₀
  have hmem := GlobalTheory.T.generic_point_mem_dense_open _ Ω ξF U hFg hd
  have hin : ResK.IsResInput M i U e := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  obtain ⟨r, X', j, f', hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes F M e _ i U hin
  letI algF : Algebra F Ω := b.toAlgebra
  letI algO : Algebra (𝓞 F) Ω := (b.comp (algebraMap (𝓞 F) F)).toAlgebra
  haveI : IsScalarTower (𝓞 F) F Ω := .of_algebraMap_eq' rfl
  have hs0 : ξ₀ ≫ s = spMap (algebraMap (𝓞 F) Ω) := by
    rw [← hF1, Category.assoc, pullback.condition, ← Category.assoc, hF2]
    show _ = Spec.map (CommRingCat.ofHom (b.comp (algebraMap (𝓞 F) F)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨nu, u, hu⟩ := GlobalTheory.T.projective_over_coords_exist (𝓞 F) P s hp Ω ξ₀ hξ₀ hs0
  have hproj : IsProjOver (f' ≫ i ≫ PSpace.str F M) := by
    have := GlobalTheory.T.closed_in_product_projective F M r X' j hj
    rwa [← Category.assoc, ← hfj, Category.assoc] at this
  have hdom := GlobalTheory.T.smooth_scheme_stalks_domains F e X' _ hsm
  obtain ⟨ξ', h1, hξ'⟩ := GlobalTheory.T.generic_point_lift_along_iso _ X' f' U Ω ξF hiso hmem hFg hdom
  have hξs : ξ' ≫ f' ≫ i ≫ PSpace.str F M = spMap (algebraMap F Ω) := by
    rw [← Category.assoc, h1, his, hF2]
  obtain ⟨nx, x2, hx2⟩ := GlobalTheory.T.projective_over_coords_exist F X' _ hproj Ω ξ' hξ' hξs
  have hg : ξ' ≫ (f' ≫ pullback.fst _ _) = ξ₀ := by rw [← Category.assoc, h1, hF1]
  have hbase := GlobalTheory.T.every_component_in_some_chart X' P Ω ξ' ξ₀ _ (𝓞 F) _ u hu hg
  obtain ⟨n, ht⟩ := GlobalTheory.T.coords_product_refinement X' Ω ξ' F _ _ x2 u hx2 hbase
  obtain ⟨c₀, hc₀, hfrac⟩ := GlobalTheory.T.coords_generate_function_field (𝓞 F) F Ω X' ξ' _ _ ht
  obtain ⟨X, ξ, sX, htX, hirr, -, -, -⟩ := GlobalTheory.T.exists_proper_integral_model Ω (𝓞 F) _ _ c₀ hc₀ hfrac
  have hreg : ∀ (a : 𝓞 F) (p : Cpt ξ), (RingHom.id Ω) (algebraMap (𝓞 F) Ω a) ∈ regAt ξ p := by
    intro a p
    obtain ⟨c, hc⟩ := htX.cover p
    exact (htX.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p hc
  have hchart : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun k => (RingHom.id Ω) (u k)) c p := by
    intro p
    obtain ⟨⟨q1, q2, q3⟩, h0, hc⟩ := htX.cover p
    have hne := h0
    simp only [mul_ne_zero_iff] at hne
    refine ⟨q3, hne.2, fun c' => ?_⟩
    have := hc ⟨q1, q2, c'⟩
    have e1 : ((∏ a, x2 (q1 a)) * x2 q2 * u c') / ((∏ a, x2 (q1 a)) * x2 q2 * u q3) = u c' / u q3 := by
      field_simp [hne.1.1, hne.1.2, hne.2]
    simpa [e1] using this
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular P Ω ξ₀ (𝓞 F) _ u X Ω ξ (RingHom.id Ω) hu htX.gen hirr hreg hchart
  have hf' : ξ ≫ f = ξ₀ := by
    have : ξ ≫ f = _ := hf
    rw [this]; simp
  obtain ⟨N, x, hx⟩ := GlobalTheory.T.coord_over_int_of_finite_order X Ω ξ (𝓞 F) _ _ htX
  obtain ⟨R1, R2⟩ := GlobalTheory.T.coord_charts_match_regular (𝓞 F) F Ω X X' ξ ξ' _ _ htX ht
  have hchar := GlobalTheory.T.char_zero_iff_nonzero_units F Ω X ξ _ _ htX
  have hFreg : ∀ (a : F) (p' : Cpt ξ'), algebraMap F Ω a ∈ regAt ξ' p' := by
    intro a p'
    obtain ⟨c, hc⟩ := ht.cover p'
    exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p' hc
  have hunit : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → Char0 ξ p := by
    intro p p' h
    refine (hchar p).2 fun d hd0 => ?_
    have hd1 : (algebraMap (𝓞 F) F d) ≠ 0 := by simpa using hd0
    have e1 : algebraMap (𝓞 F) Ω d = algebraMap F Ω (algebraMap (𝓞 F) F d) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact (map_ne_zero _).2 hd1
    · rw [h, e1]; exact hFreg _ p'
    · rw [h, e1, ← map_inv₀]; exact hFreg _ p'
  have hPts : Pts ξ = Set.range (regAt ξ') := by
    ext R
    constructor
    · rintro ⟨p, hp0, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', h.symm⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, hunit p p' h, h.symm⟩
  let B : Set (Cpt ξ) := {p | Char0 ξ p ∧ f p.1 ∉ Ab}
  let T : Set X' := f'.base ⁻¹' (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))ᶜ
  have hgen : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → (f p.1 ∉ Ab ↔ p'.1 ∈ T) := by
    intro p p' h
    have e1 : f p.1 = (f' ≫ pullback.fst _ _) p'.1 :=
      GlobalTheory.T.regular_rings_equal_images_equal P X X' Ω ξ₀ ξ ξ' f _ (𝓞 F) _ u hu htX.gen hξ' hf' hg p p' h
    have e2 : ((f' ≫ pullback.fst s (spMap (algebraMap (𝓞 F) F))) p'.1 ∈ Ab) ↔ f' p'.1 ∈ (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0}))) := by
      rw [← hAb]; simp
    rw [e1, e2]; rfl
  have hBd : regAt ξ '' B = regAt ξ' '' {p | p.1 ∈ T} := by
    ext R
    constructor
    · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', (hgen p p' h).1 hp1, h.symm⟩
    · rintro ⟨p', hp', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, ⟨hunit p p' h, (hgen p p' h).2 hp'⟩, h⟩
  have hpatch := GlobalTheory.T.snc_patch_at_each_component F X' _ e T Ω ξ' hξ' hξs hsm hsnc (GlobalTheory.T.regular_ring_determines_component X' Ω ξ' F _ _ ht)
  obtain ⟨bd, hm, hc⟩ := GlobalTheory.T.exists_snc_model_of_patches Ω X ξ N x e B hx (fun p hp => hp.1) (by
    intro p hp0
    obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
    rw [hPts, hBd, h]
    exact hpatch p')
  refine ⟨N, x, X, ξ, f, bd, hirr, hx, hf', hm, fun z w hw => ?_⟩
  rw [hc z w hw]
  constructor
  · rintro ⟨h, -, h2⟩
    exact h2
  · intro h
    exact ⟨hirr _, GlobalTheory.T.char_zero_centre_of_complex Ω X ξ z _ htX.gen, h⟩

theorem exists_sncBase : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Spec (CommRingCat.of Ω) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (bd : Ideal (MRing J)), Nonempty K ∧ (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  intro hRes E _ _ _ H D l Xo c Y Ω _ _ ξ₀ hξ₀
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hU : SmoothOfRelativeDimension D.dim (Y.jQ.opensRange.ι ≫ pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    apply GlobalTheory.T.smooth_open_immersion_range _ _ _ Y.jQ
    rw [Y.jQ_over]
    exact hsm
  obtain ⟨N, x, X, ξ, f, bd, hirr, hx, hf, hm, hc⟩ := exists_model_of_res hRes c.F Y.X Y.s Y.proj Y.normal Y.jQ.opensRange
    (by simpa using Y.jQ_dense) D.dim hU (abLocus Y.t.G) (by simpa using Y.ab_gen) Ω ξ₀ hξ₀
  exact ⟨Unit, inferInstance, fun _ => Fin (N + 1), fun _ => inferInstance, fun p => x p.2, X, ξ, f, bd, inferInstance,
    hirr, GlobalTheory.T.coords_single_block_segre X Ω ξ N x hx, hf, hm, hc⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coords_of_generic_point : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Spec (CommRingCat.of Ω) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (bd : Ideal (MRing J)), Nonempty K ∧ (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiff
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {σ k : Type} [CommRing k] (j : ℕ) (q a : MvPolynomial σ k)
    (ha : ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff a e = 0) :
    ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff (q * a) e = 0 := by
  classical
  intro e he
  rw [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h2 : x.2.degree ≤ e.degree := by
    rw [← hx, map_add (f := _)]; exact Nat.le_add_left _ _
  rw [ha x.2 (lt_of_le_of_lt h2 he), mul_zero]

private theorem coeff_eq_zero_of_mem_span_X_pow_of_degree_lt {σ k : Type} [CommRing k] :
    ∀ (j : ℕ) (P : MvPolynomial σ k), P ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ j →
      ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff P e = 0 := by
  classical
  intro j
  induction j with
  | zero => intro P _ e he; exact absurd he (Nat.not_lt_zero _)
  | succ j ih =>
    let K : Ideal (MvPolynomial σ k) :=
      { carrier := {P | ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff P e = 0}
        add_mem' := fun {a b} ha hb e he => by rw [MvPolynomial.coeff_add, ha e he, hb e he, add_zero]
        zero_mem' := fun e _ => by simp
        smul_mem' := fun c a ha => coeff_mul_eq_zero_of_order_two_of_degree_le_two (j + 1) c a ha }
    have hle : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ (j + 1) ≤ K := by
      rw [pow_succ, Ideal.mul_le]
      intro r hr s hs
      refine Submodule.span_induction (p := fun s _ => r * s ∈ K) ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨i, rfl⟩
        show ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff (r * MvPolynomial.X i) e = 0
        intro e he
        rw [MvPolynomial.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [MvPolynomial.coeff_X']
        split_ifs with hxi
        · have hx1 : x.1.degree + 1 = e.degree := by
            rw [← hx, map_add (f := _), ← hxi, Finsupp.degree_single]
          rw [ih r hr x.1 (by omega), zero_mul]
        · rw [mul_zero]
      · rw [mul_zero]; exact K.zero_mem
      · intro a b _ _ ha hb; rw [mul_add]; exact K.add_mem ha hb
      · intro c a _ ha; rw [smul_eq_mul, mul_left_comm]; exact K.mul_mem_left c ha
    exact fun P hP => hle hP

theorem pderiv_eq_zero_of_jet_pow_sub : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv (R := k) q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv (R := k) q F = 0 := by
  intro k _ p _ _ d F f hf hF q
  classical
  ext e
  obtain ⟨v, hv⟩ := hF (e.degree + 1)
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hmem : psTrunc (e.degree + 1) F + psTrunc (e.degree + 1) f - P ^ p ∈
      orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), map_pow]
    have h1 : psJet (e.degree + 1) F =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) F) := rfl
    have h2 : psJet (e.degree + 1) f =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) f) := rfl
    rw [← h1, ← h2, hv]; ring
  have hdeg : (e + Finsupp.single q 1).degree < e.degree + 1 + 1 := by
    rw [map_add (f := _), Finsupp.degree_single]; omega
  have hz := coeff_eq_zero_of_mem_span_X_pow_of_degree_lt (e.degree + 1 + 1) _ hmem (e + Finsupp.single q 1) hdeg
  have hbd : ∀ i, (e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i ≤ (e + Finsupp.single q 1).degree := by
    intro i
    exact Finsupp.le_degree i _
  have hin : e + Finsupp.single q 1 ∈ degLE (e.degree + 1) := by
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · refine ⟨fun i => ⟨(e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i, ?_⟩, ?_⟩
      · have := hbd i
        rw [map_add (f := _), Finsupp.degree_single] at this
        omega
      · ext i; simp
    · show (e + Finsupp.single q 1).degree ≤ e.degree + 1
      rw [map_add (f := _), Finsupp.degree_single]
  have htr : ∀ g : MvPowerSeries (Fin 1 × Fin d) k,
      AddMonoidAlgebra.coeff (psTrunc (e.degree + 1) g) (e + Finsupp.single q 1) =
        MvPowerSeries.coeff (e + Finsupp.single q 1) g := by
    intro g
    simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hin]
  have hpow : MvPowerSeries.pderiv (R := k) q ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k) = 0 := by
    rw [MvPolynomial.coe_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have hG : MvPowerSeries.pderiv (R := k) q F = MvPowerSeries.pderiv (R := k) q
      (F + f - ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k)) := by
    rw [map_sub, map_add (f := _), hf q, hpow, add_zero, sub_zero]
  rw [hG, MvPowerSeries.coeff_pderiv, map_zero, map_sub, map_add (f := _), MvPolynomial.coeff_coe, ← htr F, ← htr f,
    ← MvPolynomial.coeff_add, ← MvPolynomial.coeff_sub, hz, zero_mul]

end GlobalTheory.CompanionTheory.Ar.Coc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pderiv_zero_of_jet_pth_power_diff : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv (R := k) q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv (R := k) q F = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub | exact GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFirst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgLie

section Modules

theorem mem_of_mem_iSup {Ω E I : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (A : Subring Ω)
    (W : I → Submodule Ω E) (hW : iSupIndep W) (N : I → Submodule A E) (hN : ∀ s, ∀ x ∈ N s, x ∈ W s)
    {e : E} (s₀ : I) (he : e ∈ ⨆ s, N s) (hs : e ∈ W s₀) : e ∈ N s₀ := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp N e).1 he
  have hsum : (f.sum fun _ x => x) - f s₀ = ∑ i ∈ f.support.erase s₀, f i := by
    by_cases h0 : s₀ ∈ f.support
    · rw [Finsupp.sum, ← Finset.add_sum_erase _ _ h0]
      abel
    · rw [Finsupp.sum, Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0, sub_zero]
  have h1 : (f.sum fun _ x => x) - f s₀ ∈ W s₀ := sub_mem hs (hN _ _ (hf s₀))
  have h2 : (f.sum fun _ x => x) - f s₀ ∈ ⨆ (k) (_ : k ≠ s₀), W k := by
    rw [hsum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hk) (hN _ _ (hf k)))
  have h3 := (Submodule.disjoint_def.1 (hW s₀)) _ h1 h2
  rw [sub_eq_zero.1 h3]
  exact hf s₀

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (e : E) : e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

end Modules

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

theorem not_inFibre_push {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀}
    {i : Ω₀ →+* Ω} (hξ : IsCptGen ξ) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i) (q : Cpt ξ) {r : ℕ}
    (hq : ¬ InFibre ξ r q) : ¬ InFibre ξ₀ r (pushCpt hd q) := by
  intro hf
  apply hf
  obtain ⟨h0, -, s, hs⟩ : unitAt ξ q (r : Ω) := not_not.1 hq
  have hmul : (r : X.presheaf.stalk q.1) * s = 1 := hξ.inj q (by
    rw [map_mul, map_one, map_natCast, hs]
    exact mul_inv_cancel₀ h0)
  have hu : IsUnit (r : X.presheaf.stalk q.1) := IsUnit.of_mul_eq_one _ hmul
  have hu₀ : IsUnit (r : X₀.presheaf.stalk (h q.1)) :=
    isUnit_of_map_unit (h.stalkMap q.1).hom _ (by rwa [map_natCast])
  have h0' : (r : Ω₀) ≠ 0 := fun e => h0 (by rw [← map_natCast i, e, map_zero])
  refine ⟨h0', ⟨_, map_natCast (genMap ξ₀ (pushCpt hd q)) r⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu₀
  refine ⟨(u⁻¹ : (X₀.presheaf.stalk (h q.1))ˣ).val, ?_⟩
  have e1 : genMap ξ₀ (pushCpt hd q) u.val = (r : Ω₀) := (congrArg _ hu').trans (map_natCast _ r)
  exact (map_units_inv (genMap ξ₀ (pushCpt hd q)) u).trans (congrArg Inv.inv e1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_inj_of_pull {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) {ξ : Spec (CommRingCat.of Ω) ⟶ S'} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G' ξ V) {e e' : V}
    (h : (M.pt e).left ≫ φ = (M.pt e').left ≫ φ) : e = e' :=
  M.inj (Over.OverMorphism.ext (hG.1.hom_ext h ((Over.w _).trans (Over.w _).symm)))

theorem exists_value_up {t : SAB H X₀} {t' : SAB H X} {f : X ⟶ X₀} (m : SABMap t' t f)
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {i : Ω₀ →+* Ω}
    (hall : ∀ q : X, genPt ξ ⤳ q) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) {V V' : Type} [AddCommGroup V] [Module Ω₀ V]
    [AddCommGroup V'] [Module Ω V'] {M : LieModel t.G ξ₀ V} {M' : LieModel t'.G ξ V'} {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) {e : V} {v₀ : epsAt (z ≫ f) ⟶ t.G} (hv : M.ValAt (z ≫ f) e v₀) :
    ∃ v : epsAt z ⟶ t'.G, M'.ValAt z (j e) v ∧ v₀.left = v.left ≫ m.φ := by
  obtain ⟨h₀, w, hw, hwz⟩ := hv
  have hp : genPt ξ₀ ⤳ f (centre z) := h₀
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap (centre z)).hom) ≫ X₀.fromSpecStalk (f (centre z)) =
      X.fromSpecStalk (centre z) ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ ⟨centre z, hall _⟩).comp (f.stalkMap (centre z)).hom = i.comp (genMap ξ₀ ⟨f (centre z), hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd _ (hall _) hp)
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨centre z, hall _⟩
  obtain ⟨u, hu, huφ⟩ := LiePull.ext_up (A := X₀.presheaf.stalk (f (centre z))) (A' := X.presheaf.stalk (centre z))
    (g := genMap ξ₀ ⟨f (centre z), hp⟩) (g' := genMap ξ ⟨centre z, hall _⟩) (ρ := (f.stalkMap (centre z)).hom)
    (x := X₀.fromSpecStalk (f (centre z))) (x' := X.fromSpecStalk (centre z)) (M := M) (M' := M') (j := j) m.cart hj hρ
    hρ' hx' hw
  have hc : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  refine ⟨LieCarrier.epsHom _ _ z hc ≫ u, ⟨hall _, u, hu, rfl⟩, ?_⟩
  have e1 : (LieCarrier.epsHom _ _ z hc ≫ u).left =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ u.left := rfl
  have e2 : (Scheme.stalkClosedPointTo (z ≫ f)).hom =
      (Scheme.stalkClosedPointTo z).hom.comp (f.stalkMap (centre z)).hom := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have e4 : spMap (dualMap (Scheme.stalkClosedPointTo (z ≫ f)).hom) =
      spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ spMap (dualMap (f.stalkMap (centre z)).hom) := by
    rw [e2]
    exact (congrArg spMap (LiePull.dualMap_comp (f.stalkMap (centre z)).hom (Scheme.stalkClosedPointTo z).hom).symm).trans
      (spMap_comp' _ _)
  have e3 : (LieCarrier.epsHom _ _ z hc ≫ u).left ≫ m.φ = spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫
      spMap (dualMap (f.stalkMap (centre z)).hom) ≫ w.left :=
    (congrArg (· ≫ m.φ) e1).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ ·) huφ))
  exact hwz.trans (((congrArg (· ≫ w.left) e4).trans (Category.assoc _ _ _)).trans e3.symm)

end Points

section Main

theorem lie_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl hβ hcov hfl
  obtain ⟨-, hf, hcst⟩ := hcov
  obtain ⟨m₀, hφ⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  obtain ⟨j, hpt, hsemi, hind, -, hpull⟩ := GlobalTheory.T.lie_model_dominant_hodge E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ Ω₀ Ω 𝔐₀.ξ 𝔐.ξ i 𝔐₀.Li 𝔐.Li 𝔐₀.M 𝔐.M
    𝔐₀.tie.gen 𝔐.tie.gen hd
  have hact : ∀ a e, 𝔐.ρ a (j e) = j (𝔐₀.ρ a e) := fun a e => pt_inj_of_pull m₀.cart 𝔐.M (by
    have e1 := congrArg CommaMorphism.left (𝔐.act a (j e))
    have e2 := congrArg CommaMorphism.left (𝔐₀.act a e)
    have e3 := m₀.act a
    rw [hpt]
    refine (congrArg (· ≫ m₀.φ) e1).trans ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine (congrArg (_ ≫ ·) e3).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (𝔐₀.t.act.act a).left) (hpt e)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (spMap (dualMap i) ≫ ·) e2.symm)
  have hemb : ∀ s, 𝔐.emb s = i.comp (𝔐₀.emb s) := fun s => by
    simp only [HodgeCpt.emb, hcst, RingHom.comp_assoc]
  have heig : ∀ s e, e ∈ 𝔐₀.Vgen s → j e ∈ 𝔐.Vgen s := fun s e he => by
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [hact, (mem_eigSp_iff _ _ _).1 he a, hsemi, hemb]
    rfl
  refine ⟨j, hsemi, hind, fun s a => ?_, fun q hq s => ?_, fun z r b Γ hΓ => ?_⟩
  · refine pt_inj_of_pull 𝔐.m.cart 𝔐.M ?_
    have e1 : (𝔐.M.pt (j (Fl₀.b s a))).left ≫ 𝔐.m.φ =
        spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ := by
      rw [hφ, ← Category.assoc, hpt, Category.assoc]
    exact e1.trans (hfl s a).symm
  · have hq₀ : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐₀.ξ r (pushCpt hd q) :=
      fun r hr => not_inFibre_push 𝔐.tie.gen hd q (hq r hr)
    obtain ⟨hV, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y 𝔐 hβ q hq
    obtain ⟨hV₀, -, hlat₀⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ hβ (pushCpt hd q) hq₀
    obtain ⟨-, -, -, -, -, -, hindep, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
    rw [hV s, hV₀ s]
    let N : (CMType H ⊕ CMType H) → Submodule (regAt 𝔐.ξ q) 𝔐.Li := fun s' =>
      Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.dR s' (pushCpt hd q) : Set 𝔐₀.Li))
    have hle : ∀ s', N s' ≤ 𝔐.dR s' q := fun s' => by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, he, rfl⟩
      refine ⟨?_, heig s' e he.2⟩
      rw [hpull]
      exact Submodule.subset_span ⟨hd.specializes q, e, he.1, rfl⟩
    have htop : 𝔐.M.lat q ≤ ⨆ s', N s' := by
      rw [hpull]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ ⨆ s', 𝔐₀.dR s' (pushCpt hd q) := hlat₀ ▸ he
      refine Submodule.iSup_induction _ (motive := fun x => j x ∈ ⨆ s', N s') he' (fun s' x hx => ?_) ?_ ?_
      · exact Submodule.mem_iSup_of_mem s' (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro x x' hx hx'
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hx'
    refine le_antisymm (fun e he => ?_) (hle s)
    exact mem_of_mem_iSup _ 𝔐.Vgen hindep N (fun s' x hx => (hle s' hx).2) s (htop he.1) he.2
  · obtain ⟨v₀, hv₀, hIP⟩ := hΓ
    choose v hv hvφ using fun k => exists_value_up m₀ 𝔐.all hd hpt z (hv₀ k)
    exact ⟨v, hv, fun p q => (GlobalTheory.T.hodge_inner_product_map_iff E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ z (v p) (v q) (v₀ p) (v₀ q) (Γ p q) (hvφ p) (hvφ q)).2 (hIP p q)⟩

end Main

end GlobalTheory.CompanionTheory.Ar.ChgLie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFirstStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover | exact GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover <;> assumption)
end
end

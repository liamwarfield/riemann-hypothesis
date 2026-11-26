module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSeparationRegularDeterminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
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

namespace GlobalTheory.ChartKSBracket

theorem tanPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (u : TanM (𝟙 (Sp R)) Y.H), ∃ v' : TanM (𝟙 (Sp R)) t.G, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv u)) (tv v') := by
  intro E _ _ _ H R _ _ _ _ _ t P Y u
  letI := H.starRing
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hs : spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R)) := Category.comp_id _
  obtain ⟨x, hx, -⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ (tv u))
  obtain ⟨x₀, -, hu₀⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ 1)
  have h1 := hx.pull (homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R)))) (Y.rep.1 _ _ _ (tv u))
  have e : homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R))) ≫ tv u = 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem u
  rw [e] at h1
  have h2 := GlobalTheory.FormalPoint.isPointOf_one P.U.toUnifPre (GlobalTheory.ExpTan.isZero_one Y.rep (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R))))
  have hk : smT (𝟙 (Sp R)) 0 x = 1 := (hu₀ _ h1).trans (hu₀ _ h2).symm
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT x hk, hx⟩

theorem isTanAtG_tv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v' : TanM (𝟙 (Sp R)) t.G), IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv v').left) := by
  intro E _ _ _ H R _ t v'
  refine GlobalTheory.LieMet.isTan_map _ ?_ (GlobalTheory.LieMet.isTan_tv v')
  rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rfl

end GlobalTheory.ChartKSBracket
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformHeightConstant
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.ShortDet

theorem le_choose {f r p q : ℕ} (hf : 8 ≤ f) (hr : 100 ≤ r) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : p + q = r) :
    8 * f * r + 10 ≤ (f * p * q + 1).choose 2 := by
  have h1 : r ≤ p * q + 1 := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
    nlinarith [Nat.zero_le (a * b)]
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_assoc f, mul_assoc 8, Nat.le_div_iff_mul_le two_pos]
  generalize p * q = s at h1
  have h2 : f * r ≤ 2 * (f * s) := by
    rw [mul_left_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have h3 : 8 * 99 ≤ f * s := Nat.mul_le_mul hf (by omega)
  generalize f * s = N at h2 h3
  nlinarith

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem antitone_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) (τ : Psi H) : Antitone ((s • hodgeWt Dw) τ) := fun i j h => by
  have : (i : ℕ) ≤ j := h
  simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem gap_smul_hodgeWt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (s : ℤ) (τ : Psi H) : gap ((s • hodgeWt Dw) τ) (Dw.p - 1) = s := by
  have h : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
  simp only [gap, dif_pos h, hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem size_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) :
    ∑ τ, ∑ k, |((s • hodgeWt Dw) τ k : ℝ)| ≤ Module.finrank ℚ E * ((Dw.p + Dw.q : ℕ) * s) := by
  have h0 : (0 : ℝ) ≤ s := by exact_mod_cast hs
  refine (Finset.sum_le_card_nsmul _ _ (((Dw.p + Dw.q : ℕ) : ℝ) * s) fun τ _ => ?_).trans ?_
  · refine (Finset.sum_le_card_nsmul _ _ (s : ℝ) fun k _ => ?_).trans (by simp)
    simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [h0, abs_of_nonneg h0]
  · rw [nsmul_eq_mul, ← NumberField.Embeddings.card E ℂ]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) (by positivity)

end Weight


end GlobalTheory.ShortDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeight
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.TermWt

theorem isWt_term : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hV
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hV' : V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U j := hV
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ V → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b V (rsT (τ.f j) V))) =
        gs b z (LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j) (τ.f j) := by
    intro b hb z
    rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hV']
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z V (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hV (hb trivial) _
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, hJj⟩ := exists_good Q.P.L hL z (fun _ : Fin 1 => x.left ≫ Y.q.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b))
    (fun i => Set.mem_iInter.1 (hV (hV₁ (show z ∈ (⊤ : (Sp S).Opens) from trivial))) i)
  have e₁ : ∀ i, J (x.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := hJj
  have e₂ : ∀ i, J (x'.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := fun i => by rw [hqq]; exact hJj i
  have t₁ := hT (Over.mk (spMap φ)) x z J hJ
  have t₂ := hT (Over.mk (spMap φ)) x' z J hJ
  rw [sval_of τ _ z J j e₁] at t₁
  rw [sval_of τ _ z J j e₂, hq, hc α z J hJ, Units.val_mul] at t₂
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [germ _ hV₂ z, t₂, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, t₁,
    show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.Heat.TermWt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeightStatement
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
theorem _root_.GlobalTheory.T.raynaudFourierTerm_chartFunctions_isWeight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  first | exact @GlobalTheory.Heat.TermWt.isWt_term | exact GlobalTheory.Heat.TermWt.isWt_term | (intros; apply GlobalTheory.Heat.TermWt.isWt_term <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTop
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeAffine

theorem closure_range_union_eq_top_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (h : IsPushout f g i j) :
    Subring.closure (Set.range i.hom ∪ Set.range j.hom) = ⊤ := by
  set R := Subring.closure (Set.range i.hom ∪ Set.range j.hom)
  let l : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (i.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let r : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (j.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ l = g ≫ r := by
    ext a
    have := congrArg (fun q : A ⟶ P => q.hom a) h.w
    simpa [l, r] using this
  let s : CommRingCat.of R ⟶ P := CommRingCat.ofHom R.subtype
  have hid : h.desc l r w ≫ s = 𝟙 P := by
    apply h.hom_ext
    · ext b; simp [l, s]
    · ext c; simp [r, s]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (((h.desc l r w).hom x : R) : P) = x := by
    have := congrArg (fun q : P ⟶ P => q.hom x) hid
    simpa [s] using this
  rw [← hx]
  exact ((h.desc l r w).hom x).2

theorem affine_and_closure_eq_top : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (O : Z.affineOpens), O.1 ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) ∧ Subring.closure (Set.range (φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left).hom ∪ Set.range (p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right).hom) = ⊤ := by
  intro Z Z' X X' p p' φ g H U U' hU' O hO
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine U'.1.toScheme := U'.2
  have : IsAffine O.1.toScheme := O.2
  have hpb := Scheme.Hom.isPullback_resLE H (US := U.1) (UT := U'.1) (UX := O.1)
    (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) hU' hO rfl
  refine ⟨.of_isIso hpb.isoPullback.hom, ?_⟩
  have po := (isIso_pushoutSection_iff H hU' hO (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) rfl).1
    (isIso_pushoutSection_of_isAffineOpen H hU' hO rfl U.2 U'.2 O.2)
  exact closure_range_union_eq_top_of_isPushout po

end GlobalTheory.BaseChangeAffine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTopStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (O : Z.affineOpens), O.1 ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) ∧ Subring.closure (Set.range (φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left).hom ∪ Set.range (p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right).hom) = ⊤ := by
  first | exact @GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top | exact GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top | (intros; apply GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

def VS {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k : ℕ) (s : FractionRing Ω) : Prop :=
  ∃ (r : R) (σ : SecM (𝟙 Y) L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) L x g k σ ω ∧
    (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * s

theorem VS.half {R Ω : Type} [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}}
    {L : LB Y} {x : Sp Ω ⟶ Y} {g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)} {k : ℕ} {s : FractionRing Ω}
    (h : VS φ L x g k (2 * s)) : VS φ L x g k s := by
  haveI : CharZero R := algebraRat.charZero R
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  refine ⟨2 * r, σ, ω, mul_ne_zero two_ne_zero hr, hv, ?_⟩
  rw [he, map_mul, map_mul, map_ofNat, map_ofNat]
  ring

theorem ringOp_sub {Ω : Type} [CommRing Ω] {n : ℕ} (d₁ d₂ : Ω → Ω) (dd : Fin n → Ω → Ω)
    (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) Ω) (u₁ u₂ : Fin n → Ω) (p₁ p₁' p₂ p₂' : Ω) (k : ℕ) (f : Ω) :
    ringOp d₁ dd Θ₁ u₁ p₁ p₁' k f - ringOp d₂ dd Θ₂ u₂ p₂ p₂' k f =
      ringOp (fun y => d₁ y - d₂ y) dd (Θ₁ - Θ₂) (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k f := by
  simp only [ringOp, Matrix.sub_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem bracket {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (hl : ∀ a x y, dd a (x * y) = x * dd a y + y * dd a x)
    (ha : ∀ a x y, dd a (x + y) = dd a x + dd a y)
    (Θ : Matrix (Fin n) (Fin n) Ω) (hΘ : Θᵀ = Θ) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (b c : Ω) :
    b * (ringOp d dd Θ u p p' (k + k) (b * c) - b * ringOp d dd Θ u p p' k c -
        c * ringOp d dd Θ u p p' k b) -
      c * (ringOp d dd Θ u p p' (k + k) (b * b) - b * ringOp d dd Θ u p p' k b -
        b * ringOp d dd Θ u p p' k b) =
      2 * ((k : Ω) * b * (b * d c - c * d b) - ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b)) := by
  have sym : ∀ a e, Θ e a = Θ a e := fun a e => by
    have := congrFun (congrFun hΘ a) e
    simpa [Matrix.transpose_apply] using this
  have swap : ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = ∑ a, ∑ e, Θ a e * (dd a b * dd e c) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [sym]; ring
  have s2 : ∀ f h : Ω, ∑ a, ∑ e, Θ a e * dd a (dd e (f * h)) =
      f * ∑ a, ∑ e, Θ a e * dd a (dd e h) + h * ∑ a, ∑ e, Θ a e * dd a (dd e f) +
        (∑ a, ∑ e, Θ a e * (dd a f * dd e h) + ∑ a, ∑ e, Θ a e * (dd a h * dd e f)) := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hl, ha, hl, hl]
    ring
  have s1 : ∀ f h : Ω, ∑ a, u a * dd a (f * h) = f * ∑ a, u a * dd a h + h * ∑ a, u a * dd a f := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hl]
    ring
  have swap' : ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = 0 := by
    rw [swap]; ring
  have t1 : ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b) =
      b * ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - c * ∑ a, ∑ e, Θ a e * (dd a b * dd e b) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  simp only [ringOp]
  rw [s2, s2, s1, s1, t1, hd, hd]
  push_cast
  linear_combination b * swap'

end GlobalTheory.HeatSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsLocConst

theorem push_injective {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (x : S' ⟶ S) (T : Over S') :
    Function.Injective (pushHom (isGrpPullback_pullback A x) T) := by
  intro a b h
  have h' := congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h'
  · exact (Over.w a).trans (Over.w b).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem locally_const_torsion :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ (Z : Over S) (t : Z ⟶ Over.mk x) (z : Z ⟶ A), z ^ n = 1 →
      ∀ w : Z.left, ∃ (V : Over S) (i : V ⟶ Z) (y : Over.mk x ⟶ A) (w' : V.left),
        IsOpenImmersion i.left ∧ i.left w' = w ∧ y ^ n = 1 ∧ i ≫ z = i ≫ t ≫ y := by
  intro S A _ hA k _ _ x n hn Z t z hz w
  have hB : IsAbelianScheme ((Over.pullback x).obj A) := Out.TLinPf.isAb_pullback x A hA
  have hg := isGrpPullback_pullback A x
  have htx : t.left ≫ x = Z.hom := Over.w t
  let Z' : Over (Sp k) := Over.mk t.left
  let z' : Z' ⟶ (Over.pullback x).obj A :=
    Over.homMk (pullback.lift z.left t.left ((Over.w z).trans htx.symm)) (pullback.lift_snd _ _ _)
  let e : Z ⟶ Over.mk (Z'.hom ≫ x) := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ t.left ≫ x = Z.hom
    rw [Category.id_comp, htx])
  let e' : Over.mk (Z'.hom ≫ x) ⟶ Z := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ Z.hom = t.left ≫ x
    rw [Category.id_comp, htx])
  have hee : e' ≫ e = 𝟙 _ := Over.OverMorphism.ext (by show 𝟙 Z.left ≫ 𝟙 Z.left = 𝟙 Z.left; exact Category.id_comp _)
  have hez : e ≫ pushHom hg Z' z' = z := Over.OverMorphism.ext (by
    show 𝟙 _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = z.left
    rw [Category.id_comp, pullback.lift_fst])
  have hz' : z' ^ n = 1 := by
    apply push_injective A x Z'
    rw [map_pow, map_one]
    calc (pushHom hg Z' z') ^ n = e' ≫ e ≫ (pushHom hg Z' z') ^ n := by
          rw [← Category.assoc, hee, Category.id_comp]
      _ = e' ≫ (e ≫ pushHom hg Z' z') ^ n := by rw [MonObj.comp_pow]
      _ = 1 := by rw [hez, hz, MonObj.comp_one]
  have hK := GlobalTheory.KerConst.isPullback_const_ker k ((Over.pullback x).obj A) hB n hn
  have hcond : z' ≫ 𝟙 _ ^ n = toUnit Z' ≫ η[(Over.pullback x).obj A] := by
    rw [MonObj.comp_pow, Category.comp_id, hz', Hom.one_def]
  let g := hK.lift z' (toUnit Z') hcond
  have hgz : g ≫ Sigma.desc (fun c => c.1) = z' := hK.lift_fst _ _ _
  let P := {c : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback x).obj A // c ^ n = 1}
  let D : (∐ fun _ : P => 𝟙_ (Over (Sp k))) ⟶ GlobalTheory.PointQuot.constObj (Sp k) P :=
    Sigma.desc fun c => GlobalTheory.PointQuot.constPt (Sp k) c
  have hDE : D ≫ GlobalTheory.PointQuot.constDesc (fun c : P => c.1) = Sigma.desc (fun c : P => c.1) :=
    Sigma.hom_ext _ _ fun c => by
      rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, GlobalTheory.PointQuot.constPt_desc]
  obtain ⟨U, hwU, c, hc⟩ := GlobalTheory.PointQuot.locally_const_desc (fun c : P => c.1) (g ≫ D) w
  have hU : GlobalTheory.PointQuot.openι Z' U ≫ z' = toUnit _ ≫ c.1 := by
    rw [← hc, ← hgz, ← hDE]
    simp only [Category.assoc]
  let y : Over.mk x ⟶ A := Over.homMk (c.1.left ≫ pullback.fst A.hom x) (by
    show (c.1.left ≫ pullback.fst A.hom x) ≫ A.hom = x
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hc1 : c.1.left ≫ pullback.snd A.hom x = 𝟙 _ := Over.w c.1
    rw [hc1, Category.id_comp])
  let e'' : Over.mk x ⟶ Over.mk ((𝟙_ (Over (Sp k))).hom ≫ x) := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ 𝟙 _ ≫ x = x
    rw [Category.id_comp, Category.id_comp])
  have hy : y = e'' ≫ pushHom hg _ c.1 := Over.OverMorphism.ext (by
    show c.1.left ≫ pullback.fst A.hom x = 𝟙 _ ≫ (c.1.left ≫ pullback.fst A.hom x)
    rw [Category.id_comp])
  refine ⟨GlobalTheory.PointQuot.openObj Z U, GlobalTheory.PointQuot.openι Z U, y, ⟨w, hwU⟩, ?_, rfl, ?_, ?_⟩
  · show IsOpenImmersion U.ι
    infer_instance
  · rw [hy, ← MonObj.comp_pow, ← map_pow, c.2, map_one, MonObj.comp_one]
  · apply Over.OverMorphism.ext
    have h1 := congrArg CommaMorphism.left hU
    have h2 : (toUnit (GlobalTheory.PointQuot.openObj Z' U)).left = U.ι ≫ t.left :=
      (Category.comp_id _).symm.trans (Over.w (toUnit (GlobalTheory.PointQuot.openObj Z' U)))
    show U.ι ≫ z.left = U.ι ≫ t.left ≫ c.1.left ≫ pullback.fst A.hom x
    have h3 : z.left = z'.left ≫ pullback.fst A.hom x := (pullback.lift_fst _ _ _).symm
    simp only [Over.comp_left] at h1
    rw [h3, ← Category.assoc]
    erw [h1, h2]
    exact Category.assoc _ _ _

end GlobalTheory.TorsLocConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoinStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_torsionPoint_locally_constant_geomPoint : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ (Z : Over S) (t : Z ⟶ Over.mk x) (z : Z ⟶ A), z ^ n = 1 → ∀ w : Z.left, ∃ (V : Over S) (i : V ⟶ Z) (y : Over.mk x ⟶ A) (w' : V.left), IsOpenImmersion i.left ∧ i.left w' = w ∧ y ^ n = 1 ∧ i ≫ z = i ≫ t ≫ y := by
  first | (exact @GlobalTheory.TorsLocConst.locally_const_torsion) | (exact GlobalTheory.TorsLocConst.locally_const_torsion) | (intros; apply GlobalTheory.TorsLocConst.locally_const_torsion  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorOnRingConjPowFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorOnRingConjPowFractionField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Heat

theorem fractionField_derivation_pow_logDeriv {Ω : Type} [CommRing Ω] [IsDomain Ω] (D : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) {c : FractionRing Ω} (hc : c ≠ 0) (k : ℕ) :
    D (c ^ k) = c ^ k * ((k : FractionRing Ω) * (D c / c)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, smul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
    ring

theorem fractionField_derivation_pow_mul_logDeriv {Ω : Type} [CommRing Ω] [IsDomain Ω] (D : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) {c : FractionRing Ω} (hc : c ≠ 0) (k : ℕ) (g : FractionRing Ω) :
    D (c ^ k * g) = c ^ k * (D g + (k : FractionRing Ω) * (D c / c) * g) := by
  rw [Derivation.leibniz, fractionField_derivation_pow_logDeriv D hc, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.Heat


open GlobalTheory.Heat in
theorem GlobalTheory.Heat.ringOp_conj_pow : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Θᵀ = Θ → (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  intro Ω _ _ n d δ Θ hΘ h2 u p p' c hc
  have hs : ∀ (s : Finset (Fin n)) (D : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
    intro s D x
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  refine ⟨d - ∑ a, ∑ b, (Θ a b * (δ a c / c)) • δ b, u,
    p + d c / c - (1 / 2) * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c),
    p' - (1 / 2) * ∑ a, ∑ b, Θ a b * δ a (δ b c / c) + ∑ a, u a * (δ a c / c), ?_, ?_⟩
  · intro y hy
    rw [Derivation.sub_apply, hs, Finset.sum_eq_zero, sub_zero]
    intro a _
    rw [hs]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Derivation.smul_apply, hy, smul_zero]
  · intro k f
    have e1 : ∀ b, δ b (c ^ k * f) = c ^ k * (δ b f + (k : FractionRing Ω) * (δ b c / c) * f) :=
      fun b => fractionField_derivation_pow_mul_logDeriv (δ b) hc k f
    have e2 : ∀ a b, δ a (δ b (c ^ k * f)) = c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f) := by
      intro a b
      rw [e1, fractionField_derivation_pow_mul_logDeriv (δ a) hc]
      simp only [map_add (f := _), Derivation.leibniz, Derivation.map_natCast, smul_eq_mul]
      ring
    have e3 : d (c ^ k * f) = c ^ k * (d f + (k : FractionRing Ω) * (d c / c) * f) := fractionField_derivation_pow_mul_logDeriv d hc k f
    have hsym : ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f) = ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have := congrFun (congrFun hΘ a) b
      rw [Matrix.transpose_apply] at this
      rw [this]
    unfold ringOp
    simp only [e2, e3]
    simp only [e1, Derivation.sub_apply, hs, Derivation.smul_apply, smul_eq_mul]
    have hL : ∑ a, ∑ b, Θ a b * (c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f)) =
        c ^ k * (∑ a, ∑ b, Θ a b * δ a (δ b f) + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
          + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
          + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c)
          + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hU : ∑ a, u a * (c ^ k * (δ a f + (k : FractionRing Ω) * (δ a c / c) * f)) =
        c ^ k * (∑ a, u a * δ a f + (k : FractionRing Ω) * f * ∑ a, u a * (δ a c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hD : ∑ a, ∑ b, Θ a b * (δ a c / c) * δ b f = ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_assoc _ _ _
    have hh : (2 : FractionRing Ω) * (1 / 2) = 1 := mul_one_div_cancel h2
    rw [hL, hU, hD, hsym]
    linear_combination (c ^ k * f * ((k : FractionRing Ω) ^ 2 * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)
      + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * δ a (δ b c / c))) * hh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorOnRingConjPowFractionFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperatorOnRing_conj_pow_fractionField : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Θᵀ = Θ → (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  first | exact @GlobalTheory.Heat.ringOp_conj_pow | exact GlobalTheory.Heat.ringOp_conj_pow | (intros; apply GlobalTheory.Heat.ringOp_conj_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivation
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

namespace GlobalTheory.DerFieldExt

theorem cover' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) :
    W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

theorem sep' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) (s t : Γ(X, W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k s = resG X k t) : s = t :=
  X.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
    W (fun i => homOfLE i.2) (cover' X hW h) s t (fun i => e i.1 i.2)

theorem exists_field : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U),
    (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) →
    ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  intro X W₀ hW d₀ hadd hmul
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(X, X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG X (X.basicOpen_le f) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    obtain ⟨δ, h1, h2, h3⟩ := GlobalTheory.LocDerExt.der_exists f (RingHom.id _)
      (fun a => resG X (X.basicOpen_le f) (d₀ a)) (fun a b => by simp only [hadd, map_add (f := _)])
      (fun a b => by simp only [hmul, map_add (f := _), map_mul, RingHom.id_apply]; rfl)
    exact ⟨δ, h1, fun a b => by simpa using h2 a b, h3⟩
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG X k (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine GlobalTheory.LocDerExt.der_unique f (resG X k)
      (fun s => resG X k (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add (f := _), map_mul]
    · simp only [δmul, map_mul]
    · change resG X k (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [GlobalTheory.LocDerExt.res_res X, δres, δres, GlobalTheory.LocDerExt.res_res X]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(X, W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
      W (fun i => homOfLE i.2) (cover' X hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : X.basicOpen i.1 ⊓ X.basicOpen j.1 ≤ X.basicOpen (i.1 * j.1) := e.ge
        have e' : resG X ki (δ i.1 (resG X i.2 s)) = resG X kj (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X]
        have e'' := congrArg (resG X k) e'
        rw [GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add (f := _), δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep' X hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (GlobalTheory.LocDerExt.res_res X h' k _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), GlobalTheory.LocDerExt.res_res X]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep' X hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.DerFieldExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivationStatement
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
theorem _root_.GlobalTheory.T.exists_vectorField_extending_affineDerivation : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U), (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) → ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  first | exact @GlobalTheory.DerFieldExt.exists_field | exact GlobalTheory.DerFieldExt.exists_field | (intros; apply GlobalTheory.DerFieldExt.exists_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.MixVacBig

open GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem isIdemSum_atPl (hL : L.Is μ₀) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) : IsIdemSum (atPl w 1) {w} := by
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  have h := hes w hw
  rw [← GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h]
  exact ⟨⟨fun _ => es w, fun P hP => by rw [Finset.mem_singleton.1 hP]; exact h, by simp⟩, h.1.2.1⟩

theorem aa_unit_of_standing {t : T} (hst : SquareStanding G t) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1 := by
  have h := hst.2 w hw
  rw [Nat.cast_mul] at h
  exact GlobalTheory.AAUnit.aa_unit D w (fun h' => h (w.asIdeal.mul_mem_right _ h')) fun h' => h (w.asIdeal.mul_mem_left _ h')

theorem coord_int_iff (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ}
    (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (z : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D)) :
    GlobalTheory.StepData.IntM (B.coord t w hX hY (z.map (atW w))) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr (B.β X.1 X.2) (B.β Y.1 Y.2) (z.map (toEAf D))).map (cpt (D := D) w)) := by
  have e : z.map (atW w) = (z.map (toEAf D)).map (cpt (D := D) w) := rfl
  rw [e, Comparison₂.coord_map]
  refine ⟨fun H a b => ?_, fun H a b => H _ _⟩
  have := H (b.cast (rank_vertex G t w hY).symm) (a.cast (rank_vertex G t w hX).symm)
  simpa only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.cast_cast, Fin.cast_eq_self] using this

theorem mem_lat_iff (hL : L.Is μ₀) (B : Frames G) (t : T) (hst : SquareStanding G t) {i j : Fin D.R.m} (e : Num G i j)
    {w : Pl D.host.E} (hw : w ∈ locPl G t) {x : Pt G i j} (hx : x ∈ mixHalf e (atPl w 1)) :
    (mapV e x ∈ latV G i j ∧ mapW e x ∈ latW G i j) ↔
      ∀ r s, mixCo B t e w x r s ∈ (ValuativeRel.valuation (Kw w)).integer := by
  have hI := isIdemSum_atPl hL t hw
  have hA : ∀ w' ∈ ({w} : Finset (Pl D.host.E)), ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w') a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w') a) = 1) := fun w' hw' => by
    rw [Finset.mem_singleton.1 hw']
    exact aa_unit_of_standing hst hw
  have hT₁ : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) := isSelfDualC_neg hT₁
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have fW := B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2
  have fV := B.isFrame_β hL (i := (i : ℕ)) (j := (j : ℕ) + 1) i.2.le j.2
  have fV₁ := B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ)) i.2 j.2.le
  have k₁ := GlobalTheory.ColLatDict.mem_latO_iff_intM hS hT fW fV hI hA (mapV e x) hx.1
  have k₂ := GlobalTheory.ColLatDict.mem_latO_iff_intM hS₁ hT₁ fV₁ fW hI hA (mapW e x) hx.2
  simp only [Finset.mem_singleton, forall_eq] at k₁ k₂
  have c₁ := coord_int_iff B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ (mapV e x)
  have c₂ := coord_int_iff B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ (mapW e x)
  refine (and_congr (k₁.trans c₁.symm) (k₂.trans c₂.symm)).trans ?_
  rw [mixCo_eq]
  refine ⟨fun H r s => ?_, fun H => ⟨fun r s => H r (.inl s), fun r s => H s (.inr r)⟩⟩
  rcases s with s | s
  · exact H.1 r s
  · exact H.2 s r


set_option maxHeartbeats 800000 in
theorem mix_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToA G t i j w, IsMixModelA W B t e Γ w ι →
      ι (Γ.M.vac _) = ι (Γ.M.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti w hw ι hι
  classical
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hid, -⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hv := GlobalTheory.BigDat.lagr_vac hι (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _
      (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 hh.2.2.2.1
  funext z
  obtain ⟨x, hx, rfl⟩ := (hco w).2.1 z
  have key := mem_lat_iff hL B t hst e hw hx
  rw [hv.2 x hx, Pi.smul_apply, smul_eq_mul]
  by_cases hl : mapV e x ∈ latV G i j ∧ mapW e x ∈ latW G i j
  · rw [Set.indicator_of_mem (show x ∈ (latPt e (w.under (𝓞 D.host.F)) : Set _) from ⟨hh.1 x hx, hl⟩),
      Set.indicator_of_mem (show mixCo B t e w x ∈ {Z : MatA G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer}
        from key.1 hl), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (show x ∉ (latPt e (w.under (𝓞 D.host.F)) : Set _) from fun h' => hl h'.2),
      Set.indicator_of_notMem (show mixCo B t e w x ∉ {Z : MatA G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer}
        from fun h' => hl (key.2 h')), mul_zero]

end GlobalTheory.MixVacBig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_vacuum_eq_integralMatrix_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToA G t i j w, IsMixModelA W B t e Γ w ι →
      ι (Γ.M.vac _) = ι (Γ.M.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  first | exact @GlobalTheory.MixVacBig.mix_vac | exact GlobalTheory.MixVacBig.mix_vac | (intros; apply GlobalTheory.MixVacBig.mix_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
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

namespace GlobalTheory.HeatRatio

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R)

def IsRatio {N : ℕ} {α : Q.X} (σ σ' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J

def IsRem {N : ℕ} {α : Q.X} (σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f g : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    sval σp (𝟙 _) z J = gs (𝟙 _) z U f * sval σp' (𝟙 _) z J + gs (𝟙 _) z U g * sval σ' (𝟙 _) z J

end GlobalTheory.HeatRatio
end
end

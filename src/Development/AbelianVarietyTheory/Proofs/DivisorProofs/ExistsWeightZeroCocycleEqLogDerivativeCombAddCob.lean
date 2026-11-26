module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldsCechH1Relation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCob
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCob
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

namespace GlobalTheory.PullbackWeightZero

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)), IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y V f S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero

theorem h1cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := GlobalTheory.T.invariant_fields_cech_h1_relation

theorem liepush : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left) (M : Fin n → Fin g → R) (N : Fin g → Fin n → R), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) ∧ (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) ∧ (∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) ∧ ∀ (b : Fin n) (i i' : Dd.toPre.P.L.ι) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i') → dlg Y.H Y.q.left Dd.toPre.P.L (dd b) i i' W = pbT Y.q.left (∑ a, constFn Dd.toPre.P.A.hom _ (M b a) * dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) i i' (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i')) W := GlobalTheory.T.exists_logDeriv_polarization_raynaud_eq_pullback

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (c' : Fin g → R) (N : Fin g → Fin n → R)
    (M : Fin n → Fin g → R) (hNM : ∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) (X : Fin g → Γ₀) :
    ∑ a, κ (c' a) * X a = ∑ b, κ (∑ a, c' a * N a b) * ∑ a', κ (M b a') * X a' := by
  have e : ∀ a', ∑ b, (∑ a, c' a * N a b) * M b a' = c' a' := by
    intro a'
    simp_rw [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hNM]
    simp
  simp_rw [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [← Finset.sum_mul, ← map_sum, e]

theorem h1_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin n → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', pbT Y.q.left (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') + (pbT Y.q.left (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - pbT Y.q.left (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz
  obtain ⟨g, w, dd', M, N, hw, hsp, hNM, hdl⟩ := liepush R Dd O oa Y n v dd hdd
  obtain ⟨c', y, hc'⟩ := h1cover R Dd g w dd' hw hsp J V j hcov hle z hz
  refine ⟨fun b => ∑ a, c' a * N a b, y, fun i i' => ?_⟩
  have hW : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
      Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
    Y.q.left.preimage_mono (inf_le_inf (hle i) (hle i'))
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  rw [hc' i i', GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_right le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_left le_rfl]
  congr 1
  simp only [hdl _ _ _ _ hW, GlobalTheory.KS.pbT_sum, GlobalTheory.KS.pbT_mul]
  simp only [GlobalTheory.KS.pbT_constFn _ _ hW, GlobalTheory.KS.pbT_constFn _ Y.q.left (O₀ := V i ⊓ V i') (O := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (inf_le_inf (hle i) (hle i')) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) c' N M hNM _

theorem exists_comb_dlg_add_cob : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι),
    ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), IsCoc _ z → (∀ i i', IsWt Y 0 _ (z i i')) →
      ∃ (c : Fin n → R) (y : ∀ i, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V i)), (∀ i, IsWt Y 0 _ (y i)) ∧ ∀ i i',
        z i i' = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') _ +
          (rsT (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - rsT (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz hw
  have hA := descend R Dd.toPre O oa Y
  have hB := isWt_pbT R Dd.toPre O oa Y
  choose z' hz' using fun i i' => (hA (V i ⊓ V i') (z i i') (hw i i')).exists
  have hcoc : IsCoc V z' := by
    intro i i' i''
    apply (hA (V i ⊓ V i' ⊓ V i'') _ (hB _ (rsT (z' i i'') (V i ⊓ V i' ⊓ V i'')))).unique _ rfl
    rw [GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl, GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right) le_rfl,
      GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right) le_rfl]
    have e1 : rsT (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i']; exact GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left _
    have e2 : rsT (z i' i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i' i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i' i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_right) inf_le_right) _
    have e3 : rsT (z i i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_left) inf_le_right) _
    rw [← e1, ← e2, ← e3]
    exact hz i i' i''
  obtain ⟨c, y', hc⟩ := h1_pull R Dd O oa Y n v dd hdd J V j hcov hle z' hcoc
  refine ⟨c, fun i => pbT Y.q.left (y' i) (Y.q.left ⁻¹ᵁ V i), fun i => hB _ _, fun i i' => ?_⟩
  rw [GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left, GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_right, ← hc i i']
  exact (hz' i i').symm

end GlobalTheory.PullbackWeightZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCobStatement
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
theorem _root_.GlobalTheory.T.exists_weightZeroCocycle_eq_logDerivative_comb_add_coboundary : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι),
    ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), IsCoc _ z → (∀ i i', IsWt Y 0 _ (z i i')) →
      ∃ (c : Fin n → R) (y : ∀ i, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V i)), (∀ i, IsWt Y 0 _ (y i)) ∧ ∀ i i',
        z i i' = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') _ +
          (rsT (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - rsT (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) := by
  first | exact @GlobalTheory.PullbackWeightZero.exists_comb_dlg_add_cob | exact GlobalTheory.PullbackWeightZero.exists_comb_dlg_add_cob | (intros; apply GlobalTheory.PullbackWeightZero.exists_comb_dlg_add_cob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteOfFiniteGeometricFibres
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GeomFibre

theorem finite_of_finite_sections {K : Type} [Field K] [IsAlgClosed K] {P : Scheme.{0}}
    (g : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (h : Finite {p : Spec (CommRingCat.of K) ⟶ P // p ≫ g = 𝟙 _}) : Finite P := by
  have := LocallyOfFiniteType.jacobsonSpace g
  have h1 : (closedPoints P).Finite :=
    Set.finite_coe_iff.mp ((pointEquivClosedPoint g).finite_iff.mp h)
  have hc : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact h1.isClosed_biUnion fun x hx ↦ hx
  have h2 := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := P))
  rw [Set.univ_inter, hc.closure_eq] at h2
  exact Set.finite_univ_iff.mp (h2 ▸ h1)

theorem locallyQuasiFinite_of_finite_geometric_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
        Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}) → LocallyQuasiFinite f := by
  intro X Y f _ H
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  rcases (f ⁻¹' {y}).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]; exact Set.finite_empty
  obtain rfl : f x₀ = y := hx₀
  let K := AlgebraicClosure (X.residueField x₀)
  let x : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have hx : ∀ z, x z = x₀ := fun z ↦ by
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hfin : Finite ↥(pullback f (x ≫ f)) := by
    refine finite_of_finite_sections (pullback.snd f (x ≫ f)) ?_
    have := (H K x).to_subtype
    refine Finite.of_injective (β := {y : Sp K ⟶ X | y ≫ f = x ≫ f})
      (fun p ↦ ⟨p.1 ≫ pullback.fst f (x ≫ f), ?_⟩) fun a b hab ↦ ?_
    · change (p.1 ≫ _) ≫ f = x ≫ f
      rw [Category.assoc, pullback.condition, reassoc_of% p.2]
    · exact Subtype.ext (pullback.hom_ext (congrArg Subtype.val hab) (a.2.trans b.2.symm))
  refine (Set.finite_range (pullback.fst f (x ≫ f))).subset fun z hz ↦ ?_
  rw [Scheme.Pullback.range_fst]
  exact ⟨IsLocalRing.closedPoint K,
    ((Scheme.Hom.comp_apply x f _).trans (congrArg f (hx _))).trans hz.symm⟩

end GlobalTheory.GeomFibre
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SecCompact

theorem exists_openImmersion_genericFibre (F : Type) [Field F] (o : Type) [CommRing o] [Algebra o F]
    [IsFractionRing o F] [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (sX : X ⟶ Sp F) [IsReduced X]
    [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] (f : X ⟶ PSpace o m) [QuasiCompact f]
    [QuasiSeparated f] (hf : f ≫ PSpace.str o m = sX ≫ spMap (algebraMap o F))
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
      Set.Finite {y : Sp K ⟶ X | y ≫ sX = x ≫ sX ∧ y ≫ f = x ≫ f}) :
    IsFinite f.fromNormalization ∧
      ∃ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o m) (spMap (algebraMap o F)),
        IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = sX ∧
          iF ≫ pullback.fst _ _ = f.toNormalization := by
  haveI := isProper_str o m
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := IsPreimmersion.of_isLocalization (R := o) (S := F) (nonZeroDivisors o)
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  refine ⟨GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of o) f
    (PSpace.str o m) fun x _ => ?_, ?_⟩
  · have h1 : ((f ≫ PSpace.str o m).stalkMap x).hom.EssFiniteType := by
      rw [hf, Scheme.Hom.stalkMap_comp]
      exact .comp (RingHom.FiniteType.of_surjective _
        (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType (LocallyOfFiniteType.stalkMap sX x)
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h2 : (f.stalkMap x).hom.EssFiniteType := .of_comp _ h1
    exact h2.residueFieldMap
  have hb := IsPullback.of_hasPullback (PSpace.str o m) (spMap (algebraMap o F))
  let f' : X ⟶ pullback (PSpace.str o m) (spMap (algebraMap o F)) := pullback.lift f sX hf
  have e₁ : f' ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have e₂ : f' ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  haveI : LocallyOfFiniteType (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : LocallyOfFiniteType f' := locallyOfFiniteType_of_comp f' (pullback.snd _ _)
  haveI : QuasiCompact (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : QuasiCompact f' := QuasiCompact.of_comp f' (pullback.snd _ _)
  haveI : IsSeparated (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : IsSeparated f' := IsSeparated.of_comp f' (pullback.snd _ _)
  haveI : LocallyQuasiFinite f' := by
    refine GlobalTheory.GeomFibre.locallyQuasiFinite_of_finite_geometric_fibres X _ f' inferInstance fun K _ _ x => ?_
    refine (hfib K x).subset fun y (hy : y ≫ f' = x ≫ f') => ⟨?_, ?_⟩
    · rw [← e₂, ← Category.assoc, hy, Category.assoc]
    · rw [← e₁, ← Category.assoc, hy, Category.assoc]
  obtain ⟨hoi, -, hdom⟩ :=
    GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization (M := nonZeroDivisors o) hb f' f e₁.symm
  refine ⟨pullback.lift f.toNormalization f' (by simp [e₁]) ≫
    (pullbackRightPullbackFstIso (PSpace.str o m) (spMap (algebraMap o F)) f.fromNormalization).hom,
    inferInstance, (Scheme.Hom.denseRange _), ?_, ?_⟩
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc, e₂]
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst]

end GlobalTheory.SecCompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem isOpenImmersion_dense_genericFibre_normalization : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hb hfrac hN _ _ _ hfs hfib iF h1 h2
  letI : Algebra o F := b.toAlgebra
  haveI : FaithfulSMul o F := (faithfulSMul_iff_algebraMap_injective _ _).mpr hb
  haveI : IsFractionRing o F := IsFractionRing.of_field o F fun x => by
    obtain ⟨a, d, hd, e⟩ := hfrac x
    exact ⟨a, d, (eq_div_iff hd).mpr e⟩
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsReduced X := inferInstance
  obtain ⟨-, i₀, hoi, hd, hsnd, hfst⟩ :=
    GlobalTheory.SecCompact.exists_openImmersion_genericFibre F o n X s f hfs hfib
  have e : iF = i₀ := by
    apply pullback.hom_ext
    · rw [h1, hfst]
    · rw [h2, hsnd]
  subst e
  exact ⟨hoi, hd⟩

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_dense_genericFibre_normalisation : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  first | exact @GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization | exact GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization | (intros; apply GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteKernelNearDiagonalAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAmpleClosedImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessOfClosedSubscheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KernelRepFinite

theorem isClosedImmersion_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} (k : A ⟶ B)
    [IsClosedImmersion k.left] : IsClosedImmersion ((Over.pullback f).map k).left := by
  exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f k inferInstance

theorem lbIso_diag {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) {P : LB (G2 A).left} (hP : P.IsLB) :
    LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) := by
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [GlobalTheory.DiagAmpleBC.diag_comp A B β β₂ hs] at e₁
  exact LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm

theorem isFinite_restrict : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  intro S' _ G _ _ P hA hP V₀ hV hRel Z i hi hZ
  haveI : IsNoetherianRing Γ(S', V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV⟩
  let t : Sp Γ(S', V₀) ⟶ V₀.toScheme := hV.isoSpec.inv
  let GV := (Over.pullback V₀.ι).obj G
  let B := (Over.pullback t).obj GV
  have hAV : IsAbelianScheme GV := GlobalTheory.isAbelianScheme_pullback_obj _ G hA
  have hAB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj _ GV hAV
  let PV := P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)
  have hPV : PV.IsLB := pull_isLB hP _
  have h₁ := Pdiv.PullbackComparison.isGrpPullback V₀.ι G
  have h₂ := Pdiv.PullbackComparison.isGrpPullback t GV
  have hRelB : Out.RelAmple B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) :=
    GlobalTheory.DiagAmpleBC.relAmple_diag_pull _ _ GV hAV PV hPV hRel t B (Pdiv.PullbackComparison.pφ t GV)
      (Pdiv.PullbackComparison.pφ₂ t GV) h₂.1 (Pdiv.PullbackComparison.isSquare t GV)
  obtain ⟨ZL, iL, hiL, hfinL, -, hrep⟩ := GlobalTheory.kernelFiniteFlat_holds _ B hAB _
    (pull_isLB (pull_isLB hPV _) _) hRelB
  let ZV := (Over.pullback V₀.ι).obj Z
  let ZB := (Over.pullback t).obj ZV
  let iV : ZV ⟶ GV := (Over.pullback V₀.ι).map i
  let iB : ZB ⟶ B := (Over.pullback t).map iV
  have hmem : GlobalTheory.MemKL B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) iB := by
    refine GlobalTheory.memKL_of_push h₂ (pull_isLB hPV _) (pull_isLB (pull_isLB hPV _) _)
      (lbIso_diag GV B _ _ (Pdiv.PullbackComparison.isSquare t GV) hPV) iB ?_
    refine GlobalTheory.memKL_of_push h₁ (pull_isLB hP _) (pull_isLB hPV _)
      (lbIso_diag G GV _ _ (Pdiv.PullbackComparison.isSquare V₀.ι G) hP) _ ?_
    let zz : Over.mk ((ZB.hom ≫ t) ≫ V₀.ι) ⟶ Z :=
      Over.homMk (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) (by
        show (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ Z.hom = (pullback.snd ZV.hom t ≫ t) ≫ V₀.ι
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        congr 1
        exact pullback.condition)
    have e : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₁.1.w (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₂.1.w iB) = zz ≫ i := by
      apply Over.OverMorphism.ext
      show (iB.left ≫ Pdiv.PullbackComparison.pφ t GV) ≫ Pdiv.PullbackComparison.pφ V₀.ι G =
        (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ i.left
      simp only [Pdiv.PullbackComparison.pφ]
      rw [Pdiv.PullbackComparison.pullback_map_left_fst' t iV, Category.assoc,
        Pdiv.PullbackComparison.pullback_map_left_fst' V₀.ι i, Category.assoc]
    rw [e]
    apply hZ
    rintro _ ⟨y, rfl⟩
    show (((ZB.hom ≫ t) ≫ V₀.ι).base y) ∈ V₀
    exact (Scheme.Opens.range_ι V₀).subset ⟨(ZB.hom ≫ t).base y, rfl⟩
  obtain ⟨z, hz⟩ := (hrep ZB iB).1 hmem
  haveI : IsClosedImmersion iV.left := isClosedImmersion_pullback_map _ i
  haveI : IsClosedImmersion iB.left := isClosedImmersion_pullback_map _ iV
  have hz' : z.left ≫ iL.left = iB.left := congrArg (fun q => q.left) hz
  haveI : IsClosedImmersion (z.left ≫ iL.left) := by rw [hz']; infer_instance
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left iL.left
  have hZB : IsFinite ZB.hom := by
    rw [← Over.w z]; infer_instance
  have hV' : IsFinite ZV.hom := by
    have ec : ZV.hom = inv (pullback.fst ZV.hom t) ≫ pullback.snd ZV.hom t ≫ t := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [ec]
    haveI : IsFinite (pullback.snd ZV.hom t) := hZB
    infer_instance
  rw [← (isPullback_morphismRestrict Z.hom V₀).flip.isoPullback_hom_snd]
  haveI : IsFinite (pullback.snd Z.hom V₀.ι) := hV'
  infer_instance

end GlobalTheory.KernelRepFinite
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_closed_immersion : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  first | (exact @GlobalTheory.KernelRepFinite.isFinite_restrict) | (exact GlobalTheory.KernelRepFinite.isFinite_restrict) | (intros; apply GlobalTheory.KernelRepFinite.isFinite_restrict  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteKernelNearDiagonalAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem evc_symm {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    {Y : Over S} (a b : Y ⟶ G) : evc hP a b = evc hP b a := by
  have e := congrArg (CechPic.pull (lift b a).left) ((cls_eq_iff hP (pull_isLB hP _)).2 hs)
  rw [cls_pull hP _ (pull_isLB hP _), ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd] at e
  exact e.symm

theorem evc_eq_zero_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) {Y : Over S} (t : Y ⟶ T) (w : Y ⟶ G) :
    evc hP (t ≫ x) w = 0 := by
  have e := congrArg (CechPic.pull (lift w t).left) ((triv_ev_iff hP _ _).1 hx)
  rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem memKL_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    (a₁ : IsAdditive P) (a₂ : IsAdditive (AbDual.swap P)) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) :
    MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) x := by
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff G (P.pull (lift (𝟙 G) (𝟙 G)).left) x).IsLB := LB.isLB_linComb hL _ _
  have hdiag : ∀ {Y : Over S} (y : Y ⟶ G), CechPic.pull y.left (cls _ hL) = evc hP y y := fun y => by
    rw [cls_pull hP _ hL, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have z : cls _ hD = 0 := by
    have e₁ := pull_translDiff hL x hD (fst T G) (snd T G)
    rw [lift_fst_snd, Over.id_left, pull_id, hdiag, hdiag] at e₁
    rw [e₁, (isAdditive_iff hP).1 a₁, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂,
      (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂, evc_eq_zero_of_triv hP hx, evc_eq_zero_of_triv hP hx,
      evc_symm hP hs (snd T G) (fst T G ≫ x), evc_eq_zero_of_triv hP hx]
    simp
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, z, map_zero]

end GlobalTheory.KernelNear

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem exists_finite_kernel_near : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → ∀ s ∈ W, ∃ (V₀ : S'.Opens) (Z : Over S') (i : Z ⟶ G), s ∈ V₀ ∧ Mono i ∧ IsFinite (Z.hom ∣_ V₀) ∧ (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) ∧ (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) ∧ (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) ∧ (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V₀ : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → ∃ z : T ⟶ Z, z ≫ i = x) ∧ (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ ∃ c : (P.pull (lift (snd G (Over.mk (U.ι ≫ T.hom)) ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ z ≫ i) (fst G (Over.mk (U.ι ≫ T.hom)))).left).Gen, c.IsGen) := by
  intro S' _ G _ _ P hG hP h₁ h₂ hs W hW s hsW
  obtain ⟨V₀, hV₀, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := W) hsW
  obtain ⟨D, _, Q, h, hDab, q, -, hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom S' G G (𝟙 G) P hG hG inferInstance hP h₁ h₂
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have hD : ∀ {Y : Over S'} (a b : Y ⟶ G), evc hP a b = evc q.isLB a (b ≫ h) := fun a b => by
    have e' := (cls_eq_iff (pull_isLB hP _) (pull_isLB q.isLB _)).2 e
    rw [MonoidalCategory.id_tensorHom_id, Over.id_left, cls_pull hP _ (pull_isLB hP _), pull_id,
      cls_pull q.isLB _ (pull_isLB q.isLB _)] at e'
    rw [evc, e', ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd]
    rfl
  have K : ∀ {T : Over S'} (x : T ⟶ G), Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left) ↔ x ≫ h = 1 := by
    intro T x
    rw [triv_ev_iff hP, evc_symm hP hs, hD, Category.assoc]
    refine ⟨fun hx => q.eq_one _ ((triv_ev_iff q.isLB _ _).2 hx), fun hx => ?_⟩
    rw [hx, MonObj.comp_one]
    exact evc_one_right q.isLB q.zero _
  have : Mono (η[D]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
  have kerh : ∀ {T : Over S'} (z : T ⟶ pullback h (η[D])), (z ≫ pullback.fst h (η[D])) ≫ h = 1 := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, toUnit_unique (z ≫ pullback.snd _ _) (toUnit _)]
    rfl
  have fac : ∀ {T : Over S'} (x : T ⟶ G), x ≫ h = 1 → ∃ z : T ⟶ pullback h (η[D]), z ≫ pullback.fst h (η[D]) = x :=
    fun x hx => ⟨pullback.lift x (toUnit _) (by rw [hx]; rfl), pullback.lift_fst _ _ _⟩
  have hcl : IsClosedImmersion (pullback.fst h (η[D])).left := by
    have hpb := (IsPullback.of_hasPullback h (η[D])).map (Over.forget S')
    have := hDab.proper
    have : IsClosedImmersion ((η[D]).left ≫ D.hom) := by
      rw [Over.w (η[D])]
      exact (inferInstance : IsClosedImmersion (𝟙 S'))
    have : IsClosedImmersion (η[D]).left := IsClosedImmersion.of_comp _ D.hom
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip this
  refine ⟨V₀, pullback h (η[D]), pullback.fst h (η[D]), hsV, inferInstance,
    GlobalTheory.T.relatively_ample_closed_immersion S' G P hG hP V₀ hV₀ (hW V₀ fun _ hx => hVW hx) _ _ hcl
      (fun T z _ => memKL_of_triv hP hs a₁ a₂ ((K _).2 (kerh z))), ?_, ?_, ?_, ?_, ?_⟩
  · intro T _
    exact fac 1 (MonObj.one_comp h)
  · intro T a b _
    refine fac _ ?_
    rw [MonObj.mul_comp, kerh, kerh, _root_.mul_one]
  · intro T a _
    refine fac _ ?_
    rw [GrpObj.inv_comp, kerh, inv_one]
  · intro T x _ hx
    exact fac x ((K x).1 hx)
  · intro T z _ p
    refine ⟨⊤, trivial, (K _).2 ?_⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc z, kerh, MonObj.comp_one]

end GlobalTheory.KernelNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteKernelNearDiagonalAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_kernel_near_diagonal_ample : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → ∀ s ∈ W, ∃ (V₀ : S'.Opens) (Z : Over S') (i : Z ⟶ G), s ∈ V₀ ∧ Mono i ∧ IsFinite (Z.hom ∣_ V₀) ∧ (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) ∧ (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) ∧ (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) ∧ (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V₀ : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → ∃ z : T ⟶ Z, z ≫ i = x) ∧ (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ ∃ c : (P.pull (lift (snd G (Over.mk (U.ι ≫ T.hom)) ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ z ≫ i) (fst G (Over.mk (U.ι ≫ T.hom)))).left).Gen, c.IsGen) := by
  first | (exact @GlobalTheory.KernelNear.exists_finite_kernel_near) | (exact GlobalTheory.KernelNear.exists_finite_kernel_near) | (intros; apply GlobalTheory.KernelNear.exists_finite_kernel_near <;> assumption)
end
end

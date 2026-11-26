module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPol

theorem scalar_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → ∀ (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1))) (a' : D'.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D' ga' a' → ∀ y : D'.X, ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, k (xe y i) (xe y j) ^ W i j := by
  intro R _ _ _ Q D' r W pr xe w hpsi k hk ga' a' h' y
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  haveI := Q.isAb.proper
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPol.exists_int Q.B Q.M.L Q.M.isLB z
  obtain ⟨J', hJ', iJ'⟩ := GlobalTheory.Mum.TensPos.exists_int D'.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hψ' : val (D'.psi y) (𝟙 _) z J' = E (a' y) * val (ga' y) (toUnit (TK R)).left z J' :=
    Units.ext (((h' y).2 (TK R) (𝟙 _) z J' hJ').trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have mg' : val (ga' y) (toUnit (TK R)).left z J' ∈ unitsS z := GlobalTheory.Mum.TensPos.val_mem D'.P z iJ' _ _ _
  have mτ : ∀ b c : Q.X, ∃ u ∈ unitsS z, val (Q.tau b c) (𝟙 _) z J = u * E (k b c) := fun b c => by
    obtain ⟨u, -, hu⟩ := hk b c
    refine ⟨_, GlobalTheory.Mum.TensPol.val_mem z iJ (lamPts (Q.c b) (Q.c c)) (fun i => ?_) negε u, ?_⟩
    · fin_cases i <;> exact Over.w _
    · rw [hu z J hJ, gm_unitOn, _root_.mul_comm]
  choose u hu eu using mτ
  have e := hpsi y z J J' hJ hJ'
  have hφ : ∀ k, tensφ pr k ≫ Q.B.hom = D'.P.A.hom := by
    rintro ⟨⟨i, j⟩, k⟩
    fin_cases k <;> exact Over.w _
  have mw : gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) ∈ unitsS z := by
    refine gm_mem z (D'.c y).left
      (LB.wchart Q.M.L (tensφ pr) (fun k => J (D'.xK y ≫ tensφ pr k)) ⊓ D'.P.L.U (J' (D'.xK y)))
      ⟨Set.mem_iInter.2 fun k => ?_, iJ' _ (Over.w _)⟩ _
    have := iJ ((D'.c y).left ≫ tensφ pr k) (by rw [Category.assoc, hφ]; exact Over.w _)
    rw [← Category.assoc] at this
    exact this
  rw [hψ'] at e
  simp only [eu, mul_zpow, Finset.prod_mul_distrib] at e
  obtain ⟨v, hv, ev'⟩ := mul_mem (mul_mem (inv_mem mg') mw)
    (prod_mem fun i (_ : i ∈ Finset.univ) => prod_mem fun j (_ : j ∈ Finset.univ) => zpow_mem (hu (xe y i) (xe y j)) (W i j))
  refine ⟨v, hv, hE ?_⟩
  rw [map_mul, map_prod]
  simp only [map_prod, map_zpow]
  rw [show E v = _ from ev', eq_mul_inv_of_mul_eq e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum.TensPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriodsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → ∀ (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1))) (a' : D'.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D' ga' a' → ∀ y : D'.X, ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, k (xe y i) (xe y j) ^ W i j := by
  first | exact @GlobalTheory.Mum.TensPol.scalar_tens | exact GlobalTheory.Mum.TensPol.scalar_tens | (intros; apply GlobalTheory.Mum.TensPol.scalar_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodScalarCoordinatePolarisedDataLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodScalarCoordinatePolarisedDataLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

namespace GlobalTheory.Mum.TensPol

theorem exists_tauCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (a b : Q.X),
    ∃ k, Q.TauCoord a b k := by
  intro R _ _ _ Q a b
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB (lamPts (Q.c a) (Q.c b)) negε
  have e : ∀ i, (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) i =
      lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) i := by
    intro i
    fin_cases i
    · exact congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))
    · rfl
    · rfl
    · exact congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))
  obtain ⟨t, ht, hv⟩ := exists_gen Q.M.isLB (φ' := fun i => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) i) (ε' := negε)
    (fun U _ h => by simp only [e]) (Q.tau a b) (Q.tau_gen a b)
  obtain ⟨c, hc⟩ := exists_unit_val_eq_mul Q.M.isLB ht
    (DVR.pullGen_isGen Q.M.L _ _ u hu (toUnit (TK R)).left)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c, u, hu, fun z J hJ => ?_⟩
  have ec : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c) = c :=
    Units.ext (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) _)
  rw [ec, ← hv _ _ z J hJ]
  refine Units.ext ((hc _ (𝟙 _) z J hJ).trans ?_)
  refine congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial _) (congrArg Units.val ((val_pull hJ u _ (𝟙 _)).trans ?_))
  rw [Category.id_comp]

end GlobalTheory.Mum.TensPol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodScalarCoordinatePolarisedDataLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodScalarCoordinate_polarisedData_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (a b : Q.X), ∃ k, Q.TauCoord a b k := by
  first | exact @GlobalTheory.Mum.TensPol.exists_tauCoord | exact GlobalTheory.Mum.TensPol.exists_tauCoord | (intros; apply GlobalTheory.Mum.TensPol.exists_tauCoord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodScalarCoordinatesSymmBimultUpToUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodScalarCoordinatesSymmBimultUpToUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolRel

theorem tauCoord_rel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  intro R _ _ _ Q k hk
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  haveI := Q.isAb.proper
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPol.exists_int Q.B Q.M.L Q.M.isLB z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hτ : ∀ a b, ∃ v ∈ unitsS z, val (Q.tau a b) (𝟙 _) z J = E (k a b) * v := fun a b => by
    obtain ⟨u, -, hu⟩ := hk a b
    refine ⟨_, GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ u, (hu z J hJ).trans (congrArg (· * _) (gm_unitOn z _))⟩
    fin_cases i <;> exact Over.w _
  choose v hv ev' using hτ
  refine ⟨fun a b => ?_, fun a a' b => ?_⟩
  · refine ⟨k b a * (k a b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_symm a b z J hJ
    rw [ev', ev'] at e
    have : E (k b a * (k a b)⁻¹) = v a b * (v b a)⁻¹ := by
      rw [map_mul, map_inv]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) -e'
    exact this ▸ mul_mem (hv a b) (inv_mem (hv b a))
  · refine ⟨k (a + a') b * (k a b * k a' b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_add a a' b z J hJ
    have hc : cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) ∈ unitsS z := by
      rw [← val_cub Q.cub (toUnit (TK R)) hJ]
      refine GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ _
      exact Over.w (lift (Q.c a) (lift (Q.c a') (Q.c b)) ≫ psum Q.B (x3 Q.B) i.down)
    rw [ev', ev', ev'] at e
    generalize cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) = w at e hc
    have : E (k (a + a') b * (k a b * k a' b)⁻¹) = v a b * v a' b * (v (a + a') b)⁻¹ * w⁻¹ := by
      rw [map_mul, map_inv, map_mul]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e'
    exact this ▸ mul_mem (mul_mem (mul_mem (hv a b) (hv a' b)) (inv_mem (hv _ b))) (inv_mem hc)

end GlobalTheory.Mum.TensPolRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodScalarCoordinatesSymmBimultUpToUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodScalarCoordinates_symm_bimult_up_to_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  first | exact @GlobalTheory.Mum.TensPolRel.tauCoord_rel | exact GlobalTheory.Mum.TensPolRel.tauCoord_rel | (intros; apply GlobalTheory.Mum.TensPolRel.tauCoord_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolScal

theorem exists_bilin (R : Type) [CommRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    (k : X → X → (FractionRing R)ˣ) (hs : ∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b)
    (ha : ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ, ∀ a b, ∃ u ∈ unitsK R, k a b = u * (B a b).toMul := by
  set H := unitsK R
  have h1 : ∀ u ∈ H, (QuotientGroup.mk' H) u = 1 := fun u hu => (QuotientGroup.eq_one_iff u).2 hu
  let g : X → X → Additive ((FractionRing R)ˣ ⧸ H) := fun a b => Additive.ofMul (QuotientGroup.mk' H (k a b))
  have gs : ∀ a b, g b a = g a b := fun a b => by
    obtain ⟨u, hu, e⟩ := hs a b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul]
  have ga : ∀ a a' b, g (a + a') b = g a b + g a' b := fun a a' b => by
    obtain ⟨u, hu, e⟩ := ha a a' b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul, ofMul_mul]
  have gb : ∀ a b b', g a (b + b') = g a b + g a b' := fun a b b' => by
    rw [gs, ga, gs b, gs b']
  have gsa : ∀ (c : ℤ) a b, g (c • a) b = c • g a b := fun c a b =>
    map_zsmul (AddMonoidHom.mk' (fun a => g a b) (fun a a' => ga a a' b)) c a
  have gsb : ∀ (c : ℤ) a b, g a (c • b) = c • g a b := fun c a b => by
    rw [gs, gsa, gs]
  let F : X →ₗ[ℤ] X →ₗ[ℤ] Additive ((FractionRing R)ˣ ⧸ H) := LinearMap.mk₂ ℤ g ga gsa gb gsb
  let π : Additive (FractionRing R)ˣ →+ Additive ((FractionRing R)ˣ ⧸ H) := MonoidHom.toAdditive (QuotientGroup.mk' H)
  let bs := Module.Free.chooseBasis ℤ X
  let B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ :=
    bs.constr ℤ fun i => bs.constr ℤ fun j => Additive.ofMul (k (bs i) (bs j))
  have e : B.compr₂ π.toIntLinearMap = F := LinearMap.ext_basis bs bs fun i j => by
    simp [B, F, g, π]
  refine ⟨B, fun a b => ⟨k a b * ((B a b).toMul)⁻¹, ?_, by rw [inv_mul_cancel_right]⟩⟩
  have e1 : QuotientGroup.mk' H (B a b).toMul = QuotientGroup.mk' H (k a b) :=
    congrArg Additive.toMul (congrArg (fun C => C a b) e)
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' H _ = 1
  rw [map_mul, map_inv, ← e1, mul_inv_cancel]

end GlobalTheory.Mum.TensPolScal

namespace GlobalTheory.Mum.TensPolScal

theorem scalars_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ _ k hs ha hp r W hW a' h'
  obtain ⟨B, hB⟩ := exists_bilin R X k hs ha
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  let κ' : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j
  let P : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z i) (z j)).toMul ^ W i j
  let Q : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z j) (z i)).toMul ^ W i j
  have eP : ∀ z, Additive.ofMul (P z) = ∑ i, ∑ j, W i j • B (z i) (z j) := fun z => by
    simp only [P, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eQ : ∀ z, Additive.ofMul (Q z) = ∑ i, ∑ j, W i j • B (z j) (z i) := fun z => by
    simp only [Q, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eκ' : ∀ z, κ' z = P z * Q z := by
    intro z
    apply Additive.ofMul.injective
    rw [ofMul_mul, eP, eQ, ← Finset.sum_add_distrib]
    simp only [κ', κ, ofMul_prod, ofMul_zpow, ofMul_mul, ofMul_inv, ofMul_toMul, map_add (f := _), LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]
    congr 1
    abel

  have hBs : ∀ a b, ∃ v ∈ unitsK R, (B b a).toMul = v * (B a b).toMul := by
    intro a b
    obtain ⟨w, hw, e⟩ := hs a b
    refine ⟨(u b a)⁻¹ * w * u a b, mul_mem (mul_mem (inv_mem (hu b a)) hw) (hu a b), ?_⟩
    rw [show (B b a).toMul = (u b a)⁻¹ * k b a by rw [eu b a, inv_mul_cancel_left], e, eu a b]
    group
  choose v hv ev using hBs
  have eQP : ∀ z, Q z = (∏ i, ∏ j, v (z i) (z j) ^ W i j) * P z := by
    intro z
    simp only [Q, P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [ev (z i) (z j), mul_zpow]
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add (f := _), LinearMap.add_apply]
    abel
  have κp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (κ x : FractionRing R) = algebraMap R _ s := fun x hx => by
    have := mem_of_unit _ ((unitsK R).inv_mem (hu x x)) (hp x hx)
    rwa [eu x x, inv_mul_cancel_left] at this
  have κ'p := GlobalTheory.Mum.TPos.tensor_pos R X κ κn κc κp W hW

  have Pp : ∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (P z : FractionRing R) = algebraMap R _ s := by
    intro z hz
    have hd : (∏ i, ∏ j, v (z i) (z j) ^ W i j) ∈ unitsK R :=
      prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hv _ _) _
    have e2 : P z ^ 2 = (∏ i, ∏ j, v (z i) (z j) ^ W i j)⁻¹ * κ' z := by
      rw [eκ', eQP, mul_left_comm, inv_mul_cancel_left, pow_two]
    obtain ⟨s, hsm, es⟩ := mem_of_unit _ ((unitsK R).inv_mem hd) (κ'p z hz)
    rw [← e2, Units.val_pow_eq_pow_val] at es
    have hint : IsIntegral R ((P z : (FractionRing R)ˣ) : FractionRing R) :=
      IsIntegral.of_pow (by norm_num : 0 < 2) (es ▸ isIntegral_algebraMap)
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have ht2 : t ^ 2 = s := by
      apply IsFractionRing.injective R (FractionRing R)
      rw [map_pow, ht, es]
    exact ⟨t, (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 (ht2 ▸ hsm), ht.symm⟩
  have Pn : ∀ z, P (-z) = P z := fun z => by
    apply Additive.ofMul.injective
    simp [eP]
  have Pc : ∀ x y w, P (x + y + w) * P x * P y * P w = P (x + y) * P (x + w) * P (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, eP, ← Finset.sum_add_distrib, ← smul_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have Pt := GlobalTheory.QuadTend.finite_not_mem_pow R (Fin r → X) P Pn Pc Pp
  have ea : ∀ z, ∃ v ∈ unitsK R, a' z = v * P z := fun z => by
    obtain ⟨w, hw, e⟩ := h' z
    refine ⟨w * ∏ i, ∏ j, u (z i) (z j) ^ W i j,
      mul_mem hw (prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hu _ _) _), ?_⟩
    rw [e, _root_.mul_assoc]
    congr 1
    simp only [P, eu, mul_zpow, Finset.prod_mul_distrib]
  refine ⟨fun z hz => ?_, fun n => (Pt n).subset fun z hz hm => hz ?_⟩
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw (Pp z hz)
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw hm

end GlobalTheory.Mum.TensPolScal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_scalars_mem_maximalIdeal_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.Mum.TensPolScal.scalars_tens | exact GlobalTheory.Mum.TensPolScal.scalars_tens | (intros; apply GlobalTheory.Mum.TensPolScal.scalars_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiPosTendstoZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPol

theorem psi_pos_tendsto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Q.IsPos (maximalIdeal R) → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hψ hW hQ
  obtain ⟨hN, hI, -, -⟩ := hR
  have hk0 : ∀ a b, ∃ k, Q.TauCoord a b k ∧
      (a = b → a ≠ 0 → ∃ s ∈ maximalIdeal R, (k : FractionRing R) = algebraMap R _ s) := by
    intro a b
    by_cases h : a = b ∧ a ≠ 0
    · obtain ⟨rfl, ha⟩ := h
      obtain ⟨s, hs, k, hk, hc⟩ := hQ a ha
      exact ⟨k, hc, fun _ _ => ⟨s, hs, hk⟩⟩
    · obtain ⟨k, hk⟩ := GlobalTheory.T.exists_periodScalarCoordinate_polarisedData_local R Q a b
      exact ⟨k, hk, fun e ne => (h ⟨e, ne⟩).elim⟩
  choose k hk hkp using hk0
  obtain ⟨hs, ha⟩ := GlobalTheory.T.periodScalarCoordinates_symm_bimult_up_to_units R Q k hk
  obtain ⟨ga', a', h'⟩ := GlobalTheory.exists_psiScal R D'
  obtain ⟨hp, ht⟩ := GlobalTheory.T.tensorData_scalars_mem_maximalIdeal_tendsto_zero R Q.X k hs ha (fun y hy => hkp y y rfl hy) W hW (fun z => a' (xe.symm z))
    (fun z => by simpa only [AddEquiv.apply_symm_apply] using GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods R Q D' W pr xe w hψ k hk ga' a' h' (xe.symm z))
  refine ⟨fun χ hχ => ?_, fun n => ((ht n).preimage xe.injective.injOn).subset fun χ hχ hm => hχ ?_⟩
  · obtain ⟨s, hs, e⟩ := hp (xe χ) (fun h0 => hχ (xe.map_eq_zero_iff.1 h0))
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩
  · obtain ⟨s, hs, e⟩ := hm
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩

end GlobalTheory.Mum.TensPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiPosTendstoZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_psi_pos_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Q.IsPos (maximalIdeal R) → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  first | exact @GlobalTheory.Mum.TensPol.psi_pos_tendsto | exact GlobalTheory.Mum.TensPol.psi_pos_tendsto | (intros; apply GlobalTheory.Mum.TensPol.psi_pos_tendsto <;> assumption)
end

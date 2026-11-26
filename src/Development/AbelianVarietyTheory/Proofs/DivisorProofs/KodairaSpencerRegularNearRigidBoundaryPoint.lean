module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorCommutingPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaud
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerOfLogDerivationChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerChartOfHeatOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerChartOfHeatOperators
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

theorem exists_derivation_intAlgebra' {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩

theorem exists_isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (O : Type) [CommRing O] [StarRing O] [Module O P.D.toPre.X] (oa : P.D.toPre.OAct O) (Y : Ray oa) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab O _ _ _ oa Y n vY dd hdd D hD h hbas hdef
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m d
  haveI : IsNoetherianRing (ChartRing k m d) := hA.1
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) := hA.2.2.2
  letI := H.starRing
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h0 => by
    have h4 := congrArg (fun f : ChartRing k m d => MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1) f) h0
    simp [bdParam, MvPowerSeries.coeff_X] at h4
  obtain ⟨ρ, hρ⟩ := GlobalTheory.TorusModel.exists_ringAct GlobalTheory.allSixLaws.1.globalFns P.oD (Φ := Y.Φ) Y.rep
  let Y' : Ray P.oD := { H := Y.H, Φ := Y.Φ, isGt := Y.isGt, rep := Y.rep, ρ := ρ, smul := hρ }
  choose v' hv' using fun a => tanPt E H (ChartRing k m d) t P Y' (vY a)
  refine ⟨fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left,
    fun a => isTanAtG_tv E H _ t (v' a), ?_⟩
  obtain ⟨D', hD'⟩ := exists_derivation_intAlgebra' _ D
  have key := GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud E H (ChartRing k m d) t P m (bdParam k m d) gam hmon hne hab Y' n vY dd hdd v' hv' D'
  rw [hD'] at key
  exact key h hbas hdef

end GlobalTheory.ChartKSBracket
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerChartOfHeatOperatorsStatement
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
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_chart_of_heat_operators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (O : Type) [CommRing O] [StarRing O] [Module O P.D.toPre.X] (oa : P.D.toPre.OAct O) (Y : Ray oa) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  first | exact @GlobalTheory.ChartKSBracket.exists_isKS_of_heat | exact GlobalTheory.ChartKSBracket.exists_isKS_of_heat | (intros; apply GlobalTheory.ChartKSBracket.exists_isKS_of_heat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerOfLogDerivationChart
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

namespace GlobalTheory.LogKSChart

theorem exists_derivation_intAlgebra {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩


set_option maxHeartbeats 800000 in
theorem exists_isKS_of_logDer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∃ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hcomb D hD
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨Y⟩ : Nonempty (Ray P.oD) := inferInstance
  obtain ⟨n', vY, dd, hdd⟩ := GlobalTheory.T.exists_invariant_tangent_basis_raynaudExtension (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  obtain ⟨D', hD'⟩ := exists_derivation_intAlgebra _ D
  obtain ⟨h, hb, hdef⟩ := GlobalTheory.T.exists_torusInvariant_heatOperator_commuting_periods (ChartRing k m d) P.D (𝓞 E) P.oD Y n' vY dd hdd m (bdParam k m d) gam hmon hne D'
    (by rw [hD']; exact hD)
  revert h
  rw [hD']
  intro h hb hdef
  obtain ⟨v', hv', hks⟩ := GlobalTheory.T.exists_kodairaSpencer_chart_of_heat_operators E H k m d t P gam hmon hli hab (𝓞 E) P.oD Y n' vY dd hdd D hD h hb hdef
  choose B hB using fun a => (hcomb (v' a) (hv' a)).exists
  exact ⟨_, GlobalTheory.KSFrameChange.isKS_frame_change E H (Sp (ChartRing k m d)) t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) n' n v' v (Matrix.of B) (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) _ hv' hv hB hks⟩

end GlobalTheory.LogKSChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerOfLogDerivationChartStatement
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
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_of_logDerivation_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∃ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ := by
  first | exact @GlobalTheory.LogKSChart.exists_isKS_of_logDer | exact GlobalTheory.LogKSChart.exists_isKS_of_logDer | (intros; apply GlobalTheory.LogKSChart.exists_isKS_of_logDer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomain
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

namespace LocRegDesc

theorem exists_unit_mul_eq_of_flat {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    (ρ : A →+* R) (hρ : ρ.Flat) (s b : A) (r : R) (hs : ρ s = ρ b * r) :
    ∃ g a : A, IsUnit (ρ g) ∧ g * s = b * a := by
  letI := ρ.toAlgebra
  haveI : Module.Flat A R := hρ
  have hrel : ∑ i, (![s, -b] : Fin 2 → A) i • (![1, r] : Fin 2 → R) i = 0 := by
    simp [Fin.sum_univ_two, Algebra.smul_def, RingHom.algebraMap_toAlgebra, hs]
  have ht : Module.IsTrivialRelation (![s, -b] : Fin 2 → A) (![1, r] : Fin 2 → R) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, a, y, hx, hf⟩ := ht
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (ρ (a 0 j)) := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : R) ∈ maximalIdeal R := by
      have := hx 0
      simp only [Matrix.cons_val_zero] at this
      rw [this]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      exact Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 (hne j))
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨a 0 j, a 1 j, hj, ?_⟩
  have := hf j
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linear_combination this

end LocRegDesc

namespace LocRegDesc

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill_on_basicOpen (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0)
    (f : Γ(X, U.1)) (hf : X.basicOpen f ≤ W) :
    ∃ g, IsUnit (ρ g) ∧
      (X.presheaf.map (homOfLE hf).op).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0 := by
  haveI hloc := U.2.isLocalization_basicOpen f
  set δV := (X.presheaf.map (homOfLE hf).op).hom δ with hδV
  set hV := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom h with hhV
  have key : X.basicOpen hV = X.basicOpen f ⊓ X.basicOpen h := Scheme.basicOpen_res _ _ _
  have hB : X.basicOpen hV ≤ X.basicOpen h := key ▸ inf_le_right
  have hzero : (X.presheaf.map (homOfLE (X.basicOpen_le hV)).op).hom δV = 0 := by
    rw [hδV, res_res, ← res_res hh hB, hδ, map_zero]
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (U.2.basicOpen f).isCompact δV hV hzero
  obtain ⟨⟨e, m⟩, hem⟩ := IsLocalization.surj (Submonoid.powers f) δV
  simp only at hem
  have h0 : algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (h ^ n * e) = 0 := by
    rw [map_mul, ← hem, map_pow]
    change hV ^ n * (δV * _) = 0
    rw [← _root_.mul_assoc, hn, zero_mul]
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).1 h0
  simp only at hj
  have hc : ρ (f ^ j * e) = 0 := by
    have : ρ h ^ n * ρ (f ^ j * e) = 0 := by
      rw [← map_pow, ← map_mul, show h ^ n * (f ^ j * e) = f ^ j * (h ^ n * e) by ring, hj, map_zero]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hρh)
  obtain ⟨g, a, hu, hg⟩ := exists_unit_mul_eq_of_flat ρ hρ (f ^ j * e) 0 0 (by simp [hc])
  refine ⟨g, hu, ?_⟩
  rw [map_mul, res_res]
  change algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) g * δV = 0
  have u1 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (m : Γ(X, U.1))) :=
    IsLocalization.map_units _ m
  have u2 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (f ^ j)) :=
    IsLocalization.map_units _ (⟨f ^ j, j, rfl⟩ : Submonoid.powers f)
  rw [← u1.mul_left_eq_zero, ← u2.mul_left_eq_zero, _root_.mul_assoc _ δV, hem, ← map_mul, ← map_mul,
    show g * e * f ^ j = g * (f ^ j * e) by ring, hg, zero_mul, map_zero]

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0) :
    ∃ g, IsUnit (ρ g) ∧ (X.presheaf.map (homOfLE hWU).op).hom g * δ = 0 := by
  let p : Set X → Prop := fun t => ∃ g, IsUnit (ρ g) ∧ ∀ y (hy : y ∈ W), y ∈ t →
    (X.presheaf.germ W y hy).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0
  have hp : p (W : Set X) := by
    refine hW.induction_on ?_ ?_ ?_ ?_
    · exact ⟨1, by simp, fun y _ hy => hy.elim⟩
    · rintro s t hst ⟨g, hg, H⟩
      exact ⟨g, hg, fun y hy hs => H y hy (hst hs)⟩
    · rintro s t ⟨g₁, hg₁, H₁⟩ ⟨g₂, hg₂, H₂⟩
      refine ⟨g₁ * g₂, by rw [map_mul]; exact hg₁.mul hg₂, fun y hy hyst => ?_⟩
      rw [map_mul (X.presheaf.map (homOfLE hWU).op).hom g₁ g₂]
      rcases hyst with hs | ht
      · rw [mul_right_comm, map_mul (X.presheaf.germ W y hy).hom, H₁ y hy hs, zero_mul]
      · rw [_root_.mul_assoc, map_mul (X.presheaf.germ W y hy).hom, H₂ y hy ht, mul_zero]
    · intro x hx
      obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      obtain ⟨g, hg, H⟩ := exists_unit_kill_on_basicOpen X U W hWU R ρ hρ h hh hρh δ hδ f hf
      refine ⟨X.basicOpen f, mem_nhdsWithin_of_mem_nhds ((X.basicOpen f).isOpen.mem_nhds hxf),
        g, hg, fun y hy hyf => ?_⟩
      rw [← X.presheaf.germ_res_apply (homOfLE hf) y hyf, H, map_zero]
  obtain ⟨g, hg, H⟩ := hp
  refine ⟨g, hg, ?_⟩
  refine TopCat.Presheaf.section_ext X.sheaf W _ 0 fun y hy => ?_
  exact (H y hy hy).trans (map_zero (X.presheaf.germ W y hy).hom).symm

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_one (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (θ : Γ(X, W))
    (H : ∀ (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) *
        (X.presheaf.map (homOfLE hh).op).hom θ → ρ h ^ N ∣ ρ s) :
    ∃ g, IsUnit (ρ g) ∧ ∃ s : Γ(X, U.1),
      (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ := by
  haveI hloc := U.2.isLocalization_basicOpen h
  obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hsm⟩ :=
    IsLocalization.surj (Submonoid.powers h) ((X.presheaf.map (homOfLE hh).op).hom θ)
  simp only at hsm
  obtain ⟨r, hr⟩ := H s N (by
    change algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) s =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) * _
    rw [← hsm, mul_comm])
  obtain ⟨g₁, a, hu₁, hga⟩ := exists_unit_mul_eq_of_flat ρ hρ s (h ^ N) r (by rw [map_pow, hr])
  set δ := (X.presheaf.map (homOfLE hWU).op).hom a - (X.presheaf.map (homOfLE hWU).op).hom g₁ * θ
    with hδdef
  have hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0 := by
    have u : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N)) :=
      IsLocalization.map_units _ (⟨h ^ N, N, rfl⟩ : Submonoid.powers h)
    rw [← u.mul_left_eq_zero, hδdef, map_sub, map_mul, res_res, res_res]
    change (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) a - algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) g₁ *
      (X.presheaf.map (homOfLE hh).op).hom θ) * algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) = 0
    rw [sub_mul, _root_.mul_assoc, hsm, ← map_mul, ← map_mul, hga, mul_comm a, sub_self]
  obtain ⟨g₂, hu₂, hk⟩ := exists_unit_kill X U W hWU hW R ρ hρ h hh hρh δ hδ
  refine ⟨g₂ * g₁, by rw [map_mul]; exact hu₂.mul hu₁, g₂ * a, ?_⟩
  rw [map_mul, map_mul]
  rw [hδdef] at hk
  linear_combination hk

end LocRegDesc

theorem LocRegDesc.descent : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  intro X U W hWU hW R _ _ _ ρ hρ mm hmm h hh hρh J _ θ H
  choose g hg s hs using fun i => LocRegDesc.exists_unit_one X U W hWU hW R ρ hρ h hh hρh (θ i) (H i)
  haveI := Fintype.ofFinite J
  classical
  refine ⟨∏ i, g i, ?_, fun i => ⟨s i * ∏ j ∈ Finset.univ.erase i, g j, ?_⟩⟩
  · rw [← hmm, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hg i)
  · rw [map_mul, hs i, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i), map_mul]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomainStatement
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
theorem _root_.GlobalTheory.T.sections_descend_along_flat_map_to_localDomain : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  first | exact @GlobalTheory.LocRegDesc.descent | exact GlobalTheory.LocRegDesc.descent | (intros; apply GlobalTheory.LocRegDesc.descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenInteriorContainingToricChartGener
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenInteriorContainingToricChartGener
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem exists_basicOpen_chartHom_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U W : Y.X.affineOpens), W.1 = U.1 ⊓ interior Y → ∀ (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∃ h : Γ(Y.X, U.1), Y.X.basicOpen h ≤ W.1 ∧ GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y U W hW k _ m d ξ hx hbd
  let gp : Sp (ChartRing k m d) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (ChartRing k m d))
  have hprod : (∏ i, bdParam k m d i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ hX => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) hX
      simp at this
  have hgbd : ξ gp ∉ genBd Y := by
    rw [hbd]
    exact fun h => hprod ((Submodule.mem_bot _).1 h)
  have hgab : genι Y (ξ gp) ∈ interior Y := by
    have := (mem_genBd_iff (Y := Y) (x := ξ gp)).not.1 hgbd
    rw [not_not, ← coe_interior] at this
    exact this
  have hsp : gp ⤳ closedPoint (ChartRing k m d) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (fun x hx => by
      rw [(Submodule.mem_bot _).1 hx]; exact Ideal.zero_mem _)
  have hgU : ξ gp ∈ genι Y ⁻¹ᵁ U.1 :=
    (hsp.map ξ.continuous).mem_open (genι Y ⁻¹ᵁ U.1).isOpen hx
  have hyW : genι Y (ξ gp) ∈ W.1 := by
    rw [hW]; exact ⟨hgU, hgab⟩
  obtain ⟨h, hle, hmem⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨_, hyW⟩ hgU
  refine ⟨h, hle, fun h0 => ?_⟩
  have hg0 : gp ∈ ξ ⁻¹ᵁ (gen Y).basicOpen (((genι Y).app U.1).hom h) := by
    show ξ gp ∈ (gen Y).basicOpen _
    rw [← Scheme.preimage_basicOpen]; exact hmem
  rw [Scheme.preimage_basicOpen] at hg0
  have e := congrArg (fun q => q.hom (((genι Y).app U.1).hom h)) (Scheme.germ_stalkClosedPointTo ξ _ hx)
  simp only [chartHom, RingHom.comp_apply] at h0
  change (Scheme.stalkClosedPointTo ξ).hom (((gen Y).presheaf.germ _ _ hx).hom _) = 0 at h0
  rw [← CommRingCat.comp_apply] at h0
  rw [e] at h0
  have h1 := h0
  rw [CommRingCat.comp_apply] at h1
  have hz : (ξ.app (genι Y ⁻¹ᵁ U.1)).hom (((genι Y).app U.1).hom h) = 0 :=
    (ConcreteCategory.bijective_of_isIso _).1 (h1.trans (map_zero _).symm)
  rw [hz, Scheme.basicOpen_zero] at hg0
  exact hg0

end GlobalTheory.LocReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenInteriorContainingToricChartGenerStatement
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
theorem _root_.GlobalTheory.T.exists_basicOpen_interior_containing_toricChart_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U W : Y.X.affineOpens), W.1 = U.1 ⊓ interior Y → ∀ (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∃ h : Γ(Y.X, U.1), Y.X.basicOpen h ≤ W.1 ∧ GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 := by
  first | exact @GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero | exact GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero | (intros; apply GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdeal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.LocRegFlat

theorem germ_flat {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.Flat := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)

theorem chartHom_flat_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx he mm hmm hmem
  have key : GlobalTheory.LocReg.chartHom Y U ξ hx = ((Y.X.presheaf.germ U.1 (genι Y (ξ (closedPoint _))) hx ≫
      (genι Y).stalkMap (ξ (closedPoint _))) ≫ Scheme.stalkClosedPointTo ξ).hom := by
    have h := (genι Y).germ_stalkMap U.1 (ξ (closedPoint _)) hx
    unfold GlobalTheory.LocReg.chartHom
    rw [h]; rfl
  rw [key]
  simp only [CommRingCat.hom_comp]
  have hg := germ_flat U.2 _ hx
  have hs : ((genι Y).stalkMap (ξ (closedPoint _))).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  refine ⟨(hg.comp hs).comp he.1, ?_⟩
  symm
  refine hmm.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top) ?_
  intro f hf
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hmem f hf
  rw [Scheme.mem_basicOpen]
  simp only [RingHom.comp_apply] at hu
  exact isUnit_of_map_unit ((genι Y).stalkMap _).hom _ (isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom _ hu)
  exact hx
end GlobalTheory.LocRegFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdealStatement
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
theorem _root_.GlobalTheory.T.toricChart_ringMap_flat_and_comap_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  first | exact @GlobalTheory.LocRegFlat.chartHom_flat_comap | exact GlobalTheory.LocRegFlat.chartHom_flat_comap | (intros; apply GlobalTheory.LocRegFlat.chartHom_flat_comap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfLeAffineOpenToroidalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfLeAffineOpenToroidalModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelQC

theorem isCompact_of_le_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (W : Y.X.Opens), W ≤ U.1 → IsCompact (W : Set Y.X) := by
  intro E _ _ _ H Dw l Xo c Y U W hW
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  have := isProper_str c.F N
  have : IsProper Y.s := hs ▸ inferInstance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.isCompact _

end GlobalTheory.ModelQC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfLeAffineOpenToroidalModelStatement
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
theorem _root_.GlobalTheory.T.isCompact_of_le_affineOpen_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (W : Y.X.Opens), W ≤ U.1 → IsCompact (W : Set Y.X) := by
  first | exact @GlobalTheory.ModelQC.isCompact_of_le_affineOpen | exact GlobalTheory.ModelQC.isCompact_of_le_affineOpen | (intros; apply GlobalTheory.ModelQC.isCompact_of_le_affineOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem isClosed_singleton_of_maximal {X : Scheme.{0}} [JacobsonSpace X] (U : X.affineOpens)
    (mm : Ideal Γ(X, U.1)) (hm : mm.IsMaximal) (y : X) (hy : y ∈ U.1)
    (h : ∀ f ∈ mm, y ∉ X.basicOpen f) : IsClosed ({y} : Set X) := by
  have hU : IsAffineOpen U.1 := U.2
  set p := hU.primeIdealOf ⟨y, hy⟩ with hp
  have hpy : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  have hle : mm ≤ p.asIdeal := by
    intro f hf
    by_contra hfp
    apply h f hf
    have h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hfp
    rw [← hpy]; exact h1
  have heq : mm = p.asIdeal := hm.eq_of_le p.isPrime.ne_top hle
  have hcl : IsClosed ({p} : Set (PrimeSpectrum Γ(X, U.1))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 (heq ▸ hm)
  have he := hU.fromSpec.isOpenEmbedding
  have hlc := IsLocallyClosed.image (f := hU.fromSpec) (s := {p}) hcl.isLocallyClosed he.isInducing
    he.isOpen_range.isLocallyClosed
  have e : hU.fromSpec '' {p} = {y} := Set.image_singleton.trans (congrArg _ hpy)
  exact isClosed_singleton_of_isLocallyClosed_singleton (e ▸ hlc)

theorem isClosed_singleton_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (mm : Ideal Γ(Y.X, U.1)), mm.IsMaximal → ∀ x : gen Y, genι Y x ∈ U.1 → (∀ f ∈ mm, genι Y x ∉ Y.X.basicOpen f) → IsClosed ({x} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y U mm hm x hx h
  have : LocallyOfFiniteType Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have := isProper_str c.F N
    rw [← hs]; infer_instance
  have : JacobsonSpace (Sp c.F) := inferInstanceAs (JacobsonSpace (PrimeSpectrum c.F))
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace Y.s
  have hc := isClosed_singleton_of_maximal U mm hm _ hx h
  have hiso : IsIso (genι Y) := isIso_fst Y
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  have := hc.preimage (genι Y).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _ hinj] at this

end GlobalTheory.LocReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpenStatement
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
theorem _root_.GlobalTheory.T.isClosed_singleton_genericFibre_of_maximal_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (mm : Ideal Γ(Y.X, U.1)), mm.IsMaximal → ∀ x : gen Y, genι Y x ∈ U.1 → (∀ f ∈ mm, genι Y x ∉ Y.X.basicOpen f) → IsClosed ({x} : Set (gen Y)) := by
  first | exact @GlobalTheory.LocReg.isClosed_singleton_gen | exact GlobalTheory.LocReg.isClosed_singleton_gen | (intros; apply GlobalTheory.LocReg.isClosed_singleton_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LocRegRig

theorem isKS_regular_at_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ Y.X.basicOpen f) ∧ x ∉ interior Y) → ∃ g ∉ m, ∀ a b, ∃ s : Γ(Y.X, U.1), (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * Θ a b := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hchart U W hW n v hv hbasis D DW Θ hDW hKS m hm hx0
  obtain ⟨x, hxU, hxm, hxint⟩ := hx0
  haveI := isIso_fst Y
  obtain ⟨x', rfl⟩ := (genι Y).surjective x
  have hbd : x' ∈ genBd Y := mem_genBd_iff.2 fun h => hxint (by
    rw [← SetLike.mem_coe, coe_interior]; exact h)
  have hcl : IsClosed ({x'} : Set (gen Y)) := GlobalTheory.T.isClosed_singleton_genericFibre_of_maximal_affineOpen E H Dw l Xo c Y U m hm x' hxU hxm
  obtain ⟨k, _, m', d, ξ, t, P, gam, h₀, h₁, h₂, h₃, ⟨φ⟩, h₅, h₆, -⟩ := hchart x' hbd hcl
  subst h₀
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  haveI : CharZero k := GlobalTheory.T.charZero_of_toricChart_to_genericFibre E H Dw l Xo c Y k m' d ξ
  obtain ⟨D', hD', hDlog⟩ := GlobalTheory.T.logDerivation_extends_completed_toricChart_ring E H Dw l Xo c Y U D k m' d ξ hx h₁ h₂
  have hfac := GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := GlobalTheory.T.exists_tangentBasis_pullback_to_spec_of_affineOpen E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hbasis
  have hab := GlobalTheory.T.mem_abelianLocus_toricChart_iff_not_mem_boundary E H Dw l Xo c Y k m' d ξ t φ h₃
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    h₆.linearIndependent.map' (Submodule.subtype _) (by simp)
  obtain ⟨ΘR, hΘR⟩ := GlobalTheory.T.exists_kodairaSpencer_of_logDerivation_chart E H k m' d t P (fun i => gam i) h₅ hlin hab n vR hvR hbR D' hDlog
  obtain ⟨h, hhW, hh0⟩ := GlobalTheory.T.exists_basicOpen_interior_containing_toricChart_generic E H Dw l Xo c Y U W hW k m' d ξ hx h₃
  obtain ⟨hflat, hcomap⟩ := GlobalTheory.T.toricChart_ringMap_flat_and_comap_maximalIdeal E H Dw l Xo c Y U k m' d ξ hx h₁ m hm hxm
  have hWc := GlobalTheory.T.isCompact_of_le_affineOpen_toroidalModel E H Dw l Xo c Y U W.1 (hW.le.trans inf_le_left)
  obtain ⟨g, hg, hs⟩ := GlobalTheory.T.sections_descend_along_flat_map_to_localDomain Y.X U W.1 (hW.le.trans inf_le_left) hWc _ (GlobalTheory.LocReg.chartHom Y U ξ hx) hflat m hcomap
    h hhW hh0 (Fin n × Fin n) (fun p => Θ p.1 p.2) (fun p s N e => Dvd.intro _
      (GlobalTheory.T.kodairaSpencer_chart_eq_at_generic_point E H Dw l Xo c Y hpq hsm U W hW n v hv hbasis D DW Θ hDW hKS k m' d ξ hx t φ h₁ h₃ vR hvR hcomp D' hD' ΘR hΘR
        h hhW hh0 p.1 p.2 s N e).symm)
  exact ⟨g, hg, fun a b => hs (a, b)⟩

end GlobalTheory.LocRegRig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPointStatement
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
theorem _root_.GlobalTheory.T.kodairaSpencer_regular_near_rigid_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ Y.X.basicOpen f) ∧ x ∉ interior Y) → ∃ g ∉ m, ∀ a b, ∃ s : Γ(Y.X, U.1), (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * Θ a b := by
  first | exact @GlobalTheory.LocRegRig.isKS_regular_at_boundary | exact GlobalTheory.LocRegRig.isKS_regular_at_boundary | (intros; apply GlobalTheory.LocRegRig.isKS_regular_at_boundary <;> assumption)
end

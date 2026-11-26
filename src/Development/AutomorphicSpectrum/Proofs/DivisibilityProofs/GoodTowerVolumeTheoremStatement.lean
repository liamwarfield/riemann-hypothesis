module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGoodRootTower
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumHeightChangeModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Coefficients
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeight
public import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFifthCondition
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalConditions
public import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelRealTowerSmooth
public import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFinalCondition
public import Development.WeilBound.CoreStatements.VolumeEquality.VolEqOfIsFullIntersectionSystem
public import Development.WeilBound.CoreStatements.FlagImmersions.RealTowerMeanSlopeCondition
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetry
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerNefGeneral
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilInputsCombined
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstants
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagOnHodgeOfFargues
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidance
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AntisymmetryStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoefficientsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RootModelNefFibresBase
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem geoNum_zero_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W a := by
  rw [geoNum]
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 W (fun _ => a) := by
  rw [geoNum]
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun V => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg' _ _)
  · exact le_rfl

end RootFieldNumerics

theorem RootFieldNumerics.root_model_nef_fibres_base : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  intro Ψ _ N M hA p _ W _
  unfold GlobalTheory.CompanionTheory.Ar.Top.RootModel.curveDeg
  refine Finset.sum_nonneg fun j _ => ?_
  rcases j with _ | r
  · have hk : (0:ℝ) < M.kA := by exact_mod_cast M.kA_pos
    have hg := RootFieldNumerics.geoNum_one_nonneg' W M.A.a hA
    simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef, GlobalTheory.CompanionTheory.Ar.Top.RootModel.line]
    exact mul_nonneg (by positivity) (by exact_mod_cast hg)
  · simp [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VolumeTheoremOfInputs
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerI5Statement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_I5 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II := by
  exact RootFieldNumerics.global_model_tower_fifth_condition
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealI6
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealI6
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_real_I6 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).RefLinked II := by
  first | exact @RootFieldNumerics.global_model_real_tower_smooth | exact RootFieldNumerics.global_model_real_tower_smooth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealI6Statement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_I6 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).RefLinked II := by
  first | exact @GlobalTheory.CompanionTheory.Relay.good_tower_real_I6 | exact GlobalTheory.CompanionTheory.Relay.good_tower_real_I6 | (intros; apply GlobalTheory.CompanionTheory.Relay.good_tower_real_I6 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealExtra
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealExtra
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_real_extra : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  first | exact @RootFieldNumerics.global_model_tower_final_condition | exact RootFieldNumerics.global_model_tower_final_condition
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealExtraStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_extra : Fl.FlatDegree → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht :=
  @GlobalTheory.CompanionTheory.Relay.good_tower_real_extra
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FullIntersectionTowerI8Identity
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FullIntersectionTowerI8Identity
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem full_intersection_tower_I8_relation : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  @SquareStatements.good_tower_antisymmetry

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FullIntersectionTowerI8IdentityStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem _root_.GlobalTheory.T.full_intersection_tower_I8_identity :
    Cmp.CmpSt → Top.Given → Out.WeilSt →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l)
      (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)]
      (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem),
      o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q →
        T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  @Top.full_intersection_tower_I8_relation
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerIntersectionExtra
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerIntersectionExtra
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_intersection_extra : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  first | exact @SheetDecomposition.volEq_of_isFullIntersectionSystem | exact SheetDecomposition.volEq_of_isFullIntersectionSystem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerIntersectionExtraStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_intersection_extra : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  exact @GlobalTheory.CompanionTheory.Relay.good_tower_intersection_extra
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalExtra
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalExtra
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem propA_of_goodOrigin : PB.AgreementPos → TwistAut → Cmp.CmpPair → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.PropA II := by
  intro hAg hTw hCmp hG E _ _ _ _ H D Xo l c Y _ T o II _ hX hII _ _
  obtain ⟨_, _, _, _, _, _, _, _, _, hIn, _⟩ := hG
  have hConv : T.Conv II := (GlobalTheory.T.real_tower_conv_I2 hAg hIn II hII (CMType H) (D.p + D.q) T (realOf o.toTowerOrigin)).1
  refine GlobalTheory.T.tower_origin_vector_bundle hCmp hTw II hII E H D l (Xo l) c Y T o.toTowerOrigin inferInstance o.omVB hX.1 ?_ hConv
  intro B a a' p hp
  rw [hX.2 B a p hp, hX.2 B a' p hp]

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalExtraStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_propA_of_global_extra : PB.AgreementPos → TwistAut → Cmp.CmpPair → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.PropA II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.propA_of_goodOrigin | exact GlobalTheory.CompanionTheory.Ar.Top.propA_of_goodOrigin | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.propA_of_goodOrigin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM2
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM2
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem m2_of_good_tower : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.M2 := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o II hglob _ hp hq
  obtain ⟨Yl, hg, hloc, -, -, hdom⟩ := hglob
  intro B a p hpr hnS mu hmu hnef
  have hpbad : p ∉ T.bad := fun hb =>
    hnS (show Nat.Prime p ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hpr, Or.inr hb⟩)
  have h2 : 2 < p := lt_of_le_of_ne hpr.two_le (fun h => hpbad (by rw [← h]; exact T.two_mem))
  have hdisc : ¬ ((p : ℤ) ∣ NumberField.discr E) := fun hd =>
    hpbad ((o.toTowerOrigin.bad_iff p).2 ⟨hpr, dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _⟩)
  have hpS : p ∉ o.toTowerOrigin.S B := fun h => hnS ((o.toTowerOrigin.S_iff B p).1 h)
  rw [o.toTowerOrigin.j_eq] at hnef
  exact GlobalTheory.T.hodge_cpt_global_nef_bound E H D Xo Yl
    (fun p W hp hW i => ⟨((hloc p W hp hW).2 i).1, ((hloc p W hp hW).2 i).2.1⟩)
    l c hg Y hdom hp hq (o.toTowerOrigin.S B) (T.M B a) (o.toTowerOrigin.Or B a).𝔐
    (o.toTowerOrigin.Or B a).Fl (o.toTowerOrigin.Or B a).e (o.toTowerOrigin.Or B a).lines
    p hpr h2 hpS hdisc mu hmu hnef

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM2Statement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_M2 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.M2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower | exact GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelNefFibres
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelNefFibres
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rootModel_nefFib_zero_one_of_nonneg :
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 :=
  @RootFieldNumerics.root_model_nef_fibres_base

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelNefFibresStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_nef_fibres : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg | exact GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealConditionsStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_conditions : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ B a, (T.M B a).EffDiff T.nu := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o _ _ _ _ _ _ B a
  obtain ⟨n₀, N₀, hn, _, hne, hmem⟩ := GlobalTheory.T.root_origin_weight_identity
    E H D l (Xo l) c _ _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) T.nu (o.nu_eq a)
  let s : (T.M B a).Ω := (N₀ : (T.M B a).Ω) * (o.Or B a).g (o.Fx a).sE *
    ∏ r, (o.Or B a).e r ^ (o.Fx a).n r
  refine ⟨(o.Fx a).kA * (o.Fx a).q', n₀, Nat.mul_pos ?_ (o.Fx a).q'_pos, hn, s, hne, hmem⟩
  rw [← (o.Or B a).kA_eq]
  exact (T.M B a).kA_pos
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SlopeLowerBaseSettings
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SlopeLowerBaseSettings
set_option maxSynthPendingDepth 1

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem slX_lower_of_stokesAt (hZ : ZhangLowerX.Statement) {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
    [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E}
    {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (Ch Cu : ℝ)
    (hII : IsIntersectionSystem II) (hpos : CuspBundlePos X) (hconj : MUConjInvariant X)
    (hint : HtInterior Ch X) (hbd : HtBoundary Ch X) (hmean : CuspMean Cu X) (hdeg : 0 < degMu X.H)
    (hN : 3 * D.j' + 1 ≤ D.N) (B : ℕ) (hB1 : 4 * D.f + 2 ≤ B) (hB2 : 4 * D.f * D.N ^ 2 ≤ B)
    (hS : StokesAt X B) :
    -((Ch + Cu / 2) * D.f * D.j' * X.La B) ≤ slX X B := by
  set a : ℝ := -(Ch * D.f * D.j' * X.La B) with ha
  have hyp : StokesLimit.Hyp X B a := by
    intro p q hp hpq
    have hq0 : 0 < q := by omega
    have hq : (0 : ℝ) < q := Nat.cast_pos.2 hq0
    obtain ⟨t₁, ht₁, hpos'⟩ := hpos B p q hB1 hp hpq
    obtain ⟨t₂, ht₂, hconj'⟩ := hconj B p q hB1 hp hpq
    obtain ⟨t₃, ht₃, hint'⟩ := hint B p q hB2 hp hpq
    obtain ⟨t₄, ht₄, hbd'⟩ := hbd B p q hB2 hp hpq
    refine ⟨min (min t₁ t₂) (min t₃ t₄), lt_min (lt_min ht₁ ht₂) (lt_min ht₃ ht₄), fun t' ht0 ht1 => ?_⟩
    have h1 : t' ≤ t₁ := ht1.trans ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : t' ≤ t₂ := ht1.trans ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : t' ≤ t₃ := ht1.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h4 : t' ≤ t₄ := ht1.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hsemi, hnef, -⟩ := hpos' t' ht0 h1
    have hz := hZ K ι (mCoordIdeal D.y) (mCoordIdeal D.y) D.n (X.MUq B p q t')
      ((q : ℝ) * (a - (p : ℝ) / q * D.KA)) II hII D.arith le_rfl hsemi hnef
      (hconj' t' ht0 h2) (fun W hW hXW => by
        have hh : a - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W := by
          by_cases hoff : OffBoundary D.Bd W
          · exact hint' t' ht0 h3 W hW hXW hoff
          · exact hbd' t' ht0 h4 W hW hXW hoff
        have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
        have e : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height (II K ι) (X.MUq B p q t') W =
            (q : ℝ) * htMUc X.H X.S' B p q t' W := by
          simp only [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height, htMUc, ComponentSetting.MUq]
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left hh hq.le)
    simp only [topMUc, geomDegMUc]
    rw [le_div_iff₀ (pow_pos hq _)]
    have e : ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) *
        (geomDeg (mCoordIdeal D.y) (MUc X.H X.S' B p q t') D.n / (q : ℝ) ^ D.n) * (q : ℝ) ^ (D.n + 1) =
        ((D.n + 1 : ℕ) : ℝ) * ((q : ℝ) * (a - (p : ℝ) / q * D.KA)) *
          geomDeg (mCoordIdeal D.y) (MUc X.H X.S' B p q t') D.n := by
      rw [pow_succ]
      field_simp
    rw [e]
    exact hz
  have h6 := hS a hyp
  have hj' : 1 ≤ D.j' := by
    have := D.j_le
    have := D.two_le_N
    simp only [ComponentData.j']
    omega
  have hm := hmean hj' hN B hB2
  have hn : (0 : ℝ) < ((D.n + 1 : ℕ) : ℝ) * degMu X.H := mul_pos (by positivity) hdeg
  rw [slX, le_div_iff₀ hn]
  have hm' := mul_le_mul_of_nonneg_left hm hn.le
  nlinarith

theorem ppc_lower_of_setting (hZ : ZhangLowerX.Statement) {II : IntersectionSystem} (hII : IsIntersectionSystem II)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} [Nonempty Ψ] (T : RootTower Ψ N) {Ch Cu rd Lval : ℝ}
    (hvol : ∀ c, 0 < T.vol c) (hN : 3 * (N - T.j) + 1 ≤ N) {B : ℕ} (hB : 4 * Fintype.card Ψ * N ^ 2 ≤ B)
    {c : T.Comp} (h : T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) :
    -((Ch + Cu / 2) * Fintype.card Ψ * (min T.j (N - T.j) : ℕ) * bigLam B rd Lval) *
        (((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j)) ≤ T.PPc II B c (testPoly T.j) := by
  obtain ⟨K, _, ι, _, Ω, _, _, E, _, _, D, O, Lt, _, _, _, X, hDN, hDj, hrd, hL, h1, h2, h3, h4, h5, h6, -, h7, h8⟩ := h
  have hJ : 0 < testDeg Ψ N T.j := (GlobalTheory.T.test_polynomial_shift_total Ψ N T.j T.j_pos T.j_lt).2.1
  have hf : D.f = Fintype.card Ψ := rfl
  have hj' : D.j' = N - T.j := by simp only [ComponentData.j', hDN, hDj]
  have hmin : min T.j (N - T.j) = N - T.j := by
    have := T.j_lt
    omega
  have hcard : 1 ≤ Fintype.card Ψ := Fintype.card_pos
  have hN2 : 2 ≤ N := by
    have := T.j_pos
    have := T.j_lt
    omega
  have hsq : 4 * Fintype.card Ψ * 4 ≤ 4 * Fintype.card Ψ * N ^ 2 :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have hB1 : 4 * D.f + 2 ≤ B := by
    rw [hf]
    omega
  have hB2 : 4 * D.f * D.N ^ 2 ≤ B := by rwa [hf, hDN]
  have hN' : 3 * D.j' + 1 ≤ D.N := by rwa [hj', hDN]
  have hl := slX_lower_of_stokesAt hZ X Ch Cu hII h1 h2 h3 h4 h5 h6 hN' B hB1 hB2 h7
  have hLa : X.La B = bigLam B rd Lval := by
    simp only [ComponentSetting.La, abelian₂, bigLam, hrd, hL]
  rw [hLa, hf, hj'] at hl
  rw [h8, hmin]
  have hw : (0 : ℝ) < ((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j) :=
    mul_pos (by positivity) (mul_pos (hvol c) hJ)
  exact mul_le_mul_of_nonneg_right hl hw.le

theorem slope_lower_of_base_settings : ZhangLowerX.Statement → ∀ II : IntersectionSystem, IsIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ),
    T.Proportional → 3 * (N - T.j) + 1 ≤ N →
    (∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B → ∀ c,
      T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) →
    T.SlopeLower II (Ch + Cu / 2) rd Lval := by
  intro hZ II hII Ψ _ _ N _ T Ch Cu rd Lval hP hN hset B hB1 hB2 hB3
  rw [RootTower.PPt, RootTower.volT, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => ppc_lower_of_setting hZ hII T hP.1 hN hB2 (hset B hB1 hB2 hB3 c)

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SlopeLowerBaseSettingsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_lower_base_settings : GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement → ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ), T.Proportional → 3 * (N - T.j) + 1 ≤ N → (∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B → ∀ c, T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) → T.SlopeLower II (Ch + Cu / 2) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings | exact GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem linA_eq (c : Option (Ψ × Fin N) → ℝ) :
    linA (fun τ i => c (some (τ, i))) (-c none) = -∑ x, C (c x) * X x := by
  rw [Fintype.sum_option]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linA, toA, linRoot, map_neg, map_sum, map_mul, rename_C, rename_X, neg_add_rev, C_neg]
  simp only [Prod.mk.eta]
  ring

def scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) : MvPolynomial (Option (Ψ × Fin N)) ℝ :=
  ∑ m ∈ Q.support, monomial m (u ^ m none * Q.coeff m)

theorem coeff_scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    (scaleNone u Q).coeff m = u ^ m none * Q.coeff m := by
  classical
  rw [scaleNone, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' Q.support m]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, mul_zero]

theorem eval_scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (c : Option (Ψ × Fin N) → ℝ) :
    eval c (scaleNone u Q) = eval (fun o : Option (Ψ × Fin N) => o.elim (u * c none) fun p => c (some p)) Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [scaleNone, map_sum, eval_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [Fintype.prod_option, Option.elim, mul_pow]
  ring

theorem abs_le_coeff (d : ℕ) (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ)
    (h : ∀ (lam : Wt Ψ N) (s : ℝ), (n : ℝ) * Φ (linA lam s ^ d) = eval (PB.gapS (fun x => lam x.1 x.2) (s / k)) Q)
    (m : Option (Ψ × Fin N) →₀ ℕ) (hm : m.degree = d) :
    |Φ (monomial m 1)| ≤ |(PB.toWtS Q).coeff m| := by
  obtain ⟨Pl, -, hev, -, hle⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Option (Ψ × Fin N)) d Φ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set u : ℝ := -(k : ℝ)⁻¹ with hu
  have heq : C (n : ℝ) * Pl = scaleNone u (PB.toWtS Q) := by
    refine MvPolynomial.funext fun c => ?_
    have hs : -c none / (k : ℝ) = u * c none := by rw [hu]; ring
    rw [eval_scaleNone, map_mul, eval_C, hev, ← linA_eq, h, PB.eval_toWtS_gapS, hs]
  have hco := congrArg (fun p : MvPolynomial (Option (Ψ × Fin N)) ℝ => p.coeff m) heq
  rw [coeff_C_mul, coeff_scaleNone] at hco
  have hu1 : |u| ≤ 1 := by
    rw [hu, abs_neg, abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_le_one_of_one_le₀ hkR
  calc |Φ (monomial m 1)| ≤ |Pl.coeff m| := hle m hm
    _ ≤ (n : ℝ) * |Pl.coeff m| := le_mul_of_one_le_left (abs_nonneg _) hnR
    _ = |(n : ℝ) * Pl.coeff m| := by rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)]
    _ = |u| ^ m none * |(PB.toWtS Q).coeff m| := by rw [hco, abs_mul, abs_pow]
    _ ≤ |(PB.toWtS Q).coeff m| := mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hu1)

theorem PP_monomial_of_ne (II : IntersectionSystem) (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ)
    (hm : m.degree ≠ dimFl Ψ N + 1) : M.PP II (monomial m 1) = 0 := by
  have h1 : (monomial m 1 : RPA Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ m := by simp
  rw [h1, RootModel.PP, Module.Basis.constr_basis]
  have h2 : (fun t => M.arMono II t m) = fun _ => 0 := by
    funext t
    simp [RootModel.arMono, hm]
  rw [h2]
  exact tendsto_const_nhds.limUnder_eq

theorem tower_I1_of_reference_linked : PB.Coefficients → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N)
    (R : RealTower T), R.RefLinked II → T.I1 II := by
  intro hCo hAg hI II hII Ψ _ _ N T R hL
  obtain ⟨Cl, thH, Pfix, hth, hlink⟩ := hL
  have hpos : ∀ c, 0 < (R.Sys c).t₀ := fun c => ((R.Sys c).reg none).1
  choose C₂ hC₂ using fun c => hCo hI (dimFl Ψ N) N Ψ (R.Sys c) (thH c) (hth c)
  set A : ℝ := ∑ c, ∑ m ∈ (Pfix c).support, |(Pfix c).coeff m| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hAle : ∀ c m, |(Pfix c).coeff m| ≤ A := by
    intro c m
    by_cases hm : m ∈ (Pfix c).support
    · calc |(Pfix c).coeff m| ≤ ∑ m ∈ (Pfix c).support, |(Pfix c).coeff m| :=
            Finset.single_le_sum (f := fun m => |(Pfix c).coeff m|) (fun _ _ => abs_nonneg _) hm
        _ ≤ A := Finset.single_le_sum (f := fun c => ∑ m ∈ (Pfix c).support, |(Pfix c).coeff m|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ c)
    · rw [notMem_support_iff.1 hm, abs_zero]
      exact hA0
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hS0 : 0 ≤ ∑ c, |C₂ c| * |Cl| := Finset.sum_nonneg fun _ _ => by positivity
  unfold RootTower.I1
  refine ⟨A / Real.log 2 + ∑ c, |C₂ c| * |Cl|, fun B hB c m => ?_⟩
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log two_pos (by exact_mod_cast hB)
  have hlog0 : 0 ≤ Real.log B := hl2.le.trans hlogB
  by_cases hm : m.degree = dimFl Ψ N + 1
  · obtain ⟨C₃, s₀, -, hag⟩ := hAg hI _ _ (R.Sys c) 0 (hpos c)
    have htend := (hag II hII _ _ _ (R.tie B c).Re).1
    have hnum := GlobalTheory.T.real_tower_arith_agreement hI II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c)
    have hle := abs_le_coeff (dimFl Ψ N + 1) ((T.M B c).PP II) (R.n c) (T.M B c).kA (hnum 0 0).1
      (T.M B c).kA_pos ((R.tie B c).Re.PB II) (fun lam s => ((hnum lam s).2.2 htend (hpos c)).2) m hm
    obtain ⟨K, iK, ι, iι, P, Re, Re', Sf, α, H, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlink B hB c
    have hd := ((hC₂ c II hII K ι P Re).2 Re' Sf α H h3 h4 h5 h6 h7 h8).1 m
    rw [h1, h2] at hd
    have hsum0 : 0 ≤ ∑ p ∈ Sf, α p * Real.log p :=
      Finset.sum_nonneg fun p hp => mul_nonneg (h4 p hp).2 (Real.log_natCast_nonneg p)
    have hd2 : |((R.tie B c).Re.PBs II).coeff m - (Pfix c).coeff m| ≤ |C₂ c| * |Cl| * Real.log B := by
      calc _ ≤ C₂ c * ∑ p ∈ Sf, α p * Real.log p := hd
        _ ≤ |C₂ c| * ∑ p ∈ Sf, α p * Real.log p := mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
        _ ≤ |C₂ c| * (|Cl| * Real.log B) := mul_le_mul_of_nonneg_left
            (h9.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0)) (abs_nonneg _)
        _ = _ := by ring
    have hc1 : |((R.tie B c).Re.PBs II).coeff m| ≤ A + |C₂ c| * |Cl| * Real.log B := by
      have := abs_sub_abs_le_abs_sub (((R.tie B c).Re.PBs II).coeff m) ((Pfix c).coeff m)
      linarith [hAle c m]
    have hA2 : A ≤ A / Real.log 2 * Real.log B := by
      calc A = A / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogB (by positivity)
    have hS : |C₂ c| * |Cl| ≤ ∑ c, |C₂ c| * |Cl| :=
      Finset.single_le_sum (f := fun c => |C₂ c| * |Cl|) (fun _ _ => by positivity) (Finset.mem_univ c)
    have hS2 := mul_le_mul_of_nonneg_right hS hlog0
    calc _ ≤ |((R.tie B c).Re.PBs II).coeff m| := hle
      _ ≤ A + |C₂ c| * |Cl| * Real.log B := hc1
      _ ≤ _ := by rw [add_mul]; linarith
  · rw [PP_monomial_of_ne II _ m hm, abs_zero]
    exact mul_nonneg (add_nonneg (by positivity) hS0) hlog0

end GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1Statement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_I1 : PB.Coefficients → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.RefLinked II → T.I1 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked | exact GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerA1
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerA1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem tower_A1_of_real_tower : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T),
      R.Smooth → R.Flat → R.Pos → T.A1 :=
  @RootFieldNumerics.real_tower_mean_slope_condition

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerA1Statement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_A1 : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → R.Pos → T.A1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower | exact GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinkedTowerPowerSum
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogMulDegFlBracketMul
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

namespace DeltaTermLin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_add (F G : RP Ψ N) : degFl (F + G) = degFl F + degFl G := by
  simp only [degFl, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

theorem degFl_zero : degFl (0 : RP Ψ N) = 0 := by
  simp [degFl]

theorem degFl_C_mul (a : ℝ) (F : RP Ψ N) : degFl (C a * F) = a * degFl F := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem degFl_sum {ι : Type} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degFl_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, degFl_add, ih]

end DeltaTermLin

theorem log_mul_degFl_bracket_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ (φ : Equiv.Perm (Ψ ⊕ Ψ)) (τ : Ψ) (Q : RP Ψ N), Real.log p * degFl (bracket j φ p k τ * Q) = deltaTerm j p τ (fun n => (φ ^ (n + 1)) (Sum.inl τ)) k Q := by
  intro Ψ _ _ N j p k hp hk φ τ Q
  have hlie : ∀ σ : Ψ ⊕ Ψ, liePs (N := N) j (k - 1) σ = pLie j (k - 1) σ := by
    rintro (s | s) <;> rfl
  have hco := co_series_three_step.1 (Ψ ⊕ Ψ) φ p k hp hk
    (fun σ => degFl (pLie (N := N) j (k - 1) σ * Q)) (Sum.inl τ)
  have hb : degFl (bracket j φ p k τ * Q) =
      (k : ℝ) * ∑ σ, co φ p k (Sum.inl τ) σ * degFl (pLie (N := N) j (k - 1) σ * Q) := by
    unfold bracket
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, Finset.sum_mul, DeltaTermLin.degFl_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, hlie]
  rw [hb, hco]
  simp only [deltaTerm, pLie]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LimitHeightConstantShift
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LimitHeightConstantShift
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

open Filter Topology

theorem arFun_tendsto_PP {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (h : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  classical
  simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.arFun, GlobalTheory.CompanionTheory.Ar.Top.RootModel.PP, Module.Basis.constr_apply, Finsupp.sum]
  refine tendsto_finsetSum _ (fun m _ => ?_)
  obtain ⟨L, hL⟩ := h m
  exact (tendsto_nhds_limUnder ⟨L, hL⟩).const_smul _

theorem PP_eq_add_of_arFun_eq_add :
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II →
      M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) →
      M.PP II F = M'.PP II F + c := by
  intro Ψ _ N M M' II hM hM' F c hF
  have h1 := arFun_tendsto_PP M II hM F
  have h2 := (arFun_tendsto_PP M' II hM' F).add_const c
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hF t ht).symm

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LimitHeightConstantShiftStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_height_constant_shift : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II → M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) → M.PP II F = M'.PP II F + c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add | exact GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinkedTowerPowerSum
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem power_sum_term_linked_tower : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → T.Proportional → ∀ φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ), LinkedTower T II φ → T.Prop6 II fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  intro Ψ _ _ N T II hII hprop φ hL
  intro B₀ B hB₀ hB c τ k hk1 hkN Q hQ
  obtain ⟨M, R, S, hS, hMc, hRc, hMPP, hRPP, hgeo, hch, hloc⟩ := hL B₀ B hB₀ hB c
  have hstep := GlobalTheory.T.limit_height_constant_shift Ψ N M R.model II hMc hRc (toA (pk τ k * Q))
    (∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket T.j (φ p) p k τ * Q)))
    (fun t ht => GlobalTheory.T.power_sum_height_change_model Ψ N M R II hII S T.j φ hch hloc t ht τ k hk1 hkN Q hQ)
  rw [hMPP, hRPP] at hstep
  rw [hstep]
  congr 1
  have hSeq : S.map ⟨(fun p : Nat.Primes => (p : ℕ)), Nat.Primes.coe_nat_injective⟩ =
      (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_Ioc, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h := (hS p).1 hp
      exact ⟨⟨h.1, h.2.1⟩, p.2, h.2.2⟩
    · rintro ⟨⟨h1, h2⟩, hpr, hbad⟩
      exact ⟨⟨n, hpr⟩, (hS _).2 ⟨h1, h2, hbad⟩, rfl⟩
  rw [← hSeq, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  change _ = T.vol c * deltaTerm T.j (p : ℕ) τ (fun n => (φ (p : ℕ) ^ (n + 1)) (Sum.inl τ)) k Q
  rw [hgeo, hprop.2.1, ← log_mul_degFl_bracket_mul Ψ N T.j p k p.2.two_le hk1 (φ p) τ Q]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinkedTowerPowerSumStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_tower_power_sum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → T.Proportional → ∀ φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ), LinkedTower T II φ → T.Prop6 II fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower | exact GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem slopeLower_mono_top {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : Top.RootTower Ψ N)
    (II : IntersectionSystem) {C C' rd Lval : ℝ} (hCC : C ≤ C') (hrd : 1 ≤ rd) (hP : T.Proportional)
    (h : T.SlopeLower II C rd Lval) : T.SlopeLower II C' rd Lval := by
  intro B hB hB' hbad
  have h1 := h B hB hB' hbad
  have hJ : 0 < Top.testDeg Ψ N T.j := (GlobalTheory.T.test_polynomial_shift_total Ψ N T.j T.j_pos T.j_lt).2.1
  have hvol : 0 ≤ T.volT := Finset.sum_nonneg fun c _ => (hP.1 c).le
  have hB1 : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hL : 0 ≤ Top.bigLam B rd Lval := by
    unfold Top.bigLam
    have h2 : (1 : ℝ) ≤ B * rd := by nlinarith
    have := Real.log_nonneg h2
    positivity
  have hK : 0 ≤ (Fintype.card Ψ : ℝ) * ((min T.j (N - T.j) : ℕ) : ℝ) * Top.bigLam B rd Lval *
      (((Top.dimX Ψ N T.j : ℝ) + 1) * (T.volT * Top.testDeg Ψ N T.j)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hCC hK]

theorem volumeTheoremX_of_inputs : Top.Given → PtsIntegrableStatement → Out.WeilSt → (∃ Ch Cu : ℝ, NineGeoU Ch Cu) →
    HodgeLatticeFlagBound → TrivFlagOnHodge → Fl.FlatDegree → TwistAut → Cmp.CmpPair → Cmp.CmpSt → Top.VolumeTheoremX := by
  intro hG hPts hW hNineE hM3 hTF hFD hTw hCP hCS
  obtain ⟨Ch, Cu, hNine⟩ := hNineE
  obtain ⟨-, -, -, -, -, -, -, -, -, hIn, hHS, -, hNF, hAP⟩ := id hG
  obtain ⟨hZ1, hZ2, -⟩ := hHS
  obtain ⟨hZh, -, -, -, hGr⟩ := hNF
  have hAg := GlobalTheory.T.agreement_positive
  refine ⟨2 * max (Ch + Cu / 2) 0 + 3 * 4 + 5, by positivity, ?_⟩
  intro E _ _ _ _ H D Xo l c Y _ T o II hGl hX hII hq hpq hbad
  obtain ⟨hrd, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  haveI := hne
  have hp : 1 ≤ D.p := by omega
  have hqp : D.q ≤ D.p := by omega
  have hUnif := GlobalTheory.T.good_tower_real_agreement hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hProp : T.Proportional := GlobalTheory.T.real_tower_proportional GlobalTheory.T.proportional' hIn II hII _ _ T _ hUnif
  have hCI := GlobalTheory.T.real_tower_conv_I2 hAg hIn II hII _ _ T (Top.realOf o.toTowerOrigin)
  have hI1 := GlobalTheory.T.real_tower_I1 GlobalTheory.T.coefficients' hAg hIn II hII _ _ T _
    (GlobalTheory.T.good_tower_real_I6 hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hPos : (Top.realOf o.toTowerOrigin).Pos := fun a => (o.Fx a).pos
  have hA1 := GlobalTheory.T.real_tower_A1 hIn II hII _ _ T _ o.smooth o.flat hPos
  have hM1 := GlobalTheory.T.good_tower_M1_nef hG E H D Xo l c Y T o II hGl hII hp hq
  have hM2 := GlobalTheory.T.good_tower_M2 hG E H D Xo l c Y T o II hGl hII hp hq
  have hAN : T.ANef := fun B a => GlobalTheory.T.root_model_nef_fibres _ _ (T.M B a) fun k => by
    obtain ⟨h1, h0⟩ := (o.Or B a).A_deg
    by_cases hk : k = (o.Or B a).k₀
    · rw [hk, h1]; norm_num
    · rw [h0 k hk]
  have hI56 := GlobalTheory.T.good_tower_I5 hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hI7 : T.I7 := fun B a =>
    ⟨(GlobalTheory.T.real_tower_nef_general GlobalTheory.T.nef_polarization hIn II hII _ _ T _ o.smooth o.flat B a).1,
      (GlobalTheory.T.real_tower_nef_general GlobalTheory.T.nef_polarization hIn II hII _ _ T _ o.smooth o.flat B a).2,
      GlobalTheory.T.good_tower_real_conditions hG E H D Xo l c Y T o II hGl hX hII hp hq B a⟩
  have hI8 := GlobalTheory.T.full_intersection_tower_I8_identity hCS hG hW E H D Xo l c Y T o II hX hII hp hq
  obtain ⟨φ, hfs, hLk⟩ := GlobalTheory.T.good_tower_global_conditions hCS hAg hM3 hTF hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hP6 := GlobalTheory.T.linked_tower_power_sum _ _ T II hII.1 hProp φ hLk
  have hPA := GlobalTheory.T.good_tower_propA_of_global_extra hAg hTw hCP hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp' => ((o.bad_iff p).1 hp').1
  have hPF := GlobalTheory.T.PropFTop_holds hPts hIn.2.2.1.2 hIn.2.1.2.1 _ _ T II _ (hostRd E) (hostLval H) hII.1 hCI.1 hProp hP6
    (by linarith) hbadP (GlobalTheory.T.good_tower_real_extra hFD hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hVol := GlobalTheory.T.good_tower_intersection_extra hCS hG E H D Xo l c Y T o II hGl hX hII hq hpq
  have hj3 : 3 * (D.p + D.q - T.j) + 1 ≤ D.p + D.q := by rw [o.j_eq]; omega
  have hSL0 := GlobalTheory.T.slope_lower_base_settings hZh II hII.1 _ _ T Ch Cu (hostRd E) (hostLval H) hProp hj3
    fun B _ hB _ a => GlobalTheory.T.base_setting_of_good_tower Ch Cu hNine hW hAg GlobalTheory.T.proportional' hCS hG hPts E H D Xo l c Y T o II hGl hX hII
      hp hq hqp hbad B hB a
  have hSL := slopeLower_mono_top T II (le_max_left (Ch + Cu / 2) 0) (by linarith) hProp hSL0
  have hch := GlobalTheory.T.tower_weil_inputs_combined GlobalTheory.T.flag_height hIn hZ1 hZ2 hAP hGr II hII _ _ T _ (max (Ch + Cu / 2) 0) 4 (hostRd E)
    (hostLval H) (le_max_right _ _) (by norm_num) (by linarith) hfs hProp hI1 hCI.2 hA1 hM1 hM2 hAN hI56.1 hI56.2
    hI7 hI8 hP6 hPA hPF hVol hSL
  exact ⟨hProp, hVol, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_volume_theorem : Top.Given → PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → Out.WeilSt → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → Cmp.CmpPair → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hG hPts hAv hW hFam hPair
  have hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have hFHT : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hGaga : Flat.GagaSections := hG.2.2.2.2.2.2.2.1
  have hPB : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hA0 := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hGaga
  have hA1 := GlobalTheory.T.flat_first_from_resolution_and_gaga hR hGaga
  refine ⟨?_, ?_⟩
  · intro E _ _ _ H D Xo l c Y _ hgl hs hp hq
    exact GlobalTheory.CompanionTheory.Ar.TopTower.exists_good_tower hG hW hA0 hA1 E H D Xo l c Y hgl hs hp hq
  · exact GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs hG hPts hW (GlobalTheory.T.exists_geometric_height_constants hG hW GlobalTheory.T.FlatDegree_holds) (GlobalTheory.T.model_on_hodge_from_family hFam)
      (GlobalTheory.T.triv_flag_on_hodge_of_fargues hFHT) GlobalTheory.T.FlatDegree_holds GlobalTheory.T.TwistAut_holds hPair (GlobalTheory.T.comparison_of_inputs_avoidance hPB hAv hR)

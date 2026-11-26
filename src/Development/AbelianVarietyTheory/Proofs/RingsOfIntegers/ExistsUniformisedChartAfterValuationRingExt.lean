module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsExtAllModelsUniformised

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodChartExt

theorem vV_nonneg (T : CDVR) (a : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
  by_cases ha : algebraMap T.V T.Fr a = 0
  · rw [ha]; simp [vV]
  · have hv : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one a
    have := (WithZero.log_le_log (valV_ne_zero (V := T.V) ha) one_ne_zero).2 hv
    simp only [WithZero.log_one] at this
    simp only [vV]; omega

theorem exists_local_restrict (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (he : 0 < e)
    (hv : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) :
    ∃ φ : T.V →+* T'.V, (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) ∧ IsLocalHom φ := _root_.GlobalTheory.ThetaBound.Prep.exists_local_restrict T T' iT e he hv

theorem split_of_pullback {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsLocalRing V']
    (φ : V →+* V') [IsLocalHom φ] {D : DegData V (maximalIdeal V)} {A : PolAV (Sp (FractionRing V))}
    {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    {G' : Over (Sp V')} [GrpObj G'] {ψ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap φ) ψ) :
    ∃ S : SplitExt (Sp (ResidueField V')), S.IsGt ((Over.pullback (spMap (residue V'))).obj G') := by
  obtain ⟨E₀, -, -, -, -, ⟨d⟩⟩ := GlobalTheory.gtCoord_isGt V _ D.toPre 0 G ⟨U.gt 0⟩
  let g : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V' :=
    (ResidueField.map φ).comp (Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num)))
  have hr : spMap g ≫ thick V (maximalIdeal V) 0 = spMap (residue V') ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  obtain ⟨j, hj, -⟩ := grpPullback_iso (((isGrpPullback_pullback (thickObj V (maximalIdeal V) 0 G)
    (spMap g)).comp (isGrpPullback_pullback G (thick V (maximalIdeal V) 0))).congr hr rfl)
    ((isGrpPullback_pullback G' (spMap (residue V'))).comp h)
  obtain ⟨S, _, _, _, _, hS⟩ := GlobalTheory.gtBaseChange _ _ (spMap g) E₀ _ ⟨d⟩
  exact ⟨S, isGt_of_iso j hS⟩

theorem exists_good_chart_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)), IsExt y iT e y' → ∃ C' : IntegralChartA3 Xo c T' (iT.comp io) y', Good3 C' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC T' iT e y' hy
  obtain ⟨-, P, -⟩ := hC
  obtain ⟨he, hv, ψ, hψ, hx, -⟩ := hy
  have hx' : xOf y' = spMap iT ≫ xOf y := hx.trans (congrArg (fun r => spMap r ≫ xOf y) hψ)
  obtain ⟨C', hC'⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T' (iT.comp io) y'
  refine ⟨C', hC', ?_⟩
  obtain ⟨φ, hφ, hloc⟩ := exists_local_restrict T T' iT e he hv
  have hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp, hφ]
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f →
      Nonempty (SABMap s' s g) := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m⟩
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ C.I.G (spMap φ)) := by
    obtain ⟨PP, cub, sym, adj, prim, m, hm⟩ := sabPull Out.CubePf.cubePull (spMap φ) C.I.G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ C.I.t' (spMap iT)) := by
    obtain ⟨PP, cub, sym, adj, prim, m, hm⟩ := sabPull Out.CubePf.cubePull (spMap iT) C.I.t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨a₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.I.m1 p
  obtain ⟨n₁⟩ := tr hx'.symm a₁
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.I.m2 p
  obtain ⟨b₂⟩ := tr hsq a₂
  obtain ⟨n₂, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂
  obtain ⟨-, n, -⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr (xOf y') C'.I.G G₂ C'.I.t' t₂ C'.I.m1 C'.I.m2 n₁ n₂
  obtain ⟨a₃, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n
  obtain ⟨k⟩ := tr (Category.id_comp _) a₃
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap k C.I.m2 C.I.m1 Xo.univ.proper Xo.univ.ample Xo.univ.ktriv
    (jK T'.V) (spMap iT) hsq.symm
  obtain ⟨-, P', -, hP'⟩ := GlobalTheory.UnifAfterExt.isOpen_and_uniformised T'.V inferInstance C'.I.G hp
    (split_of_pullback φ P.U.toUnifPre k.cart)
  exact ⟨P', hP'⟩

end GlobalTheory.GoodChartExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_chart_after_valuation_ring_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)), IsExt y iT e y' → ∃ C' : IntegralChartA3 Xo c T' (iT.comp io) y', Good3 C' := by
  first | exact @GlobalTheory.GoodChartExt.exists_good_chart_ext | exact GlobalTheory.GoodChartExt.exists_good_chart_ext | (intros; apply GlobalTheory.GoodChartExt.exists_good_chart_ext <;> assumption)
end

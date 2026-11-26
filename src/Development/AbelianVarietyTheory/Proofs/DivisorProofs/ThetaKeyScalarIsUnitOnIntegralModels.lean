module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPoleOfBounded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalAtOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfArcsAndGoodReductionPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendOfIntegralAtDvr
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenExt
open GlobalTheory.FlagMod

theorem generic_le {X : Scheme.{0}} {G W : X.Opens} (hG : IsAffineOpen G) [IsDomain Γ(X, G)]
    (hW : W ≤ G) (hne : ∃ x, x ∈ W) :
    ⊤ ≤ (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G))) ≫ tau hG) ⁻¹ᵁ W := by
  intro y _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq⟩ := hG.range_fromSpec.ge (hW hx)
  have hq' : q ∈ (tau hG ⁻¹ᵁ W : (Sp Γ(X, G)).Opens) := by
    show hG.fromSpec q ∈ W
    rw [hq]; exact hx
  have hsp : (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes (R := Γ(X, G)) ((spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y) q).1 ?_
    show Ideal.comap _ y.asIdeal ≤ q.asIdeal
    rw [@Ideal.eq_bot_of_prime _ _ y.asIdeal y.2]
    exact Ideal.comap_bot_le_of_injective _ (IsFractionRing.injective Γ(X, G) (FractionRing Γ(X, G)))
  exact hsp.mem_open (tau hG ⁻¹ᵁ W).isOpen hq'

theorem extend_of_integral_at_dvr : ∀ (X : Scheme.{0}) (G W₀ : X.Opens) (hle : W₀ ≤ G), IsAffineOpen G → IsDomain Γ(X, G) → IsNoetherianRing Γ(X, G) → IsIntegrallyClosed Γ(X, G) → Countable Γ(X, G) → (∃ x, x ∈ W₀) → Function.Injective (resG X hle) ∧ ∀ f₀ : Γ(X, W₀), (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ X), Countable R → ⊤ ≤ z ⁻¹ᵁ G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∃ f : Γ(X, G), resG X hle f = f₀ := by
  intro X G W₀ hle hG hD hN hI hC hne
  let K := FractionRing Γ(X, G)
  let η : Sp K ⟶ X := spMap (algebraMap Γ(X, G) K) ≫ tau hG
  have hηG : ⊤ ≤ η ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
  have key : ∀ (W : X.Opens) (hW : W ≤ G) (h : ⊤ ≤ η ⁻¹ᵁ W) (a : Γ(X, G)),
      ev η W h (resG X hW a) = algebraMap Γ(X, G) K a := by
    intro W hW h a
    rw [ev_res η hW h hηG, ev_spMap_tau hG]
  have hW₀ : ⊤ ≤ η ⁻¹ᵁ W₀ := generic_le hG hle hne
  refine ⟨fun a b e => IsFractionRing.injective Γ(X, G) K (by rw [← key W₀ hle hW₀, ← key W₀ hle hW₀, e]), ?_⟩
  intro f₀ hf
  have hKc : Countable K := by
    have hs : Function.Surjective (fun p : Γ(X, G) × nonZeroDivisors Γ(X, G) => IsLocalization.mk' K p.1 p.2) :=
      fun x => by
        obtain ⟨p, e⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(X, G)) x
        exact ⟨p, e⟩
    exact hs.countable
  have hint : _root_.IsIntegral Γ(X, G) (ev η W₀ hW₀ f₀) := by
    apply GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring Γ(X, G) K
    intro V hV hBV
    let ι : Γ(X, G) →+* V := (algebraMap Γ(X, G) K).codRestrict V.toSubring hBV
    have hz : ⊤ ≤ (spMap ι ≫ tau hG) ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
    have hc : (algebraMap V K).comp ι = algebraMap Γ(X, G) K := RingHom.ext fun _ => rfl
    have he : spMap (algebraMap V K) ≫ spMap ι ≫ tau hG = η := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    have h' : ⊤ ≤ (spMap (algebraMap V K) ≫ spMap ι ≫ tau hG) ⁻¹ᵁ W₀ := by rw [he]; exact hW₀
    obtain ⟨v, hv⟩ := hf V K (spMap ι ≫ tau hG) inferInstance hz h'
    rw [ev_congr he W₀ h' hW₀] at hv
    rw [← hv]
    exact v.2
  obtain ⟨f, hf'⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).1 hint
  refine ⟨f, ext_ev_loc fun p hp => ?_⟩
  obtain ⟨s, hsle, hps⟩ := hG.exists_basicOpen_le ⟨p, hp⟩ (hle hp)
  have hN : ⊤ ≤ η ⁻¹ᵁ X.basicOpen s := generic_le hG (X.basicOpen_le s) ⟨p, hps⟩
  have inj : Function.Injective (ev η (X.basicOpen s) hN) := by
    haveI := hG.isLocalization_basicOpen s
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) x
    have h1 : algebraMap Γ(X, G) K a = 0 := by
      rw [← key _ (X.basicOpen_le s) hN a]
      change ev η _ hN (algebraMap Γ(X, G) Γ(X, X.basicOpen s) a) = 0
      rw [← e, map_mul, hx, zero_mul]
    have ha : a = 0 := IsFractionRing.injective Γ(X, G) K (by rw [h1, map_zero])
    have hu : IsUnit (algebraMap Γ(X, G) Γ(X, X.basicOpen s) m) := IsLocalization.map_units _ m
    rw [ha, map_zero] at e
    exact hu.mul_left_eq_zero.1 e
  have hres : resG X hsle (resG X hle f) = resG X hsle f₀ := by
    apply inj
    rw [ev_res η hsle hN hW₀, ev_res η hsle hN hW₀, key W₀ hle hW₀, hf']
  refine ⟨X.basicOpen s, hps, fun S _ z hz hzN => ?_⟩
  rw [← ev_res z hsle hzN hz, ← ev_res z hsle hzN hz (f₀), hres]

end GlobalTheory.GenExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChart
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpenModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem charZero_of_range [IsOpenImmersion Y.j] {R : Type} [CommRing R] [Nontrivial R] (z : Sp R ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : CharZero R :=
  charZero_of_injective_ringHom (Spec.preimage (IsOpenImmersion.lift Y.j z h ≫ pullback.snd _ _)).hom.injective

theorem exists_keyAt_of_range [IsOpenImmersion Y.j] (hpq : 1 ≤ D.p + D.q) (M : GChart Y) {R : Type} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (h : Set.range z ⊆ Set.range Y.j) :
    ∃ x : KeyIn R, KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := exists_sab z Y.t
  have e : IsOpenImmersion.lift Y.j z h ≫ Y.j = z := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t Y.j (IsOpenImmersion.lift Y.j z h) Y.m (e.symm ▸ m)
  have hp₀ := Y.oF.proper
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp₀
  have hA : Out.RelAmple t.G t.PP.L := by
    have h₁ := AmpleBaseChange.relAmple_of_isPullback Y.oF.t.PP.isLB Y.oF.ample m'.cart.1
    refine (GlobalTheory.KeyAtFam.relAmple_iff_of_cls (pull_isLB Y.oF.t.PP.isLB m'.φ) t.PP.isLB le_rfl ?_).2 h₁
    rw [one_smul]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m')
  have := charZero_of_range z h
  have : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h₂ := IsTotallyComplex.finrank E
    exact Nat.mul_pos (by omega) hpq
  obtain ⟨x₀, -, h₀⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (spMap (algebraMap R (FractionRing R)) ≫ z)
    (le_preimage_comp _ hz) (by
      rintro _ ⟨s, rfl⟩
      exact h ⟨_, rfl⟩) hpos
  obtain ⟨x, -, hx⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hz m hp hA _ h₀
  exact ⟨x, hx⟩

theorem exists_unit_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y hO hj hpq κ hκ M
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : IsReduced Y.X := by
    have (x : Y.X) : _root_.IsReduced (Y.X.presheaf.stalk x) := by
      have := GlobalTheory.IsNormalScheme.isDomain_stalk x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  let W₀ : Y.X.Opens := M.U ⊓ Y.j.opensRange
  have hW₀ : ∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j := fun x => Iff.rfl
  have hr : ∀ {R : Type} [CommRing R] (z : Sp R ⟶ Y.X), ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := by
    rintro R _ z hz _ ⟨s, rfl⟩
    exact ((hW₀ _).1 (hz (Set.mem_univ s))).2
  let P : Y.X.Opens → Prop := fun W => IsDomain Γ(Y.X, W)
  have hP : ∀ q ∈ W₀, ∃ W : Y.X.Opens, IsAffineOpen W ∧ W ≤ W₀ ∧ P W ∧ q ∈ W := fun q hq => by
    obtain ⟨D', hqD, hD⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X q
    obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hle⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show q ∈ ((W₀ ⊓ D' : Y.X.Opens) : Set Y.X) from ⟨hq, hqD⟩) (W₀ ⊓ D').isOpen
    exact ⟨W, hW, fun r hr => (hle hr).1, hD W hqW fun r hr => (hle hr).2, hqW⟩
  have loc₁ : ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (hWV : W ≤ W₀), P W →
      ∃ (y : KeyIn Γ(Y.X, W)) (u : Γ(Y.X, W)ˣ),
        KeyAt M (tau hW) (tau_le hW (hWV.trans inf_le_left)) y ∧ GlobalTheory.KeyCl.IsValue κ y (u : Γ(Y.X, W)) := by
    intro W hW hWV hdom
    have : IsDomain Γ(Y.X, W) := hdom
    have : IsNoetherianRing Γ(Y.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : IsIntegrallyClosed Γ(Y.X, W) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
    have : CharZero Γ(Y.X, W) := charZero_of_range (tau hW) (hr _ (tau_le hW hWV))
    obtain ⟨y, hy⟩ := exists_keyAt_of_range hpq M (tau hW) (tau_le hW (hWV.trans inf_le_left)) (hr _ (tau_le hW hWV))
    obtain ⟨u, hu⟩ := GlobalTheory.KeyFamUnit.famUnit κ hκ.2.1 hκ.2.2.1 Γ(Y.X, W) y
    exact ⟨y, u, hy, hu⟩
  obtain ⟨f, hf⟩ := GlobalTheory.KeyOpen.glue_units W₀ P hP
    (fun L _ z v => ∀ (hc : CharZero L) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn L), KeyAt M z hz' x → v = (κ L x : L))
    (fun L _ z hz v w hv hw => by
      have hc : CharZero L := charZero_of_range z (hr z hz)
      have hz' : ⊤ ≤ z ⁻¹ᵁ M.U := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      obtain ⟨x, hx⟩ := exists_keyAt_of_range hpq M z hz' (hr z hz)
      exact (hv hc _ x hx).trans (hw hc _ x hx).symm)
    (fun W hW hWV hPW => by
      obtain ⟨y, u, hy, hu⟩ := loc₁ W hW hWV hPW
      refine ⟨u, fun L _ z hz hc hz' x hx => ?_⟩
      have e : spMap (ev z W hz) ≫ tau hW = z := GlobalTheory.FlagMod.spMap_ev z hW hz
      generalize ev z W hz = φ at e ⊢
      subst e
      exact (hu L φ x (GlobalTheory.KeyAtBC.keyPB_of_keyAt hy hx)).symm)
  exact ⟨W₀, f, hW₀, fun K _ hK z hz hz' x hx => hf K z hz hK hz' x hx⟩

end GlobalTheory.KeyOpenModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChartStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  first | exact @GlobalTheory.KeyOpenModel.exists_unit_open | exact GlobalTheory.KeyOpenModel.exists_unit_open | (intros; apply GlobalTheory.KeyOpenModel.exists_unit_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChart
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.KeyUnitGood

theorem exists_unit_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K) (u : Aˣ)
    (hx : la x = algebraMap A B u) : ∃ v : Rˣ, x = algebraMap R K v := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h : e r = u := IsFractionRing.injective A B (by rw [← hla, hr, hx])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ u.isUnit)
    exact ⟨v, hr.symm⟩
  · have h : e r = (u⁻¹ : Aˣ) := IsFractionRing.injective A B (by rw [← hla, hr, map_inv₀, hx, map_units_inv])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ (u⁻¹).isUnit)
    exact ⟨v⁻¹, by rw [map_units_inv, hr, inv_inv]⟩

theorem isUnit_key_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y κ hκ M R K _ _ _ _ _ _ _ z hz y hy hab x hx
  have : CharZero R := (algebraMap R K).charZero
  obtain ⟨T, i, hi, hil⟩ : ∃ (T : Formalism.L2.Pj.CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i :=
    ⟨GlobalTheory.CountableCompletion.completionCDVR R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance⟩
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  let iK : K →+* T.Fr := IsFractionRing.lift hiF
  have hiK : ∀ r, iK (algebraMap R K r) = algebraMap T.V T.Fr (i r) := fun r => IsFractionRing.lift_algebraMap hiF r
  have hsq : spMap iK ≫ spMap (algebraMap R K) = spMap (algebraMap T.V T.Fr) ≫ spMap i := by
    rw [← GlobalTheory.KeyAtBC.spMap_comp₀, ← GlobalTheory.KeyAtBC.spMap_comp₀]
    exact congrArg spMap (RingHom.ext hiK)
  have hpt : spMap iK ≫ spMap (algebraMap R K) ≫ z = spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z := by
    rw [← Category.assoc, hsq, Category.assoc]
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap i ≫ z) Y.t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_sab (spMap (algebraMap T.V T.Fr)) t
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp m mK
  have hj : spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z = (spMap iK ≫ y) ≫ Y.j := by
    rw [← hpt, Category.assoc, hy]
  obtain ⟨n₁, -⟩ := ObjMaps.exists_sab_cancel (show SABMap Y.oF.t Y.t Y.j from Y.m) (hj ▸ n)
  obtain ⟨n₂, -⟩ := ObjMaps.exists_sab_comp Y.m0.toSABMap n₁
  have hp : IsProper t.G.hom := GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H D l Xo T _ t tK n₂ mK
    (Set.eq_univ_of_forall fun q => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 q).1
      (hab ⟨spMap i q, (Scheme.Hom.comp_apply _ _ _).symm⟩))
  obtain ⟨-, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv (show SABMap Y.oF.t Y.t Y.j from Y.m)
    Y.oF.proper Y.oF.ample Y.oF.ktriv n (by
      rw [hj]
      rintro _ ⟨q, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩)
  have hA' : Out.RelAmple t.G t.PP.L := GlobalTheory.GoodPol.relAmple_of_generic GlobalTheory.firstFiveLaws.1
    ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.cub mK.cart tK.PP.isLB
    (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mK) hA hK
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x iK
  have hzT : ⊤ ≤ (spMap i ≫ z) ⁻¹ᵁ M.U := le_preimage_comp _ hz
  have h₁ : KeyAt M (spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z) (le_preimage_comp _ hzT) x' := by
    have cast : ∀ (p q : Sp T.Fr ⟶ Y.X) (_ : p = q) hp hq, KeyAt M p hp x' → KeyAt M q hq x' := by
      rintro p q rfl _ _ h
      exact h
    exact cast _ _ hpt _ _ (GlobalTheory.KeyAtBC.keyAt_of_keyPB hx hx')
  obtain ⟨xT, -, hT⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hzT m hp hA' _ h₁
  obtain ⟨u, hu, -⟩ := hκ.2.2.1 T.V T.Fr xT x' (GlobalTheory.KeyAtBC.keyPB_of_keyAt hT h₁)
  exact exists_unit_of_map i iK hiK _ u ((hκ.2.1 K T.Fr iK x x' hx').symm.trans hu)

end GlobalTheory.KeyUnitGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChartStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  first | exact @GlobalTheory.KeyUnitGood.isUnit_key_of_good | exact GlobalTheory.KeyUnitGood.isUnit_key_of_good | (intros; apply GlobalTheory.KeyUnitGood.isUnit_key_of_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcPropertyLocalisationBaseChangeOfModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcPropertyLocalisationBaseChangeOfModel
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

noncomputable section

namespace GlobalTheory.LocArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

@[reducible] def arcRestrict (b : O →+* O') (hb : β'.comp b = β) {O'' : Type} [CommRing O''] [IsDomain O'']
    {b' : O' →+* O''} (a : ArcIn D l β' O'' b') : ArcIn D l β O'' (b'.comp b) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom := fun F _ _ _ r z hr hz => a.geom F (b r) (b z) (by rw [← hb] at hr; exact hr) (by rw [← hb] at hz; exact hz)

variable (Y : Model Xo c β) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)]

theorem mono_locMap : Mono (locMap Y b).φ :=
  (MorphismProperty.monomorphisms Scheme.{0}).of_isPullback (locMap Y b).cart.1.flip
    (show Mono (pullback.fst Y.s (spMap b)) from inferInstance)

theorem hasArcData_iff {O'' R : Type} [CommRing O''] [IsDomain O''] [CommRing R] [IsDomain R] {b' : O' →+* O''}
    (a : ArcIn D l β' O'' b') (I : Ideal R) (f : O'' →+* R) (u : R) (χ : Sp R ⟶ (locModel Y b hb).X) :
    (locModel Y b hb).HasArcData a I f u χ ↔
      Y.HasArcData (arcRestrict b hb a) I f u (χ ≫ pullback.fst Y.s (spMap b)) := by
  have ej := locModel_j Y b hb
  have em := locModel_m Y b hb
  constructor
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, ej, hy]
      simp only [Category.assoc]
    · have := mono_locMap Y b
      rw [← cancel_mono (locMap Y b).φ]
      rw [hn, ← em] at k₄
      simp only [Category.assoc]
      exact k₄
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_cancel (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← ej, ← Category.assoc, hy]
      simp only [Category.assoc]
    · have := congrArg (· ≫ (locMap Y b).φ) k₄
      simp only [Category.assoc] at this
      rw [hn, ← em]
      exact this

theorem mem_range_j_iff (x : (locModel Y b hb).X) :
    x ∈ Set.range (locModel Y b hb).j ↔ pullback.fst Y.s (spMap b) x ∈ Set.range Y.j := by
  rw [← locModel_j Y b hb]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, (pullback.fst Y.s (spMap b)).isEmbedding.injective ?_⟩
    rw [← hu, Scheme.Hom.comp_apply]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem locModel_arc (h : Y.N4) : (locModel Y b hb).N4 := by
  intro O'' _ _ _ b' ϖ a hO
  obtain ⟨χ₀, hu, hs⟩ := h O'' (b'.comp b) ϖ (arcRestrict b hb a) hO
  obtain ⟨c₁, c₂, c₃, c₄⟩ := (hu χ₀).1 rfl
  have hw : χ₀ ≫ Y.s = (spMap (PowerSeries.C (R := O'')) ≫ spMap b') ≫ spMap b := by
    rw [c₁, spMap_comp', Category.assoc]
  have hχ : pullback.lift χ₀ _ hw ≫ pullback.fst Y.s (spMap b) = χ₀ := pullback.lift_fst _ _ _
  refine ⟨pullback.lift χ₀ _ hw, fun χ' => ⟨?_, ?_⟩, fun hi y' ev d₁ d₂ d₃ d₄ d₅ => ?_⟩
  · rintro rfl
    refine ⟨pullback.lift_snd _ _ _, fun x => ?_, fun x hx => ?_, ?_⟩
    · rw [mem_abLocus_locModel, ← Scheme.Hom.comp_apply, hχ]
      exact c₂ x
    · rw [mem_range_j_iff, ← Scheme.Hom.comp_apply, hχ]
      exact c₃ x hx
    · rw [hasArcData_iff, hχ]
      exact c₄
  · rintro ⟨d₁, d₂, d₃, d₄⟩
    rw [← cancel_mono (pullback.fst Y.s (spMap b)), hχ]
    refine (hu _).2 ⟨?_, fun x => ?_, fun x hx => ?_, (hasArcData_iff Y b hb a _ _ _ _).1 d₄⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp', ← Category.assoc]
      exact congrArg (· ≫ spMap b) d₁
    · rw [Scheme.Hom.comp_apply, ← mem_abLocus_locModel Y b hb]
      exact d₂ x
    · rw [Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₃ x hx
  · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, hχ]
    refine hs hi _ ev ?_ ?_ ((hasArcData_iff Y b hb a _ _ _ _).1 d₃) d₄ d₅
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp']
      exact congrArg (· ≫ spMap b) d₁
    · rintro _ ⟨q, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₂ ⟨q, rfl⟩

end GlobalTheory.LocArc

theorem GlobalTheory.LocArc.arc_localise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ b hb _ _ h => GlobalTheory.LocArc.locModel_arc Y b hb h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcPropertyLocalisationBaseChangeOfModelStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcProperty_localisationBaseChange_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 := by
  first | exact @GlobalTheory.LocArc.arc_localise | exact GlobalTheory.LocArc.arc_localise | (intros; apply GlobalTheory.LocArc.arc_localise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFlatValuationSubringBaseRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFlatValuationSubringBaseRing
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ValLocal

theorem exists_dvd_away {A : Type} [CommRing A] [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (a b : A) (hb : b ≠ 0) :
    ∃ s r : A, s ∉ q ∧ (s * a = r * b ∨ s * b = r * a) := by
  by_cases hq : q = ⊥
  · exact ⟨b, a, by simpa [hq] using hb, Or.inl (mul_comm _ _)⟩
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have key : ∀ (u v : A) (z : Localization.AtPrime q), algebraMap A _ u * z = algebraMap A _ v →
      ∃ s r : A, s ∉ q ∧ s * v = r * u := by
    intro u v z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj q.primeCompl z
    refine ⟨s, r, s.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hrs]
    ring
  obtain ⟨z, hz | hz⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) a) (algebraMap A _ b)
  · obtain ⟨s, r, hs, h⟩ := key a b z hz
    exact ⟨s, r, hs, Or.inr h⟩
  · obtain ⟨s, r, hs, h⟩ := key b a z hz
    exact ⟨s, r, hs, Or.inl h⟩

theorem exists_integral_frac {F : Type} [Field F] [NumberField F] (W : ValuationSubring F) (x : W) :
    ∃ a s : W, IsIntegral ℤ (a : F) ∧ IsIntegral ℤ (s : F) ∧ IsUnit s ∧ x * s = a := by
  have hmem : ∀ y : 𝓞 F, (y : F) ∈ W := fun y => by
    have h : IsIntegral W (y : F) := y.isIntegral_coe.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
    rw [← hz]
    exact z.2
  let φ : 𝓞 F →+* W := (algebraMap (𝓞 F) F).codRestrict W.toSubring hmem
  have hφ : ∀ y : 𝓞 F, ((φ y : W) : F) = (y : F) := fun _ => rfl
  let q : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal W).comap φ
  have hunit : ∀ s : 𝓞 F, s ∉ q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb0
  have hxb : (x : F) * b = a := by
    rw [← hx]
    exact div_mul_cancel₀ _ hbF
  obtain ⟨s, r, hs, h | h⟩ := exists_dvd_away q a b hb0
  · refine ⟨φ r, φ s, r.isIntegral_coe, s.isIntegral_coe, hunit s hs, Subtype.ext ?_⟩
    have h' : (s : F) * a = r * b := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    show (x : F) * s = r
    apply mul_right_cancel₀ hbF
    rw [← h', ← hxb]
    ring
  · have h' : (s : F) * b = r * a := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    have hxr : x * φ r = φ s := by
      apply Subtype.ext
      show (x : F) * r = s
      apply mul_right_cancel₀ hbF
      rw [h', ← hxb]
      ring
    exact ⟨φ s, φ r, s.isIntegral_coe, r.isIntegral_coe,
      isUnit_of_mul_isUnit_right (hxr ▸ hunit s hs), hxr⟩

theorem preimmersion_flat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  intro E _ _ _ H l c O _ β hβ W b hb
  haveI := c.fin
  haveI : NumberField c.F := {}
  letI : Algebra O W := b.toAlgebra
  have hbv : ∀ o : O, ((b o : W) : c.F) = β o := fun o => by rw [← hb]; rfl
  have hinj : Function.Injective b := fun u v h => hβ.1 (by rw [← hbv, ← hbv, h])
  let S : Submonoid O := (IsUnit.submonoid W).comap b
  haveI : IsLocalization S W := by
    refine (isLocalization_iff S W).2 ⟨fun y => y.2, fun z => ?_, fun {u v} h => ⟨1, by rw [hinj h]⟩⟩
    obtain ⟨a, s, ha, hs, hu, hz⟩ := exists_integral_frac W z
    obtain ⟨a', ha'⟩ := hβ.2 _ ha
    obtain ⟨s', hs'⟩ := hβ.2 _ hs
    have e1 : b a' = a := Subtype.ext (by rw [hbv, ha'])
    have e2 : b s' = s := Subtype.ext (by rw [hbv, hs'])
    refine ⟨⟨a', ⟨s', ?_⟩⟩, ?_⟩
    · show IsUnit (b s')
      rwa [e2]
    · show z * b s' = b a'
      rw [e1, e2, hz]
  refine ⟨IsPreimmersion.of_isLocalization (R := O) (S := W) S, ?_⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact (RingHom.flat_algebraMap_iff (R := O) (S := W)).2 (IsLocalization.flat W S)

end GlobalTheory.ValLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFlatValuationSubringBaseRingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  first | exact @GlobalTheory.ValLocal.preimmersion_flat | exact GlobalTheory.ValLocal.preimmersion_flat | (intros; apply GlobalTheory.ValLocal.preimmersion_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFibresLocalisedModelBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFibresLocalisedModelBaseChange
noncomputable section

namespace GlobalTheory.KeyUnitModels.SplitLoc

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open scoped CategoryTheory.Obj

theorem isIso_residueFieldMap {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] (z : Z) :
    IsIso (i.residueFieldMap z) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, fun u => ?_⟩
  obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
  obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
  exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩

theorem split_of_pullback {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] {G : Over X} {G' : Over Z} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G i φ) (z : Z)
    (h : ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField (i z)) k),
      FiniteDimensional (X.residueField (i z)) k ∧ Algebra.IsSeparable (X.residueField (i z)) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z))).obj G)) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField z) k),
      FiniteDimensional (Z.residueField z) k ∧ Algebra.IsSeparable (Z.residueField z) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z)).obj G') := by
  obtain ⟨k, _, _, hfin, hsep, S, hS⟩ := h
  have := isIso_residueFieldMap i z
  let e : X.residueField (i z) ≃+* Z.residueField z := (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv
  let _ : Algebra (Z.residueField z) k := ((algebraMap (X.residueField (i z)) k).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (Z.residueField z) k).comp (e : _ →+* _) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (X.residueField (i z)) k) :=
    RingHom.ext fun a => congrArg (algebraMap (X.residueField (i z)) k) (e.symm_apply_apply a)
  refine ⟨k, inferInstance, inferInstance, Module.Finite.of_equiv_equiv e (RingEquiv.refl k) he,
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl k) he, S, ?_⟩
  have hc : i.residueFieldMap z ≫ CommRingCat.ofHom (algebraMap (Z.residueField z) k) =
      CommRingCat.ofHom (algebraMap (X.residueField (i z)) k) := CommRingCat.hom_ext he
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z) ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.fromSpecResidueField (i z)) (Spec.map_comp _ _).symm)
  obtain ⟨j, hj, -⟩ := grpPullback_iso (isGrpPullback_pullback G _)
    (((isGrpPullback_pullback G' _).comp hφ).congr key rfl)
  exact isGt_of_iso j hS

theorem locModel_splitFibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)]
    [Flat (spMap b)], Y.SplitFibres → (locModel Y b hb).SplitFibres := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' b hb _ _ h x
  exact split_of_pullback (pullback.fst Y.s (spMap b)) (locMap Y b).cart x (h _)

end GlobalTheory.KeyUnitModels.SplitLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFibresLocalisedModelBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFibres_localisedModel_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.SplitFibres → (locModel Y b hb).SplitFibres := by
  first | exact @GlobalTheory.KeyUnitModels.SplitLoc.locModel_splitFibres | exact GlobalTheory.KeyUnitModels.SplitLoc.locModel_splitFibres | (intros; apply GlobalTheory.KeyUnitModels.SplitLoc.locModel_splitFibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRigidifiedSectionOfScalarMultipl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRigidifiedSectionOfScalarMultipl
noncomputable section

namespace GlobalTheory.KeySwapSec

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open ReciprocityTheory.ChartRestriction.G.H1

theorem exists_isFibreOf_of_isMul (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G))
    (x : KeyIn R') (hL : L.IsLB) (hx : IsFibreOf x G L rig θ w f) (θ₀ : L.Sec) (b : R) (hb : IsMul (X := G) θ b θ₀) :
    ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀),
      (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧
      IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  obtain ⟨φ, he, e, hg, F, hp, hgen, hr, hs, hF, hFe, hv⟩ := hx
  obtain ⟨th₀, h₀⟩ := sec_pull_down ((isGen_iff e).1 hgen) hL x.P.isLB θ₀
  have h₁ := (KeyCancel.appLE_eq_iff_stalk e θ x.th).1 hs
  have hm : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i := by
    refine (sec_eq_iff _ _ _ _).2 fun k y hk => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (φ y)
    have e₁ := h₁ _ (𝟙 _) y j k hj hk
    have e₀ := h₀ _ (𝟙 _) y j k hj hk
    rw [hb j, gs_mul (𝟙 _ ≫ φ) y _ hj, gs_constFn _ _ (𝟙 _ ≫ φ) y hj, e₀, Category.id_comp, hp.1.w, cst_comp,
      mul_left_comm] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  refine ⟨th₀, fun s => ?_, hm, φ, he, e, hg, F, hp, hgen, hr, (KeyCancel.appLE_eq_iff_stalk e θ₀ th₀).2 h₀, hF, hFe, hv⟩
  obtain ⟨z, hz, hne⟩ := x.th_ne s
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hne
  refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩⟩
  rw [hm k, Scheme.basicOpen_mul] at hk
  exact hk.2

end GlobalTheory.KeySwapSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRigidifiedSectionOfScalarMultiplStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G)) (x : KeyIn R'), L.IsLB → IsFibreOf x G L rig θ w f → ∀ (θ₀ : L.Sec) (b : R), IsMul (X := G) θ b θ₀ → ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀), (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧ IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  first | exact @GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | exact GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | (intros; apply GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModels
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyUnitModels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

open GlobalTheory.FlagMod (ev_res ev_spMap le_preimage_mono)

theorem norm_bounds {κ : KeyRule} (hκ : IsKeyRule κ) (x : KeyIn ℂ) {τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hab : GlobalTheory.KeyPow.charHalf _ a b) (hc : c₀ ≠ 0)
    (hN : GlobalTheory.KeyPow.NormalAt x τ Mx a b c₀) {C : ℝ} (hC : 0 < C) (h₁ : C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2)
    (h₂ : ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C) : ‖(κ ℂ x : ℂ)‖ ≤ C ^ 4 ∧ ‖(κ ℂ x : ℂ)⁻¹‖ ≤ C ^ 4 := by
  have hr : 0 < ‖Mx.det‖ / ‖c₀‖ ^ 2 := (inv_pos.2 hC).trans_le h₁
  have hM : Mx.det ≠ 0 := fun h0 => by simp [h0] at hr
  obtain ⟨P, hg, rig, hrig, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := GlobalTheory.KeyConst.exists_rescale P hg rig hrig th hth v hv τ Mx _ _ c₀ hc hM hN
  obtain ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff _ _ _ _).1 hN₀
  have e := hκ.1 ℂ P hg rig hrig _ hth₀ v₀ hv₀ th hth v hv c₀ Mx e₁ hMv
  rw [hκ.2.2.2.1 ⟨P, hg, rig, hrig, th₀, hth₀, v₀, hv₀⟩ u τ a b k₁ k₂ hab.1 hab.2 k₃ k₄ k₅ k₆, Units.val_one,
    _root_.mul_one] at e
  have q : 0 < ‖c₀‖ := norm_pos_iff.2 hc
  have e' : ‖(κ ℂ ⟨P, hg, rig, hrig, th, hth, v, hv⟩ : ℂ)‖ = (‖Mx.det‖ / ‖c₀‖ ^ 2) ^ 4 := by
    have := congrArg (‖·‖) e
    simp only [norm_mul, norm_pow] at this
    rw [div_pow, ← pow_mul, eq_div_iff (by positivity), ← this, _root_.mul_comm]
  constructor
  · rw [e']
    gcongr
  · rw [norm_inv, e', ← inv_pow]
    gcongr
    exact inv_le_of_inv_le₀ hC h₁

theorem countable_sections {X : Scheme.{0}} {O : Type} [CommRing O] [Countable O] (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : Countable Γ(X, U) := by
  have hf : (s.appLE ⊤ _ le_top).hom.FiniteType :=
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨_, hU⟩ le_top)
  letI := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp O, ⊤) Γ(X, U) := hf
  have hc : Countable Γ(Sp O, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.symm.injective.countable
  obtain ⟨n, f, hfs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  have : Countable (MvPolynomial (Fin n) Γ(Sp O, ⊤)) :=
    (MvPolynomial.basisMonomials (Fin n) Γ(Sp O, ⊤)).repr.injective.countable
  exact hfs.countable

theorem exists_chart_unit {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (M : GChart Y) : ∃ u : Γ(Y.X, M.U), IsUnit u ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X)
      (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), Set.range z ⊆ Set.range Y.j → KeyAt M z hz x → (κ K x : K) = ev z M.U hz u := by
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, hopen⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  have := Y.jQ_open
  have hj : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  obtain ⟨-, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen W c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  obtain ⟨W₀, f₀, hW, hf⟩ := GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart E H D l Xo c _ _ Y inferInstance hj hpq κ hκ M
  have hcF : Countable c.F := by
    have := c.fin
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F
    rw [← Cardinal.mk_le_aleph0_iff]
    simpa [Cardinal.mkRat] using this
  have : Countable W := Subtype.val_injective.countable
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := M.dom
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ := IsTotallyComplex.finrank E
    have h₂ : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact Nat.mul_pos (by omega) hpq
  have hWU : W₀ ≤ M.U := fun x hx => ((hW x).1 hx).1
  have hWj : ∀ {K : Type} [Field K] {z : Sp K ⟶ Y.X}, ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := fun hz => by
    rintro _ ⟨q, rfl⟩; exact ((hW _).1 (hz (Set.mem_univ q))).2
  have hne : ∃ x, x ∈ W₀ := by
    obtain ⟨q⟩ : Nonempty (Sp Γ(Y.X, M.U)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    obtain ⟨x, hx, hx'⟩ := hdense.exists_mem_open M.U.isOpen ⟨_, tau_le M.hU le_rfl (Set.mem_univ q)⟩
    exact ⟨x, (hW x).2 ⟨hx', hx⟩⟩
  obtain ⟨hinj, hext⟩ := GlobalTheory.GenExt.extend_of_integral_at_dvr _ _ W₀ hWU M.hU M.dom
    (IsLocallyNoetherian.component_noetherian ⟨_, M.hU⟩) (GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen M.hU)
    (countable_sections Y.s M.hU) hne
  have key : ∀ u : Γ(Y.X, W₀), (u = f₀.val ∨ u = (f₀⁻¹).val) → ∃ f, resG _ hWU f = u := by
    intro u hu
    refine hext u fun R K _ _ _ _ _ _ z hR hz h => ?_
    let y := IsOpenImmersion.lift Y.j (spMap (algebraMap R K) ≫ z) (hWj h)
    have : CharZero K := charZero_of_injective_ringHom (Spec.preimage (y ≫ pullback.snd _ _)).hom.injective
    refine GlobalTheory.T.integral_of_arcs_and_goodReduction_points E H D l Xo c W Y h3 h4 hs hj M.U W₀ u (fun x hx hx' => (hW x).2 ⟨hx, hx'⟩)
      (fun a χ hA hover hgen hχ => ?_) (fun R K _ _ _ _ _ _ _ z y hz hy hab h => ?_) R K z y hR hz
      (IsOpenImmersion.lift_fac _ _ _) h
    · obtain ⟨y, hy, T, C', hC', hT⟩ := GlobalTheory.ArcNormal.arc_normal_form _ _ _ _ _ _ _ Y hpq hP a χ hA hover hgen M hχ
      refine GlobalTheory.ArcReg.not_pole_of_bounded _ M.U W₀ u χ y M.hU hWU hχ hy ⟨T, C' ^ 4, fun w hw hyw => ?_⟩
      obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (y w) (le_preimage_mono hWU hyw) (hWj hyw) hpos
      obtain ⟨τ, Mx, a', b', c₀, k₁, k₂, k₃, k₄, k₅⟩ := hT w hw _ x hk
      obtain ⟨b₁, b₂⟩ := norm_bounds hκ x k₁ k₂ k₃ hC' k₄ k₅
      have e := hf ℂ (y w) hyw _ x hk
      rcases hu with rfl | rfl
      · rwa [e]
      · rwa [map_units_inv, e]
    · obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M _ (le_preimage_comp _ hz) (hWj h) hpos
      obtain ⟨v, hv⟩ := GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart E H D l Xo c _ _ Y κ hκ M R K z hz y hy hab x hk
      have e := hf K _ h _ x hk
      rcases hu with rfl | rfl
      · exact ⟨v, by rw [e, hv]⟩
      · exact ⟨(v⁻¹ : Rˣ), by rw [map_units_inv, map_units_inv, e, hv]⟩
  obtain ⟨f, hf₁⟩ := key _ (Or.inl rfl)
  obtain ⟨f', hf₂⟩ := key _ (Or.inr rfl)
  refine ⟨f, IsUnit.of_mul_eq_one f' (hinj ?_), fun K _ _ z hz x hr hk => ?_⟩
  · exact ((RingHom.map_mul _ f f').trans ((congrArg₂ (· * ·) hf₁ hf₂).trans f₀.mul_inv)).trans (RingHom.map_one _).symm
  · have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := fun q hq => (hW _).2 ⟨hz hq, hr ⟨q, rfl⟩⟩
    rw [← hf K z hz₀ _ x hk, ← hf₁, ev_res z hWU hz₀ hz]

theorem lieComb_one {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) :
    IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i) x.v (x.v i) := by
  have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  have := x.P.isAb.comm
  exact (GlobalTheory.LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i

theorem unitAt_local {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] :
    UnitAt κ Y V K := by
  intro y yt hyt t m n w hw θ x hx
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, -⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  obtain ⟨M, hM⟩ := GlobalTheory.FlagMod.exists_gChart hP (yt (IsLocalRing.closedPoint V))
  have hz : ⊤ ≤ yt ⁻¹ᵁ M.U := ((IsLocalRing.closed_point_mem_iff (U := yt ⁻¹ᵁ M.U)).1 hM).ge
  obtain ⟨u, hu, hval⟩ := exists_chart_unit Y hpq hP h3 h4 hs hκ M
  have := t.semi.smooth
  obtain ⟨θ₀, h₀⟩ : ∃ θ₀ : t.PP.L.Sec, NonzeroClosed (X := t.G) θ₀ := by
    obtain ⟨-, θ₀, -, -, hne⟩ := GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact ⟨θ₀, g, h₁, TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  have hC : ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) →
      Generates (X := t.G) θ → ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := fun θ x hx hθ => by
    obtain ⟨x', a, d, hk, e⟩ := GlobalTheory.T.exists_generatingFrame_unit_change_to_chart E H D l Xo c _ _ Y M V K yt hz t m n w hw θ x hx hθ
    have e₁ := e κ hκ
    rw [hval K _ _ x' (by
      rw [hyt]; rintro _ ⟨q, rfl⟩; exact ⟨y q, (Scheme.Hom.comp_apply _ _ _).symm⟩) hk,
      ev_spMap (algebraMap V K) yt M.U hz, RingHom.comp_apply] at e₁
    refine ⟨(d ^ 4)⁻¹ * (a ^ 8 * (hu.map (ev yt M.U hz)).unit), ?_⟩
    have hd : algebraMap V K d ≠ 0 := (d.isUnit.map _).ne_zero
    rw [Units.val_mul, map_mul, map_units_inv, Units.val_mul, map_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow, map_pow, e₁, inv_mul_cancel_left₀ (pow_ne_zero _ hd)]
  have hB : ∀ (θ : t.PP.L.Sec), Generates (X := t.G) θ → ∀ N : ℕ, Generates (X := pow t.G N) (boxSec t.G θ N) :=
    fun θ' hθ N => by
      obtain ⟨a, ha, -⟩ := hθ θ₀
      obtain ⟨hfl, g, hg, hnz⟩ := GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre V t.G t.PP.L θ' (NonzeroClosed.of_isMul ha h₀).2 N
      obtain ⟨X', p', φ, L', b, k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.exists_line_sections_externalTensorPower_fibre V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx N
      exact generates_of_generic_line (pow t.G N).hom k₁ (LB.isLB_linComb t.PP.isLB _ _) k₂ k₃ b k₄ _ hg hnz
  refine ⟨fun hθ => ⟨hC θ x hx hθ, fun N _ => hB θ hθ N⟩, ?_⟩
  intro N hN σ a hσ hmul
  have hg₀ := generates_of_isFibreOf t.PP.isLB hx h₀
  obtain ⟨b, hθb, -⟩ := hg₀ θ
  obtain ⟨th₀, hth₀, hth, hx₀⟩ := GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx θ₀ b hθb
  obtain ⟨u₀, hu₀⟩ := hC θ₀ _ hx₀ hg₀
  have hbox₀ := hB θ₀ hg₀ N
  have hom := hκ.1 K x.P x.g_pos x.rig x.rig_gen th₀ hth₀ x.v x.basis x.th x.th_ne x.v x.basis (algebraMap V K b) 1
    hth (lieComb_one x)
  rw [Matrix.det_one, one_pow, _root_.one_mul] at hom
  obtain ⟨c', hc', -⟩ := hσ (boxSec t.G θ₀ N)
  have hcu : IsUnit c' := Generates.isUnit hσ hbox₀ hc'
  have ha : a = b ^ N * c' := (hσ (boxSec t.G θ N)).unique hmul (IsMul.trans (isMul_boxSec hθb N) hc')
  obtain ⟨k, rfl⟩ := hN
  refine ⟨hcu.unit * u₀ ^ k, ?_⟩
  rw [ha, Nat.mul_div_cancel_left k (by norm_num : 0 < 8)]
  simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [← hu₀, ← hom, pow_mul]
  ring

theorem unitAt_valuation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (hpq : 1 ≤ D.p + D.q)
    (hβ : IsBaseRing β) (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule}
    (hκ : IsKeyRule κ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] : UnitAt κ Y V K := by
  intro y yt hyt t m
  have hinj := IsFractionRing.injective V K
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B),
      spMap f ≫ spMap g = spMap (f.comp g) := fun _ _ => (Spec.map_comp _ _).symm
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* K, spMap io = y ≫ pullback.snd _ _ := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : O →+* V, spMap b₀ = yt ≫ Y.s := ⟨_, Spec.map_preimage _⟩
  have hc : (algebraMap V K).comp b₀ = io.comp β := by
    have e : spMap ((algebraMap V K).comp b₀) = spMap (io.comp β) := by
      rw [← sp, ← sp, hb₀, hio, ← Category.assoc, hyt, Model.j, Category.assoc, Category.assoc, Category.assoc,
        pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let W : ValuationSubring c.F :=
    { (algebraMap V K).range.comap io with
      mem_or_inv_mem' := fun a => by
        have := ValuationRing.isInteger_or_isInteger V (io a)
        rw [← map_inv₀] at this
        exact this }
  let b : O →+* W := β.codRestrict W.toSubring fun a => ⟨b₀ a, RingHom.congr_fun hc a⟩
  have hb : W.subtype.comp b = β := rfl
  let e := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a a' h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  let b' : W →+* V := e.symm.toRingHom.comp ((io.comp W.subtype).codRestrict (algebraMap V K).range fun a => a.2)
  have hb' : b'.comp b = b₀ := RingHom.ext fun a => by
    apply e.injective
    exact (e.apply_symm_apply _).trans (Subtype.ext (RingHom.congr_fun hc a).symm)
  obtain ⟨_, _⟩ := GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing E H l c O β hβ W b hb
  let yt' : Sp V ⟶ (locModel Y b hb).X := pullback.lift yt (spMap b') (by rw [sp, hb', hb₀])
  have hy' : yt' ≫ pullback.fst Y.s (spMap b) = yt := pullback.lift_fst _ _ _
  obtain ⟨m', -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := yt') (locMap Y b) (hy'.symm ▸ m)
  exact unitAt_local (locModel Y b hb) hpq (locModel_pushInvertible Y b hb (GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W).1 hP) (localisedModel_uniformisation_baseChange Y b hb h3)
    (GlobalTheory.T.arcProperty_localisationBaseChange_of_model E H D l Xo c O β Y _ _ b hb h4) (GlobalTheory.T.splitFibres_localisedModel_baseChange E H D l Xo c O β Y _ _ b hb hs) hκ V K y yt' (by
      rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, Category.assoc, hy', locModel_j, hyt]) t m'

theorem keyUnitOnModels : KeyUnitOnModels := by
  intro κ hκ E _ _ _ H D l Xo c O _ β Y p h₁ h₂ _ h₄ h₅ h₆ h₇
  refine ⟨fun V K _ _ _ _ _ _ _ _ => unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V K, fun V C _ _ _ _ _ _ _ hV => ?_⟩
  obtain ⟨_, _, _⟩ := GlobalTheory.GoodRedUnitBall.valuationRing_of_unitBall hV
  exact unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V C

end GlobalTheory.KeyUnitModels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModelsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.KeyUnitOnModels := by
  first | exact @GlobalTheory.KeyUnitModels.keyUnitOnModels | exact GlobalTheory.KeyUnitModels.keyUnitOnModels | (intros; apply GlobalTheory.KeyUnitModels.keyUnitOnModels <;> assumption)
end

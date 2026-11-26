module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemClassSumsUnboundedLevelsOneInde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberOfUnitaryMonomialUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinkedThetaSystemRegularMonomialFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemOfUniversalSectionBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemExactOfGeometricUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemExactOfGeometricUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.GSep.ExactSums

theorem congMod_pi_iff {X : Type} [AddCommGroup X] {s : ℕ} (N : ℕ) (a b : Fin s → X) :
    CongMod N a b ↔ ∀ v, CongMod N (a v) (b v) := by
  constructor
  · rintro ⟨w, hw⟩ v
    exact ⟨w v, by rw [hw]; rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext fun v => by rw [hw v]; rfl⟩

theorem labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (H : AddSubgroup S.Gam)
    {X : Type} [AddCommGroup X] (YY : S.Gam → X → Prop)
    (h1 : ∀ a, ∃ mu, YY a mu) (h2 : ∀ mu, ∃ a, YY a mu)
    (h3 : ∀ a mu mu', YY a mu → (YY a mu' ↔ CongMod (S.r * S.N) mu' mu))
    (h4 : ∀ a a' mu mu', YY a mu → YY a' mu' → YY (a + a') (mu + mu'))
    (hH : ∀ a, a ∈ H ↔ YY a 0) :
    ∃ l : X → S.Gam, (∀ mu, YY (l mu) mu) ∧
      (∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu)) ∧
      ∀ mu κ, (∀ τ ∈ S.perp H, eStd S.g _ τ (l mu) = eStd S.g _ τ (l κ)) ↔ CongMod (S.r * S.N) mu κ := by
  obtain ⟨l, hl⟩ : ∃ l : X → S.Gam, ∀ mu, YY (l mu) mu := ⟨fun mu => (h2 mu).choose, fun mu => (h2 mu).choose_spec⟩
  have sub : ∀ a a' mu, YY a mu → YY a' mu → a - a' ∈ H := by
    intro a a' mu ha ha'
    obtain ⟨b, hb⟩ := h2 (-mu)
    have e1 := h4 _ _ _ _ ha hb
    have e2 := h4 _ _ _ _ ha' hb
    rw [add_neg_cancel] at e1 e2
    have := H.sub_mem ((hH _).2 e1) ((hH _).2 e2)
    simpa using this
  have D1 : ∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu) := by
    intro τ hτ a mu ha
    have h0 : eStd S.g _ τ (a - l mu) = 0 := hτ _ (sub a (l mu) mu ha (hl mu))
    have e : a = (a - l mu) + l mu := (sub_add_cancel a (l mu)).symm
    conv_lhs => rw [e]
    rw [eStd_add_right, h0, zero_add]
  refine ⟨l, hl, D1, fun mu κ => ⟨fun h => ?_, fun h τ hτ => ?_⟩⟩
  · have hb : l mu - l κ ∈ H := by
      rw [← TestBasis.perp_perp S H]
      intro τ hτ
      have e : eStd S.g _ τ (l mu) = eStd S.g _ τ (l mu - l κ) + eStd S.g _ τ (l κ) := by
        rw [← eStd_add_right, sub_add_cancel]
      have h0 : eStd S.g _ τ (l mu - l κ) = 0 := by rw [h τ hτ] at e; simpa using e.symm
      rw [eStd_swap, h0, neg_zero]
    have e1 := h4 _ _ _ _ (hl κ) ((hH _).1 hb)
    rw [add_sub_cancel, add_zero] at e1
    obtain ⟨w, hw⟩ := (h3 _ _ _ (hl mu)).1 e1
    exact ⟨-w, by rw [hw, smul_neg, add_neg_cancel_right]⟩
  · exact (D1 τ hτ (l κ) mu ((h3 _ _ _ (hl κ)).2 h)).symm


open Classical GlobalTheory.Poinc.Sep.ExactSums in
theorem exact_of_isGeo : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  intro O _ bar q s W X₁ z₁ act x₀ Φ lab hG
  obtain ⟨hdiv, hlab, hmem⟩ := hG
  obtain ⟨sg, eps, hlink⟩ := GlobalTheory.T.thetaConstants_translate_eq_twisted_sums O X₁ z₁ act x₀ hdiv
  intro y κ c
  obtain ⟨𝔪, hT⟩ := hmem y
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩
  haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
  obtain ⟨yy1, yy2, yy3, yy4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level O X₁ z₁ act (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪
  have hH := GlobalTheory.T.mem_dividingLabels_iff_class_zero O X₁ z₁ act x₀ hdiv (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪
  obtain ⟨l, -, hlY, hlC⟩ := labels X₁.S (X₁.S.HH X₁.M z₁) 𝔪.YY yy1 yy2 yy3 yy4 hH

  let φ : X₁.o₁ →+* X₁.M.Z.presheaf.stalk z₁ :=
    (X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))
  have hsh : ∀ b : X₁.M.O z₁, X₁.M.stalkHom z₁ ((X₁.M.stalkEquiv z₁).symm b) = b := fun b => by
    rw [← RatModel.coe_stalkEquiv (M := X₁.M), RingEquiv.apply_symm_apply]
  have hφ : ∀ a, X₁.M.stalkHom z₁ (φ a) = algebraMap X₁.o₁ X₁.Ω₁ a := fun a => hsh _

  let zt := φ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  have hzt : X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := hφ _
  have hunitV : IsUnit (((X₁.S.r * X₁.S.N : ℕ) : Φ.V y)) := by
    have := X₁.S.unit.map ((Φ.ev y).comp φ)
    rwa [map_natCast] at this
  have hω : IsPrimitiveRoot (Φ.ev y zt) (X₁.S.r * X₁.S.N) := by
    have h0 : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
      X₁.S.prim.pow (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) 2) (sq _)
    exact isPrimitiveRoot_map' ((Φ.ev y).comp φ) hunitV.ne_zero h0

  let TT := X₁.S.TT X₁.M z₁
  have hmemO : ∀ τ : TT, algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ ∈ X₁.M.O z₁ :=
    fun τ => by rw [mul_div_assoc]; exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv.2 _)
  let hτ : TT → X₁.M.Z.presheaf.stalk z₁ := fun τ => (X₁.M.stalkEquiv z₁).symm ⟨_, hmemO τ⟩
  have hhτ : ∀ τ : TT, X₁.M.stalkHom z₁ (hτ τ) =
      algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := fun τ => hsh _

  have hcard : IsUnit ((Fintype.card TT : ℕ) : X₁.o₁) := by
    have h1 : Fintype.card TT ∣ Fintype.card X₁.S.Gam := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact AddSubgroup.card_addSubgroup_dvd_card _
    have h2 : IsUnit ((Fintype.card X₁.S.Gam : ℕ) : X₁.o₁) := by
      rw [Fintype.card_fun, ZMod.card, Nat.cast_pow]; exact X₁.S.unit.pow _
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast h1) h2
  obtain ⟨u, hu⟩ := hcard.map φ
  let d := ((u⁻¹ : (X₁.M.Z.presheaf.stalk z₁)ˣ) : X₁.M.Z.presheaf.stalk z₁)
  have hd : Φ.ev y d * (Fintype.card TT : Φ.V y) = 1 := by
    rw [← map_natCast (Φ.ev y), ← map_mul, ← map_natCast φ, ← hu, Units.inv_mul, map_one]

  let w : (Fin s → Φ.X y) → TT → ZMod (X₁.S.r * X₁.S.N) := fun mu τ => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (l mu)
  have hw : ∀ mu τ τ', w mu (τ + τ') = w mu τ + w mu τ' := fun mu τ τ' => by
    simp only [w, AddSubgroup.coe_add, eStd_add_left, smul_add]
  have hsg : ∀ a b : ZMod (X₁.S.r * X₁.S.N), (sg : ℤ) • a = (sg : ℤ) • b → a = b := fun a b h => by
    have := congrArg (fun t => (sg : ℤ) • t) h
    have e : ((sg : ℤ) * sg) = 1 := by rcases Int.units_eq_one_or sg with h | h <;> simp [h]
    simpa only [smul_smul, e, one_smul] using this
  have hwκ : ∀ mu, (∀ τ, w mu τ = w κ τ) ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) := fun mu => by
    rw [← congMod_pi_iff, ← hlC mu κ]
    exact ⟨fun h τ hτ' => hsg _ _ (h ⟨τ, hτ'⟩), fun h τ => by simp only [w, h τ τ.2]⟩
  have hlab' : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁ := fun c => by
    rw [← SetLike.mem_coe, ← hlab]; exact Set.mem_range_self c
  have hsum : ∀ τ : TT, SumI (maximalIdeal (Φ.V y)) (fun mu => Φ.ev y zt ^ (w mu τ).val * Φ.term y mu c) (Φ.ev y (hτ τ)) :=
    fun τ => hlink (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪 Φ.Q lab hlab' (Φ.term y) hT c τ τ.2 zt (hτ τ) hzt
      (hhτ τ) (fun mu => w mu τ) (fun a mu hY => by simp only [w, hlY τ τ.2 a mu hY])
  let f : (Fin s → Φ.X y) → Φ.V y := fun mu => if ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) then Φ.term y mu c else 0
  have hf := sumI_fourier (maximalIdeal (Φ.V y)) hω (Φ.ev y d) hd w hw κ (fun mu => Φ.term y mu c) (fun τ => Φ.ev y (hτ τ))
    hsum f (fun mu h => if_pos ((hwκ mu).1 h)) (fun mu h => if_neg fun h' => h ((hwκ mu).2 h'))
  refine ⟨d * ∑ τ : TT, zt ^ (-(w κ τ)).val * hτ τ, isClassSum_of_sumI Φ y _ κ c (RingHom.id _) _ f
    (fun mu h => if_pos h) (fun mu h => if_neg h) ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_pow] using hf

end GlobalTheory.GSep.ExactSums
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemExactOfGeometricUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_exact_of_geometric_uniformisation : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.GSep.ExactSums.exact_of_isGeo | exact GlobalTheory.GSep.ExactSums.exact_of_isGeo | (intros; apply GlobalTheory.GSep.ExactSums.exact_of_isGeo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsIsThetaTermsTorsionFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsIsThetaTermsTorsionFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.GSep.ThetaTerms

theorem yK_ne_zero {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V}
    {δ : I → X → X} (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) :
    𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  intro h0
  apply ha
  set y := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq] at h0 ⊢
  change X₁.M.val y (X₁.S.th a) = 0
  change X₁.M.val y (X₁.S.th x₀) = 0 at h0
  rw [e, RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀)), h0, mul_zero]

theorem isThetaTerms₀_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  intro I X₁ z₁ act x₀ hd V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, hT⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  have h0 := yK_ne_zero hd 𝔪

  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', c, hc, hN, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  choose w' fr' hw' hfr' hov hco hval using fun a : C => liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
    (g' a) (w a) (x (lab a)) (fr (lab a)) (hg a).2.1 (hfr _).1 (hg a).2.2 c hc
  have htors : ∀ a, (g' a).b ^ (X₁.S.r * X₁.S.N) = 1 := fun a => by
    obtain ⟨o, h₁, h₂⟩ := (hg a).1
    letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
    have e := congrArg (GlobalTheory.TorusExt.gtProj 𝔪.D.toPre (FractionRing V)) ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁)
    rw [map_nsmul] at e
    exact (congrArg Additive.toMul e).symm.trans ((isZero_iff o).1 h₂).1
  choose b hb₁ hb₂ using fun a => GlobalTheory.T.torsionPoint_extends_over_normal_domain hL.1 V 𝔪.cn.1 𝔪.cn.2.1 𝔪.D.toPre.P _ hk (g' a).b (htors a)
  refine ⟨(c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0, g', b, w', hb₂, fun a => (hg a).1, ?_, fun a => ⟨hw' a, ?_⟩,
    fun mu a => ?_⟩
  · refine GlobalTheory.T.torsion_sections_exhaust_geometric_fibres hL.1 V 𝔪.cn.1 𝔪.D.toPre.P _ hk hu C b hb₁ fun p hp => ?_
    obtain ⟨a, ha⟩ := exhaust_of_labels hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hk C g' (fun a => x (lab a)) (fun a => (hg a).1)
      (fun a a' e => by
        have h₁ := hg a
        have h₂ := hg a'
        generalize w a' = om at h₂
        generalize g' a' = ga at e om h₂
        subst e
        exact GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ hw₀ _ _ _ _ _ _ _ h₁.2.1 h₂.2.1 (hfr _).1 (hfr _).1
          h₁.2.2 h₂.2.2)
      (fun q y hq hy => by
        have hyN : y ^ (X₁.S.r * X₁.S.N) = 1 := (hy w₀ hw₀).1
        have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
            spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
          (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
        obtain ⟨l, hl, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ (Geo.Tor.pushHom 𝔪.cart _ y)
          (by rw [← map_pow, hyN, map_one])
        have hl' : y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
            (X₁.ρ.pt l).left := by
          rw [← e]
          exact (congrArg (fun q => q.left) hl).symm
        have hH : l ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hd V ev X t δ 𝔪 l).2
          ⟨q, y, by rw [hq, map_zero], hy, hl'⟩
        obtain ⟨a, rfl⟩ : l ∈ Set.range lab := by rw [hlab]; exact hH
        refine ⟨a, 𝔪.cart.1.hom_ext ?_ ?_⟩
        · rw [hl', ← e]
          exact ((Category.assoc _ _ _).trans ((congrArg _ (hx _)).trans (Category.assoc _ _ _).symm)).symm
        · refine (Over.w y).trans (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg _ (Over.w (x (lab a))))).symm)
          exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) p hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    rw [ha, hb₂ a, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    change spMap _ ≫ spMap _ ≫ jK V = spMap _ ≫ jK V
    rw [Algebra.algebraMap_self, show spMap (RingHom.id (FractionRing V)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  · obtain ⟨o, h₁, h₂⟩ := (hg a).1
    exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hN _ hk _ o h₁ h₂ _ _ _ (hw' a) (hov a)
      (hmove _ _ _ _ _ (htf _) (hfr' a) (hval a))
  · have h₁ := ((CoefBasic.coef_basic V 𝔪.D.toPre (FractionRing V) 1 (g' a)).2.2 (w' a) (hw' a)).2.1
    have h₂ : coef (0 : Fam 𝔪.D.toPre (FractionRing V) 1) (g' a) (w' a) (𝔪.e₈ mu) = 0 := by
      have := h₁ 0 0 1 (𝔪.e₈ mu)
      rw [one_smul, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    have h₃ : algebraMap V (FractionRing V) (T mu a) =
        coef ((c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0) (g' a) (w' a) (𝔪.e₈ mu) := by
      rw [h₁, h₂, add_zero, div_mul_eq_mul_div, hco, ← hT, mul_div_cancel_right₀ _ h0]
    rw [h₃]
    exact CoefBasic.isCoef_coef _ (hw' a) _ _

end GlobalTheory.GSep.ThetaTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsIsThetaTermsTorsionFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_terms_isThetaTerms_torsionFrames : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  first | exact @GlobalTheory.GSep.ThetaTerms.isThetaTerms₀_of_terms | exact GlobalTheory.GSep.ThetaTerms.isThetaTerms₀_of_terms | (intros; apply GlobalTheory.GSep.ThetaTerms.isThetaTerms₀_of_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtSqrtUniformiserCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtSqrtUniformiserCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep


open Polynomial in
theorem exists_finite_ext_sq_eq_uniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsPrincipalIdealRing V → ∀ ϖ : V, Irreducible ϖ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (t : V'), IsCN V' ∧ IsPrincipalIdealRing V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ t ^ 2 = f ϖ := by
  intro V _ _ _ hV hP ϖ hϖ
  let K₀ := FractionRing V
  let p : K₀[X] := X ^ 2 - C (algebraMap V K₀ ϖ)
  let L := p.SplittingField
  have hdeg : (p.map (algebraMap K₀ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]
    norm_num
  obtain ⟨s, hs⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero hdeg
  have hs2 : s ^ 2 = algebraMap K₀ L (algebraMap V K₀ ϖ) := by
    simpa [p, sub_eq_zero] using hs
  obtain ⟨V₁, _, _, _, ρ, σ, hCN, hinj, hfin, hloc, hcomp⟩ :=
    GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local V hV L
  obtain ⟨hN₁, hIC₁, _, _⟩ := hCN

  have hy2 : (σ s) ^ 2 = algebraMap V₁ (FractionRing V₁) (ρ ϖ) := by
    rw [← map_pow, hs2, hcomp]
  have hint : IsIntegral V₁ (σ s) := by
    refine ⟨X ^ 2 - C (ρ ϖ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub, hy2, Algebra.algebraMap_eq_smul_one]
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have ht2 : t ^ 2 = ρ ϖ := by
    apply IsFractionRing.injective V₁ (FractionRing V₁)
    rw [map_pow, ht, hy2]

  letI : Algebra V V₁ := ρ.toAlgebra
  haveI : Module.Finite V V₁ := hfin
  haveI : Algebra.IsIntegral V V₁ := Algebra.IsIntegral.of_finite V V₁
  have hϖ0 : ρ ϖ ≠ 0 := by
    intro h; apply hϖ.ne_zero; apply hinj; simpa using h
  have hϖnu : ¬ IsUnit (ρ ϖ) := fun h => hϖ.not_isUnit ((isUnit_map_iff ρ ϖ).mp h)
  have hnf : ¬ IsField V₁ := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hϖ0
    exact hϖnu (IsUnit.of_mul_eq_one _ hb)
  have hdvr : IsDiscreteValuationRing V₁ := by
    have h03 := (IsDiscreteValuationRing.TFAE V₁ hnf).out 1 4
    refine h03.mpr ⟨hIC₁, ⟨maximalIdeal V₁, ⟨?_, inferInstance⟩, ?_⟩⟩
    · intro h
      apply hϖnu
      by_contra hu
      have : ρ ϖ ∈ maximalIdeal V₁ := hu
      rw [h] at this
      exact hϖ0 ((Submodule.mem_bot _).mp this)
    · rintro P ⟨hP0, hPp⟩
      obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
      have hc : P.comap (algebraMap V V₁) ≠ ⊥ :=
        Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
      haveI : (P.comap (algebraMap V V₁)).IsPrime := Ideal.IsPrime.comap _
      have hm : (P.comap (algebraMap V V₁)).IsMaximal := IsPrime.to_maximal_ideal hc
      have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := V) P hm
      exact IsLocalRing.eq_maximalIdeal hPm
  exact ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, t, ⟨hN₁, hIC₁, by assumption, by assumption⟩,
    inferInstance, hinj, hloc, hfin, ht2⟩

end GlobalTheory.USep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtSqrtUniformiserCompleteDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_sqrt_uniformiser_complete_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsPrincipalIdealRing V → ∀ ϖ : V, Irreducible ϖ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (t : V'), IsCN V' ∧ IsPrincipalIdealRing V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ t ^ 2 = f ϖ := by
  first | exact @GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser | exact GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser | (intros; apply GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemUniversalUnitaryDeepTowers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemUniversalUnitaryDeepTowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.GSep.UTower

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem lbIso_pull_comp_of_eq {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isMonHom_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) (e : G ⟶ G) [IsMonHom e] (e' : G' ⟶ G')
    (he : e'.left ≫ φ = φ ≫ e.left) : IsMonHom e' := by
  have push_comp : ∀ {T₁ : Over S'} (x : T₁ ⟶ G'), pushPt hφ.1.w (x ≫ e') = pushPt hφ.1.w x ≫ e :=
    fun x => Over.OverMorphism.ext (by
      show (x.left ≫ e'.left) ≫ φ = (x.left ≫ φ) ≫ e.left
      rw [Category.assoc, he, Category.assoc])
  have pm : ∀ {T₁ : Over S'} (x y : T₁ ⟶ G'), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have inj : ∀ {T₁ : Over S'} {x y : T₁ ⟶ G'}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun h => GlobalTheory.SiegelPull.push_injective hφ _ h
  refine isMonHom_of_mul _ fun T₁ x y => inj ?_
  rw [push_comp, pm, pm, push_comp, push_comp]
  exact MonObj.mul_comp _ _ _

theorem deep_of_uLink : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → GlobalTheory.GSep.Deep X₁ act := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hU N₀
  have hact : IsAct X₁ act := hU.1
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j₀, hk, hBk, hj₀, big⟩ := GlobalTheory.Poinc.GSetup.exists_big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 N₀
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  haveI : CharZero X₁.Ω₁ := ArithBase.char (o := X₁.o₁)
  have hM : 0 < X₁.S.r * X₁.S.N := by rw [hL₁]; exact pow_pos hℓp.pos _
  have hζ₀ : ∃ ζ₀ : X₁.Ω₁, IsPrimitiveRoot ζ₀ (X₁.S.r * X₁.S.N) :=
    ⟨_, (X₁.S.prim.pow (by positivity) (sq _)).map_of_injective (ArithBase.inj (o := X₁.o₁) (Ω := X₁.Ω₁))⟩
  have htors : ∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp X₁.S.R) (z : Over.mk x ⟶ X₁.ρ.P.A),
      z ^ (X₁.S.r * X₁.S.N) = 1 → ∃ y : baseOver (Sp X₁.S.R) ⟶ X₁.ρ.P.A,
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp X₁.S.R)) ≫ y = z := by
    intro E _ _ x z hz
    obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij E x z hz
    exact ⟨_, ha⟩
  set j := j₀ + (j₁ + 2 * X₁.ρ.k) with hj
  set K := (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 with hK
  have hKpos : 0 < K := by have := hℓp.pos; positivity
  obtain ⟨Ω₂, _, _, Q, φQ, ζ, fd, gal, -, hζ, hQg, hQpb, hQlb, ⟨levQ⟩⟩ :=
    GlobalTheory.T.exists_primePower_galois_ext_symplecticLevel X₁.S.R.val.toRingHom X₁.ρ.P X₁.ρ.n (X₁.S.r * X₁.S.N) K hℓp hM
      (by rw [hL₁]; exact dvd_pow_self _ (by omega)) ⟨2 * (j + 2 * k), by rw [hK]; ring⟩ hζ₀ htors
  haveI := fd
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hc, hze⟩ :=
    GlobalTheory.Poinc.exists_arithBase_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hKpos hζ
  haveI : CharZero Ω₂ := ArithBase.char (o := o₂)
  obtain ⟨R, h, hfg, hfr, hh, hfin, hic, hstab⟩ := GlobalTheory.T.exists_integralClosure_finite_galoisStable_thetaRing X₁.S.R X₁.S.fg X₁.S.frac κ hκ hc
  haveI := GlobalTheory.ThetaReal.isNoetherian_of_fg hfg
  haveI := GlobalTheory.GenSpread.isFractionRing_of_forall_div hfr
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using hun1.map κ
  have hKunit : IsUnit (K : R) := by
    have := (hun2.map (algebraMap o₂ R))
    rw [map_natCast] at this
    rw [hK]; push_cast
    exact ((this.pow _).mul ((this.pow _).pow _)).pow _
  let zeR : (↥R)ˣ := Units.map (algebraMap o₂ R).toMonoidHom ze
  have hzeR : Units.map (algebraMap R Ω₂).toMonoidHom zeR = ζ := by
    rw [← hze]; ext; rfl
  have hQpb' : IsGrpPullback Q.A X₁.ρ.P.A (spMap ((algebraMap R Ω₂).comp h)) φQ := by
    have e : (algebraMap R Ω₂).comp h = (algebraMap X₁.Ω₁ Ω₂).comp X₁.S.R.val.toRingHom := RingHom.ext hh
    rw [e]; exact hQpb
  obtain ⟨P, ψ, hPg, hpb, hlb, ⟨lev⟩⟩ := GlobalTheory.T.symplecticLevel_extends_noetherian_normalDomain X₁.ρ.P R Ω₂ h Q φQ K zeR hKpos hKunit hQg hQpb' hQlb
    ⟨by rw [hzeR]; exact levQ⟩
  have hS := GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  obtain ⟨th, hth⟩ := GlobalTheory.T.exists_polarization_sectionBasis_pullback_affine X₁.ρ.P P h ψ hpb hlb X₁.ρ.th₁ X₁.ρ.th₁_basis
  obtain ⟨S₂, ρ₂, hR, φ₂, hSR, -, -, hN₂, hr₂, hg₂, hpb₂, hlb₂⟩ :=
    GlobalTheory.T.exists_realisedThetaSystem_of_universalSectionBasis o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk (by omega) hun2 hS th hth lev
  set om : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hom
  have hval : ∀ a, ((om a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hcart : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) := by
    rw [hom, ← spMap_comp_ring]
    exact hpb₂.comp hpb
  have hlbc : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ₂ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp_of_eq hlb φ₂ rfl)

  have hφp := hcart.1
  have wε : ∀ a, ((φ₂ ≫ ψ) ≫ (act a).left) ≫ X₁.ρ.P.A.hom = ρ₂.P.A.hom ≫ spMap om := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let act₂ : 𝓞 E → (ρ₂.P.A ⟶ ρ₂.P.A) := fun a =>
    Over.homMk (hφp.lift ((φ₂ ≫ ψ) ≫ (act a).left) ρ₂.P.A.hom (wε a)) (hφp.lift_snd _ _ _)
  have hact₂ : ∀ a, (act₂ a).left ≫ (φ₂ ≫ ψ) = (φ₂ ≫ ψ) ≫ (act a).left := fun a => hφp.lift_fst _ _ _
  have hmon : ∀ a, IsMonHom (act₂ a) := fun a => by
    haveI := hact a
    exact isMonHom_of_isGrpPullback hcart (act a) (act₂ a) (hact₂ a)

  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.M.s = spMap ((algebraMap o₂ Ω₂).comp κ) := by
    rw [Category.assoc, X₁.M.pt_s, hc]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))
      (CommRingCat.ofHom (algebraMap X₁.Ω₁ Ω₂))).symm
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (GlobalTheory.Poinc.stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (GlobalTheory.Poinc.RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := GlobalTheory.Poinc.exists_ratModel_normalization X₁.o₁ o₂ Ω₂ κ hκ X₁.M.Z X₁.M.s X₁.M.lft
    X₁.M.qc X₁.M.sep _ hp hst
  have hs : M₂.s ≫ spMap κ = q ≫ X₁.M.s := by
    refine ext_of_isDominant M₂.pt ?_
    rw [← Category.assoc, M₂.pt_s, spMap_comp_ring, ← Category.assoc, hqgen, hp]
  have hproj : IsProjOver M₂.s :=
    GlobalTheory.T.isProjOver_of_isFinite_over_projective X₁.o₁ o₂ κ M₂.Z X₁.M.Z X₁.M.s q M₂.s X₁.projM hq inferInstance hs

  have hrat : ∀ x : ratHull X₁.S.R, algebraMap X₁.Ω₁ Ω₂ (x : X₁.Ω₁) ∈ ratHull S₂.R := fun x => by
    obtain ⟨n, hn, hx⟩ := mem_ratHull.1 x.2
    refine mem_ratHull.2 ⟨n, hn, ?_⟩
    have h₀ := (om ⟨_, hx⟩).2
    rw [hval] at h₀
    simpa using h₀
  let rh : ratHull X₁.S.R →+* ratHull S₂.R :=
    ((algebraMap X₁.Ω₁ Ω₂).comp (ratHull X₁.S.R).val.toRingHom).codRestrict (ratHull S₂.R) hrat
  have hrv : spMap (ratHull S₂.R).val.toRingHom ≫ spMap rh =
      spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [spMap_comp_ring, spMap_comp_ring]
    rfl
  have hUO₂ : UOver Xo c ρ₂.P (toRat S₂.R) (spMap rh ≫ u) := by
    refine (uOver_baseChange_iff hcart hlbc (toRat S₂.R)).2 ?_
    have e : (toRat S₂.R).comp om = rh.comp (toRat X₁.S.R) := RingHom.ext fun a => Subtype.ext (hval a)
    rw [e]
    exact hU.uOver.comp rh
  have hgen₂ : ∀ w, (spMap (ratHull S₂.R).val.toRingHom ≫ spMap rh ≫ u) w ∈ genericPoints (Xo.XF c) := fun w => by
    rw [← Category.assoc, hrv, Category.assoc, Scheme.Hom.comp_apply]
    exact hU.2.2.1 _
  have hcomp₂ : M₂.pt ≫ q ≫ π = spMap (ratHull S₂.R).val.toRingHom ≫ (spMap rh ≫ u) ≫ C.i := by
    rw [← Category.assoc, hqgen, Category.assoc, hU.2.2.2, ← Category.assoc (spMap (ratHull S₂.R).val.toRingHom),
      ← Category.assoc (spMap (ratHull S₂.R).val.toRingHom), hrv]
    simp only [Category.assoc]
  have hMn' : GlobalTheory.IsNormalScheme M₂.Z := GlobalTheory.IsNormalScheme.of_pred hMn
  have hdiv : M₂.HasDiv S₂.th :=
    C.thetaInt o₂ Ω₂ S₂ ρ₂ (spMap rh ≫ u) hUO₂ hgen₂ M₂ (q ≫ π) hMn' hcomp₂
  have hbig : S₂.Big := big j (by omega) o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : GSet :=
    { o₁ := o₂, Ω₁ := Ω₂, S := S₂, ρ := ρ₂, big := hbig, M := M₂, normal := hMn', projM := hproj, div := hdiv }
  set d := X₁.ρ.n ^ (j₀ + 2 * k) with hd
  have hlev : S₂.r * S₂.N = X₁.S.r * X₁.S.N * d := by
    rw [hr₂, hN₂, hL₁, hd, hj, ← pow_mul, ← pow_add, ← pow_add, mul_comm k 2]
    ring_nf
  obtain ⟨lam, hlam, hlamr⟩ := GlobalTheory.T.exists_thetaRealisation_labels_of_grpPullback X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) d hcart hlev
  have hRS : ∀ x : Ω₂, x ∈ S₂.R ↔ x ∈ R := fun x => by rw [hSR]
  let sR : (Ω₂ ≃ₐ[X₁.Ω₁] Ω₂) → (S₂.R →+* S₂.R) := fun σ =>
    RingHom.codRestrict (((σ : Ω₂ ≃+* Ω₂) : Ω₂ →+* Ω₂).comp S₂.R.val.toRingHom) S₂.R
      (fun x => (hRS _).2 (hstab σ x ((hRS _).1 x.2)))
  have hsR : ∀ σ, (sR σ).comp om = om := fun σ => RingHom.ext fun a => Subtype.ext
    ((congrArg σ (hval a)).trans ((σ.commutes _).trans (hval a).symm))
  choose gl hgl using fun σ => GlobalTheory.T.exists_thetaRealisation_label_perm_of_ringEndo X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) hcart (sR σ) (hsR σ)
  have hgll : ∀ σ a, gl σ (lam a) = lam a := fun σ a => GlobalTheory.T.thetaRealisation_labels_injective_of_grpPullback S₂ ρ₂ X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) hcart _ _ (by
      rw [hgl, hlam, ← Category.assoc, spMap_comp_ring, hsR])
  let 𝔗 : Tower X₁ act :=
    { X₂ := X₂
      act₂ := act₂
      isAct := hmon
      alg := inferInstance
      fd := fd
      gal := gal
      d := d
      lev := hlev
      om := om
      om_eq := hval
      om_fin := RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun x => ⟨⟨x.1, (hRS _).1 x.2⟩, rfl⟩) hfin
      sR := sR
      sR_eq := fun σ a => rfl
      p := q
      p_fin := hq
      p_pt := hqgen
      φ := φ₂ ≫ ψ
      cart := hcart
      lb := hlbc
      act_eq := hact₂
      lam := lam
      lam_pt := hlam
      lam_range := hlamr
      gl := gl
      gl_pt := hgl
      gl_lam := hgll }
  refine ⟨𝔗, ?_⟩
  show N₀ ≤ S₂.r * S₂.N
  rw [hN₂, hr₂]
  exact hBk.trans (Nat.le_mul_of_pos_left _ (by have := hℓp.pos; positivity))

end GlobalTheory.GSep.UTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemUniversalUnitaryDeepTowersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_universalUnitary_deep_towers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → GlobalTheory.GSep.Deep X₁ act := by
  first | exact @GlobalTheory.GSep.UTower.deep_of_uLink | exact GlobalTheory.GSep.UTower.deep_of_uLink | (intros; apply GlobalTheory.GSep.UTower.deep_of_uLink <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.GSep.UAssembly

theorem posW_one : PosW (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) := by
  unfold PosW
  have : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) = Matrix.diagonal fun _ => 2 := by
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.vecHead, Function.swap]
  rw [this, Matrix.posDef_diagonal_iff]
  intro _; norm_num

theorem projective_of_free (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Projective (𝓞 E) X := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Flat (𝓞 E) X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨c, hc⟩
    by_contra hx
    have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (c : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hc0)
    have h0 : r • x = 0 := by
      rw [← algebraMap_smul (𝓞 E) r x, hα, mul_comm, mul_smul]
      rw [← Submonoid.smul_def, hc, smul_zero]
    exact hx ((smul_eq_zero.1 h0).resolve_left hr)
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem jK_spMap {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁)
    (fK : FractionRing V →+* FractionRing V₁) (h : ∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) :
    jK V₁ ≫ spMap ρ = spMap fK ≫ jK V := by
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext a
  simp [h]

theorem isUnit_natCast_of_spec {A : Type} [CommRing A] [Nontrivial A] {K : Type} [Field K] [CharZero K] (g : Sp A ⟶ Sp K)
    (m : ℕ) (hm : m ≠ 0) : IsUnit (m : A) := by
  have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hm : (m : K) ≠ 0)).map (Spec.preimage g).hom
  simpa using this

end GlobalTheory.GSep.UAssembly

namespace GlobalTheory.GSep.UAssembly
open GlobalTheory.GSep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem nonempty_gMem_trait (hpq : 1 ≤ Dw.p + Dw.q) (C : UCompact Xo c) (X₁ : GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (hlink : ULink C X₁ act u π) (z₁ : X₁.M.Z)
    (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b))
    (hcov₃ : ζ ≫ pullback.fst _ _ = X₁.M.Z.fromSpecStalk z₁ ≫ π) (U : X₁.M.Z.Opens)
    (hU : ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z) (T : UTrait Xo c) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V']
    (f : T.V →+* V') (t : V') (hcn : IsCN V') (hinj : Function.Injective f) (hf : IsLocalHom f) (ht : t ^ 2 = f T.ϖ)
    (e : X₁.M.Z.presheaf.stalk z₁ →+* T.V) (he : IsLocalHom e) (hc : jK T.V ≫ spMap e ≫ ζ = T.y ≫ C.iF)
    (hrg : Set.range (jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁) ⊆ (U : Set X₁.M.Z)) :
    Nonempty (GMem X₁ z₁ act V' (f.comp e) (Fin 1 → T.P.D.toPre.X) (mono !![(1 : ℤ)] ![t] ![T.be])
      (fun a mu => a • mu)) := by
  have hcnT : IsCN T.V := by
    haveI := T.cdvr.1
    exact ⟨inferInstance, inferInstance, T.cdvr.2.1, T.cdvr.2.2⟩
  let fK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (S := FractionRing T.V) (FractionRing V') f
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hinj)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hjk := jK_spMap f fK hfK
  have key : jK V' ≫ spMap (f.comp e) ≫ X₁.M.Z.fromSpecStalk z₁ =
      spMap fK ≫ (jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁) := by
    rw [show spMap (f.comp e) = spMap f ≫ spMap e from Spec.map_comp _ _]
    simp only [← Category.assoc]
    rw [hjk]
  have hloc : IsLocalHom (f.comp e) := RingHom.isLocalHom_comp f e
  have hreg : RegAt X₁ z₁ (f.comp e) := by
    intro a ha
    rw [key]
    exact hU _ (hrg ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩) ha
  have hcmp : jK V' ≫ spMap (f.comp e) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ T.y ≫ C.i := by
    calc _ = (jK V' ≫ spMap (f.comp e) ≫ X₁.M.Z.fromSpecStalk z₁) ≫ π := by simp only [Category.assoc]
      _ = spMap fK ≫ (jK T.V ≫ spMap e ≫ ζ) ≫ pullback.fst _ _ := by
        rw [key]; simp only [Category.assoc, hcov₃]
      _ = _ := by rw [hc]; simp only [Category.assoc]
  have hr : ∀ k : Fin 1, ![t] k ^ 2 = f (![T.ϖ] k) := fun k => by
    rw [Subsingleton.elim k 0]; exact ht
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.thetaMember_of_unitary_monomial_uniformisation E H Dw hpq l Xo c C X₁ act u π hlink z₁ T.V hcnT T.t T.y T.P T.gen 1 ![T.ϖ] ![T.be]
    T.mono V' f fK ![t] hcn hinj hf hfK hr (f.comp e) hloc hreg hcmp
  exact ⟨𝔪⟩

end GlobalTheory.GSep.UAssembly


open GlobalTheory.GSep.UAssembly in
theorem GlobalTheory.GSep.exists_vPre_traitsOn_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (U : X₁.M.Z.Opens) (Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (c₀ : Φ.Q), j₀ ≤ j ∧ IsCov C π z₁ ζ ∧ (U : Set X₁.M.Z).Nonempty ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ U ∧ GlobalTheory.GSep.IsMemberP ζ Φ ((n ^ j) ^ 2) Cm ξ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((n ^ j) ^ 2) ∧ Φ.ClassSums ((n ^ j) ^ 2) := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hB ξ hξ n hn hodd j₀
  obtain ⟨j, X₁, act, u, π, z₁, ζ, V₁, _, _, _, ρ₁, ev₁, r, hj, hN, hlink, hcov, hcn₁, hinj, hfin, hloc, hreg, hcomp, hr⟩ :=
    GlobalTheory.T.exists_linked_thetaSystem_regular_monomialFamily E H Dw hpq l Xo c C φ V Cm hB ξ hξ n hn hodd j₀
  obtain ⟨U, hUne, hU⟩ := GlobalTheory.T.exists_nonempty_open_thetaRing_regular X₁
  have hdom := (GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁).1
  have hact : GlobalTheory.GSep.IsAct X₁ act := hlink.1
  have hdeep := GlobalTheory.T.thetaSystem_universalUnitary_deep_towers E H Dw hpq l Xo c C X₁ act u π hlink
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have hunit : ∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁) := fun m hm =>
    isUnit_natCast_of_spec (ζ ≫ pullback.snd C.z (spMap C.b)) m hm
  have hρ : IsLocalHom ρ₁ := by
    letI := ρ₁.toAlgebra
    haveI : Module.Finite V V₁ := hfin
    haveI : FaithfulSMul V V₁ := (faithfulSMul_iff_algebraMap_injective V V₁).2 hinj
    exact (inferInstance : IsLocalHom (algebraMap V V₁))
  have hcnV : IsCN V := ⟨hB.1.1, hB.1.2.2.1, hB.1.2.2.2, hB.2⟩
  let fK₁ : FractionRing V →+* FractionRing V₁ := IsLocalization.map (S := FractionRing V) (FractionRing V₁) ρ₁
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ₁ hinj)
  have hfK₁ : ∀ a, fK₁ (algebraMap V _ a) = algebraMap V₁ _ (ρ₁ a) := fun a => IsLocalization.map_eq _ a
  have key₀ := jK_spMap ρ₁ fK₁ hfK₁
  have hcov₃ : ζ ≫ pullback.fst _ _ = X₁.M.Z.fromSpecStalk z₁ ≫ π := hcov.2.2.1
  obtain ⟨𝔪₀, p₀, hp₀⟩ := GlobalTheory.T.thetaMember_of_unitary_monomial_uniformisation E H Dw hpq l Xo c C X₁ act u π hlink z₁ V hcnV Cm.t Cm.y Cm.P Cm.gen Cm.m Cm.s
    (fun i => (l.M' : ℤ) • Cm.δ i) Cm.mono V₁ ρ₁ fK₁ r hcn₁ hinj hρ hfK₁ hr ev₁ hloc hreg (by
      calc _ = (jK V₁ ≫ (spMap ev₁ ≫ ζ)) ≫ pullback.fst _ _ := by simp only [Category.assoc, hcov₃]
        _ = (jK V₁ ≫ spMap ρ₁) ≫ ξ ≫ pullback.fst _ _ := by rw [hcomp]; simp only [Category.assoc]
        _ = spMap fK₁ ≫ (jK V ≫ ξ) ≫ pullback.fst _ _ := by rw [key₀]; simp only [Category.assoc]
        _ = _ := by rw [← hξ]; simp only [Category.assoc])

  have hcnT : ∀ T : UTrait Xo c, IsCN T.V := fun T => by
    haveI := T.cdvr.1
    exact ⟨inferInstance, inferInstance, T.cdvr.2.1, T.cdvr.2.2⟩
  have hsq := fun T : UTrait Xo c => GlobalTheory.T.exists_finite_ext_sqrt_uniformiser_complete_dvr T.V (hcnT T) (by haveI := T.cdvr.1; infer_instance) T.ϖ T.irr
  choose VT iRT iDT iLT fT tT hcnW hpirW hinjW hlocW hfinW htW using hsq
  let Tr : Type 1 := Σ T : UTrait Xo c, {e : X₁.M.Z.presheaf.stalk z₁ →+* T.V // IsLocalHom e ∧
    jK T.V ≫ spMap e ≫ ζ = T.y ≫ C.iF ∧ Set.range (jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁) ⊆ (U : Set X₁.M.Z)}
  have hmT : ∀ T : Tr, Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act (VT T.1) ((fT T.1).comp T.2.1) (Fin 1 → T.1.P.D.toPre.X)
      (mono !![(1 : ℤ)] ![tT T.1] ![T.1.be]) (fun a mu => a • mu)) := by
    rintro ⟨T, e, he, hc, hrg⟩
    exact nonempty_gMem_trait hpq C X₁ act u π hlink z₁ ζ hcov₃ U hU T (VT T) (fT T) (tT T) (hcnW T) (hinjW T)
      (hlocW T) (htW T) e he hc hrg

  let VV : Option Tr → Type := fun y => match y with | none => V₁ | some T => VT T.1
  letI iR : ∀ y, CommRing (VV y) := fun y => match y with
    | none => inferInstanceAs (CommRing V₁) | some T => iRT T.1
  haveI iD : ∀ y, IsDomain (VV y) := fun y => match y with
    | none => inferInstanceAs (IsDomain V₁) | some T => iDT T.1
  haveI iL : ∀ y, IsLocalRing (VV y) := fun y => match y with
    | none => inferInstanceAs (IsLocalRing V₁) | some T => iLT T.1
  let EV : ∀ y, X₁.M.Z.presheaf.stalk z₁ →+* VV y := fun y => match y with
    | none => ev₁ | some T => (fT T.1).comp T.2.1
  let XX : Option Tr → Type := fun y => match y with | none => Cm.P.D.toPre.X | some T => T.1.P.D.toPre.X
  letI iA : ∀ y, AddCommGroup (XX y) := fun y => match y with
    | none => inferInstanceAs (AddCommGroup Cm.P.D.toPre.X) | some T => inferInstanceAs (AddCommGroup T.1.P.D.toPre.X)
  letI iM : ∀ y, Module (𝓞 E) (XX y) := fun y => match y with
    | none => inferInstanceAs (Module (𝓞 E) Cm.P.D.toPre.X) | some T => inferInstanceAs (Module (𝓞 E) T.1.P.D.toPre.X)
  haveI iFZ : ∀ y, Module.Free ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Free ℤ Cm.P.D.toPre.X) | some T => inferInstanceAs (Module.Free ℤ T.1.P.D.toPre.X)
  haveI iGZ : ∀ y, Module.Finite ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Finite ℤ Cm.P.D.toPre.X) | some T => inferInstanceAs (Module.Finite ℤ T.1.P.D.toPre.X)
  haveI iFO : ∀ y, Module.Finite (𝓞 E) (XX y) := fun y => Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI iPO : ∀ y, Module.Projective (𝓞 E) (XX y) := fun y => projective_of_free E (XX y)
  let MM : Option Tr → ℕ := fun y => match y with | none => Cm.m | some _ => 1
  let tt : ∀ y, Fin (MM y) → VV y := fun y => match y with | none => r | some T => ![tT T.1]
  let dd : ∀ y, Fin (MM y) → LinearMap.BilinForm ℤ (XX y) := fun y => match y with
    | none => fun k => (l.M' : ℤ) • Cm.δ k | some T => ![T.1.be]
  let 𝔪 : ∀ y, GlobalTheory.GSep.GMem X₁ z₁ act (VV y) (EV y) (Fin 1 → XX y) (mono !![(1 : ℤ)] (tt y) (dd y))
      (fun a mu => a • mu) := fun y => match y with
    | none => 𝔪₀
    | some T => (hmT T).some
  have hlab : Set.range (Subtype.val : X₁.S.HH X₁.M z₁ → X₁.S.Gam) = X₁.S.HH X₁.M z₁ := Subtype.range_val
  choose uu hu₁ hu₂ hu₃ using fun y => GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift (𝓞 E) X₁ z₁ act x₀ hx₀ (VV y) (EV y) (Fin 1 → XX y) _ _ (𝔪 y)
    (X₁.S.HH X₁.M z₁) Subtype.val hlab
  have ht₀ : ∀ k, r k ∈ maximalIdeal V₁ ∧ r k ≠ 0 := fun k => by
    refine ⟨(mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_), fun h0 => ?_⟩
    · have h1 : IsUnit (ρ₁ (Cm.s k)) := (hr k) ▸ hu.pow 2
      exact (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 (Cm.s_mem k))) ((isUnit_map_iff ρ₁ _).1 h1)
    · apply Cm.s_ne_zero k
      apply hinj
      rw [map_zero, ← hr k, h0]
      ring
  have htT : ∀ T : UTrait Xo c, tT T ∈ maximalIdeal (VT T) ∧ tT T ≠ 0 := fun T => by
    haveI := hlocW T
    refine ⟨(mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_), fun h0 => ?_⟩
    · have h1 : IsUnit (fT T T.ϖ) := (htW T) ▸ hu.pow 2
      exact T.irr.not_isUnit ((isUnit_map_iff (fT T) _).1 h1)
    · apply T.irr.ne_zero
      apply hinjW T
      rw [map_zero, ← htW T, h0]
      ring
  let Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] (X₁.M.Z.presheaf.stalk z₁) :=
    { posW := posW_one
      Y := Option Tr
      V := VV
      cn := fun y => (𝔪 y).cn
      ev := EV
      ev_loc := fun y => (𝔪 y).loc
      X := XX
      rank_le := fun y => match y with
        | none => Cm.rank
        | some T => UTrait.finrank_le_min E H Dw l Xo c T.1
      m := MM
      t := tt
      t_mem := fun y => match y with
        | none => ht₀
        | some T => fun k => by rw [Subsingleton.elim k 0]; exact htT T.1
      δ := dd
      bal := fun y => match y with
        | none => fun k => Submodule.smul_mem _ _ (Cm.cone.mem k)
        | some T => fun k => by
            rw [Subsingleton.elim k 0]
            exact ⟨T.1.lev.1, T.1.lev.2.1⟩
      nonneg := fun y => match y with
        | none => fun k x => Cm.mono.nonneg k x
        | some T => fun k x => T.1.mono.nonneg k x
      pos := fun y => match y with
        | none => fun x hx => Cm.mono.exists_pos (maximalIdeal.isMaximal V).ne_top (Dd := Cm.P.D) hx
        | some T => fun x hx => T.1.mono.exists_pos (maximalIdeal.isMaximal T.1.V).ne_top (Dd := T.1.P.D) hx
      Q := X₁.S.HH X₁.M z₁
      u := uu
      u_unit := hu₂ }
  have hgeo : GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ Subtype.val := ⟨hx₀, hlab, fun y => ⟨𝔪 y, hu₁ y⟩⟩
  refine ⟨j, X₁, π, z₁, ζ, hdom, U, Φ, none, ρ₁, LinearEquiv.refl _ _, Equiv.refl _,
    ⟨x₀, AddSubgroup.subset_closure hx₀⟩, hj, hcov, hUne, ?_, ?_, fun y => hu₃ y _ rfl, ?_, ?_, ?_⟩
  · intro T e h₁ h₂ h₃
    refine ⟨some ⟨T, e, h₁, h₂, h₃⟩, fT T, LinearEquiv.refl _ _, rfl, hpirW T, hinjW T, hlocW T, rfl, fun k => ?_⟩
    rw [Subsingleton.elim k 0]
    exact ⟨htW T, fun _ _ => rfl⟩
  · refine ⟨hinj, hfin, hcomp, fun k => ⟨hr k, fun _ _ => rfl⟩, 𝔪₀.D.toPre, p₀, ?_⟩
    have hth := GlobalTheory.T.thetaMember_terms_isThetaTerms_torsionFrames (𝓞 E) X₁ z₁ act x₀ hx₀ V₁ ev₁ (Fin 1 → Cm.P.D.toPre.X) _ _ 𝔪₀ _ Subtype.val hlab _ (hu₁ none)
    rw [← hN]
    obtain ⟨th, g, b, w, h1, h2, h3, h4, h5⟩ := hth
    refine ⟨th, g, b, w, h1, h2, h3, h4, fun mu c => ?_⟩
    have e1 : p₀.xe.symm mu = 𝔪₀.e₈ (fun _ => mu) := p₀.xe.symm_apply_eq.2 (hp₀ (fun _ => mu)).symm
    rw [e1]
    exact h5 (fun _ => mu) c
  · rintro (_ | T) h
    · rfl
    · exact absurd rfl h
  · rw [← hN]
    exact GlobalTheory.T.fourierTermSystem_exact_of_geometric_uniformisation (𝓞 E) _ _ _ _ X₁ z₁ act x₀ Φ _ hgeo
  · rw [← hN]
    exact GlobalTheory.T.fourierTermSystem_class_sums_unbounded_levels_one_index (𝓞 E) _ _ _ X₁ z₁ act hact hdeep hunit x₀ Φ _ hgeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_fourier_system_traits_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (U : X₁.M.Z.Opens) (Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (c₀ : Φ.Q), j₀ ≤ j ∧ IsCov C π z₁ ζ ∧ (U : Set X₁.M.Z).Nonempty ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ U ∧ GlobalTheory.GSep.IsMemberP ζ Φ ((n ^ j) ^ 2) Cm ξ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((n ^ j) ^ 2) ∧ Φ.ClassSums ((n ^ j) ^ 2) := by
  first | exact @GlobalTheory.GSep.exists_vPre_traitsOn_chart | exact GlobalTheory.GSep.exists_vPre_traitsOn_chart | (intros; apply GlobalTheory.GSep.exists_vPre_traitsOn_chart <;> assumption)
end

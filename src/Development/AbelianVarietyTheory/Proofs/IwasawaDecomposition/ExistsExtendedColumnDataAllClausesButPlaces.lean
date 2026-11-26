module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataEnlargedBaseTupleFree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBase
public import Development.AutomorphicArithmetic.SemilinearForms.GeoExtFW
public import Development.AutomorphicArithmetic.SemilinearForms.GeoExtTies

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.SemilinearForms.GeoExtOm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsEnl
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBcStages
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem levOver_cast' {D : D7} {G : Type} [Group G] {i : Fin D.R.m} {Pg₁ Pg₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    {β₁ β₂ : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} {e₁ : G ≃* G0 Pg₁ D.R.r} {e₂ : G ≃* G0 Pg₂ D.R.r}
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Dw : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    {ι : ∀ j : ℕ, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} (hP : HEq Pg₂ Pg₁) (hβ : HEq β₂ β₁) (he : HEq e₂ e₁)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La} (h : LevOver D i Pg₁ β₁ e₁ l Dw ι lev) :
    LevOver D i Pg₂ β₂ e₂ l Dw ι lev := by
  cases hP; cases hβ; cases he
  exact h


set_option maxHeartbeats 4000000 in
theorem exists_bc_stages (X X' : Stages) (hP : X'.B.toPre = X.B.toPre) (hLL : Set.range X.B.embLL ⊆ Set.range X'.B.embLL)
    {G : Type} [Group G] [Fintype G] {Pl0 T0 Pl0' T0' : Type} {A : FamIn X.toD7.what₂.LL G Pl0 T0 X.toD7.R.m}
    {A' : FamIn X'.toD7.what₂.LL G Pl0' T0' X'.toD7.R.m} (T : CoreJ X.toD7) [Algebra T.Q.c.F X.toD7.what₂.LL]
    (T' : CoreJ X'.toD7) [alg' : Algebra T'.Q.c.F X'.toD7.what₂.LL] (R : RealDat X.toD7 A T.Q.c.F) (R' : RealDat X'.toD7 A' T'.Q.c.F)
    (eH : HEq T'.Q.H T.Q.H) (el : HEq T'.Q.l T.Q.l) (ec : HEq T'.Q.c T.Q.c) (eD : HEq T'.Q.Dw T.Q.Dw) (eX : HEq T'.Q.Xo T.Q.Xo)
    (ex : HEq T'.x₀ T.x₀) (eι : HEq T'.iota T.iota) (ePg : HEq R'.Pg R.Pg) (eβV : HEq R'.βV R.βV) (eβW : HEq R'.βW R.βW)
    (eG : HEq R'.eG R.eG) (emu : HEq R'.C.mu0 R.C.mu0) (eeta : HEq R'.C.eta R.C.eta)
    {κ : ∀ i : Fin X.toD7.R.m, WeightFamilies.Wt X.toD7 ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin X.toD7.R.m) (σ : X.toD7.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {κ' : ∀ i : Fin X'.toD7.R.m, WeightFamilies.Wt X'.toD7 ((i : ℕ) + 1)}
    {v₀' : ∀ (i : Fin X'.toD7.R.m) (σ : X'.toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec}
    (hL : R.toLevCh.Is A.μ0) (hV : R.models_HV) (hκ : KapIs κ) (hL' : R'.toLevCh.Is A'.μ0) (hM' : R'.IsModels) (hF' : R'.fam_tie)
    (ht' : TieIn T' R' κ' v₀') (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (eW : HEq (R'.cV i').W (R.cV i).W) (en : HEq (R'.cV i').nW (R.cV i).nW) (ei : HEq (R'.cV i').iW (R.cV i).iW)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (hOF : O.c'.F = X.toD7.what₂.embLL.toRatAlgHom.fieldRange)
    (hO : O.Pins (κ i) (v₀ i (sg0 X.toD7 A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (P : Prop)
    (hc : ∀ c0L, CoefFam R c0L → P ∨ ∃ c0L', CoefFam R' c0L' ∧
      ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) :
    ∃ O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0), O'.c'.F = X'.toD7.what₂.embLL.toRatAlgHom.fieldRange ∧
      O'.Pins (κ' i') (v₀' i' (sg0 X'.toD7 A')) (iotaW T' i') (T'.x₀ ((i' : ℕ) + 1) O'.s0) ∧
      IsBCOf O' (v₀' i' (sg0 X'.toD7 A')) O (v₀ i (sg0 X.toD7 A)) (κ i) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) P := by
  obtain ⟨c₃, hF₃, h₃⟩ := GlobalTheory.RefPins.exists_coeff_rows T' ht'.alg ht'.laws.pins.2.2.1
  have hmem : ∀ y, X'.toD7.what₂.embLL y ∈ c₃.F := fun y => hF₃.ge ⟨y, rfl⟩
  let jL' : X'.toD7.what₂.LL →+* c₃.F := X'.toD7.what₂.embLL.codRestrict c₃.F hmem
  have hjL' : (inC c₃).comp jL' = X'.toD7.what₂.embLL := RingHom.ext fun _ => rfl
  have sj' : Function.Surjective jL' := fun y => by
    obtain ⟨x, hx⟩ := hF₃.le y.2
    exact ⟨x, Subtype.ext hx⟩
  have sj : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ := hOF.le y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hO.lift.field x).trans hx)⟩
  have hs : O.c'.F ≤ c₃.F := fun y hy => by
    obtain ⟨x, hx⟩ := hOF.le hy
    obtain ⟨x', hx'⟩ := hLL ⟨x, hx⟩
    exact hF₃.ge ⟨x', hx'⟩
  have hQ := GlobalTheory.RefPins.places_ref R hL
  have hQ' := GlobalTheory.RefPins.places_ref R' hL'
  have hV₃ : T'.V ((i' : ℕ) + 1) (sOv T'.toCore c₃ h₃) = Wc X'.toD7 i' := ht'.laws.spaceW _ (inR i') _ rfl
  obtain ⟨g, r, c0L, hT, hbc⟩ := hO.lift.c0
  have hx1 := hL.xi A.μ0
  have hx1' := hL'.xi A'.μ0
  rw [hL.xi_base] at hx1
  rw [hL'.xi_base] at hx1'
  have hplace : ∀ (c0L') (c0'' : VsV X'.toD7 i' c₃.F →ₛₗ[inC c₃] (R'.cV i').W), CoefFam R' c0L' →
      CoefficientBaseChange R' i' jL' (inC c₃) (c0L' i') c0'' → ∀ (Cl : Type) [Fintype Cl] (h : Cl → GA X'.toD7 (Vc X'.toD7 i')),
      PlaceEx R' i' A'.μ0 h c0'' := by
    rintro c0L' c0'' ⟨_, _, htie⟩ hc0 Cl _ h
    exact GlobalTheory.RationalValues.placeEx_of_type_mem R' i' jL' (inC c₃) A'.μ0 h c0'' hM'.jV htie hc0
      (GlobalTheory.RationalValues.type_mem R' i' A'.μ0 _
        (fun PP hPP x => by
          obtain ⟨y, hy⟩ := GlobalTheory.RefPins.chiVal_of_tie T' R' κ' v₀' hL' ht' i' PP hPP x
          exact ⟨jL' y, hy⟩)
        fun PP hPP => absurd (hQ' ▸ hPP) (Finset.notMem_empty _))
  have hv0' := ht'.hv₀ i' (sg0 X'.toD7 A')
  have hκ' := ht'.kap i'
  clear ht'
  have hc' : ∃ c0L', CoefFam R' c0L' ∧ (P ∨ ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) := by
    rcases hc c0L ⟨g, r, hT⟩ with h | ⟨c, h1, h2⟩
    · obtain ⟨g', r', c, h1⟩ := hF'
      exact ⟨c, ⟨g', r', h1⟩, Or.inl h⟩
    · exact ⟨c, h1, Or.inr h2⟩
  clear hc
  obtain ⟨c0L', hT', hag⟩ := hc'
  obtain ⟨c0'', hbc'⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R'.cV i').W) jL' (inC c₃) hjL' (lamV X'.toD7 i') (c0L' i')
  have hpl' := hplace c0L' c0'' hT' hbc'
  clear hplace
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  rcases B' with ⟨P'⟩
  change P' = X.B.toPre at hP
  subst hP
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at eH el ec eD eX ex eι
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq eD
  obtain rfl := eq_of_heq eX
  obtain rfl := eq_of_heq ex
  obtain rfl := eq_of_heq eι
  obtain rfl : i = i' := Fin.ext hi
  have h0 : ∃ c0₃ : VsV X.toD7 i c₃.F →ₛₗ[inC c₃] (R.cV i).W, (∀ (v : VsV X.toD7 i O.c'.F) (v' : VsV X.toD7 i c₃.F),
      (v' : Pol c₃.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) =
        MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) → c0₃ v' = O.c0' v) ∧
      (HEq c0'' c0₃ ∨ P) := by
    rcases hag with hp | hag
    · obtain ⟨c0₃, h⟩ := exists_coef_ext (incF O.c' c₃ hs) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV X.toD7 i) O.c0'
      exact ⟨c0₃, h, Or.inr hp⟩
    · obtain ⟨c0₃, h1, h2⟩ := exists_cast_map (V := VsV X.toD7 i c₃.F) (σ := inC c₃) (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW
        eW en ei ((by with_unfolding_all exact (c0'' :)))
      refine ⟨c0₃, fun v v' e => eq_of_heq ((h2 v').symm.trans ?_), Or.inl ((by with_unfolding_all exact (h1 :)))⟩
      exact coef_agree (W' := (R'.cV i).W) (lamV X.toD7 i) O.jL jL' (incF O.c' c₃ hs) hO.lift.field hjL' (RingHom.ext fun _ => rfl) sj sj'
        (cL' := (by with_unfolding_all exact ((c0L' i) :))) hbc ((by with_unfolding_all exact (hbc' :))) ((by with_unfolding_all exact (hag :))) v v' e
  obtain ⟨c0₃, hc0, hor⟩ := h0
  obtain ⟨io₃, hw₃, h, J', hB⟩ := exists_isBC O c₃ hs c0₃ (v₀ i (sg0 X.toD7 A)) hV hO hc0
  have hM := hB.pins
  have eχ : R'.C.mu0 i * R'.xiH A'.μ0 * R'.C.eta⁻¹ = R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹ := (by with_unfolding_all exact ((congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b⁻¹)
      (congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b) (congrFun (eq_of_heq emu) i) (hL'.xi_base.trans hL.xi_base.symm))
      (eq_of_heq eeta)) :))
  have eξ : R'.xi A'.μ0 = R.xi A.μ0 := (GlobalTheory.ChrEqUnique.chrEq_unique X.toD7).2.1 _ _ _ ((by with_unfolding_all exact (hx1' :))) hx1
  have hT1 := (tupOver_iff R A.μ0).2 ⟨repsR_map (incF O.c' c₃ hs) hB.reps, (hM.tuple ()).B, (hM.tuple ()).xi, (hM.tuple ()).phi,
    (hM.tuple ()).half⟩
  have hT2 := tupOver_cast (D := X.toD7) (Pg₂ := R'.Pg) (Q₂ := R'.Q A'.μ0) (βV₂ := (by with_unfolding_all exact (R'.βV :))) (βW₂ := (by with_unfolding_all exact (R'.βW :)))
    (ξR₂ := (by with_unfolding_all exact ((R'.xiR A'.μ0) :))) ePg hQ hQ' ((by with_unfolding_all exact (eβV :))) ((by with_unfolding_all exact (eβW :))) eχ eξ hT1
  have hl2 := levOver_cast' (D := X.toD7) (Pg₂ := R'.Pg) (β₂ := (by with_unfolding_all exact (R'.βW :))) (e₂ := (by with_unfolding_all exact (R'.eG :))) ePg ((by with_unfolding_all exact (eβW :))) ((by with_unfolding_all exact (eG :)))
    ((levOver_iff T R i O.lev).2 hO.lift.lev)
  let κ₀ : WeightFamilies.Wt X.toD7 ((i : ℕ) + 1) := ⟨(by with_unfolding_all exact ((κ' i).aP :)), (by with_unfolding_all exact ((κ' i).aM :)), (by with_unfolding_all exact ((κ' i).aPlus_antitone :)), (by with_unfolding_all exact ((κ' i).aM_anti :)), (κ' i).n, (κ' i).n_even⟩
  have ew : wtA κ₀ = wtA (κ i) := wtA_eq _ _
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).1 k) :))) ((hκ i τ).1 k).symm)
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).2.1 k) :))) ((hκ i τ).2.1 k).symm)
  have hio := hM.io
  rw [← ew] at hio
  let M := bc O c₃ hs c0₃ io₃ hw₃ h (v₀ i (sg0 X.toD7 A))
  refine ⟨@OMDat.mk _ G _ _ Pl0' T0' A' _ alg' R' i Unit _ (c' := c₃) (hle := h₃) (jL := jL') (hV := hV₃) (c0' := c0'') (lev := (by with_unfolding_all exact (M.lev :)))
    (dδ := (by with_unfolding_all exact (M.dδ :))) (Cl' := M.Cl') (fCl := M.fCl) (bad := M.bad) (Lh := (by with_unfolding_all exact (M.Lh :))) (La := (by with_unfolding_all exact (M.La :))) (Nc := (by with_unfolding_all exact (M.Nc :))) (gam := (by with_unfolding_all exact (M.gam :)))
    (vol := (by with_unfolding_all exact (M.vol :))) (ep := (by with_unfolding_all exact (M.ep :))) (B := (by with_unfolding_all exact (M.B :))) (epF := (by with_unfolding_all exact (M.epF :))) (io := (by with_unfolding_all exact (M.io :))) (hw := (by with_unfolding_all exact (M.hw :))) (φ := (by with_unfolding_all exact (M.φ :)))
    (w := (by with_unfolding_all exact (M.w :))) (U₂ := (by with_unfolding_all exact (M.U₂ :))) (dict₂ := (by with_unfolding_all exact (M.dict₂ :))) (xi := (by with_unfolding_all exact (M.xi :)))
    (thAd := fun _ => thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (v₀' i (sg0 _ A')))
    (Plc := fun _ x => ∃ x₀, Place R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (jVx R' i A'.μ0 x₀) x), hF₃, ?_, ?_⟩
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    obtain ⟨g', r', hT'⟩ := hT'
    apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
    case lift =>
      apply (config := { synthAssignedInstances := false }) ThPinsR.mk
      case field => exact hjL'
      case std => exact (by with_unfolding_all exact (hO.lift.std :))
      case v0 => exact hv0'
      case lev => exact (by with_unfolding_all exact (hl2 :))
      case c0 => exact ⟨g', r', c0L', hT', hbc'⟩
    case tuple =>
      intro t
      apply (config := { synthAssignedInstances := false }) ThPinsT.mk
      case reps => exact ⟨(by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact (hT2.1 :)), (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
      case B => exact (by with_unfolding_all exact (hT2.2.1 :))
      case xi => exact (by with_unfolding_all exact (hT2.2.2.1 :))
      case phi => exact (by with_unfolding_all exact (hT2.2.2.2.1 :))
      case half => exact (by with_unfolding_all exact (hT2.2.2.2.2 :))
    case act => exact (by with_unfolding_all exact (hM.act :))
    case bad => exact (by with_unfolding_all exact (hM.bad :))
    case reps => exact (by with_unfolding_all exact (hM.reps :))
    case ep => exact (by with_unfolding_all exact (hM.ep :))
    case io => exact (by with_unfolding_all exact (hio :))
    case w => exact (by with_unfolding_all exact (hM.w :))
    case cov => exact (by with_unfolding_all exact (hM.cov :))
    case cxi => exact (by with_unfolding_all exact (hM.cxi :))
    case model₂ => exact (by with_unfolding_all exact (hM.model₂ :))
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    refine ⟨c₃, hs, c0₃, io₃, hw₃, h, J', hB, ?_, hor, (by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact ((HEq.refl h) :)), (by with_unfolding_all exact ((HEq.refl J') :)), (by with_unfolding_all exact (hT2.1 :)),
      (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
    exact ⟨(by with_unfolding_all exact ((HEq.refl M.c') :)), (by with_unfolding_all exact ((HEq.refl M.lev) :)), (by with_unfolding_all exact ((HEq.refl M.dδ) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.fCl) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.Lh) :)),
      (by with_unfolding_all exact ((HEq.refl M.La) :)), (by with_unfolding_all exact ((HEq.refl M.Nc) :)), (by with_unfolding_all exact ((HEq.refl M.gam) :)), (by with_unfolding_all exact ((HEq.refl M.vol) :)), (by with_unfolding_all exact ((HEq.refl M.ep) :)), (by with_unfolding_all exact ((HEq.refl M.B) :)),
      (by with_unfolding_all exact ((HEq.refl M.epF) :)), (by with_unfolding_all exact ((HEq.refl M.io) :)), (by with_unfolding_all exact ((HEq.refl M.hw) :)), (by with_unfolding_all exact ((HEq.refl M.φ) :)), (by with_unfolding_all exact ((HEq.refl M.w) :)), (by with_unfolding_all exact ((HEq.refl M.U₂) :)),
      (by with_unfolding_all exact ((HEq.refl M.dict₂) :)), (by with_unfolding_all exact ((HEq.refl M.xi) :))⟩

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt


set_option maxHeartbeats 4000000 in
theorem exists_omPins_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
    ∀ (core' : CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
      HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c → HEq core'.Q.Dw z.core.Q.Dw →
      HEq core'.Q.Xo z.core.Q.Xo → HEq core'.x₀ z.core.x₀ → HEq core'.iota z.core.iota →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
      (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
      Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
      (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
      TieIn core' R'.toRealDat κ' v₀' →
      ∃ O' : ∀ i', OMDat core'.toCore R'.toRealDat i' Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0),
        (∀ i', OMPins core' R'.toRealDat κ' v₀' O' i') ∧
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev ∧
          IsBCOf (O' i') (v₀' i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) (z.geo.O i)
            (z.geo.v₀ i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (z.geo.κ i) (iotaW z.core i)
            (z.core.x₀ ((i : ℕ) + 1) (z.geo.O i).s0)
            (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
              (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS core' alg' eH el ec eD eX ex eι Xg tr R' cG' hP hL hB hW κ' v₀' ht
  have hc := GlobalTheory.T.exists_coefficientMap_extension_over_enlarged_base z hE hf hp hS R' cG' hP hL hB hW
  have a1 : HEq R'.C.mu0 f'.mu0 ∧ HEq R'.C.eta f'.eta := by
    have e := hL.C
    rw [w'.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  have a2 : HEq z.R.C.mu0 f.mu0 ∧ HEq z.R.C.eta f.eta := by
    have e := z.lev.C
    rw [w.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  obtain ⟨-, -, eβW, -, -, -, eβV, -, -, ePg, eG, -, hcV, -⟩ := hW
  have hcV' := fun i i' hi => (⟨(hcV i i' hi).1, (hcV i i' hi).2.2.1, (hcV i i' hi).2.2.2.1⟩ : _ ∧ _ ∧ _)
  have h1 := hP.char.base.lev
  have h2 := hP.char.base.models
  have h3 := hP.char.base.fam.tie
  clear hcV hP hL hB hS
  obtain ⟨hPre, -, -, hLL⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  have key := fun i => exists_bc_stages (w.st Z) _ ((by with_unfolding_all exact ((Eq.refl B.toPre) :))) hLL z.core core' z.R.toRealDat R'.toRealDat eH el ec eD eX ex eι
    ePg eβV eβW eG (a1.1.trans a2.1.symm) (a1.2.trans a2.2.symm) z.pins.char.base.lev z.pins.char.base.models.HV z.geo.fw.kap h1 h2 h3 ht
    i i rfl (hcV' i i rfl).1 (hcV' i i rfl).2.1 (hcV' i i rfl).2.2 (z.geo.O i) (z.geo.pins i).1 (z.geo.pins i).2 _ (hc i i rfl)
  choose O' k1 k2 k3 using key
  refine ⟨(by with_unfolding_all exact (O' :)), fun i => (by with_unfolding_all exact ((And.intro (k1 i) (k2 i)) :)), fun i i' hi => ?_⟩
  obtain rfl : i = i' := Fin.ext hi
  exact (by with_unfolding_all exact ((And.intro (k3 i).lev (k3 i)) :))

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedDataCoefficientMapInjective
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem heq_val {Γ W W' : Type} (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W')
    (p' : InnerProductSpace ℂ W') (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (H : HMod (Γ → W)) (H' : HMod (Γ → W'))
    (hH : HEq H' H) (y : H.H) (y' : H'.H) (hy : HEq y' y) (g : Γ) : HEq (H'.e y' g) (H.e y g) ∧ HEq (0 : W') (0 : W) := by
  cases hW; cases hn; cases hp; cases hH; cases hy
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heq_app {K V W W' : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}
    (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W') (p' : InnerProductSpace ℂ W')
    (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (c' : V →ₛₗ[σ] W') (c : V →ₛₗ[σ] W) (h : HEq c' c) (v : V) :
    HEq (c' v) (c v) := by
  cases hW; cases hn; cases hp; cases h
  exact HEq.rfl

def RepsOver (D : D7) (i : Fin D.R.m) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (βV : ∀ i, GL (Fin (Vc D i).rank) (Lev.EAf D))
    {K' : Type} [Field K'] (bad : ℕ) {Cl : Type} (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K') : Prop :=
  bad ≠ 0 ∧ (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ (levEnv (Vc D i) (βV i) (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ∧
    J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ≠ 0 ∧
    vol = ((J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))

theorem repsOver_cast {D : D7} {i : Fin D.R.m} {Pg₁ Pg₂ Q₁ Q₂ : Finset (Formalism.L2.DIV.Pl D.host.E)} {β₁ β₂} {K' : Type} [Field K'] {bad : ℕ}
    {Cl : Type} {h : Cl → GA D (Vc D i)} {J' Lh gam} {vol : K'} (hP : HEq Pg₂ Pg₁) (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅) (hβ : HEq β₂ β₁)
    (H : RepsOver D i Pg₁ Q₁ β₁ bad h J' Lh gam vol) : RepsOver D i Pg₂ Q₂ β₂ bad h J' Lh gam vol := by
  cases hP; cases hβ; subst hQ₁ hQ₂
  exact H

theorem inj_of_li {L K I W : Type} [Field L] [CharZero L] [Field K] [Fintype I] [AddCommGroup W] [Module ℂ W] {n : ℕ} (lam : I → DomWeight n)
    {σL : L →+* ℂ} {σK : K →+* ℂ} (jL : L →+* K) (s : Function.Surjective jL)
    {cL : VV L lam →ₛₗ[σL] W} {cK : VV K lam →ₛₗ[σK] W}
    (hc : ∀ v : VV L lam, ∃ v' : VV K lam, (v' : Pol K I n) = MvPolynomial.map jL (v : Pol L I n) ∧ cK v' = cL v)
    (hli : LinearIndependent ℂ fun i => cL (bVV L lam i)) : Function.Injective cK := by
  have hL : ∀ u : VV L lam, cL u = 0 → u = 0 := fun u hu => by
    have e := (bVV L lam).sum_repr u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, map_sum] at hu
    simp only [LinearMap.map_smulₛₗ] at hu
    have := Fintype.linearIndependent_iff.1 hli _ hu
    exact (bVV L lam).repr.injective (Finsupp.ext fun i => by
      rw [map_zero]; exact σL.injective ((this i).trans (map_zero _).symm))
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  let q := (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).symm
  have h1 : jL.comp q.toRingHom = RingHom.id K := RingHom.ext fun x => (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).apply_symm_apply x
  obtain ⟨a, a1, a2⟩ := hc ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV q.toRingHom lam _ v.2⟩
  have e : a = v := Subtype.ext (a1.trans (by rw [MvPolynomial.map_map, h1, MvPolynomial.map_id]))
  subst e
  have h0 := hL _ (a2.symm.trans hv)
  rw [h0] at a1
  exact Subtype.ext (a1.trans (map_zero _))

theorem normalisedData_coefficientMap_injective {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
    (O : OMDat C R i Unit (fun _ => A.μ0)) {κ v₀ ι x₀} (hOF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hO : O.Pins κ v₀ ι x₀) : Function.Injective O.c0' := by
  have sj : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ := hOF.le y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hO.lift.field x).trans hx)⟩
  obtain ⟨g, r, c0L, hT, hbc⟩ := hO.lift.c0
  exact inj_of_li (lamV D i) O.jL sj hbc (hT.mapL i).2.1


set_option maxHeartbeats 4000000 in
theorem omOver_of_isBCOf (X X' : Stages) (hP : X'.B.toPre = X.B.toPre)
    {G : Type} [Group G] [Fintype G] {Pl0 T0 Pl0' T0' : Type} {A : FamIn X.toD7.what₂.LL G Pl0 T0 X.toD7.R.m}
    {A' : FamIn X'.toD7.what₂.LL G Pl0' T0' X'.toD7.R.m} (T : CoreJ X.toD7) [Algebra T.Q.c.F X.toD7.what₂.LL]
    (T' : CoreJ X'.toD7) [alg' : Algebra T'.Q.c.F X'.toD7.what₂.LL] (R : RealDat X.toD7 A T.Q.c.F) (R' : RealDat X'.toD7 A' T'.Q.c.F)
    (eH : HEq T'.Q.H T.Q.H) (el : HEq T'.Q.l T.Q.l) (ec : HEq T'.Q.c T.Q.c) (eD : HEq T'.Q.Dw T.Q.Dw) (eX : HEq T'.Q.Xo T.Q.Xo)
    (ePg : HEq R'.Pg R.Pg) (eβV : HEq R'.βV R.βV) (hL : R.toLevCh.Is A.μ0) (hL' : R'.toLevCh.Is A'.μ0)
    (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (eW : HEq (R'.cV i').W (R.cV i).W) (en : HEq (R'.cV i').nW (R.cV i).nW) (ei : HEq (R'.cV i').iW (R.cV i).iW)
    (eHV : HEq (R'.HV i' A'.μ0) (R.HV i A.μ0))
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0))
    {κ ι x₀} {v₀ : (R.MW i (sg0 X.toD7 A)).Vec} {v₀' : (R'.MW i' (sg0 X'.toD7 A')).Vec} (hO : O.Pins κ v₀ ι x₀)
    (hinj : Function.Injective O.c0')
    (h : IsBCOf O' v₀' O v₀ κ ι x₀ (∀ x : A.fam.amb.FL i A.μ0, x = 0)) : GeoTies.OmOver O O' := by
  have hQ := GlobalTheory.RefPins.places_ref R hL
  have hQ' := GlobalTheory.RefPins.places_ref R' hL'
  obtain ⟨c₃, hs, c0₃, io₃, hw₃, h₀, J₀, hB, hS, hor, -⟩ := h
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  rcases B' with ⟨P'⟩
  change P' = X.B.toPre at hP
  subst hP
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at eH el ec eD eX
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq eD
  obtain rfl := eq_of_heq eX
  obtain rfl : i = i' := Fin.ext hi
  obtain @⟨c'', hle, jL, hV, c0', lev, dδ, Cl', fCl, bad, Lh, La, Nc, gam, vol, ep, BB, epF, io, hw, φ, w, U₂, dict₂, xi, thAd, Plc⟩ := O'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -, s15, -, -, s18, -, -, -⟩ := hS
  dsimp only [bc, merge] at s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s15 s18 hor
  obtain rfl := eq_of_heq s1
  subst s4
  subst s6
  obtain rfl := eq_of_heq s3
  obtain rfl := eq_of_heq s5
  obtain rfl := eq_of_heq s7
  obtain rfl := eq_of_heq s8
  obtain rfl := eq_of_heq s9
  obtain rfl := eq_of_heq s10
  obtain rfl := eq_of_heq s11
  obtain rfl := eq_of_heq s12
  obtain rfl := eq_of_heq s15
  obtain rfl := eq_of_heq s18
  refine ⟨s2, c'', hs, HEq.rfl, fun h J hr => ⟨(by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J :)), ?_, fun x₀ x hx y' hy => ?_⟩⟩
  · exact (by with_unfolding_all exact ((repsOver_cast (D := X.toD7) (Pg₂ := R'.Pg) (Q₂ := R'.Q A'.μ0) (β₂ := (R'.βV)) ePg hQ hQ' ((eβV))
      (show RepsOver X.toD7 i R.Pg (R.Q A.μ0) R.βV _ h J _ _ _ from repsR_map (incF O.c' c'' hs) hr)) : _))
  · choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over hs (lamV X.toD7 i) (x k)
    refine ⟨(by with_unfolding_all exact (x' :)), ?_, fun a n f hf hfx f' e => ?_⟩
    · intro k
      have hv := heq_val (Γ := Bridge.Gf (Vc X.toD7 i)) (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW eW en ei (R.HV i A.μ0)
        ((by with_unfolding_all exact ((R'.HV i A'.μ0) :))) ((by with_unfolding_all exact (eHV :))) (jVx R i A.μ0 x₀) ((by with_unfolding_all exact (y' :))) ((by with_unfolding_all exact (hy :))) (fin _ (h k))
      rcases hor with hc | hp
      · have ha := heq_app (V := VsV X.toD7 i c''.F) (σ := inC c'') (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW eW en ei
          ((by with_unfolding_all exact (c0' :))) c0₃ ((by with_unfolding_all exact (hc :))) (x' k)
        exact (by with_unfolding_all exact ((eq_of_heq (hv.1.trans ((heq_of_eq ((hx k).trans (hB.c0 _ _ (hx' k)).symm)).trans ha.symm))) :))
      · have h0 : (R.HV i A.μ0).e (jVx R i A.μ0 x₀) (fin _ (h k)) = 0 := by
          rw [hp x₀]
          unfold jVx
          rw [map_zero, map_zero]
          rfl
        have h1 : x k = 0 := hinj (((hx k).symm.trans h0).trans (map_zero _).symm)
        have h2 : x' k = 0 := Subtype.ext ((hx' k).trans (by rw [h1]; exact map_zero _))
        have h3 := eq_of_heq (hv.1.trans ((heq_of_eq h0).trans hv.2.symm))
        have h4 : ∀ c : VsV X.toD7 i c''.F →ₛₗ[inC c''] (R'.cV i).W, 0 = c (x' k) := fun c => by rw [h2, map_zero]
        exact (by with_unfolding_all exact ((h3.trans (h4 ((c0')))) : _))
    · obtain rfl := eq_of_heq e
      exact (by with_unfolding_all exact ((isThClsD_covBC_one hs (O.dδ ()) rfl _ _ _ _ _ _ O.io io x x' (fun k => hB.io _ _ (hx' k))
        (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx) :))

end GlobalTheory.Mem.R3.Rw.OmExt
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.Mem.R3.Rw.GeoTies

namespace UpperTheory.Mem.GeoExt

theorem exists_omOver : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
    ∀ (core' : CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
      HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c → HEq core'.Q.Dw z.core.Q.Dw →
      HEq core'.Q.Xo z.core.Q.Xo → HEq core'.x₀ z.core.x₀ → HEq core'.iota z.core.iota →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
      (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
      GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSide z Wt' R' →
    ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
      (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
      TieIn core' R'.toRealDat κ' v₀' →
      ∃ O' : ∀ i', OMDat core'.toCore R'.toRealDat i' Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0),
        (∀ i', OMPins core' R'.toRealDat κ' v₀' O' i') ∧
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → OmOver (z.geo.O i) (O' i') := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS core' alg' eH el ec eD eX ex eι Xg tr R' cG' hP hL hB hW κ' v₀' ht
  obtain ⟨O', k1, k2⟩ := OmExt.exists_omPins_enl (w := w) (w' := w') (Z := Z) (Z' := Z') (Wt := Wt) (Wt' := Wt') z hE hf hp hS core' eH el ec eD eX ex eι R' cG' hP hL hB hW.1 κ' v₀' ht
  refine ⟨O', k1, fun i i' hi => ?_⟩
  have k3 := (k2 i i' hi).2
  have eHV := (hW.2 i i' hi).2.2.1
  obtain ⟨-, -, -, -, -, -, eβV, -, -, ePg, -, -, hcV, -⟩ := hW.1
  have e1 := (hcV i i' hi).1
  have e2 := (hcV i i' hi).2.2.1
  have e3 := (hcV i i' hi).2.2.2.1
  have h1 := hP.char.base.lev
  have hinj := OmExt.normalisedData_coefficientMap_injective (z.geo.O i) (z.geo.pins i).1 (z.geo.pins i).2
  clear hcV hP hL hB hS hW k1 k2
  obtain ⟨hPre, -, -, hLL⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  exact (by with_unfolding_all exact ((OmExt.omOver_of_isBCOf (w.st Z) _ (((Eq.refl B.toPre))) z.core core' z.R.toRealDat R'.toRealDat eH el ec eD eX ePg eβV
    z.pins.char.base.lev h1 i i' hi e1 e2 e3 eHV (z.geo.O i) (O' i') (z.geo.pins i).2 hinj k3) : _))

end UpperTheory.Mem.GeoExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedAdelicDataWithIntertwinersOverEnla
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfToAnalyticDataEnlargedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsOfWeakCharacterisation
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw

theorem geometricHalf_coreForms_of_weakCharacterisation (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {C : CoreJ D} [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F)
    (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {ph : Fin D.R.m → ℂ}
    (geo : GeoHalf C R.toRealDat ph) : InGeo geo := by
  have hC : PreChar R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hp : C.pb = R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins C R.toRealDat geo.κ geo.v₀ geo.O hC.lev geo.fw.laws geo.pins
  exact (GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP _ _ _ _ _ C R.toRealDat _ geo hC hch.base.grp.chiW hp hn).1

theorem stepW_rank_large (p : WP) :
    StepW p fun _ _ _ _ w => ∀ Z : w.Lt, 8 * (w.st Z).toD7.R.f * (w.st Z).toD7.R.r + 4 ≤ (w.st Z).toD7.R.nV :=
  Step.of_evG ((evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun _ _ _ _ _ H _ _ _ hO _ _ _ w _ Z => (H (w.st Z) hO).2)


set_option maxHeartbeats 1000000 in
theorem inGeo_stepW (hP : GlobalTheory.Published.CuspRapidDecay) (p : WP) :
    StepW p fun _ B' _ _ w' => ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok) (U : Set w'.I.ι) (core' : CoreJ (w'.st Z').toD7)
      (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL), letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' U Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' U Xg tr) cG' → R'.toRealDat.ExAt →
        ∀ (ph : Fin (w'.st Z').toD7.R.m → ℂ) (geo : GeoHalf core' R'.toRealDat ph), InGeo geo :=
  (stepW_rank_large p).trans (StepW.of_all fun _ _ _ _ _ _ _ H Z' _ _ _ _ _ _ R' _ hPin hEx _ geo =>
    geometricHalf_coreForms_of_weakCharacterisation hP R' _ hPin.char hEx (H Z') geo)

end GlobalTheory.Mem.R3.Rw

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.geometricHalf_to_analyticData_enlargedBase : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R' → (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ x' ∈ (R'.FW i').WK, ∃ x ∈ (z.R.FW i).WK,
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) → CrdOver ι x x') →
        ∃ geo : GlobalTheory.RealGeo.GeoHalf core' R'.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo geo ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
          (∀ φ φ', HEq φ' φ → HEq ((R'.FW i').j (w'.st Z').toD7.what₂.embLL (geo.fw.e i' φ' : (R'.FW i').WK).1)
            ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)) ∧
          (HEq (geo.κ i').aP (z.geo.κ i).aP ∧ HEq (geo.κ i').aM (z.geo.κ i).aM ∧ (geo.κ i').n = (z.geo.κ i).n)) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((geo.fw.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k))) := by
  intro _ _ h3 _ _ _ _
  refine (GlobalTheory.Mem.R3.Rw.inGeo_stepW h3 Pinned).trans (Step.of_all fun K B' f' T' _ _ _ _ w' H => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1 _
  letI := alg'
  obtain ⟨hPins, hLev, -, -, -, hBrg, hEx', hRS⟩ := s1
  have hex : ∃ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL,
      ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := ⟨(by with_unfolding_all exact ((enlEmb hE.2.2.2) :)), (by with_unfolding_all exact ((enlEmb_spec hE.2.2.2) :))⟩
  refine hex.elim fun ι hι => ?_
  have hcomp : (w'.st Z').toD7.what₂.embLL.comp ι = (w.st Z).toD7.what₂.embLL := RingHom.ext hι
  have hfw := UpperTheory.Mem.GeoExt.exists_fw B B' f f' T T' w w' hE.1 Z hX Wt z Z' hX' {v | B'.places.resChar v ∈ T'.pl} core' alg' ha1 hc hL
    Xg tr R' hRS.1 hf hLev ι hι
  refine hfw.elim fun κ' hfw => hfw.elim fun v₀' hfw => hfw.elim fun fw' hfw => ?_
  have hκ := hfw.1
  have hv := hfw.2.1
  have he := hfw.2.2
  have hcrd : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
      ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
      (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') =
        (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k) :=
    fun i i' hi φ φ' hφ k k' hk => (congrArg _ ((he i i' hi φ φ' hφ).2 k k' hk)).trans (hι _)
  have hv0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (v₀' i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) :=
    fun i i' hi => (hv i i' hi _).trans (congr_arg_heq (z.geo.v₀ i) hcomp)
  have hMW : GeoTies.MWOver z.R.toRealDat R'.toRealDat := fun i i' hi ι' hι' σ' => by
    have hcl := (((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι' hι').1 σ').1
    exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.1, hcl.2.2.2.2.1, hcl.2.2.2.2.2.1, hcl.2.2.2.2.2.2.1⟩
  have hO := UpperTheory.Mem.GeoExt.exists_omOver z hE hf hpx hF.2.2.2 core' hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2 R' cG' hPins hLev hBrg hRS κ' v₀'
    (GlobalTheory.OneMapRefObj.tieIn_of_fwTie fw')
  refine hO.elim fun O' hO => ?_
  have hOP := hO.1
  have hOm := hO.2
  have t := UpperTheory.Mem.GeoExt.ties_enl w w' Z Z' hX hX' Wt {v | B'.places.resChar v ∈ T'.pl} z hE hpx core' alg' ha1 hc Xg tr R' cG' hPins hRS
    κ' hκ v₀' fw' hcrd hv0 O' hOP hOm hF.1 hH.unif hEx' hMW
  refine ⟨⟨κ', v₀', fw', t.1, O', hOP, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩, H Z' hX' _ core' alg' Xg tr R' cG' hPins hEx' _ _,
    fun i i' hi => ⟨hv0 i i' hi, fun φ φ' hφ => ?_, hκ i i' hi⟩, hcrd⟩
  have hj := (((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1
    (w'.st Z').toD7.what₂.embLL).2.2.2 _ _ (he i i' hi φ φ' hφ)
  exact hj.trans (congr_arg_heq (fun σ => (z.R.FW i).j σ (z.geo.fw.e i φ : (z.R.FW i).WK).1) hcomp)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatExtRestOfParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem GlobalTheory.Mem.R3.Rw.frame_pb_heq {P P' : Pre} (e : P' = P) {g' : Fr P'} {g : Fr P} (h : HEq g' g) : HEq g'.P.pb g.P.pb := by
  subst e; cases h; rfl


set_option maxHeartbeats 8000000 in
theorem GlobalTheory.Mem.R3.Rw.datExt_rest_of_parts :
    (GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀)) →
    (GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀ →
        ∃ (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R')) →
    (GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R' →
        ∃ geo : GlobalTheory.RealGeo.GeoHalf core' R'.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo geo ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
          (∀ φ φ', HEq φ' φ → HEq ((R'.FW i').j (w'.st Z').toD7.what₂.embLL (geo.fw.e i' φ' : (R'.FW i').WK).1)
            ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)) ∧
          (HEq (geo.κ i').aP (z.geo.κ i).aP ∧ HEq (geo.κ i').aM (z.geo.κ i).aM ∧ (geo.κ i').n = (z.geo.κ i).n)) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((geo.fw.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)))) →
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, z'.core = core' ∧
        z'.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z'.geo ∧ z'.Std ∧ ExtN z z') := by
  intro k1 k2 k3 h1 h2 h3 h4 h5 h6 h7
  refine (((k1 h1 h2 h3 h4 h5 h6 h7).and (k2 h1 h2 h3 h4 h5 h6 h7)).and (k3 h1 h2 h3 h4 h5 h6 h7)).trans
    (Step.of_all fun K B' f' T' _ _ _ _ w' hw => ?_)
  obtain ⟨⟨ha, hb⟩, hd⟩ := hw
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb
  obtain ⟨Xg, tr₀, R₀, cG, s0⟩ :=
    ha B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb
  obtain ⟨tr, R', cG', s1⟩ :=
    hb B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr₀ R₀ cG s0
  obtain ⟨geo, hg⟩ :=
    hd B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1
  obtain ⟨p, l, i, g, m, s, e, ⟨rW, rT⟩⟩ := s1
  letI := alg'
  refine ⟨⟨Xg, tr, core', ha1, R', cG', geo, p, l, i, g, m, ha2, ha3⟩, rfl, e, hg.1, s, ?_⟩
  obtain ⟨hH, hl, hcc, hDw, hXo, hU, hV', hdict, hmu, hKf, hcE, hchiW, hx₀, hiota⟩ := hc
  obtain ⟨rψ, rθ, rβW, rβY, rΛY, rnW, rβV, rΛV, rΛW, rPg, reG, rSb, rI, rjL⟩ := rW
  exact
    { H := hH, l := hl, c := hcc, Dw := hDw, Xo := hXo, U := hU, V := hV', dict := hdict, mu := hmu, Kf := hKf, cE := hcE,
      chiW := hchiW, x₀ := hx₀, iota := hiota, ψ := rψ, θ := rθ, βW := rβW, βY := rβY, nW := rnW, βV := rβV, ΛV := rΛV,
      ΛW := rΛW, Pg := rPg, eG := reG, Sb := rSb
      BV := fun i i' hi => by
        obtain ⟨a1, a2, -, -, a5, a6, a7, -⟩ := rI i i' hi
        exact ⟨a1, a2, a5, a6, (rT i i' hi).1, a7⟩
      MW := fun i i' hi => by
        obtain ⟨-, -, -, -, -, -, -, b1, b2, b3, b4, b5, b6, b7, b8, b9, -⟩ := rI i i' hi
        exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, (hg.2.1 i i' hi).1, (hg.2.1 i i' hi).2.1⟩
      forms := hg.2.2
      cV := fun i i' hi => by
        obtain ⟨-, -, a3, a4, -⟩ := rI i i' hi
        exact ⟨a3, a4⟩
      pb := (heq_of_eq hpb).trans ((GlobalTheory.Mem.R3.Rw.frame_pb_heq hE.1 hf).trans (heq_of_eq hF.2.2.1.2.2.2.symm))
      ΛY := rΛY
      κ := fun i i' hi => (hg.2.1 i i' hi).2.2
      ref := fun i i' hi => by
        obtain ⟨-, t2, t3, t4, t5, t6, t7⟩ := rT i i' hi
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c1, c2, -⟩ := rI i i' hi
        exact ⟨t2, t3, t4, t5, t6, t7, c1, c2⟩
      jL := rjL }
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedAdelicDataWithIntertwinersOverEnla
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.RSideW.wk_image {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
    {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} {z : Dat (w.st Z) w.I hX T Wt} {Wt' : Set B'.places.Pl}
    {R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks} (h : RSideW z Wt' R')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    ∀ x' ∈ (R'.FW i').WK, ∃ x ∈ (z.R.FW i).WK, ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL,
      (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) → CrdOver ι x x' := by
  intro x' hx'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, rI, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rι⟩ := rI i i' hi
  by_cases hex : ∃ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL,
      ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y
  · obtain ⟨ι, hι⟩ := hex
    obtain ⟨-, ⟨a, b⟩, -⟩ := rι ι hι
    obtain ⟨x, hx⟩ := b x' hx'
    refine ⟨x, (a x x' hx).1 hx', fun ι' hι' => ?_⟩
    have e : ι' = ι := RingHom.ext fun y => (w'.st Z').toD7.what₂.embLL.injective ((hι' y).trans (hι y).symm)
    rw [e]
    exact hx
  · exact ⟨0, Submodule.zero_mem _, fun ι hι => absurd ⟨ι, hι⟩ hex⟩


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.datExt_rest : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, z'.core = core' ∧
        z'.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z'.geo ∧ z'.Std ∧ ExtN z z') := by
  refine GlobalTheory.Mem.R3.Rw.datExt_rest_of_parts GlobalTheory.T.exists_analyticData_enlargedBase_tupleFree GlobalTheory.T.exists_characterisedData_weil_enlargedBase fun h1 h2 h3 h4 h5 h6 h7 => by
    refine (GlobalTheory.T.geometricHalf_to_analyticData_enlargedBase h1 h2 h3 h4 h5 h6 h7).trans (Step.of_all fun K B' f' T' _ _ _ _ w' hd => ?_)
    intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1
    exact hd B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1
      (@GlobalTheory.Mem.R3.Rw.RSideW.wk_image _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ alg' _ _ _ _ _ s1.2.2.2.2.2.2.2.1)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedAdelicDataWithIntertwinersOverEnlaStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extendedAdelicData_with_intertwiners_over_enlargedCore : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, z'.core = core' ∧
        z'.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z'.geo ∧ z'.Std ∧ ExtN z z')  := by
  first | exact @GlobalTheory.Mem.R3.Rw.datExt_rest | exact GlobalTheory.Mem.R3.Rw.datExt_rest | (intros; apply GlobalTheory.Mem.R3.Rw.datExt_rest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedColumnDataAllClausesButPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.ExtBuild


set_option maxHeartbeats 4000000 in
theorem exists_ext_build : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ ExtN z z') := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (GlobalTheory.T.exists_extendedAdelicData_with_intertwiners_over_enlargedCore h1 h2 h3 h4 h5 h6 h7) (StepW.of_all fun K B' f' T' w' _ _ hq => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV
  obtain ⟨core', alg', a1, a2, a3, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, l1, l2, l3, l4⟩ :=
    GlobalTheory.T.exists_adelicCore_transport_enlargedCoefficientBase_alt w w' Z Z' hX Wt z hE hf hF.2.2.1
  obtain ⟨z', hc, hex, hin, hstd, hN⟩ :=
    hq B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' a1 a2 a3
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ l1 l2 l3 l4
  refine ⟨z', ⟨hex, hin, ?_, hstd⟩, hN⟩
  unfold CoreP
  rw [hc]
  exact ⟨l1, l2, l3, l4⟩

end GlobalTheory.Mem.R3.Rw.ExtBuild
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedColumnDataAllClausesButPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extendedColumnData_all_clauses_but_places : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ ExtN z z') := by
  first | exact @GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build | exact GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build | (intros; apply GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build <;> assumption)
end

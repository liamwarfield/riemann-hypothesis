module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaSeriesRationalVectorNeZeroOfCuspForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharEqOneOfTrivialOverSplitPlacesCm
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalScalarNormalisedStandardFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalScalarNormalisedStandardFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist GlobalTheory.SeriesTie GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.NormRatStd

section Steps

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

theorem fixBase_of_fix (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀))
    (hti : TieIn T Rl.toRealDat κ v₀) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ z ∈ (embLL0 D).fieldRange, τ z = z) :
    FixBase T Rl.toRealDat j τ :=
  GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ hT hcore hfw hti hgal hval hray hroots j τ hτ

theorem exists_extC {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) : ∃ c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W, ExtC R j (inC O.c') O.c0' c :=
  GlobalTheory.T.exists_complexLinear_extension_coefficientMap D G Pl0 T1 A T R j Tp tup O

theorem exists_ser_ne_zero {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hio : IoExt Rl.toRealDat)
    (j : Fin D.R.m) (hpins : OMPins T Rl.toRealDat κ v₀ O j) (hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j)
    (hcusp : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) :
    ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)),
      (∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL)) ∧
      (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧
      h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 :=
  GlobalTheory.T.exists_thetaSeries_rational_vector_ne_zero_of_cuspForms D Γ Pl0 I0 T0 A3 T Rl F κ v₀ O hnV hcore hfw hio j hpins hrow0 hcusp c hc u hu

theorem expands_of_isRatPhase (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
    {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    {F : Face D A3.A} {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
    {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat)
    (hQ : QGuard Rl.toRealDat) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    {j : Fin D.R.m} (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (hpins : OMPins T Rl.toRealDat κ v₀ O j)
    (hfp : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV)
    {gramR c0R c0L} (hft : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L)
    (hbc : CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0')
    {u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ} (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) {ph₀ : ℂ}
    (hph : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank))
    (h : GA D (Vc D j)) (hh : h ∈ GfC (Vc D j)) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n),
      Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧
        ∀ k, e k ∈ (embLL0 D).fieldRange :=
  GlobalTheory.T.rationalPhaseThetaSeries_expands_cuspForms_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hnV hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp gramR c0R c0L hft hbc u hu ph₀ hph c hc v hv x hx h hh

theorem fixed_of_expands {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {Φ Ψ Ψ' : GA D (Wc D j) → ℂ} {a : ℂ}
    (hc : ConjFun O κ τ 1 Ψ Ψ') (hΨ : ∀ g, Ψ g = a * Φ g) (hΨ' : ∀ g, Ψ' g = a * Φ g) {n : ℕ} {e : Fin n → ℂ}
    {f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA κ) κ.n} (he : Expands O κ Φ e f) (hτ : ∀ k, τ (e k) = e k)
    {g₀ : GA D (Wc D j)} (hg₀ : Φ g₀ ≠ 0) : τ a = a := by
  have h1 : Expands O κ Ψ (fun k => a * e k) f := by
    intro g
    rw [hΨ g, he g, Finset.mul_sum]
    simp only [mul_assoc]
  have h2 := hc.2 _ _ _ h1 g₀
  have h3 : a * Φ g₀ = τ a * Φ g₀ := by
    rw [← hΨ' g₀, h2, he g₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show 1 * τ (a * e k) * _ = _
    rw [one_mul, map_mul, hτ, mul_assoc]
  exact (mul_right_cancel₀ hg₀ h3).symm

theorem conjVec_self_of_rat (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    ConjVec j τ x x := by
  unfold ConjVec
  rw [hx]
  ext m
  obtain ⟨q, hq⟩ := hv m
  simp [MvPolynomial.coeff_map, hq]

end Steps

theorem exists_isNorm_isRatScalar_std : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS →
    ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j),
    RealPin Rl cG ρ → RatHyp T Rl F κ v₀ O i j hV → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ →
    ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν := by
  intro _ hRF row D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin H hcusp
  have hCI : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  have hcore := H.core
  have hT := H.laws
  have hti := H.tieIn
  have hfw := H.fw
  have hio := H.io
  have hQ := H.guard
  have hfin := H.fin
  have hpins := H.pins
  have hphase := H.phase
  have hfp := H.frame
  have hnV := H.size
  have hgal := H.galois
  have hval := H.small.val
  have hray := H.small.ray
  have hroots := H.small.roots
  have hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j :=
    GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses hCI D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hcore.lev hcore.grp hcore.fam
      hcore.models hcore.thP hti hio O j hpins

  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hpins.2.lift.c0
  obtain ⟨u, w₀, hu, -, hw⟩ := FWT.IsChosenExtremalVector.io _ (hti.hv₀ j (sg0 D A3.A)) hio
  obtain ⟨c, hc0, hsc⟩ := Scale.exists_scale hcore.lev hcore.thP (hcore.models.cV j) (hρ.base i j b) (hpin.psi i j b)
    (hpin.inf i j b) (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b)
    (hpin.ap i j b) (hpin.am i j b) (c0L j) (hft.mapL j) _ w₀ hw
  obtain ⟨ph₀, hph₀1, hph₀⟩ : ∃ ph : ℂ, ‖ph‖ = 1 ∧ IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph := by
    obtain ⟨ph, h1, h2⟩ := row D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hT hcore.lev hcore.grp hcore.fam hcore.models hcore.thP hti
      j hV hfp H.std gramR c0R c0L hft u hu
    exact ⟨ph, h1, fun C hC _ => h2 C hC⟩
  have hph₀0 : ph₀ ≠ 0 := fun e => by simp [e] at hph₀1

  have hph1 : ‖cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)‖ = 1 := (hphase hrow0).2.1.2.2.2.2.1
  have hph0 : cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) ≠ 0 := fun e => by rw [e, norm_zero] at hph1; exact zero_ne_one hph1

  obtain ⟨cx, hcx⟩ := exists_extC (O j)
  obtain ⟨ζ, ⟨n, hn, hζn⟩, hζ⟩ := GlobalTheory.ConjRefTup.conjFun_base_root hCI D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O
    (fun j => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)) hnV hcore hfin hfw hio hQ j hpins hphase cx hcx
  have hζ1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζn hn.ne'
  have hζ0 : ζ ≠ 0 := fun e => by simp [e] at hζ1

  obtain ⟨v, x, h, g₀, hv, hx, hh, hg₀⟩ := exists_ser_ne_zero O hnV hcore hfw hio j hpins hrow0 hcusp cx hcx u hu
  obtain ⟨m, e, f, hexp, heL⟩ := expands_of_isRatPhase hRF YS O hnV hT hcore hfw hti hio hQ hgal hval hray hroots hV hpins hfp
    hft hbc hu hph₀ cx hcx v hv x hx h hh

  obtain ⟨a, ha_def⟩ : ∃ a, a = ζ * cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * ph₀⁻¹ := ⟨_, rfl⟩
  have hv0 : (fun ρ => ((u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ))) = v₀ j (sg0 D A3.A) := funext hu
  have haL : a ∈ (embLL0 D).fieldRange := by
    refine GlobalTheory.FixedRoots.mem_of_forall_ringEquiv_fixed _ a fun τ hτ => ?_
    have hfix := fixBase_of_fix hRF YS hT hcore hfw hti hgal hval hray hroots j τ hτ
    have hct : ConjTup Rl.toRealDat τ A3.A.μ0 A3.A.μ0 := by
      refine ⟨rfl, fun z => ?_⟩
      have h1 := hcore.lev.xi A3.A.μ0
      rw [hcore.lev.xi_base] at h1
      rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 z]
      simp
    obtain ⟨y, y', hyy, hy⟩ := GlobalTheory.T.exists_conjugateForms_thetaLift_eq_thetaSeries D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hcore hfw j Unit (fun _ => A3.A.μ0) (O j)
      hpins.2 cx hcx τ A3.A.μ0 A3.A.μ0 hfix hct h hh x x (conjVec_self_of_rat j τ v hv x hx)
    have hcf := hζ τ hfix y y' hyy
    have hy1 : ∀ g, (Rl.thF j A3.A.μ0) y (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g :=
      fun g => by have e := (hy u g).1; rwa [hv0] at e
    have hy2 : ∀ g, (Rl.thF j A3.A.μ0) y' (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g :=
      fun g => by have e := (hy u g).2; rwa [hv0] at e
    refine fixed_of_expands (O j) (κ j) τ hcf (fun g => ?_) (fun g => ?_) hexp (fun k => hτ _ (heL k)) (g₀ := g₀)
      (mul_ne_zero hph₀0 hg₀)
    · rw [hy1 g, ha_def, mul_assoc (ζ * _) ph₀⁻¹, inv_mul_cancel_left₀ hph₀0]
    · rw [hy2 g, ha_def, mul_assoc (ζ * _) ph₀⁻¹, inv_mul_cancel_left₀ hph₀0]
  have ha1 : ‖a‖ = 1 := by rw [ha_def, norm_mul, norm_mul, norm_inv, hζ1, hph1, hph₀1]; norm_num

  have hν : a * (ph₀ * c) = ζ * cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c := by
    rw [ha_def, ← mul_assoc, mul_assoc (ζ * _) ph₀⁻¹, inv_mul_cancel₀ hph₀0, mul_one]
  refine ⟨a * (ph₀ * c), ⟨?_, c, ⟨gramR, c0R, c0L, hft, u, hu, hsc⟩, n, hn.ne', ?_⟩, ?_⟩
  · rw [hν]; exact mul_ne_zero (mul_ne_zero hζ0 hph0) hc0
  · rw [hν, mul_assoc, mul_pow, hζn, one_mul]
  · exact (IsRatScalar.intro hft hu hc0 hph₀1 hsc hph₀).mul haL ha1

end GlobalTheory.SeriesTie.NormRatStd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalScalarNormalisedStandardFrameStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.SeriesTie GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalScalar_normalised_standardFrame : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → RatHyp T Rl F κ v₀ O i j hV → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ → ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν := by
  first | exact @GlobalTheory.SeriesTie.NormRatStd.exists_isNorm_isRatScalar_std | exact GlobalTheory.SeriesTie.NormRatStd.exists_isNorm_isRatScalar_std | (intros; apply GlobalTheory.SeriesTie.NormRatStd.exists_isNorm_isRatScalar_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAdelesStableRangeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAdelesStableRangeOne
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.StableRange

theorem adeles_tensor_stableRange_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a b : AF F ⊗[F] E),
    IsCoprime a b → ∃ t : AF F ⊗[F] E, IsUnit (a + t * b) := by
  intro F E _ _ _ _ _ a b h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.IsIntegral (AF F) (AF F ⊗[F] E) := Algebra.IsIntegral.of_finite _ _
  exact stable_adele F a b h

end GlobalTheory.StableRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAdelesStableRangeOneStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionAdeles_stableRange_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a b : AF F ⊗[F] E),
    IsCoprime a b → ∃ t : AF F ⊗[F] E, IsUnit (a + t * b) := by
  first | exact @GlobalTheory.StableRange.adeles_tensor_stableRange_one | exact GlobalTheory.StableRange.adeles_tensor_stableRange_one | (intros; apply GlobalTheory.StableRange.adeles_tensor_stableRange_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangian
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SiegelLawDblTargetF

theorem exists_gaf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (p : UG (cA σ) (incM F J)ᵀ) :
    ∃ h : GAF σ J, mtF σ J h = p.1.1 := by
  have hmem : p.1 ∈ HR (AF F) σ J := by
    show Formalism.UG.cT _ _ * _ * _ = _
    have e1 : ((p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (sigR (AF F) σ)) =
        (p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (cA σ) := by
      ext i j; exact (GlobalTheory.TransportHeisF.cA_eq_cAF σ _).symm
    have e2 : JR (AF F) J = (incM F Jᵀ)ᵀ := by ext i j; rfl
    have hp' : (p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵀ * incM F Jᵀ *
        (p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (cA σ) = incM F Jᵀ := p.2
    unfold Formalism.UG.cT
    rw [e1, e2]
    have := congrArg Matrix.transpose hp'
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  exact ⟨⟨p.1, hmem⟩, rfl⟩

theorem two_isUnit (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsUnit (2 : AF F ⊗[F] E) := by
  have h := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AF F ⊗[F] E))
  rwa [map_ofNat] at h

theorem char_det_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (α : GL (Fin n) (AF F ⊗[F] E) →* Circle) (a : GL (Fin n) (AF F ⊗[F] E))
    (ha : Matrix.GeneralLinearGroup.det a = 1) : α a = 1 :=
  MonoidHom.mem_ker.mp (GlobalTheory.T.special_linear_generated_by_transvections (AF F ⊗[F] E) (GlobalTheory.T.extensionAdeles_stableRange_one F E) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (GlobalTheory.glChar_transvection (two_isUnit F E) α i j hij t u hu)) a ha)

theorem lagr_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (χS (Matrix.GeneralLinearGroup.det t) : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨α, hαc, hαr, hlaw⟩ := GlobalTheory.T.diagonal_lagrangian_integral_siegel_parabolic_transform F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  intro h t hht f hf
  by_cases h0 : ∀ g, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ g →
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) g = 0
  · rw [h0 _ (hωd.om_pres _ f hf), h0 f hf, mul_zero]
  push_neg at h0
  obtain ⟨f₀, hf₀, hne⟩ := h0
  have hsp := GlobalTheory.T.splitPlace_siegelLaw_diagonalLagrangian_character F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd α hlaw f₀ hf₀ hne
  have hα : ∀ a : GL (Fin nT) (AF F ⊗[F] E), α a = χS (Matrix.GeneralLinearGroup.det a) := by
    rcases Nat.eq_zero_or_pos nT with hn0 | hpos
    · intro a
      have hd : Matrix.GeneralLinearGroup.det a = 1 := by
        ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst hn0; simp
      rw [char_det_one F E nT α a hd, hd, map_one]
    obtain ⟨i0⟩ : Nonempty (Fin nT) := ⟨⟨0, hpos⟩⟩
    have hhec : IsHeckeCharF (α.comp (GlobalTheory.LeviOrigin.dgU nT i0) * χS⁻¹) := by
      refine ⟨?_, ?_⟩
      · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU nT i0)).mul (hωd.hecS.1.inv)
      · intro x
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, hωd.hecS.2 x, inv_one, mul_one,
          GlobalTheory.LeviOrigin.dgU_map (incAF F E) nT i0 x]
        exact hαr _
    have hν1 := GlobalTheory.T.unitaryHeckeChar_eq_one_of_trivial_over_split_places_cm F E σ B hB _ hhec (by
      intro e he x hx
      have h2 := hsp e he (GlobalTheory.LeviOrigin.dgU nT i0 x) (by
        intro k l
        rw [GlobalTheory.LeviOrigin.dgU_sub_one]
        split_ifs
        · exact hx
        · exact mul_zero _)
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, MonoidHom.inv_apply,
        mul_inv_cancel])
    have hdg : ∀ x, α (GlobalTheory.LeviOrigin.dgU nT i0 x) = χS x := by
      intro x
      have := hν1 x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at this
      exact mul_inv_eq_one.mp this
    intro a
    have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a))⁻¹) = 1 := by
      rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
    have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
        α (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a)) := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h3, char_det_one F E nT α _ hb, one_mul]
    exact hdg _
  rw [hlaw h t hht f hf, hα t]

theorem main_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
      ∀ (p : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        p.1.1 * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
      ∀ Φ ∈ schA F κ, omp (p, 1) Φ ∈ schA F κ ∧
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (omp (p, 1) Φ)) =
          (χS (Matrix.GeneralLinearGroup.det t) : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 χS hχS rχS ωd hωd omp htr p t hpt Φ hΦ
  obtain ⟨h, hh⟩ := exists_gaf σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) p
  have hg : mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    first
      | (simp only [mtF, map_one, inv_one]; simp; done)
      | (simp [mtF, matHomF]; exact map_one _)
      | (simp [mtF, matHomF]; rfl)
  obtain ⟨hmem, heq⟩ := htr p 1 1 h hh hg Φ hΦ
  refine ⟨hmem, ?_⟩
  have hth := GlobalTheory.TransportHeisF.isThetaFunOF_thetaTr F E σ B hB nS (nT + nT) JS
    (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hS (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀ hξ₀ hσ hωd.std _ JB ξ
    rfl hξ κ co hco Φ hΦ
  exact (congrArg (GlobalTheory.LagrTheta.lagrInt ν 𝓕
    ((diagCols (Fin nT)).submatrix finSumFinEquiv.symm id)) heq).trans
    (lagr_law F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t (by rw [hh]; exact hpt) _ hth)

end GlobalTheory.SiegelLawDblTargetF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangianStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.siegelWeil_section_law_diagonalLagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
      ∀ (p : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        p.1.1 * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
      ∀ Φ ∈ schA F κ, omp (p, 1) Φ ∈ schA F κ ∧
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (omp (p, 1) Φ)) =
          (χS (Matrix.GeneralLinearGroup.det t) : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.SiegelLawDblTargetF.main_law | exact GlobalTheory.SiegelLawDblTargetF.main_law | (intros; apply GlobalTheory.SiegelLawDblTargetF.main_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBack
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBack
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensCub

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR

section Box

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {pr : K₀ → (X' ⟶ X)} {εp : K₀ → ℤ}

def bwg {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr εp)) (ψ : Z ⟶ X') (z : Z) (jN : K₀ → M.ι) (k : M'.ι) :
    (Z.presheaf.stalk z)ˣ := gm ψ z (LB.wchart M pr jN ⊓ M'.U k) (w.s (jN, k))

theorem bwg_trans {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : K₀ → M.ι} {k k' : M'.ι} (h₁ : ψ z ∈ LB.wchart M pr jN) (h₁' : ψ z ∈ LB.wchart M pr jN')
    (h₂ : ψ z ∈ M'.U k) (h₂' : ψ z ∈ M'.U k') :
    bwg w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i)) ^ εp i) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bwg w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  have d := gm_div M' (LB.LinComb M pr εp) ψ z (jN, k) (jN', k') hm
  have l := gm_linComb M pr εp ψ z jN jN' h₁ h₁'
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res ψ z _ hm _))))

theorem gm_linCombIsoG {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr εp)) {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (jN : K → K₀ → M.ι) (jM : K → M'.ι)
    (hz : r z ∈ LB.wchart (LB.LinComb M pr εp) φ jN ⊓ LB.wchart M' φ jM) :
    gm r z (LB.wchart (LB.LinComb M pr εp) φ jN ⊓ LB.wchart M' φ jM) ((LB.linCombIso w φ ε).s (jN, jM)) =
      ∏ a, bwg w (r ≫ φ a) z (jN a) (jM a) ^ ε a :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a)
    ((gm_res r z _ hz _).trans (gm_pull r (φ a) z (LB.wchart M pr (jN a) ⊓ M'.U (jM a))
      ⟨Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a⟩ _))))

variable {K : Type} [Fintype K]

def ratio (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (ρ : K₀ → (Y ⟶ Y₀)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → K₀ → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bwg w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) ^ εp i)⁻¹

theorem chart_le {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ρ : K₀ → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a) (jN : K → K₀ → M.ι) (i : K₀) :
    LB.wchart (LB.LinComb M pr εp) φ' jN ≤ ρ i ⁻¹ᵁ LB.wchart M φ (fun a => jN a i) := fun y hy =>
  Set.mem_iInter.2 fun a => (congrArg (fun g : Y ⟶ X => g y ∈ M.U (jN a i)) (hψ i a)).mp
    (Set.mem_iInter.1 (Set.mem_iInter.1 hy a) i)

end Box

end GlobalTheory.TensCub

namespace GlobalTheory.TensCub
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR
section Box2
variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {pr : K₀ → (X' ⟶ X)} {εp : K₀ → ℤ}
variable {K : Type} [Fintype K]

theorem ratio_trans (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : K₀ → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {jN jN' : K → K₀ → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)
    (h' : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN' ⊓ LB.wchart M' φ' jM') :
    ratio w ρ t' t r z jN jM = ratio w ρ t' t r z jN' jM' := by
  have e₁ : ∀ a, bwg w (r ≫ φ' a) z (jN a) (jM a) = _ := fun a => bwg_trans w hw (r ≫ φ' a) z (jN' := jN' a) (k' := jM' a)
    (Set.mem_iInter.1 h.1 a) (Set.mem_iInter.1 h'.1 a) (Set.mem_iInter.1 h.2 a) (Set.mem_iInter.1 h'.2 a)
  have e₂ := gen_trans ht' r z h.2 h'.2
  have e₃ : ∀ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) = _ := fun i =>
    gen_trans ht (r ≫ ρ i) z (j' := fun a => jN' a i) (chart_le hψ jN i h.1) (chart_le hψ jN' i h'.1)
  have e₄ : ∏ i, trF (L := M) φ ε (r ≫ ρ i) z (fun a => jN a i) (fun a => jN' a i) ^ εp i =
      ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (jN a i) ⊓ M.U (jN' a i)) (M.g (jN a i) (jN' a i)) ^ εp i) ^ ε a := by
    unfold trF
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, ← zpow_mul, mul_comm, Category.assoc, Category.assoc, hψ]
  unfold ratio
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂,
    Finset.prod_congr rfl fun i _ => congrArg (· ^ εp i) (e₃ i)]
  simp only [mul_zpow, Finset.prod_mul_distrib, e₄]
  simp only [inv_zpow, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : K₀ → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε)) (jN : K → K₀ → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
        r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM →
        gm r z _ u = ratio w ρ t' t r z jN jM := by
  refine ⟨@id (Γ(Y, LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM)) * res inf_le_right (t'.s jM) *
      (∏ i, res (inf_le_left.trans (chart_le hψ jN i)) (pullU (ρ i) _ (t.s (fun a => jN a i))) ^ εp i)⁻¹,
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linCombIsoG w φ' ε r z jN jM hz) (gm_res r z _ hz _))) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ εp i) ?_))))))
  exact (gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (chart_le hψ jN i hz.1) _)

theorem box_unique {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr εp))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : K₀ → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bwg w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ i, val t (e ≫ ρ i) y J ^ εp i)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bwg w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ i, val t (r ≫ ρ i) z J ^ εp i := by
  choose u hu using fun q : (K → K₀ → M.ι) × (K → M'.ι) => exists_ratio w hψ t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens)
    (fun q : (K → K₀ → M.ι) × (K → M'.ι) =>
      LB.wchart (LB.LinComb M pr εp) φ' q.1 ⊓ LB.wchart M' φ' q.2) (fun _ => le_top)
    (fun y _ => by
      choose a ha using fun k i => exists_chart hM (pr i (φ' k y))
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 fun k => Set.mem_iInter.2 (ha k), Set.mem_iInter.2 hb⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratio_trans w hw hψ ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bwg w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ i, val t (r ≫ ρ i) z J ^ εp i)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have v : ∏ i, val t (r ≫ ρ i) z J ^ εp i = ∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => J ((r ≫ φ' a) ≫ pr i)))
        (t.s (fun a => J ((r ≫ φ' a) ≫ pr i))) ^ εp i := Finset.prod_congr rfl fun i _ =>
      congrArg (· ^ εp i) (val_of t _ z J _ (fun a => by rw [Category.assoc, Category.assoc, hψ]))
    rw [v]
    have w₁ := (hu (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Box2
end GlobalTheory.TensCub

namespace GlobalTheory.TensCub

def tensP {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W)
    (k : (Fin r × Fin r) × Fin 4) : D'.P.A ⟶ D.P.A :=
  ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2

theorem tensorMap_left {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : (tensP T k).left = tensφ T.pr k := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m <;> rfl

theorem isMonHom_tensorMap {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : IsMonHom (tensP T k) := by
  letI := D.P.isAb.comm
  have := T.pr_hom k.1.1
  have := T.pr_hom k.1.2
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m
  · exact GlobalTheory.Serre.isMonHom_mul _ _
  · exact T.pr_hom i
  · exact T.pr_hom j
  · exact GlobalTheory.Serre.isMonHom_one

theorem cubV_tens : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (S : Over (Spec (CommRingCat.of R))) (z : S.left) (J : (S.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (S.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ x x' y : S ⟶ D'.P.A, (let om := fun p : S ⟶ D'.P.A => gm p.left z _ (T.w.s (fun k => J (p.left ≫ tensφ T.pr k), J' p.left)); cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ k : (Fin r × Fin r) × Fin 4, cubV D.cub z J (x ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (x' ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (y ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) ^ tensε W k) := by
  intro hG R _ _ D D' r W T S z J J' hJ hJ' x x' y om
  let P := tensP T
  let ρ : (Fin r × Fin r) × Fin 4 → ((G3 D'.P.A).left ⟶ (G3 D.P.A).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ D'.P.A (x3 D'.P.A) a ≫ tensφ T.pr k = ρ k ≫ thφ D.P.A (x3 D.P.A) a := fun k a => by
    rw [← tensorMap_left T k]
    letI := isMonHom_tensorMap T k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (a b c : T ⟶ D'.P.A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := tensφ T.pr) (εp := tensε W) D.P.isLB D'.P.isLB T.w T.w_gen (ε := thε) hψ
    D'.cub.isGen D.cub.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV D'.cub s I') := isCub_cubV D'.cub hI'
      have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I) := isCub_cubV D.cub hI
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
        (fun q => bwg T.w q s (fun i => I (q ≫ tensφ T.pr i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := isMonHom_tensorMap T k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ tensε W k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bwg T.w q z (fun i => J (q ≫ tensφ T.pr i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

end GlobalTheory.TensCub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (S : Over (Spec (CommRingCat.of R))) (z : S.left) (J : (S.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (S.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ x x' y : S ⟶ D'.P.A, (let om := fun p : S ⟶ D'.P.A => gm p.left z _ (T.w.s (fun k => J (p.left ≫ tensφ T.pr k), J' p.left)); cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ k : (Fin r × Fin r) × Fin 4, cubV D.cub z J (x ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (x' ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (y ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) ^ tensε W k) := by
  first | exact @GlobalTheory.TensCub.cubV_tens | exact GlobalTheory.TensCub.cubV_tens | (intros; apply GlobalTheory.TensCub.cubV_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyOfPullbackFiniteSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyOfPullbackFiniteSurjective
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_fam_of_pull : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left],
    IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left)
    (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB →
    ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  intro S A U U' _ _ hA p hfin hsurj N' h c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hL a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    have e : lift a (u ≫ p) = lift a u ≫ (A ◁ p) := by ext <;> simp
    rw [evc, e, Over.comp_left, pull_comp, hc]
    rfl
  obtain ⟨M, hM, hMc⟩ := cls_surj (cls L hL - CechPic.pull (snd A U).left (evc hL (1 : U ⟶ A) (𝟙 U)))
  have form : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t = evc hL a t - evc hL (1 : Y ⟶ A) t := by
    intro Y a t
    rw [evc, hMc, map_sub, ← pull_comp, ← Over.comp_left, lift_snd, pull_evc, MonObj.comp_one, Category.comp_id]
    rfl
  have keyM : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hM a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    rw [form, key, key, h.add.evc_one h.isLB, sub_zero]
  refine ⟨M, ⟨hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [form, sub_self])) ?_⟩, ?_⟩
  · intro K _ _ s t
    haveI := hfin
    haveI := hsurj
    obtain ⟨b, hb⟩ := exists_lift_pt p.left t.left
    let t' : Over.mk s ⟶ U' := Over.homMk b (by
      rw [← Over.w p, ← Category.assoc, hb, Over.w t])
    have ht : t = t' ≫ p := Over.OverMorphism.ext hb.symm
    rw [ht]
    refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
    have e : ∀ a₀ : Y ⟶ A, evc (pull_isLB hM _) a₀ y = evc h.isLB a₀ (y ≫ t') := fun a₀ ↦ by
      rw [evc_ev hM, lift_fst, lift_snd_assoc, ← Category.assoc, keyM]
    rw [e, e, e]
    exact (isAdditive_iff h.isLB).1 h.add _ _ _ _
  · rw [same_iff hM h.isLB, Category.comp_id]
    exact keyM _ _ _

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyOfPullbackFiniteSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveFamily_of_pullback_finiteSurjective : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left], IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left) (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB → ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  first | exact @GlobalTheory.Pinch.exists_fam_of_pull | exact GlobalTheory.Pinch.exists_fam_of_pull | (intros; apply GlobalTheory.Pinch.exists_fam_of_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeTwoMulPadicValIntDiscr
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.RootDiscrExp

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem finrank_le_two_mul_padicValInt_discr (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (hp : p.Prime) (hd : (p : ℤ) ∣ discr E) : Module.finrank ℚ E ≤ 2 * padicValInt p (discr E) := by
  classical
  have := Fact.mk hp
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have ha : padicValInt p (discr E) = a := by
    rw [padicValInt, hdisc, Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hm
    have h1 := Int.natCast_dvd.1 hd
    rwa [hdisc, pow_zero, one_mul] at h1
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨P, hPmax, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hP : P.IsPrime := hPmax.isPrime
  have hpP : (p : 𝓞 E) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPo.over]
      exact Ideal.mem_span_singleton_self _
    rwa [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  have h := diffExp E p a m hp hm hdisc P hP hpP
  have hpos := count_span_pos E p hp hP hpP
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hI0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := span_nat_ne_bot p
  have hdvd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ differentIdeal ℤ (𝓞 E) := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact pow_multiplicity_dvd _ _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) p ((Submodule.mem_bot _).1 hpP)
  have fD := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 hP) hD0
  have hd' := fD.le_multiplicity_of_pow_dvd hdvd
  have hc : ∀ X : Ideal (𝓞 E), X ≠ ⊥ → (normalizedFactors X).count P = multiplicity P X := fun X hX =>
    (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 E)).count_normalizedFactors_eq_multiplicity hX
  rw [hc _ hD0, hc _ hI0] at h
  rw [hc _ hI0] at hpos
  rw [ha]
  generalize multiplicity P (differentIdeal ℤ (𝓞 E)) = k at h hd'
  generalize multiplicity P (Ideal.span {(p : 𝓞 E)}) = e at h hd' hpos
  generalize Module.finrank ℚ E = n at h ⊢
  have hk : k ≠ 0 := by
    rintro rfl
    have : a * e ≠ 0 := mul_ne_zero ha0 hpos.ne'
    apply this
    nlinarith
  have hek : e ≤ 2 * k := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  nlinarith [Nat.mul_le_mul_left n hek]

theorem half_le_delta_two_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type)
    [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ →
    (1 / 2 : ℝ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E 2 := by
  intro E _ _ _ _ I _ d φ h
  have h1 := finrank_le_two_mul_padicValInt_discr E 2 Nat.prime_two (by exact_mod_cast h.2.2.2.2.1)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h2 : (Module.finrank ℚ E : ℝ) ≤ 2 * (padicValInt 2 (discr E) : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp, le_div_iff₀ hn]
  linarith

end GlobalTheory.RootDiscrExp
end

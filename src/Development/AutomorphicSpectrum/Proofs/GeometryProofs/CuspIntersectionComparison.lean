module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeBound
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSeqCover
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBounds

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ChartCentre
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPrincipal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair

theorem weil_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (z : Sp ℂ ⟶ X) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ t.G.left) (g : ℕ) (u : HolUnif A (t.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hpb : IsGrpPullback A t.G z φ) (hAH : u.IsAH Hm χ)
    (tB : SAB H (Sp ℂ)) (m : SABMap tB t z)
    (hP : IsPrincipal tB) (N : ℕ) (ζ : ℂˣ) (a b : Fin g → ℂ) (hN : 0 < N) (ha : a ∈ u.Λ) (hb : b ∈ u.Λ)
    (x y : Over.mk z ⟶ t.G) (hx : x.left = (u.ex ((N : ℂ)⁻¹ • a)).left ≫ φ)
    (hy : y.left = (u.ex ((N : ℂ)⁻¹ • b)).left ≫ φ) (h : CubWeil t.cub N x y (unitOn ζ)) :
    (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm *ᵥ star b).im : ℝ) : ℂ) / N) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hL' := pull_isLB t.PP.isLB φ
  obtain ⟨ψ, hψ, e₀, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := z)
    (hpb.congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB tB.PP.isLB hL'
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hL'⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  have hak := amplePt _ _ (𝟙 _) _ _ ψ hψ _ _ tB.PP.isLB hL' e₀ hP.2.1 hP.2.2
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hψ
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 hd
      L := t.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpb ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpb fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := hak.1
      ktriv := hak.2 }
  haveI : IsCommMonObj A := hA.comm
  have tors : ∀ w : Fin g → ℂ, w ∈ u.Λ → u.ex ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul_hol, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (u.ker w).2 hw
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeMapOf hpb) t.PP t.cub
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil c' (tors a ha) (tors b hb)
  have hw' : (cubeMapOf hpb).F ≫ t.G.hom = A.hom ≫ z := hpb.1.w
  have mul : ∀ (T : Over (Sp ℂ)) (p q : T ⟶ A), Out.toBase hw' (p * q) = Out.toBase hw' p * Out.toBase hw' q :=
    fun T p q => Over.OverMorphism.ext (hpb.2 T p q _ _ rfl rfl).symm
  have h1 := cubWeil_of_isPullCubical _ _ z t.G A (cubeMapOf hpb) hw' mul _ _ t.cub c' hc N _ _ _ ξ hξ
  have h2 : CubWeil t.cub N x y ξ := cubWeil_congr (Category.id_comp z) hx hy h1
  obtain rfl : ξ = unitOn ζ := h2.unique h
  have hW₁ : Out.WeilIs Q.A Q.L N (u.ex ((N : ℂ)⁻¹ • a)) (u.ex ((N : ℂ)⁻¹ • b)) (unitOn ζ) :=
    (cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA (tors a ha) (tors b hb) _).1 hξ
  obtain ⟨Ef, hE, -, -, -, -, hWe⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hAH
  let c : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (Ef ⟨a, ha⟩ ⟨b, hb⟩ : ℂ) / N)) (Complex.exp_ne_zero _)
  have hW₂ := hWe N ⟨a, ha⟩ ⟨b, hb⟩ c hN rfl
  have e := ((GlobalTheory.abelianSchemeLaws_all.1.weil (Sp ℂ) Q N (𝟙_ _)).1 _ _ (tors a ha) (tors b hb)).unique hW₁ hW₂
  have e' : ζ = c := Units.ext (by
    have := congrArg (fun v : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom v.val) e
    simpa [unitOn] using this)
  rw [e']
  show Complex.exp _ = _
  have i := hE ⟨a, ha⟩ ⟨b, hb⟩
  congr 3
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) i

theorem cubWeil_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {Z : Scheme.{0}} (a : Z ⟶ S') {N : ℕ}
    {x y : Over.mk a ⟶ t'.G} {x₀ y₀ : Over.mk (a ≫ f) ⟶ t.G} (ex : x₀.left = x.left ≫ m.φ)
    (ey : y₀.left = y.left ≫ m.φ) {ζ : Γ(Z, ⊤)ˣ} (h : CubWeil t'.cub N x y ζ) : CubWeil t.cub N x₀ y₀ ζ := by
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y _ _ rfl rfl).symm
  have h1 := GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin N (Over.mk a) x y ζ h
  exact cubWeil_congr rfl ex ey h1

theorem exists_principal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : Flat.BdryChart Xo σ n a) {X : Scheme.{0}} {t : SAB H X}
    {jj : Sp C.R ⟶ X} (m : SABMap C.t t jj) {b : Fin n → ℂ} (hb : b ∈ Flat.punct n a 1) :
    ∃ (tB : SAB H (Sp ℂ)) (_ : SABMap tB t (spMap (C.ψ b) ≫ jj)), IsPrincipal tB := by
  obtain ⟨t', ⟨m₀⟩⟩ := exists_sab (C.pt b) C.tV
  obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₁ m₀
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₂ m₀
  obtain ⟨mX, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m mK
  obtain ⟨w₂, g₂, -⟩ := mx.lin
  obtain ⟨am, kt⟩ := amplePt _ _ _ _ _ mx.φ mx.cart _ _ Xo.univ.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Xo.univ.ample
    Xo.univ.ktriv
  rw [(C.pt_eq b hb).1] at mX
  exact ⟨t', mX, MorphismProperty.of_isPullback (P := @IsProper) mx.cart.1 Xo.univ.proper, am, kt⟩

end LevelTowerAlt.Val
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt.Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem chart_centre (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts) (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ)
    (ht₀ : t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1)) (z₀ : Sp ℂ ⟶ Or.𝔐.X) (hz₀ : CoordsAt Or.𝔐.ξ Dc.y z₀ ((Dc.chart a).γ t₀))
    (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (hsm : Or.IsSmallPart d s)
    (ν : ℝ) (hν : Or.𝔐.GeoPhi Or.sm z₀ s ν) :
    ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ : ℝ) (σ : CMType H → (𝓞 E →+* ℂ)) (pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ), 0 < ρ ∧ IsCMFam σ ∧ IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B σ b ∧ (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), t₀ + (ρ : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧ InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ Or.𝔐.LabVal (pt u) Or.sm σ ∧ (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧ (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G), (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧ FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) ∧
      ∃ I : Submodule (𝓞 E) Λ, IsSaturated I ∧ IsIsoSub L.toLogPeriods.E I ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ‖GroundTheory.Heights₂.Heights.Regular.expCover a₀ w‖ < δ →
        Real.log ν - ε ≤ (Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi) +
          (L.riem w hw).logDet (fun τ i => b τ i (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) -
            Real.log ((L.riem w hw).nz σ I) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpq : 1 ≤ D.p + D.q := by
    have h1 := Or.N_eq
    have h2 := Dc.two_le_N
    omega
  have hfr := (((GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z₀ _ hz₀).2 d).2 s hsm).1
  have hval0 : ∀ i : CMType H × Fin (Dc.N - Dc.j), ∃ v : epsAt z₀ ⟶ Or.𝔐.t.G, Or.𝔐.M.ValAt z₀ (s i.1 i.2) v := fun i =>
    GlobalTheory.T.hodge_component_label_frame E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z₀ (Or.sm i.1) _ (s i.1) (Or.𝔐.all _) (hfr i.1 _) i.2
  obtain ⟨a₀, π, ρ₁, σ₀, C, jj, m, sc, hρ₁, hA⟩ := GlobalTheory.T.snc_chart_hodge_component_local hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 _ Dc.Bd (Dc.chart a) t₀
    d.c d.f (CMType H × Fin (Dc.N - Dc.j)) (fun i => s i.1 i.2) z₀ Or.bd ht₀ hz₀ d.inDom hval0
  obtain ⟨ρ₂, Λ, _, L₀, e, hρ₂, hρ₂1, hper, hRiem⟩ := GlobalTheory.T.boundary_chart_log_period_family E H D l (Xo l) σ₀ _ a₀ C hpq
  obtain ⟨Bf, hBd, hBe⟩ := GlobalTheory.T.holomorphic_endomorphism_family E H C.R C.t C.g _ C.M ρ₂ C.ψ e hρ₂
  have hnorm : ∀ u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ, ‖(ρ₂ : ℂ) • u‖ = ρ₂ * ‖u‖ := fun u => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ₂.le]
  have hsmρ : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ρ₂ := fun u hu => by
    rw [mem_ball_zero_iff] at hu ⊢
    rw [hnorm]
    nlinarith
  have hsm1 : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := fun u hu =>
    Metric.ball_subset_ball hρ₂1 (hsmρ u hu)
  have hsmd : DifferentiableOn ℂ (fun u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ => (ρ₂ : ℂ) • u)
      (Metric.ball 0 1) := (differentiable_id.fun_const_smul _).differentiableOn
  have hBhol : ∀ c x, DifferentiableOn ℂ (fun z => Bf ((ρ₂ : ℂ) • z) c x) (Metric.ball 0 1) := fun c x =>
    (hBd c x).comp hsmd hsmρ
  have hpb : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le,
      GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := fun w hw => ChartFree.expCover_mem_punct L₀.a_le hw
  have hclosed : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, ∀ c x, ∃ y, L₀.P w y =
      Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) c (L₀.P w x) := by
    intro w hw c x
    have hb := hsmρ _ (hpb w hw).1
    have h1 : e.ex _ (L₀.P w x) = 1 := ((hper w hw _).2 ⟨x, rfl⟩ : _)
    refine (hper w hw _).1 ?_
    show e.ex _ _ = 1
    rw [hBe _ hb, h1]
    haveI := C.t.act.hom c
    simp
  obtain ⟨instM, hact⟩ := GlobalTheory.T.log_periods_module_structure E _ a₀ C.g Λ L₀ (fun z => Bf ((ρ₂ : ℂ) • z)) hBhol hclosed
  have hInt : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ u ∈ Flat.punct _ a₀ 1) := by
    intro u hu
    obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 u hu)
    have h5 := Or.bd _ _ h3
    have h6 : Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ (ρ₂ : ℂ) • u ∈ Flat.punct _ a₀ 1 := by
      rw [← h4, h5, not_not]
    rw [h6]
    have hne : (ρ₂ : ℂ) ≠ 0 := by exact_mod_cast hρ₂.ne'
    constructor
    · rintro ⟨-, h⟩
      exact ⟨hu, fun i hi h0 => h i hi (by simp [h0])⟩
    · rintro ⟨-, h⟩
      exact ⟨hsm1 u hu, fun i hi => by simpa [hne] using h i hi⟩
  have hF : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, _ := fun w hw =>
    GlobalTheory.T.boundary_chart_hodge_map hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 σ₀ _ a₀ C jj m (Metric.ball 0 ρ₂) e
      ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) (Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w))
      (L₀.H (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) hpq (hsmρ _ (hpb w hw).1)
      ((hInt _ (hpb w hw).1).2 (hpb w hw)) (hRiem _ (hpb w hw)) (hBe _ (hsmρ _ (hpb w hw).1))
  have hinj : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, Function.Injective (L₀.P w) := by
    intro w hw
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    refine L₀.unimod.1 ?_
    ext y
    have h := L₀.im w hw x y
    rw [hx] at h
    simpa using h.symm
  have hw₀ : ∃ w₀, w₀ ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le := by
    refine ⟨fun k => if (k : ℕ) < a₀ then -1 else 0, fun i => ?_, fun k hk => ?_⟩
    · simp
    · simp [not_lt.2 hk]
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hadj : ∀ c c' : 𝓞 E, (c' : E) = IsCMField.complexConj E (c : E) → ∀ x y, L₀.E (c • x) y = L₀.E x (c' • y) := by
    intro c c' hc x y
    obtain ⟨A, _, φ, u, χ', -, -, -, -, -, h⟩ := hF w₀ hw₀
    have h1 := L₀.im w₀ hw₀ (c • x) y
    have h2 := L₀.im w₀ hw₀ x (c' • y)
    rw [hact w₀ hw₀] at h1
    rw [hact w₀ hw₀] at h2
    have h3 := h c c' hc (L₀.P w₀ x) (L₀.P w₀ y)
    have h4 : ((L₀.E (c • x) y : ℤ) : ℝ) = ((L₀.E x (c' • y) : ℤ) : ℝ) := by
      rw [← h1, ← h2]
      exact congrArg Complex.im h3
    exact_mod_cast h4
  let L : ActPeriods E _ a₀ C.g Λ :=
    { toLogPeriods := L₀
      adj := hadj
      B := fun z => Bf ((ρ₂ : ℂ) • z)
      B_hol := hBhol
      act := hact }
  obtain ⟨σa, hσ, hinl, hinr⟩ := GlobalTheory.T.holomorphic_points_of_component E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R jj _ C.ψ C.hol
  have hcm : IsCMFam (fun τ => σa (Or.sm τ)) := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h]
    · exact hinr
    · exact hinl
  have hdiffb : ∀ (r : C.R), DifferentiableOn ℂ (fun u => C.ψ ((ρ₂ : ℂ) • u) r) (Metric.ball 0 1) := fun r =>
    (C.hol.2 r).comp hsmd hsm1
  have hframe : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, ∀ τ
      (h : genPt Or.𝔐.ξ ⤳ centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj)),
      (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj), h⟩ := by
    intro u hu τ h
    obtain ⟨-, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    have h4 := (GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or _ _ h3).2 { d with inDom := h2 }
    exact (h4.2 s hsm).1 τ h
  have hEig : IsEigFrames (Metric.ball 0 1) L.B (fun τ => σa (Or.sm τ))
      (fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i)) := by
    refine ⟨fun τ k => differentiableOn_pi.2 fun i => hdiffb _, fun t ht τ => ?_⟩
    exact GlobalTheory.T.abelian_family_hodge_lattice E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R C.t jj m C.g _ C.M (Metric.ball 0 ρ₂) C.ψ e ((ρ₂ : ℂ) • t)
      (Bf ((ρ₂ : ℂ) • t)) (Or.sm τ) _ (s τ) (fun k => sc (τ, k)) σa (hsmρ t ht) (hBe _ (hsmρ t ht))
      (hσ _ (hsm1 t ht)) (hframe t ht τ) (fun k => (hA _ (hsm1 t ht)).2.2.2.2 (τ, k))
  refine ⟨a₀, C.g, Λ, inferInstance, instM, L, π, ρ₁ * ρ₂, fun τ => σa (Or.sm τ),
    fun u => spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj, fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i),
    mul_pos hρ₁ hρ₂, hcm, hEig, fun u hu => ?_, fun w hw => ?_, ?_⟩
  · have heq : t₀ + (((ρ₁ * ρ₂ : ℝ)) : ℂ) • (u ∘ π) = t₀ + (ρ₁ : ℂ) • (((ρ₂ : ℂ) • u) ∘ π) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      push_cast
      ring
    rw [heq]
    obtain ⟨h1, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    exact ⟨h1, h2, h3, fun i a' => hσ _ (hsm1 u hu) (Or.sm i) a', hInt u hu⟩
  · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, hdv, -⟩ := hF w hw
    have hbρ := hsmρ _ (hpb w hw).1
    choose v hv1 hv2 using (hA _ (hsm1 _ (hpb w hw).1)).2.2.2.2
    refine ⟨v, fun i => hv1 i, ?_⟩
    refine ⟨A, instA, φ, u, χ', hgp, hAH, fun a' p => ?_, hinj w hw, fun p => ?_, fun i => ?_⟩
    · show (u.ex (Bf _ a' p)).left ≫ φ = _
      have e1 : (u.ex p).left ≫ φ ≫ (Or.𝔐.t.act.act a').left = ((e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) p).left ≫ m.φ) ≫ (Or.𝔐.t.act.act a').left := by
        rw [← hex p, Category.assoc]
      rw [hex, e1, hBe _ hbρ, Over.comp_left, Category.assoc, Category.assoc, m.act]
    · rw [hlat p]
      exact hper w hw p
    · obtain ⟨v', h1, h2⟩ := hdv _ _ (Flat.FrameDeriv.isDerivAt0_pt e hbρ (sc i))
      exact ⟨v', by rw [h1, hv2 i, Category.assoc], h2⟩

  · have h0 : (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := Metric.mem_ball_self one_pos
    obtain ⟨-, -, co0, -, hv0⟩ := hA _ (hsm1 0 h0)
    have hT0 : t₀ + (ρ₁ : ℂ) • (((ρ₂ : ℂ) • (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ)) ∘ π) = t₀ := by
      funext i; simp
    rw [hT0] at co0
    have hz : z₀ = spMap (C.ψ ((ρ₂ : ℂ) • 0)) ≫ jj :=
      GlobalTheory.T.normal_scheme_coords_injective _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie (fun x => ⟨Or.𝔐.normal.1 x, Or.𝔐.normal.2 x⟩) Or.𝔐.all _ _ _ hz₀ co0
    rw [hz] at hν
    obtain ⟨P, V, _, _, MV, ρV, I₀, hf, σ', bz, g1, g2, g3, g4, g5, g6⟩ := hν
    have hσ' : σ' = fun τ => σa (Or.sm τ) := funext fun τ => RingHom.ext fun a' =>
      WeightSheet.valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (g3 τ a') (hσ _ (hsm1 0 h0) (Or.sm τ) a')
    rw [hσ'] at g6
    refine centre_phi C m hρ₂ hρ₂1 e L (fun w hw => ⟨hper w hw, fun N ζ x x' hN hc => ?_⟩) (hBe _ (hsmρ 0 h0)) _ _
      (fun τ k => sc (τ, k)) (fun _ _ => rfl) hcm hEig P MV ρV I₀ hf g1 g2 g4 bz (fun τ k => ?_) g6
    · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, -, -⟩ := hF w hw
      have hpp : (ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := by
        obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 _ (hpb w hw).1)
        exact h4.1 fun hb => (Or.bd _ _ h3).1 hb ((hInt _ (hpb w hw).1).2 (hpb w hw))
      obtain ⟨tB, mB, hP⟩ := exists_principal C m hpp
      have hw' : ∀ p, ((e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) p).left ≫ m.φ) ≫ Or.𝔐.t.G.hom =
          spMap (C.ψ ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ≫ jj := fun p => by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (e.ex _ p)]
        rfl
      have h1 := cubWeil_push m _ (x₀ := Over.homMk _ (hw' _)) (y₀ := Over.homMk _ (hw' _)) rfl rfl hc
      have h2 := weil_fibre Or.𝔐.t _ A φ _ u _ χ' hgp hAH tB mB hP N ζ (L₀.P w x) (L₀.P w x') hN
        ((hlat _).2 ((hper w hw _).2 ⟨x, rfl⟩)) ((hlat _).2 ((hper w hw _).2 ⟨x', rfl⟩)) _ _ (hex _).symm (hex _).symm h1
      rw [L₀.im w hw] at h2
      exact_mod_cast h2
    · obtain ⟨v, hv1, hv2⟩ := g5 τ k
      obtain ⟨v', hv1', hv2'⟩ := hv0 (τ, k)
      rw [hv2, LieModel.ValAt.unique Or.𝔐.tie.gen hv1 hv1', hv2']

end LevelTowerAlt.Val
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionComparison
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.GVal

open LevelTowerAlt
open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric
open GroundTheory.Heights₂.Heights.Regular (logCover expCover logLift)

def aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def affInv {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  ((ρ : ℂ)⁻¹ • (t - t₀)) ∘ π.symm

theorem aff_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    aff t₀ ρ π (affInv t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [aff, affInv, Function.comp, h]


open scoped ComplexOrder in
theorem gram_det_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) (hu : LinearIndependent ℂ u) :
    0 < (R.gram u).det.re := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  have hM : (R.Hmᵀ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := R.pos x hx
    have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
    rw [Complex.pos_iff]
    exact ⟨by rw [e]; exact h1, him.symm⟩
  let C : Matrix (Fin g) (Fin m) ℂ := (Matrix.of u)ᵀ
  have hC : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hu
  have e : R.gram u = Cᴴ * R.Hmᵀ * C := by
    ext a b
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply, C]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hp := (hM.conjTranspose_mul_mul_same hC).det_pos
  rw [← e] at hp
  exact (Complex.pos_iff.1 hp).1

theorem hodgeInnerProduct_of_fibreLatticeVector {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem point_formula (Or : CptOrigin Y S₀ Dc Hd) {z : Sp ℂ ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (co : CoordsAt Or.𝔐.ξ Dc.y z w) (hI : Or.𝔐.Interior z) (hG : Top.Given) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s)
    {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ)
    (x : CMType H → Fin (Dc.N - Dc.j) → Fin g → ℂ) (hx : ∀ τ, LinearIndependent ℂ (x τ))
    (v : CMType H × Fin (Dc.N - Dc.j) → (epsAt z ⟶ Or.𝔐.t.G)) (hv : ∀ i, Or.𝔐.M.ValAt z (s i.1 i.2) (v i))
    (hfib : FibreLatVec Or.𝔐.t z R (fun i => x i.1 i.2) v) :
    phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      ((Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi) + R.logDet x) / 2 := by
  obtain ⟨-, hP⟩ := GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z w co
  obtain ⟨-, hP2⟩ := hP d
  obtain ⟨-, -, hform⟩ := hP2 s hs
  let Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ := fun τ =>
    Matrix.of fun p q => (Real.pi : ℂ) * R.ip (x τ p) (x τ q)
  have hΓ : ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ) := fun τ =>
    ⟨fun p => v (τ, p), fun p => hv (τ, p), fun p q =>
      hodgeInnerProduct_of_fibreLatticeVector hfib (fun i => (hv i).isTanAt) (τ, p) (τ, q)⟩
  have hdet : ∀ τ, Real.log (Γ τ).det.re = ((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi +
      Real.log (R.gram (x τ)).det.re := by
    intro τ
    have hpos := gram_det_pos R (x τ) (hx τ)
    have e1 : Γ τ = (Real.pi : ℂ) • R.gram (x τ) := by
      ext p q; rfl
    rw [e1, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Real.log_mul (pow_ne_zero _ Real.pi_ne_zero) hpos.ne', Real.log_pow]
  have h1 := hform hI Γ hΓ
  simp only [hdet, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  exact h1

theorem fibreLat_of_vec {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) : FibreLat t z R := by
  obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun i => i.elim⟩

end Pt

open GroundTheory.Heights₂.Heights.Regular (logCover expCover logLift)

namespace Val

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] {y : (Σ k, J k) → Ω}

theorem inFrameDomain_torus {cc : (k : K) → J k} {f : Ω} {z : (Σ k, J k) → ℂ} (h : InFrameDomain y cc f z)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : InFrameDomain y cc f (torusSmul c z) := by
  obtain ⟨h1, v, ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩, hv⟩ := h
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨fun k => mul_ne_zero (hc k) (h1 k), _, ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩, hv⟩
  · unfold torusSmul
    rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · unfold torusSmul
    rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem torusSmul_inv {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
  funext p
  simp [torusSmul, hc]

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem torusSmul_inv' {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    torusSmul c (torusSmul (fun k => (c k)⁻¹) z) = z := by
  funext p
  simp [torusSmul, hc]

theorem factor_near {u : Ω} {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) (hv : valAt y u w ≠ 0)
    (cc : (k : K) → J k) (hc : ∀ k, w ⟨k, cc k⟩ ≠ 0) (a : K → ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w' in 𝓝 w, w' ∈ mcPts (mCoordIdeal y) →
      Real.log (‖valAt y u w‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ a k) - ε ≤
        Real.log (‖valAt y u w'‖ * ∏ k, ‖w' ⟨k, cc k⟩‖ ^ a k) := by
  have hex : ∃ v, IsValueAt y u w v := by
    by_contra hn
    exact hv (dif_neg hn)
  obtain ⟨v₀, dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩ := hex
  have e0 : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = v₀ :=
    valAt_eq hw ⟨dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩
  have c1 := (MvPolynomial.continuous_eval (MvPolynomial.map (Int.castRingHom ℂ) pg)).continuousAt (x := w)
  have c2 := (MvPolynomial.continuous_eval (MvPolynomial.map (Int.castRingHom ℂ) ph)).continuousAt (x := w)
  have c3 : ContinuousAt (fun w' : (Σ k, J k) → ℂ => ∏ k, ‖w' ⟨k, cc k⟩‖ ^ a k) w :=
    tendsto_finsetProd _ fun k _ =>
      ((continuous_apply (⟨k, cc k⟩ : Σ k, J k)).norm.continuousAt.zpow₀ _ (Or.inl (norm_ne_zero_iff.2 (hc k))))
  have hne0 : ‖MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) pg) /
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) ph)‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ a k ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.2 (by rw [← hv₀, ← e0]; exact hv))
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))
  have c4 := (((c1.div c2 hhne).norm.mul c3).log hne0).eventually (lt_mem_nhds (sub_lt_self _ hε))
  filter_upwards [c4, c2.eventually_ne hhne] with w' h1 h2 hw'
  have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w' = _ :=
    valAt_eq hw' ⟨dg, pg, ph, hpg, hph, hne, heq, h2, rfl⟩
  rw [e0, hv₀, e1]
  exact h1.le

end Free

theorem exists_lift {n a : ℕ} (h : a ≤ n) {u : Fin n → ℂ} (hu : u ∈ Flat.punct n a 1) :
    ∃ w ∈ logCover h, expCover a w = u := by
  have h1 : ∀ k, ‖u k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hu.1)
  refine ⟨logLift a u, ⟨fun i => ?_, fun k hk => ?_⟩, funext fun k => ?_⟩
  · have hi : ((Fin.castLE h i : Fin n) : ℕ) < a := i.2
    simp only [logLift, if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.2 (hu.2 _ hi)) (h1 _)
  · simp only [logLift, if_neg (not_lt.2 hk)]
    exact h1 k
  · by_cases hk : (k : ℕ) < a
    · simp only [expCover, logLift, if_pos hk]
      exact Complex.exp_log (hu.2 k hk)
    · simp only [expCover, logLift, if_neg hk]

theorem neg_log_nz_le {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) {m : ℕ} (hσ : IsCMFam σ)
    (hr : R.HasRank σ m) (hm : 1 ≤ m) {I : Submodule (𝓞 E) Λ} (h1 : IsSaturated I) (h2 : IsIsoSub R.form I) :
    -Real.log (R.nz σ I) ≤ R.cuspW σ := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ R σ m hσ hr hm
  by_cases hI : I = ⊥
  · have : R.nz σ I = 1 := by
      refine dif_neg ?_
      rintro ⟨r, v, hr1, hv, hli, -⟩
      have := hv ⟨0, hr1⟩
      rw [hI, Submodule.mem_bot] at this
      exact hli.ne_zero _ this
    rw [this, Real.log_one, neg_zero]
    exact h4
  · exact (h3 I ⟨hI, h1, h2⟩).1

end Val


open Val in
theorem corrW_lower_near : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ), Or.𝔐.IsCuspWeight Or.sm U → CoordsAt Or.𝔐.ξ Dc.y z w → Or.PhiWeight z w x → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w' ∈ Dc.Xo, ‖w' - w‖ < δ → x - ε ≤ corrW Hd U w' := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or U z w x hU hz hx ε hε
  obtain ⟨d, s, ν, hs, hν, -, rfl⟩ := hx
  have hw : w ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).2 ⟨z, Or.𝔐.all _, hz⟩
  obtain ⟨a, t₀, ht, cw, hcw, hwe⟩ := Dc.chart_cover w hw
  have ht₀ : t₀ ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := mem_ball_zero_iff.2 (by linarith)
  have hγ : (Dc.chart a).γ t₀ = torusSmul (fun k => (cw k)⁻¹) w := by rw [hwe, torusSmul_inv hcw]
  have hci : ∀ k, (cw k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hcw k)
  have hz₀ : CoordsAt Or.𝔐.ξ Dc.y z ((Dc.chart a).γ t₀) := by
    rw [hγ]
    exact WeightSheet.coordsAt_torusSmul _ hz hci
  have hd₀ : InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ t₀) := by
    rw [hγ]
    exact inFrameDomain_torus d.inDom hci
  obtain ⟨a₀, g, Λ, i₁, i₂, L, π, ρ, σ, pt, b, hρ, hσ, hb, hu, hfib, I, hI1, hI2, hlim⟩ :=
    chart_centre hG Or a t₀ ht₀ z hz₀ { d with inDom := hd₀ } s hs ν hν
  obtain ⟨δ₁, hδ₁, hlim⟩ := hlim ε hε
  obtain ⟨V, T, hV, hV0, hT, hT0, hVT⟩ := GlobalTheory.T.chart_local_analytic_trivialization K J II (CMType H) Ω W Dc a t₀ ht₀
  have hv0 : valAt Dc.y d.u w ≠ 0 :=
    (((GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z w hz).2 d).2 s hs).2.1
  have c1 : Tendsto (torusSmul (fun k => (cw k)⁻¹)) (𝓝 w) (𝓝 ((Dc.chart a).γ t₀)) := by
    rw [hγ]
    refine Continuous.tendsto ?_ _
    unfold torusSmul
    fun_prop
  have c2 : Tendsto (fun w' => T (torusSmul (fun k => (cw k)⁻¹) w')) (𝓝 w) (𝓝 t₀) := by
    have := (hT _ hV0).continuousAt.tendsto
    rw [hT0] at this
    exact this.comp c1
  have c3 : Tendsto (fun w' => affInv t₀ ρ π (T (torusSmul (fun k => (cw k)⁻¹) w'))) (𝓝 w) (𝓝 0) := by
    have hc : Continuous (affInv t₀ ρ π) := by
      unfold affInv
      fun_prop
    refine (hc.tendsto' t₀ 0 ?_).comp c2
    funext i
    simp [affInv]
  have hev : ∀ᶠ w' in 𝓝 w, w' ∈ Dc.Xo → Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      Real.log ν / 2 - ε ≤ corrW Hd U w' := by
    filter_upwards [c1.eventually (hV.mem_nhds hV0), c3.eventually (Metric.ball_mem_nhds 0 hδ₁),
      c3.eventually (Metric.ball_mem_nhds 0 one_pos), ChartGeo.inFrameDomain_eventually Dc.y d.c d.f d.inDom,
      factor_near hw hv0 d.c d.inDom.1 Hd.aMu (half_pos hε)] with w' a1 a2 a3 a4 a5 hw'
    obtain ⟨-, c', hc', he⟩ := hVT _ ⟨a1, mcPts_smul Dc.arith.2.1.2.1 _ hci hw'.1⟩
    set u := affInv t₀ ρ π (T (torusSmul (fun k => (cw k)⁻¹) w')) with hud
    obtain ⟨-, -, co, hL, hint⟩ := hu u a3
    have e1 : t₀ + (ρ : ℂ) • (u ∘ π) = T (torusSmul (fun k => (cw k)⁻¹) w') := aff_affInv t₀ hρ π _
    rw [e1] at co
    have co' : CoordsAt Or.𝔐.ξ Dc.y (pt u) w' := by
      have := WeightSheet.coordsAt_torusSmul _ (WeightSheet.coordsAt_torusSmul _ co hc') hcw
      rwa [← he, torusSmul_inv' hcw] at this
    have hI : Or.𝔐.Interior (pt u) := not_not.1 fun hn => hw'.2 ((Or.bd _ _ co').2 hn)
    obtain ⟨q, hq, hqu⟩ := exists_lift L.a_le (hint.1 hI)
    clear_value u
    subst hqu
    obtain ⟨v, hv, hf⟩ := hfib q hq
    have k1 := point_formula Or co' hI hG { d with inDom := a4 } hs (L.riem q hq)
      (fun τ i => b τ i (expCover a₀ q)) (fun τ => (hb.2 _ a3 τ).1) v hv hf
    have k2 := WeightSheet.eq_cuspW_of_fibre Or hU co' hI _ (fibreLat_of_vec hf) hL
    have hr : (L.riem q hq).HasRank σ (Dc.N - Dc.j) := fun τ => by
      have h1 := finrank_span_eq_card (hb.2 _ a3 τ).1
      rw [(hb.2 _ a3 τ).2, Fintype.card_fin] at h1
      exact h1
    have hm : 1 ≤ Dc.N - Dc.j := by
      have h1 := Dc.j_le
      have h2 := Dc.two_le_N
      omega
    have k3 := neg_log_nz_le (L.riem q hq) σ hσ hr hm hI1 hI2
    have k4 := hlim q hq (mem_ball_zero_iff.1 a2)
    have k5 := a5 hw'.1
    unfold corrW
    rw [k1, k2]
    dsimp only
    linarith
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨δ, hδ, fun w' h1 h2 => h w' (by rwa [Metric.mem_ball, dist_eq_norm]) h1⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.GVal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionComparisonStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_intersection_comparison : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ), Or.𝔐.IsCuspWeight Or.sm U → CoordsAt Or.𝔐.ξ Dc.y z w → Or.PhiWeight z w x → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w' ∈ Dc.Xo, ‖w' - w‖ < δ → x - ε ≤ corrW Hd U w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GVal.corrW_lower_near | exact GlobalTheory.CompanionTheory.Ar.Cusp.GVal.corrW_lower_near | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GVal.corrW_lower_near <;> assumption)
end

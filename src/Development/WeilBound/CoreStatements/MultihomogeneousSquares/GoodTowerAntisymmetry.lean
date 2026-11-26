module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGiven
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGiven
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelArithDimensionBoundary
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerOriginVectorBundle
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Antisymmetry
public import Development.WeilBound.CoreStatements.CentralCharts.PotLoc
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.HtCancel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystem
public import Development.WeilBound.CoreStatements.FlagImmersions.AevalEqZeroOfMem
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.StSing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AntisymmetryStatement

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetryOf
section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.ChooseTwoAdd
noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights (antisymDegree)

theorem choose_two_add (j m : ℕ) : (j + m).choose 2 = j * m + j.choose 2 + m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, Nat.choose_succ_succ', Nat.choose_one_right, ih, Nat.choose_succ_succ' m 1,
      Nat.choose_one_right]
    ring

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω)
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem genPt_of_over {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' : Finset ℕ}
    {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'} {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h : A'.X ⟶ A.X}
    {i : Ω →+* Ω'} {j : A.Li →+ A'.Li} (a : PB.HodgeOver A' A h i j) :
    GlobalTheory.CompanionTheory.Ar.genPt A'.ξ₀ = GlobalTheory.CompanionTheory.Ar.genPt A.ξ₀ := by
  have e₁ : A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom A'.fn) ≫ A'.ξ₀ := A'.fn_over
  have e₂ : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := A.fn_over
  have e₃ : A'.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := a.1
  rw [← genPt_comp A'.fn, ← e₁, a.2.1, ← Category.assoc, e₃, Category.assoc, e₂, genPt_comp, genPt_comp]

theorem PB_eq_of_lines {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    {σ : Type} [Fintype σ] {S : PB.AnSys e σ} (Re Re' : PB.Realis S P) (hd : Re.deg = Re'.deg)
    (hl : ∀ a t, Re.line a t = Re'.line a t) (II : IntersectionSystem) : Re.PB II = Re'.PB II := by
  have : ∀ t w, Re.num II t w = Re'.num II t w := fun t w => by
    simp only [PB.Realis.num, hd, hl]
  refine congrArg (PB.formPoly (e + 1)) (funext fun w => ?_)
  simp only [PB.Realis.limNum, this]

theorem tie_of (hX : StX) (hAlg : StAlg) (hHt : StHt) (hSing : StSing) (hBase : StBase) : StTie := by
  intro hG hW E _ _ _ H D l Xo c Y _ S Ω₀ _ ξ₀ hξ₀ hSp hSd hp hq
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hRes : ResK.ResKStatement := hG.2.2.2.2.1
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨Ω, _, _, K₀, _, J₀, _, x₀, 𝔐, dg, ⟨k₀⟩, hgen, hcov, harith, hsnc, hR, hom⟩ :=
    hBase hRes hW E H D l Xo c Y S Ω₀ ξ₀ hξ₀ hSp hSd
  rw [← PB.card_mul_eq_dim D] at harith hsnc
  obtain ⟨⟨bW⟩, ⟨bO⟩⟩ := PB.nonempty_bases 𝔐
  obtain ⟨K, _, ι, _, Φ, _, y, M, 𝔐₁, tie, κ, v, φ, π, j, 𝔐', Fl, xdeg, e, ⟨-, -, -, -, hov, hR₁, -⟩,
    ⟨hcov₁, -, hsnc₁⟩, hv, htot, hFl⟩ := GlobalTheory.T.flag_model_exists_of_given hG E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 _ dg bW bO harith hcov
  obtain ⟨BM, hBM, hcj⟩ := GlobalTheory.T.base_metric_exists_of_given hG E H D l Xo c Y S K ι Φ y M 𝔐₁ tie dg hp hq hcov₁ (hsnc₁ _ hsnc)
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have hcard : 0 < Fintype.card (CMType H) := Fintype.card_pos_iff.2 hne
  have hN : antisymDegree (CMType H) (D.p + D.q) = Fintype.card (CMType H) * D.p * D.q +
      Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) := by
    show Fintype.card (CMType H) * (D.p + D.q).choose 2 = _
    rw [choose_two_add]; ring
  have hdim : dimFl (CMType H) (D.p + D.q) = antisymDegree (CMType H) (D.p + D.q) := by
    simp [dimFl, antisymDegree, Nat.choose_two_right]
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = antisymDegree (CMType H) (D.p + D.q) := by
    refine ⟨antisymDegree (CMType H) (D.p + D.q) - 1, Nat.sub_add_cancel ?_⟩
    rw [hN]
    have := Nat.mul_pos (Nat.mul_pos hcard hp) hq
    omega
  have hv' : IsArithVar (mCoordIdeal y) (d + 2) := by
    rw [show d + 2 = (d + 1) + 1 from rfl, hd, hN]; exact hv
  have hsub : D.p + D.q - D.p = D.q := by omega
  obtain ⟨FA, hFAc⟩ := GlobalTheory.T.flagModel_arith_dimension_boundary hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM hv' (by rw [hsub, hd, hN])
    hcj.1 hcj.2
  have hU := GlobalTheory.T.flag_analytic_data_uniformised K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA (by rw [hsub]) hd
  obtain ⟨Cv, CR, hCv, -, hCRl⟩ := GlobalTheory.T.flag_cover_degree_one_realisation K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA
  have FS : Nonempty (PB.FlagSys CR.Re D.p) := ⟨⟨M.j_le, hd, hU, fun τ a b hab hb =>
    (GlobalTheory.T.flag_cover_realisation_pullback hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA K ι Φ y M Cv CR hv' τ a b hab hb).some⟩⟩
  obtain ⟨⟨pr, j', hov', hR', -⟩, hroots, hdy, -⟩ := id htot
  choose sing hsd hho hsc using GlobalTheory.T.hodge_cpt_flag_xdeg E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl xdeg e hβ hroots
  have hrd : ∀ a, ((FA.Re.comap some).ref a).a = (Top.combLine sing (Cmp.fundOnRoot a)).a := fun a => by
    show (FA.Re.ref (some a)).a = ∑ r, _ • (sing r).a
    rw [FA.ref_some, RootFieldNumerics.Sq.sum_fundOnRoot]
    simp only [hsd]
    exact hdy a.1 a.2
  have hse : ∀ a x, (FA.Re.comap some).π x ∉ ReciprocityTheory.AnForm.P.bdry (FA.S.comap some).s →
      Real.log ((Top.combLine sing (Cmp.fundOnRoot a)).h ((FA.Re.comap some).R.lift x x)) =
        Real.log (((FA.Re.comap some).ref a).h ((FA.Re.comap some).R.lift x x)) +
          (FA.S.comap some).ph a ((FA.Re.comap some).π x) := fun a x hx => by
    have hx' : FA.Re.π x ∈ FA.S.open' := hx
    refine Eq.trans ?_ (FA.hom_eq a x hx')
    refine hSing E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ BM 𝔐' Fl xdeg e sing hBM htot hsd hho a _
      (FA.Re.R.mem x x (FA.Re.R.mem_U x)) (FA.pr (FA.Re.π x)) (fun h => hx' ?_) (FA.pr_eq x)
    show FA.S.s _ _ = 0
    rw [FA.s_eq]
    exact h
  have halg := hAlg E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ d BM FA hBM
  obtain ⟨x, hxa, hxs, hxc, hxl⟩ := hX _ _ K ι _ _ (FA.S.comap some) (FA.Re.comap some) sing (FA.S.reg none).1 hrd
    fun a t => hFAc (some a) t
  have hF : 0 < Module.finrank ℚ c.F := by haveI := c.fin; exact Module.finrank_pos
  have hFlpos : 0 < Fl.deg := by rw [hFl]; exact hcov.1
  have hKne : Nonempty K := ⟨(κ k₀).1⟩
  obtain ⟨hbir, -⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl hβ
  have hovT := hov'.trans hov
  have hht := hHt E H D l Xo c Y S Ω Φ K₀ K J₀ ι x₀ y 𝔐 𝔐' _ _ _ hovT (hR'.trans hR₁) hSd fun p hp => (hom p hp).2
  let M' : RootModel (CMType H) (D.p + D.q) :=
    { K := K, «ι» := ι, Ω := Φ, y := y, arith := by rw [hdim, hN]; exact hv, birational := hbir, xdeg := xdeg, x := x,
      x_deg := fun t r => (hxa t r).trans (hsd r), x_smooth := hxs, x_conj := hxc, kA := 1, kA_pos := one_pos,
      A := trivLine ι, A_smooth := contDiffOn_const, A_conj := fun _ => rfl,
      δ := Module.finrank ℚ c.F * Fl.deg, δ_pos := Nat.mul_pos hF hFlpos }
  have key : ∀ (D' : ℕ) (_ : d + 1 = D'), ∃ (Sy' : PB.AnSys D' (CMType H × Fin (D.p + D.q)))
      (Re' : PB.Realis Sy' (mCoordIdeal y)), (FA.S.comap some).degPoly = Sy'.degPoly ∧
      (∀ II, CR.Re.PB II = Re'.PB II) ∧ Cmp.AlgOver Re' ∧ Re'.deg = 1 ∧
      (∀ r, (Re'.ref r).a = (Top.combLine sing (Cmp.fundOnRoot r)).a) ∧
      (∀ r x, Re'.π x ∉ ReciprocityTheory.AnForm.P.bdry Sy'.s → Real.log ((Top.combLine sing (Cmp.fundOnRoot r)).h
        (Re'.R.lift x x)) = Real.log ((Re'.ref r).h (Re'.R.lift x x)) + Sy'.ph r (Re'.π x)) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ r, ∀ z ∈ mcPts (mCoordIdeal y),
        (x t r).h z = (Top.combLine (fun a => Re'.line a t) (Cmp.rootOnFund r)).h z := by
    intro D' h
    subst h
    exact ⟨_, FA.Re.comap some, rfl, PB_eq_of_lines _ _ ((CR.deg_eq.trans hCv).trans FA.deg_one.symm) hCRl, halg,
      FA.deg_one, hrd, hse, hxl⟩
  obtain ⟨Sy', Re', e1, e2, halg', hRd', hrd', hse', hxl'⟩ := key _ (hd.trans hdim.symm)
  let t : Cmp.HodgeTie Y S (Module.finrank ℚ c.F) M' :=
    { A := 𝔐', Fl := Fl, e := e, roots := hroots, sing := sing, sing_deg := hsd, hodge := hho,
      Sy := Sy', Re := Re', alg := halg', ref_deg := by convert hrd', sing_eq := by convert hse',
      line_eq := by
        classical
        have hi : (inferInstance : DecidableEq (CMType H)) =
            (fun a b => Subtype.instDecidableEq a b) := Subsingleton.elim _ _
        have hr : @Cmp.rootOnFund (CMType H) (inferInstance : DecidableEq (CMType H)) (D.p + D.q) =
            @Cmp.rootOnFund (CMType H) (fun a b => Subtype.instDecidableEq a b) (D.p + D.q) := by rw [hi]
        rw [hr] at hxl'
        exact hxl',
      δ_eq := rfl, discr := hSd, ht_vb := hht }
  exact ⟨M', t, d, _, K, _, ι, _, _, CR.Re, (genPt_of_over hovT).trans hgen,
    fun p hp => by rw [← hR p hp, ← hR₁, ← hR'], hRd', hFlpos, e1, FS, e2⟩

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.SqOf
noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem sq_of (hT : StTie) (hCmp : StCmp) : StSq := by
  intro hC hG hW E _ _ _ H D Xo l c Y _ T o II hX hII hp hq B a
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := TowerPropA.mono_spMap_ringOfIntegers c.F
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.toTowerOrigin.S B := by
    intro p hp hdv
    rw [o.toTowerOrigin.S_iff]
    refine ⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hdv 2) _
  obtain ⟨M', t, d, S, K, _, ι, _, P, Re, hgen, hR, hdeg, hpos, hS, hF, hPB⟩ :=
    hT hG hW E H D l (Xo l) c Y (o.S B) _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ (o.Or B a).𝔐.S_prime hdisc hp hq
  obtain ⟨-, ⟨x, hx⟩, -⟩ := HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.root_model_origin_compatibility E H D l (Xo l) c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx hmono (hX.1 a)
  obtain ⟨f₁, f₂⟩ := hCmp hIn hC II hII E H D l (Xo l) c _ _ Y _ _ _ _ t
    (RootFieldNumerics.Sq.tieOf (o.Or B a) ((o.Sys a).reg none).1 (o.omVB B a) t.discr hA) hmono hgen
    (fun p hp => (hX.2 B a p hp).trans (hR p hp).symm) hdeg (o.Or B a).Re_deg
  refine ⟨t.Fl.deg, d, S, K, _, ι, _, P, Re, Nat.cast_pos.2 hpos, by rw [o.j_eq]; exact hF, ?_, hS.trans f₂⟩
  rw [hPB II, f₁, map_smul]
  rfl

end SquareStatements
end
end

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

def GoodTowerAntisymmetry : Prop :=
  Cmp.CmpSt → Given → Out.WeilSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)]
    (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem),
    o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II)

theorem good_tower_antisymmetry_of (hX : StX) (hAlg : StAlg) (hHt : StHt) (hSing : StSing) (hBase : StBase) (hCmp : StCmp)
    (hI8 : AntisymmetryFibreSquares) : GoodTowerAntisymmetry := by
  intro hC hG hW E _ _ _ H D Xo l c Y _ T o II hE hII hp hq
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  exact hI8 GlobalTheory.T.antisymmetry' GlobalTheory.T.agreement_positive hG.2.2.2.2.2.2.2.2.2.1 II hII _ _ T _
    (sq_of (tie_of hX hAlg hHt hSing hBase) hCmp hC hG hW E H D Xo l c Y T o II hE hII hp hq)

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryOfSingularStatement
section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.EmbImmersion
noncomputable section

namespace SquareStatements

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

theorem emb_holoOn {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X)
    (B : FinHolAtlas e Y) (ψ : X → Y) (hψ : HoloMap A B ψ) (V : Set Y) (g : Y → ℂ) (hg : B.HoloOn V g) :
    A.HoloOn (ψ ⁻¹' V) (g ∘ ψ) := by
  intro j t ht
  obtain ⟨k, hk⟩ := B.cover (ψ ((A.chart j).symm t))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((B.chart k).open_source.preimage hψ.1)
  have hm : t ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source) := ⟨ht.1, hk⟩
  have hgk : AnalyticAt ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) t := hψ.2 j k t hm
  have hF : AnalyticAt ℂ (g ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) t) := by
    refine hg k _ ⟨(B.chart k).map_source hk, ?_⟩
    show (B.chart k).symm (B.chart k (ψ ((A.chart j).symm t))) ∈ V
    rw [(B.chart k).left_inv hk]
    exact ht.2
  refine (hF.comp hgk).congr ?_
  filter_upwards [hO.mem_nhds hm] with u hu
  simp only [Function.comp_apply, (B.chart k).left_inv hu.2]

theorem emb_immersion {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (ψ : X → Y) (π : Y → X)
    (hψ : HoloMap A B ψ) (hπ : HoloMap B A π) (h1 : ∀ x, π (ψ x) = x) (f : Y → W) (x : X) (j : Fin A.n)
    (k : Fin B.n) (hx : x ∈ (A.chart j).source) (hk : ψ x ∈ (B.chart k).source)
    (hf : (fderiv ℂ (fun y => f ((B.chart k).symm y)) (B.chart k (ψ x))).ker = ⊥) :
    (fderiv ℂ (fun y => f (ψ ((A.chart j).symm y))) (A.chart j x)).ker = ⊥ := by
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((B.chart k).open_source.preimage hψ.1)
  have hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source) := by
    refine ⟨(A.chart j).map_source hx, ?_⟩
    show ψ ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
    rw [(A.chart j).left_inv hx]
    exact hk
  have hg : AnalyticAt ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) := hψ.2 j k _ hm
  have hgt : (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) = B.chart k (ψ x) := by
    simp only [Function.comp_apply, (A.chart j).left_inv hx]
  have hh : AnalyticAt ℂ (A.chart j ∘ π ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) := by
    rw [hgt]
    refine hπ.2 k j _ ⟨(B.chart k).map_source hk, ?_⟩
    show π ((B.chart k).symm (B.chart k (ψ x))) ∈ (A.chart j).source
    rw [(B.chart k).left_inv hk, h1]
    exact hx
  have hid : (A.chart j ∘ π ∘ (B.chart k).symm) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j x)] id := by
    filter_upwards [hO.mem_nhds hm] with u hu
    simp only [Function.comp_apply, id, (B.chart k).left_inv hu.2, h1, (A.chart j).right_inv hu.1]
  have hfg : (fun y => f (ψ ((A.chart j).symm y))) =ᶠ[𝓝 (A.chart j x)]
      (fun y => f ((B.chart k).symm y)) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm) := by
    filter_upwards [hO.mem_nhds hm] with u hu
    simp only [Function.comp_apply, (B.chart k).left_inv hu.2]
  have hcomp : (fderiv ℂ (A.chart j ∘ π ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).comp
      (fderiv ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) = ContinuousLinearMap.id ℂ _ := by
    rw [← fderiv_comp _ hh.differentiableAt hg.differentiableAt, hid.fderiv_eq, fderiv_id]
  rw [← hgt] at hf
  rw [hfg.fderiv_eq, eq_bot_iff]
  intro v hv
  have hv' : fderiv ℂ ((fun y => f ((B.chart k).symm y)) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm)) (A.chart j x) v = 0 :=
    hv
  rw [Submodule.mem_bot]
  by_cases hF : DifferentiableAt ℂ (fun y => f ((B.chart k).symm y))
      ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))
  · rw [fderiv_comp _ hF hg.differentiableAt] at hv'
    have h0 : fderiv ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) v ∈
        (fderiv ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).ker :=
      hv'
    rw [hf, Submodule.mem_bot] at h0
    have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) hcomp
    simp only [ContinuousLinearMap.comp_apply, h0, map_zero, ContinuousLinearMap.id_apply] at this
    exact this.symm
  · have h0 : v ∈ (fderiv ℂ (fun y => f ((B.chart k).symm y))
        ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).ker := by
      have : fderiv ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) v = 0 := by
        rw [fderiv_zero_of_not_differentiableAt hF]
        rfl
      exact this
    rw [hf, Submodule.mem_bot] at h0
    exact h0

theorem stEmb : StEmb := by
  intro K _ ι _ P e σ S Re β b hJ hdeg hbr hβ hβP hbd
  have hd := Re.degree
  rw [hdeg, hbr] at hd
  have hbij : Function.Bijective Re.π := by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 (Re.π x) (by simp))
      have hx : x ∈ Re.π ⁻¹' {Re.π x} := rfl
      have hy : y ∈ Re.π ⁻¹' {Re.π x} := hxy.symm
      rw [ha] at hx hy
      exact hx.trans hy.symm
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 x (by simp))
      have : a ∈ Re.π ⁻¹' {x} := by rw [ha]; rfl
      exact ⟨a, this⟩
  obtain ⟨ψ, hψ, h1, h2⟩ := AnalyticReference.exists_inv S.A Re.R.A Re.π ∅ Re.holo hd hbij
  have hmc : ∀ z, z ∉ mcPts Re.J := by
    intro z hz
    rw [hJ] at hz
    have := hz.2 1 Submodule.mem_top
    simp at this
  have hI : imageZ (id : (Σ k, ι k) → Σ k, ι k) P = P := by
    ext f
    simp [imageZ]
  refine ⟨K, inferInstance, ι, inferInstance, id, id, fun x => ψ ⁻¹' Re.R.U (ψ x),
    fun x y => Re.R.lift (ψ x) (ψ y), β, b,
    ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩,
    ⟨fun x => (Re.R.isOpen_U _).preimage hψ.1, fun x => Re.R.mem_U (ψ x),
      fun x p => emb_holoOn S.A Re.R.A ψ hψ _ _ (Re.R.holo (ψ x) p), ?_, ?_, ?_, ?_, ?_⟩, ?_, hβ, ?_, ?_⟩
  · intro x y hy
    rw [hI]
    exact Re.R.mem (ψ x) (ψ y) hy
  · intro x x' y hy
    exact Re.R.compat (ψ x) (ψ x') (ψ y) hy
  · intro z hz
    rw [hI] at hz
    obtain ⟨x', hx'⟩ := Re.R.surj z hz (hmc z)
    refine ⟨Re.π x', ?_⟩
    show SameOrbit (Re.R.lift (ψ (Re.π x')) (ψ (Re.π x'))) z
    rw [h2]
    exact hx'
  · intro x x' h
    have := Re.R.inj (ψ x) (ψ x') (hmc _) h
    rw [← h1 x, ← h1 x', this]
  · intro x p hp j hj
    obtain ⟨k, hk⟩ := Re.R.A.cover (ψ x)
    exact emb_immersion S.A Re.R.A ψ Re.π hψ Re.holo h1 (fun u => affCoord p (Re.R.lift (ψ x) u)) x j k hj hk
      (Re.R.immersion (ψ x) (hmc _) p hp k hk)
  · intro x
    show SameOrbit (Re.R.lift (ψ (Re.π x)) (ψ (Re.π x))) fun p => Re.R.lift x x p
    rw [h2]
    exact ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩
  · rw [hI]
    exact hβP
  · intro x hx
    exact hbd (ψ x) (by rw [h1]; exact hx)

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.ExistsBase
noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

def overCpt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (A : HodgeCpt Y S y)
    {Ω₀ : Type} [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (h₀ : IsCptGen ξ₀) (i : Ω₀ →+* Ω)
    (hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i) : HodgeCpt Y S y where
  X := A.X
  ξ := A.ξ
  all := A.all
  tie := A.tie
  normal := A.normal
  f := A.f
  Ω₀ := Ω₀
  ξ₀ := ξ₀
  gen₀ := h₀
  cst := A.cst
  cst_over := A.cst_over
  fn := i
  fn_over := hi
  t := A.t
  m := A.m
  Li := A.Li
  M := A.M
  ρ := A.ρ
  act := A.act
  S_prime := A.S_prime
  R := A.R
  R_ge := A.R_ge
  tors := A.tors
  vb := A.vb


open Limits GeoModel in
theorem exists_base' (hRes : ResK.ResKStatement) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀]
    (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (hg : IsCptGen ξ₀) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k))
      (y : (Σ k, J k) → Ω) (M₁ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f₁ : M₁.X ⟶ Y.X)
      (y₀ : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Nonempty K ∧ (letI := i.toAlgebra; FiniteDimensional Ω₀ Ω) ∧
      Flat.NormalCpt M₁.ξ ∧ M₁.ξ ≫ f₁ = y₀ ≫ Y.j ∧ M₁.ξ ≫ f₁ = spMap i ≫ ξ₀ ∧
      (∀ p ∈ S, FullTorsion Y.t.G (M₁.ξ ≫ f₁) (p ^ 4)) ∧ (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4)) ∧
      SncPts M₁.ξ D.dim {p | Char0 M₁.ξ p ∧ p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} ∧
      Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨w₀, -⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω₀ ξ₀ hgen₀
  obtain ⟨cst, -⟩ := exists_cst (Y := Y) w₀
  haveI : CharZero Ω₀ := charZero_of_injective_ringHom cst.injective
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := ChgField.exists_field E H D l Xo c Y Ω₀ ξ₀ S hgen₀ hS
  obtain ⟨K₀, _, J₀, _, yc, X₀, ξ', f₀, bd₀, -, hall₀, htie₀, hf₀, -, -⟩ := GlobalTheory.T.exists_coords_of_generic_point hRes E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, M, h, -, -, hdom, hnorm, hsm⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes K₀ J₀ Ω₀ Ω i yc X₀ ξ' hfin hall₀ htie₀
  have hMξ : M.ξ ≫ h ≫ f₀ = spMap i ≫ ξ₀ := by
    have e : M.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ ξ' := hdom
    rw [← Category.assoc, e, Category.assoc, hf₀]
  have hgenM : GlobalTheory.CompanionTheory.Ar.genPt (M.ξ ≫ h ≫ f₀) ∈ genericPoints Y.X := by
    rw [hMξ]
    show GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) ∈ _
    rw [genPt_comp]
    exact hgen₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω _ hgenM
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c _ _ Y Ω₀ ξ₀ Ω y₀ i hinj hg (hy₀ ▸ hMξ)
  have htr : Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
    letI : Algebra Ω₀ Ω := i.toAlgebra
    haveI : FiniteDimensional Ω₀ Ω := hfin
    haveI : FaithfulSMul ℤ Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ Ω₀).mpr Int.cast_injective
    haveI : FaithfulSMul Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective Ω₀ Ω).mpr i.injective
    have htow := trdeg_add_eq ℤ Ω₀ (A := Ω)
    rw [hA, trdeg_eq_zero_iff.2 (Algebra.IsAlgebraic.of_finite Ω₀ Ω), add_zero] at htow
    exact htow.symm
  obtain ⟨U, hd, hAb⟩ := GlobalTheory.T.dense_open_generic_fibre E H D l Xo c Y Ω _ _ M (h ≫ f₀) y₀ hy₀
  have hU := GlobalTheory.T.generic_fibre_open_coords E H D l Xo c Y Ω K₁ J₁ y₁ M (h ≫ f₀) y₀ U hy₀ hsm htr
  have hnm : Tor.IsNormalScheme M.X := ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω M.ξ M.tie.gen M.all).2).1 hnorm
  obtain ⟨N, x, X, ξ, f₂, hall, htie, hf₂, hp⟩ := exists_patches_of_res hRes c.F M.X ((h ≫ f₀) ≫ Y.s)
    (GlobalTheory.T.projective_model_over_base E H D l Xo c Y Ω _ _ M (h ≫ f₀)) hnm U hd D.dim hU _ hAb Ω M.ξ M.tie.gen
  obtain ⟨K, _, J, _, y, M₁, g, hne, hdom₁, hn₁, hp₁⟩ := GlobalTheory.T.exists_projective_coord_model Ω X ξ N x D.dim
    (f₂ ⁻¹' ((h ≫ f₀) ⁻¹' abLocus Y.t.G)) hall htie hp
  have hg₁ : M₁.ξ ≫ g = ξ := by
    have e : M₁.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ := hdom₁
    rw [e]; simp
  have hξ₁ : M₁.ξ ≫ g ≫ f₂ ≫ h ≫ f₀ = M.ξ ≫ h ≫ f₀ := by
    rw [← Category.assoc, hg₁, ← Category.assoc, hf₂]
  refine ⟨Ω, inferInstance, inferInstance, K, inferInstance, J, inferInstance, y, M₁, g ≫ f₂ ≫ h ≫ f₀, y₀, i, hne, hfin, hn₁,
    hξ₁.trans hy₀, hξ₁.trans hMξ, fun p hp' => ?_, hroot, ?_, htr⟩
  · rw [hξ₁, hMξ]
    exact htors p hp'
  · convert hp₁ using 4
    simp

theorem stBase : StBase := by
  intro hRes hW E _ _ _ H D l Xo c Y S Ω₀ _ ξ₀ hξ₀ hS hSd
  obtain ⟨Ω, _, _, K₁, _, J₁, _, y₁, M₁, f₁, z₀, i, ⟨k₁⟩, hfin, hN, hz₀, hdomi, htors, hroot, hsnc₁, htr⟩ :=
    exists_base' hRes E H D l Xo c Y Ω₀ ξ₀ hξ₀ S hS
  have hgen₁ : f₁ (GlobalTheory.CompanionTheory.Ar.genPt M₁.ξ) ∈ genericPoints Y.X := by
    have e : GlobalTheory.CompanionTheory.Ar.genPt (M₁.ξ ≫ f₁) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
      rw [hdomi]; exact GeoModel.genPt_comp i ξ₀
    have h0 := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hξ₀
    rw [← e] at h0
    exact h0
  obtain ⟨K₂, _, J₂, _, y₂, bk, bx, A, g, -, -, hdom₂, hf₂, hR₂, hfree, hiso⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S (fun _ => 4) Ω K₁ J₁ y₁ M₁ f₁ z₀ hN hz₀ hgen₁ hS hSd
      (fun _ _ => le_rfl) htors hroot
  have hgA : A.ξ ≫ g = M₁.ξ := by
    have e : A.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hsncA : GeoModel.SncPts A.ξ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} :=
    GlobalTheory.T.snc_points_transfer_dominating Ω _ _ _ _ M₁.X A.X M₁.ξ A.ξ g D.dim _ M₁.all A.all M₁.tie A.tie hdom₂ hiso hsnc₁
  have hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i := by
    show A.ξ ≫ A.f = _
    rw [hf₂, ← Category.assoc, hgA]
    exact hdomi
  obtain ⟨bd, hbd, hbd'⟩ := GlobalTheory.T.snc_model_boundary_coords Ω A.X A.ξ K₂ J₂ y₂ D.dim
    {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} A.tie (fun p hp' => hp'.1) hsncA
  have hab : abLocus A.t.G = A.f ⁻¹' abLocus Y.t.G :=
    (Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x).symm
  letI algi : Algebra Ω₀ Ω := i.toAlgebra
  haveI : FiniteDimensional Ω₀ Ω := hfin
  haveI : Nonempty K₂ := ⟨bk k₁⟩
  refine ⟨Ω, inferInstance, inferInstance, K₂, inferInstance, J₂, inferInstance, y₂, overCpt A ξ₀ hξ₀ i hi,
    Module.finrank Ω₀ Ω, inferInstance, rfl, ⟨Module.finrank_pos, rfl⟩,
    (GlobalTheory.T.birational_of_transcendence_degree A.X Ω A.ξ K₂ J₂ y₂ _ A.tie htr).2, ⟨bd, hbd, fun z w hw => ?_⟩, fun p _ => congrFun hR₂ p, hfree⟩
  rw [hbd' z w hw]
  constructor
  · rintro ⟨h, -, h2⟩ hI
    have h3 : centre z ∈ abLocus A.t.G := hI
    rw [hab, hf₂] at h3
    exact h2 h3
  · intro hn
    refine ⟨A.all _, GlobalTheory.T.char_zero_centre_of_complex Ω A.X A.ξ z _ A.tie.gen, fun h => hn ?_⟩
    show centre z ∈ abLocus A.t.G
    rw [hab, hf₂]
    exact h

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.PolySmulOfSameSing
noncomputable section

namespace SquareStatements

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp RootFieldNumerics.Sq
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem cmp_arith {a b e₁ e₂ d₁ d₂ m : ℝ} (p₁ : e₁ ≠ 0) (p₂ : e₂ ≠ 0) (hm : m ≠ 0) (h : e₁ * (m * d₁) = e₂ * d₂) :
    (a / d₁ - (e₁ * a - e₂ * b) / (e₁ * d₁)) / m = b / d₂ := by
  rw [sub_div (e₁ * a), mul_div_mul_left _ _ p₁, sub_sub_cancel, div_div, show e₁ * d₁ * m = e₂ * d₂ by rw [← h]; ring,
    mul_div_mul_left _ _ p₂]

theorem poly_smul_of_sameSing (hN : SheetDecomposition.NumPull) (hIn : PB.Inputs) (hC : CmpSt) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K} {v₂ : (Σ k, ι₂ k) → Σ k, ι k}
    {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {σ : Type} [Fintype σ] {S₁ S₂ : PB.AnSys D σ}
    {P₁ : Ideal (MRing ι₁)} {P₂ : Ideal (MRing ι₂)} (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂)
    (h₁ : mCoordIdeal (y ∘ v₁) = P₁) (h₂ : mCoordIdeal (y ∘ v₂) = P₂) {β : MRing ι} {b : K → ℕ}
    (hv₁ : IsBlockMap κ₁ v₁) (hv₂ : IsBlockMap κ₂ v₂) (hy : IsArithVar (mCoordIdeal y) (D + 1))
    (hβ : IsMultiHomog β b) (hβy : β ∉ mCoordIdeal y) (hA₁ : AlgOver Re₁) (hA₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a)
    (hne : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0)
    {m : ℕ} (hm : m ≠ 0) (hdeg : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) * (m * Re₁.deg) =
      IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) * Re₂.deg) :
    Re₁.PB II = (m : ℝ) • Re₂.PB II ∧ S₁.degPoly = (m : ℝ) • S₂.degPoly := by
  have hne' : IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) ≠ 0 :=
    left_ne_zero_of_mul (hdeg ▸ mul_ne_zero hne (mul_ne_zero hm Re₁.deg_pos.ne'))
  have hW := PairTop.cmpSt_of_eq hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ P₁ P₂ Re₁ Re₂ h₁ h₂ β b hv₁ hv₂ hy hβ hβy
    hA₁ hA₂ hS
  have hG := fun w : Fin D → σ => intNum_cmp hN y hv₁ hv₂ hy hne hne' (fun j => (Re₁.ref (w j)).a) (fun j => (Re₂.ref (w j)).a)
    fun j => (hS (w j)).imp fun f => Exists.imp fun g h => h.1
  rw [h₁, h₂] at hG
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = e₁ at *
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = e₂ at *
  have hdeg' : (e₁ : ℝ) * (m * Re₁.deg) = e₂ * Re₂.deg := by exact_mod_cast hdeg
  have p₁ : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have p₂ : (e₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne'
  have q₁ : (Re₁.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re₁.deg_pos.ne'
  have pm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  constructor
  · rw [PB.Realis.PB, PB.Realis.PB, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly (D + 1)) (funext fun w => ?_)
    obtain ⟨C₃, s₀, -, h⟩ := GlobalTheory.T.agreement_positive hIn D σ S₁ 0 (S₁.reg (w 0)).1
    have c₁ := (h II hII _ _ _ Re₁).1 w
    have c₂ : Tendsto (fun t => Re₂.num II t w) (𝓝[>] 0) (𝓝 (Re₁.limNum II w / m)) := by
      have := (c₁.sub ((hW w).div_const ((e₁ : ℝ) * Re₁.deg))).div_const (m : ℝ)
      rw [zero_div, sub_zero] at this
      refine this.congr fun t => ?_
      exact cmp_arith p₁ p₂ pm hdeg'
    rw [show Re₂.limNum II w = _ from c₂.limUnder_eq, mul_div_cancel₀ _ pm]
  · rw [PB.AnSys.degPoly, PB.AnSys.degPoly, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly D) (funext fun w => ?_)
    have h := congrArg (Int.cast : ℤ → ℝ) (hG w)
    push_cast at h
    rw [← degNum_eq hIn Re₁, ← degNum_eq hIn Re₂, ← mul_assoc, ← mul_assoc, ← hdeg'] at h
    exact mul_left_cancel₀ (mul_ne_zero p₁ q₁) (h.trans (by ring))

theorem stCmp : StCmp := by
  intro hIn hC II hII E _ _ _ H D l Xo c O _ β Y S n M M' T T' hβ hgen hR hd hd'
  classical
  have hm : T.Fl.deg ≠ 0 := by
    obtain ⟨_, _, -, -, -, -, -, -, -, -, h, -⟩ := T.Fl.generic
    exact h.ne'
  have hsab : SABMap (twistSAB Xo.univ.t (HostAut.refl H)) Xo.univ.t (Iso.refl Xo.X).hom := by
    rw [(twistSAB_symm_refl E H Xo.X Xo.univ.t (HostAut.refl H)).2.2]
    exact (exists_sabMap_id E H Xo.X Xo.univ.t).choose
  obtain ⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩ :=
    GlobalTheory.T.twisted_hodge_tie_compare PositivityTheory.UnitarySelfGeneration.cmpHodgeTiedAlt GlobalTheory.T.theta_uniformisation_complex_abelian_varieties E H D l Xo c O β Y (HostAut.refl H) (Iso.refl Xo.X) hsab (Equiv.refl _) S n M M' T T'
      hβ (by simp) (fun τ => by ext; rfl)
      (Indep.imageCpt_refl_of_genPt E H D l Xo c O β Y S _ _ _ _ _ _ _ _ T.A T'.A hβ hgen) hR
  have hJ := GlobalTheory.T.block_pullback_herm_line M.K M.ι K ι κ v hbv
  have hJ' := GlobalTheory.T.block_pullback_herm_line M'.K M'.ι K ι κ' v' hbv'
  have hmpp : IsMultiProjPrime (mCoordIdeal y) := harith.2.1
  obtain ⟨hc1, -, -, hc4⟩ := GlobalTheory.T.iso_line_on_equivalence K ι (mCoordIdeal y)
    {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)
  choose Lr hLr using fun r => (hJ.1 (T.sing r)).exists
  choose Lr' hLr' using fun r => (hJ'.1 (T'.sing r)).exists
  refine poly_smul_of_sameSing SheetDecomposition.numPull hIn hC II hII T.Re T'.Re hP hP' hbv hbv' harith hmh hb T.alg T'.alg (fun a => ?_) hne hm
    (by rw [hd, hd', mul_one, hdeg])
  exact GlobalTheory.T.realisation_fibre_product_compatible K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy T'.Sy T.Re T'.Re b a a _ _ _ _ hbv hbv'
    (hc4 _ _ κ v _ _ _ _ hbv hLr) (hc4 _ _ κ' v' _ _ _ _ hbv' hLr') (T.ref_deg a) (T'.ref_deg a) (T.sing_eq a)
    (T'.sing_eq a) hmpp (hc1 _ Lr Lr' _ fun r => hiso r _ _ (hLr r) (hLr' r))

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.StFormB
noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

theorem stFormB : StForm := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ x 𝔐
  obtain ⟨hint, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J x 𝔐 RingOfIntegers.coe_injective
  have : IsLocallyNoetherian 𝔐.X := Cmp.HInterior.isLocallyNoetherian_of_coordTie 𝔐.ξ _ 𝔐.tie 𝔐.all
  let U : 𝔐.X.Opens :=
    ⟨abLocus 𝔐.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian 𝔐.t.G 𝔐.t.semi⟩
  have hU : genPt 𝔐.ξ ∈ U := hint
  obtain ⟨β, b, hb, hβ, hw⟩ := Cmp.HInterior.exists_homog_form_point 𝔐.ξ x 𝔐.tie U hU
  refine ⟨β, b, hb, hβ, fun z w hz hnot => ?_⟩
  by_contra hne
  have hmc : w ∈ mcPts (mCoordIdeal x) :=
    ⟨fun k => (hz.1 k).imp fun _ h => h.ne_zero, fun g hg => by
      rw [MvPolynomial.eval_map]
      exact ((tie_points _ _ 𝔐.ξ K J x 𝔐.tie ℂ).2.2 z _ (𝔐.all _) hz).1 g hg⟩
  obtain ⟨z', hz', hzU⟩ := hw w hmc hne
  have e : z = z' := GlobalTheory.T.normal_scheme_coords_injective _ _ 𝔐.ξ K J x 𝔐.tie (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩) 𝔐.all z z' w hz hz'
  subst e
  exact hnot hzU

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryTranspositionFactor
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace SquareStatements

theorem antisymmetry_transposition_factor : AntisymmetryFibreSquares := by
  intro hA hAg hIn II hII Ψ _ _ N _ T R hSq B hB c τ a b hab hbj lam
  have hN : 2 ≤ N := by
    have h1 := T.j_pos
    have h2 := T.j_lt
    omega
  have hjN : T.j ≤ N := T.j_lt.le
  have hdim : Top.dimFl Ψ N = antisymDegree Ψ N := by
    simp [Top.dimFl, antisymDegree, Nat.choose_two_right]
  have harith : IsArithVar (PFl Ψ N) (Top.dimFl Ψ N + 1) := hdim ▸ (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  obtain ⟨m, d, S', K, _, ι, _, P, Re', hm, ⟨F⟩, hPB, hdeg⟩ := hSq B c
  obtain ⟨⟨c₀, hc₀, hfl⟩, hprop⟩ := GlobalTheory.T.proportional' hIn Ψ N T.j hN hjN
  obtain ⟨-, hv⟩ := hprop (d + 1) S' F.dim F.unif
  have hnpos : 0 < R.n c := (GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) lam 0).1
  have hn0 : (R.n c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hnpos.ne'

  have hvol : m * ((R.n c : ℝ) * T.vol c) = PB.volOf S' := by
    have h1 := GlobalTheory.T.real_tower_geometric_agreement hIn II hII Ψ N (T.M 2 c) (R.Sys c) (R.n c) (R.tie 2 c) (rhoWt : Wt Ψ N) 0
    have h2 := GlobalTheory.T.flag_degree_polynomial_eval hIn II hII Ψ N (rhoWt : Wt Ψ N) hN
    have hρ : flagDeg (rhoWt : Wt Ψ N) ≠ 0 := by
      rw [← h2, hfl, eval_mul, eval_C]
      exact mul_ne_zero hc₀.ne' eval_rho_antisymDelta_ne
    have h3 : m * eval (PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (0 / ((T.M 2 c).kA : ℝ))) (R.Sys c).degPoly =
        PB.volOf S' * flagDeg (rhoWt : Wt Ψ N) := by
      rw [zero_div]
      have e : PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) 0 =
          fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) := rfl
      rw [e, AnSys_degPoly_gapS_zero, ← smul_eval, ← hdeg, ← PB.eval_toWt_gap, hv, eval_mul, eval_C, h2]
    rw [linA_zero_pow] at h1
    unfold RootTower.vol
    rw [← mul_div_assoc, h1, ← mul_div_assoc, h3, mul_div_cancel_right₀ _ hρ]

  have hpos : 0 < (R.Sys c).t₀ := ((R.Sys c).reg none).1
  have hconv : ∀ w, Tendsto (fun t => (R.tie B c).Re.num II t w) (𝓝[>] 0) (𝓝 ((R.tie B c).Re.limNum II w)) := by
    obtain ⟨C₃, s₀, -, h⟩ := hAg hIn (Top.dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) 0 hpos
    exact (h II hII _ _ _ (R.tie B c).Re).1
  have hnum : ∀ mu : Wt Ψ N, m * ((R.n c : ℝ) * T.PPc II B c (linRoot mu ^ (Top.dimFl Ψ N + 1))) =
      eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.toWt (Re'.PB II)) := by
    intro mu
    have h1 := ((GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) mu 0).2.2 hconv hpos).2
    rw [zero_div, linA_zero_pow] at h1
    have e : PB.gapS (fun x : Ψ × Fin N => mu x.1 x.2) 0 =
        fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => mu x.1 x.2) := rfl
    rw [e, Realis_PB_gapS_zero, ← PB.eval_toWt_gap] at h1
    rw [hPB, smul_eval]
    exact congrArg (m * ·) h1
  have hh : ∀ mu : Wt Ψ N, hhFl Ψ N II (linRoot mu ^ (Top.dimFl Ψ N + 1)) =
      eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.hFlPoly Ψ N II) :=
    fun mu => GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N mu hN harith

  have hQ := (hA hIn II hII Ψ N T.j d hN S' K ι P Re' F).2 (Equiv.swap (τ, a) (τ, b))
    ⟨τ, a, b, hab, by omega, rfl⟩
  have hE := congrArg (eval fun x : Ψ × Fin N => lam x.1 x.2) hQ
  rw [eval_rename, ← swapWt_uncurry] at hE
  simp only [map_sub, map_neg, smul_eval] at hE
  rw [← hnum, ← hnum, ← hh, ← hh, ← hvol] at hE
  apply mul_left_cancel₀ (mul_ne_zero hm.ne' hn0)
  linear_combination hE

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.IsMultiHomogRenameBaseInc
noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} (blk : σ → Option K)

def baseInc : (Σ k, baseIdx ι blk k) → Σ k, ι k := fun q => ⟨q.1.1, q.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem baseInc_injective : Function.Injective (baseInc (ι := ι) blk) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [baseInc, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl


open Classical in
def extDeg (b : NonPluckerBlocks blk → ℕ) : K → ℕ := fun k => if h : ∀ p, blk p ≠ some k then b ⟨k, h⟩ else 0

theorem isMultiHomog_rename_baseInc {β : MRing (baseIdx ι blk)} {b : NonPluckerBlocks blk → ℕ} (hβ : IsMultiHomog β b) :
    IsMultiHomog (rename (baseInc (ι := ι) blk) β) (extDeg blk b) := by
  classical
  intro m hm k
  rw [support_rename_of_injective (baseInc_injective blk)] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.1 hm
  by_cases h : ∀ p, blk p ≠ some k
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = m₀ ⟨⟨k, h⟩, i⟩ := fun i =>
      Finsupp.mapDomain_apply_of_injective (baseInc_injective blk) m₀ (⟨⟨k, h⟩, i⟩ : Σ k, baseIdx ι blk k)
    simp only [e, extDeg, dif_pos h]
    exact hβ m₀ hm₀ ⟨k, h⟩
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_of_notMem_range _ _ (by
        rintro ⟨q, hq⟩
        have : q.1.1 = k := congrArg Sigma.fst hq
        exact h (this ▸ q.1.2))
    simp only [e, extDeg, dif_neg h, Finset.sum_const_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem evC_rename_baseInc (z : (Σ k, ι k) → ℂ) (β : MRing (baseIdx ι blk)) :
    Cmp.evC z (rename (baseInc blk) β) = Cmp.evC (basePart blk z) β := by
  simp only [Cmp.evC, map_rename, eval_rename]
  rfl

end SlopeTestRemainingChoices

theorem alg_of : StEmb → StForm → StAlg := by
  intro hE hF E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie n d BM FA hH
  obtain ⟨β, b, hβ, hβn, hβz⟩ := hF E H D l Xo c Y S M.Ω (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐
  have hβ' := isMultiHomog_rename_baseInc M.blk hβ
  refine hE K ι (mCoordIdeal y) (d + 1) _ (FA.S.comap some) (FA.Re.comap some) (rename (baseInc M.blk) β)
    (extDeg M.blk b) FA.J_top FA.deg_one FA.br_empty hβ' ?_ ?_
  · rw [form_mem_mCoordIdeal_iff y hβ', aeval_rename]
    have e : y ∘ baseInc M.blk = algebraMap M.Ω Φ ∘ M.x := funext fun q => M.y_base q
    rw [e, aeval_algebraMap_apply]
    intro h0
    apply hβn
    rw [form_mem_mCoordIdeal_iff M.x hβ]
    exact (algebraMap M.Ω Φ).injective (by rw [h0, map_zero])
  · intro x hx
    have hx' : FA.pr (FA.Re.π x) ∈ ReciprocityTheory.AnForm.P.bdry BM.s := by
      have : FA.S.s (FA.Re.π x) (FA.Re.π x) = 0 := hx
      rw [FA.s_eq] at this
      exact this
    set xb := FA.pr (FA.Re.π x)
    have hmem : BM.Rb.lift xb xb ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem xb xb (BM.Rb.mem_U xb)
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).1 hmem
    have hnot : ¬ 𝔐.Interior z := fun hI => ((hH.interior xb z hz).2 hI) hx'
    have h0 : Cmp.evC (BM.Rb.lift xb xb) β = 0 := hβz z _ hz hnot
    obtain ⟨c₀, -, hc⟩ := FA.pr_eq x
    show Cmp.evC (FA.Re.R.lift x x) (rename (baseInc M.blk) β) = 0
    rw [evC_rename_baseInc, hc]
    unfold Cmp.evC at h0 ⊢
    rw [eval_smul_homog β b hβ c₀, h0, mul_zero]

end SquareStatements
end
end

section -- merged from Development.WeilBound.CoreStatements.MultihomogeneousSquares.SmoothComb
noncomputable section

namespace SquareStatements

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem smooth_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (Top.combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  refine contDiffOn_prod fun j _ => ?_
  rcases n j with m | m
  · simpa using (h j).pow m
  · simp only [zpow_negSucc]
    exact ((h j).pow (m + 1)).inv fun z hz => (pow_pos ((ℓ j).pos z hz) _).ne'

theorem stXB : StX := by
  intro Ψ _ _ N K _ ι _ P e S Re sing h0 hd hc
  classical
  let cl : ℝ → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then t else S.t₀
  have hcl : ∀ t, 0 < cl t ∧ cl t ≤ S.t₀ := fun t => by
    by_cases h : 0 < t ∧ t ≤ S.t₀
    · simp only [cl, if_pos h]; exact h
    · simp only [cl, if_neg h]; exact ⟨h0, le_rfl⟩
  refine ⟨fun t r => Top.combLine (fun a => Re.line a (cl t)) (Cmp.rootOnFund r), fun t r => ?_,
    fun t r => smooth_comb _ _ fun a => Re.line_smooth a _ (hcl t).1 (hcl t).2, fun t r z => ?_, ?_⟩
  · funext k
    have h1 : ∀ a, (Re.line a (cl t)).a k = -∑ m ∈ Finset.Iic a.2, (sing (a.1, m)).a k := fun a => by
      rw [Re.line_deg, hd]
      show (∑ r, _ • (sing r).a) k = _
      rw [RootFieldNumerics.Sq.sum_fundOnRoot]
      simp [Finset.sum_apply]
    have h2 := RootFieldNumerics.Sq.sum_root_fund r fun r' => ((sing r').a k : ℝ)
    show (∑ a, Cmp.rootOnFund r a • (Re.line a (cl t)).a) k = _
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, h1, smul_eq_mul]
    simp only [zsmul_eq_mul] at h2
    exact_mod_cast h2
  · show ∏ a, _ = ∏ a, _
    exact Finset.prod_congr rfl fun a _ => by rw [hc a (cl t) z]
  · filter_upwards [Ioo_mem_nhdsGT h0] with t ht r z _
    have : cl t = t := if_pos ⟨ht.1, ht.2.le⟩
    rw [this]

end SquareStatements
end
end

namespace SquareStatements

theorem antisymmetry_of_singular_statement (hSing : StSing) : GoodTowerAntisymmetry :=
  good_tower_antisymmetry_of stXB (alg_of stEmb stFormB) HeightCancellation.stHt hSing stBase stCmp
    antisymmetry_transposition_factor

end SquareStatements
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem SquareStatements.good_tower_antisymmetry : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  SquareStatements.antisymmetry_of_singular_statement HeightCancellation.stSing

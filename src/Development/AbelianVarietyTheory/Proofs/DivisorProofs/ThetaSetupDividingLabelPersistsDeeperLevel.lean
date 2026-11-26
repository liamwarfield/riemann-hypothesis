module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

theorem root_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {z : M.Z}
    (hn : IsIntegrallyClosed (M.O z)) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : u ∈ M.O z := by
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

theorem exists_eq_smul_of_smul_eq_zero {L k : ℕ} (hL : 0 < L) (hk : k ∣ L) (a : ZMod L) (ha : k • a = 0) :
    ∃ x : ZMod L, (L / k) • x = a := by
  obtain ⟨d, rfl⟩ := hk
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hL)
  haveI : NeZero (k * d) := ⟨hL.ne'⟩
  rw [Nat.mul_div_cancel_left _ hk]
  have h : ((k * a.val : ℕ) : ZMod (k * d)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, ha]
  obtain ⟨e, he⟩ := Nat.dvd_of_mul_dvd_mul_left hk ((ZMod.natCast_eq_zero_iff _ _).1 h)
  exact ⟨e, by rw [nsmul_eq_mul, ← Nat.cast_mul, ← he, ZMod.natCast_zmod_val]⟩

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem exists_div_of_isLab (X : Setup F W i) {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (c : CTrait X p z) {yy}
    (h : IsLab X ε c yy) {k : ℕ} (hk : 2 ≤ k) (hd : k ∣ X.S.r * X.S.N) :
    ∃ a : X.S.Gam, k • a = 0 ∧ X.M.Div X.S.th a z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hle, y₀, hy₀, u, l, j, hq, -⟩ := h
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one c.cen ((X.M.O z).algebraMap_mem a)
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    refine hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg ?_ (by positivity)))))
    rw [hq]
    exact mul_nonneg c.scale_pos.le (by
      exact_mod_cast qW_nonneg_of_posW W X.posW c.T.β c.T.symm (Basic₂.trait_nonneg c.T) (j w))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, ?_⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff c.cen (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes c.cen
  have e : ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ =
      ‖y₀ ⟨c₀ * X.S.th d, hth d⟩‖ * ‖X.M.val (gPt p ≫ c.y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul (z := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)))
      (fun w => by rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]) (hle (hth d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have hn' : ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ = sc := hn
  have b₁ := RatModel.norm_val_le_one c.cen (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ c.y) (X.S.th a / X.S.th d)))
  nlinarith

theorem exists_div_torsion (X : Setup F W i) {ε} (hε : IsDiagEnd F W X.ρ.P X.u ε) (z : X.M.Z) {k : ℕ} (hk : 2 ≤ k)
    (hd : k ∣ X.S.r * X.S.N) : ∃ a : X.S.Gam, k • a = 0 ∧ X.M.Div X.S.th a z := by
  haveI := X.M.qc
  haveI := X.imm
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z', hz', hcl⟩ := (isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩
  have hsp : z ⤳ z' := specializes_iff_mem_closure.2 hz'
  obtain ⟨p, _, y, hy, hU⟩ := exists_cen_main _ _ X.M z' hcl (X.π ⁻¹ᵁ i.opensRange)
    ⟨X.M.pt (closedPoint X.Ω₁), by
      show (X.M.pt ≫ X.π) _ ∈ Set.range i
      rw [X.comp]
      exact ⟨_, rfl⟩⟩
  obtain ⟨c, -⟩ := GCTrait.exists_cTrait g n F W Z i X X.one_le X.three_le X.odd X.imm p y (by
    rintro _ ⟨w, rfl⟩
    exact hU ⟨w, rfl⟩)
  obtain ⟨yy, hyy⟩ := exists_isLab g n F W Z i X X.one_le X.three_le X.odd X.imm X.e8 X.thetaInt X.projM ε hε p _ c
  obtain ⟨a, ha, hdv⟩ := exists_div_of_isLab X c hyy hk hd
  exact ⟨a, ha, hdv.of_specializes (hy ▸ hsp)⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (z₁ : X₁.M.Z) (x₀ : X₁.S.Gam), x₀ ∈ X₁.S.supI X₁.M z₁ → ∀ (z' : D.X.M.Z), D.q z' = z₁ → D.X.M.Div D.X.S.th (D.lab x₀) z' := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D z₁ x₀ hx₀ z' hz'
  have hx : X₁.M.Div X₁.S.th x₀ z₁ := hx₀
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N :=
    (D.dvd.trans (D.sq ▸ dvd_pow_self D.m two_ne_zero)).trans (dvd_mul_left _ _)
  obtain ⟨a, ha, hdv⟩ := exists_div_torsion D.X D.diag z'
    (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  choose x hxa using fun s => exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  obtain ⟨b, hb⟩ := D.lab_range x
  obtain rfl : D.lab b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := same_ratio D.same x₀ b
  set φ := algebraMap X₁.Ω₁ D.X.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : D.X.S.th (D.lab x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (D.X.M.O z') := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := D.X.normal
    exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z'
  have m₁ : D.X.S.th (D.lab b) * φ (X₁.S.th x₀) / (D.X.S.th (D.lab x₀) * φ (X₁.S.th b)) ∈ D.X.M.O z' :=
    root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ D.X.M.O z' := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨D.q ⁻¹ᵁ U, D.q.app U f, show D.q z' ∈ U from hz' ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp D.X.M.pt D.q U f).symm.trans ?_
    rw [D.gen, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp

end GlobalTheory.Poinc.DivDeep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (z₁ : X₁.M.Z) (x₀ : X₁.S.Gam), x₀ ∈ X₁.S.supI X₁.M z₁ → ∀ (z' : D.X.M.Z), D.q z' = z₁ → D.X.M.Div D.X.S.th (D.lab x₀) z' := by
  first | exact @GlobalTheory.Poinc.DivDeep.main | exact GlobalTheory.Poinc.DivDeep.main | (intros; apply GlobalTheory.Poinc.DivDeep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZero
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

theorem integrable_dbar_integral_eq_zero {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem dens_dbarAt_eq_sum {n : ℕ} (F : V n → Alt n) (v : V n) :
    dens (dbarAt F v) = ∑ a, ∑ S, dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dens, dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_re_dens_dbarAt_eq_zero {n : ℕ} (F : V n → Alt n)
    (hF : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S)) (hc : HasCompactSupport F) :
    ∫ v, (dens (dbarAt F v)).re = 0 := by
  have h (a : Fin n) (S : Finset (Fin (n + n))) :=
    integrable_dbar_integral_eq_zero (hF S)
      (hc.comp_left (g := fun α : Alt n => (bas n).repr α S) (by simp)) (coordVec a)
  have hi (a : Fin n) (S : Finset (Fin (n + n))) :
      Integrable fun v => dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) :=
    (h a S).1.mul_const _
  have hD : Integrable fun v => dens (dbarAt F v) := by
    simp only [dens_dbarAt_eq_sum]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S
  have h0 : ∫ v, dens (dbarAt F v) = 0 := by
    simp only [dens_dbarAt_eq_sum]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finsetSum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [integral_mul_const, (h a S).2, zero_mul]
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZeroStatement
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero : ∀ {n : ℕ} (F : V n → GlobalTheory.CxForm.Alt n), (∀ S, ContDiff ℝ 1 (fun v => (GlobalTheory.CxForm.bas n).repr (F v) S)) → HasCompactSupport F → ∫ v, (GlobalTheory.CxForm.dens (GlobalTheory.CxForm.dbarAt F v)).re = 0 := by
  first | exact @GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | exact GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | (intros; apply GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokes
set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem dbarAt_eq_zero_of_eventually {n : ℕ} {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) :
    dbarAt F v = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have : coefwise (fun f => GlobalTheory.dbar f v (coordVec a)) F = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    have hS : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [h] with x hx
      simp [hx]
    beta_reduce
    rw [GlobalTheory.dbar_congr hS, GlobalTheory.dbar_const]
    simp
  rw [this, mul_zero]

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_fn_mul_eq_zero (γ : A.Fld) (χ : M → ℝ) (j : A.ι) (w : V n)
    (h : w ∈ (A.e j).target → χ ((A.e j).symm w) = 0) : A.loc (A.fn χ * γ) j w = 0 := by
  unfold HolAtlas.loc
  split_ifs with hw
  · have key : ∀ x : A.Pt, x.pt = (A.e j).symm w → (A.fn χ * γ) x = 0 := fun x hx => by
      rw [Pi.mul_apply, HolAtlas.fn, hx, h hw]; simp
    exact key _ rfl
  · rfl

end GlobalTheory.CxForm.DbarLocStokes

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem integral_dbar_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hK
  set K := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hP : A.IsForm (A.fn χ * γ) :=
    ((GlobalTheory.T.isForm_one_add_mul_smul M n A).2 0 _ _ (A.isForm_fn hχ) hγ).2.1
  have hω : A.IsForm (A.dbar (A.fn χ * γ)) :=
    (GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A _ hP).2

  have hnear : ∀ (j : A.ι) (w : V n), w ∈ (A.e j).target → (A.e j).symm w ∉ K →
      A.loc (A.fn χ * γ) j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j w hw hwK
    have hW := ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl
    filter_upwards [hW.mem_nhds ⟨hw, hwK⟩] with u hu
    exact loc_fn_mul_eq_zero A γ χ j u fun _ => image_eq_zero_of_notMem_tsupport hu.2
  have hvan : ∀ x : A.Pt, x.pt ∉ K → A.dbar (A.fn χ * γ) x = 0 := by
    intro x hx
    refine dbarAt_eq_zero_of_eventually (hnear _ _ (x.ch.map_source x.2) ?_)
    rwa [x.ch.left_inv x.2]
  rw [GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart A _ i K hω hKc hK hvan]

  set F := A.loc (A.fn χ * γ) i with hFdef
  set B : Set (V n) := A.e i '' K with hBdef
  have hB : IsCompact B := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hK)
  have hBt : B ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hK hy)
  have hF0 : ∀ v ∉ B, F =ᶠ[𝓝 v] fun _ => 0 := by
    intro v hv
    filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hv] with u hu
    refine loc_fn_mul_eq_zero A γ χ i u fun ht => image_eq_zero_of_notMem_tsupport fun hk => hu ⟨_, hk, ?_⟩
    exact (A.e i).right_inv ht
  have hFs : HasCompactSupport F := HasCompactSupport.intro hB fun v hv => (hF0 v hv).self_of_nhds
  have hFC : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S) := fun S =>
    contDiff_iff_contDiffAt.2 fun v => by
      by_cases ht : v ∈ (A.e i).target
      · exact ((hP.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by norm_num)
      · have h0 : (fun v => (bas n).repr (F v) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
          filter_upwards [hF0 v fun h => ht (hBt h)] with u hu
          simp [hu]
        exact contDiffAt_const.congr_of_eventuallyEq h0
  have hloc : A.loc (A.dbar (A.fn χ * γ)) i = dbarAt F := by
    funext v
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht]
      simp only [HolAtlas.dbar, Pt.crd, Pt.ch, (A.e i).right_inv ht]
      rfl
    · rw [HolAtlas.loc, dite_eq_right ht, dbarAt_eq_zero_of_eventually (hF0 v fun h => ht (hBt h))]
  rw [hloc]
  exact GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero F hFC hFs

end GlobalTheory.CxForm.DbarLocStokes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokesStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  first | exact @GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | exact GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | (intros; apply GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.CxFormStokesBoth

open Set

section
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem eq_sum_fn_mul {N : ℕ} (χ : Fin N → M → ℝ) (hχ : ∀ y, ∑ j, χ j y = 1) (η : A.Fld) :
    η = ∑ j, A.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  have : (∑ j, A.fn (χ j)) = 1 := by
    funext x
    simp only [Finset.sum_apply, HolAtlas.fn, Pi.one_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Complex.ofReal_sum, hχ, Complex.ofReal_one, map_one]
  rw [this, one_mul]

theorem dbar_sum {N : ℕ} (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) :
    A.dbar (∑ j, α j) = ∑ j, A.dbar (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [HolAtlas.loc, dite_eq_left hw]
      exact Finset.sum_apply _ _ _
    · simp [HolAtlas.loc, hw]
  have hx := (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt hx
  have hcoeff : ∀ S u,
      GlobalTheory.dbar (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
        ∑ j, GlobalTheory.dbar (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have hsum : (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j, (bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w
      rw [hloc, map_sum, Finsupp.finsetSum_apply]
    rw [hsum, GlobalTheory.dbar_sum (fun j _ => hdiff j S), _root_.sum_apply]
  rw [Finset.sum_apply]
  simp only [HolAtlas.dbar, dbarAt, coefwise, hcoeff, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
end

theorem stokes : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  intro M _ _ _ _ _ _ n A η hη
  obtain ⟨N, c, χ, hs, hsupp, hone⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * η) := fun j =>
    FormMul.isForm_mul A _ _ (A.isForm_fn (hs j)) hη
  have hdiff : ∀ j, A.IsForm (A.del (A.fn (χ j) * η)) ∧ A.IsForm (A.dbar (A.fn (χ j) * η)) :=
    fun j => GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A _ (hf j)
  have hdec := eq_sum_fn_mul A χ hone η
  constructor
  · rw [hdec, GlobalTheory.T.holAtlas_del_finset_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)
  · rw [hdec, dbar_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).2)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes A η (χ j) (c j) hη (hs j) (hsupp j)

end GlobalTheory.CxFormStokesBoth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjective
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem theory_V_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
    Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧
      (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) = T.map (verschiebung (p_eq_zero p k) G) m) ∧
      (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[WittVector p k] T.M G),
        (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), T.map f (T.V H m) = T.V G (T.map f m) := by
  intro p _ T k _ _ _ G

  have tor : ∀ (K : PDivGroup p k) (m : T.M K), p • m = 0 → m = 0 := by
    intro K m hm
    exact T.base.eq_zero_of_pow_smul (G := K) trivial 1 m (by simpa only [pow_one] using hm)
  have Finj : ∀ K : PDivGroup p k, Function.Injective (T.F K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.V_F K x, ← T.V_F K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have Vinj : ∀ K : PDivGroup p k, Function.Injective (T.V K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.F_V K x, ← T.F_V K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have comm : ∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G),
      (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m) := by
    intro H φ hφ m
    apply Finj G
    rw [← hφ, T.F_V H m, T.F_V G, map_nsmul]
  refine ⟨Finj G, Vinj G, ?_, comm, ?_⟩
  · intro m
    have ht := frobTwist_module p T.base k G
    obtain ⟨n, hn⟩ := ht.1.2 (T.map (verschiebung (p_eq_zero p k) G) m)
    have hF : T.F G n = p • m := ht.2.2 m n hn
    have : n = T.V G m := Finj G (by rw [hF, T.F_V])
    rw [← this]; exact hn
  · intro H f m
    exact comm H (T.map f) (T.base.map_F trivial trivial f) m

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjectiveStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧
      (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) =
        T.map (verschiebung (p_eq_zero p k) G) m) ∧
      (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[WittVector p k] T.M G),
        (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
        T.map f (T.V H m) = T.V G (T.map f m) :=
  @GlobalTheory.Dieu.theory_V_verschiebung
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosure
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CycFin

theorem cycle_facts : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (z : X), topologicalKrullDim (closure ({z} : Set X)) = e → (∀ ε : ℤˣ, IsFiniteMeasure (part (fun i => (L i).pull (closι z) rfl) ε)) ∧ (∀ f : CxPts p σ → ℝ, Continuous f → CycIntg L f z) ∧ (∀ (U : X.Opens), z ∈ U → ∀ ε : ℤˣ, part (fun i => (L i).pull (closι z) rfl) ε (ptMap (closι z) rfl σ ⁻¹' ptsIn p σ U)ᶜ = 0) ∧ ∀ (M : MLine p σ) (s : M.B.Sec), z ∈ nonzeroLocus s → CycIntg L (M.logSec s) z := by
  intro hP F _ X p σ hp e L z hdim
  obtain ⟨hint, hgen, hdimeq, -⟩ := GlobalTheory.T.reducedClosureOfPoint_properties X z
  haveI := hint
  have hp' : IsProjOver (closι z ≫ p) := by
    obtain ⟨N, φ, hφ, rfl⟩ := hp
    exact ⟨N, closι z ≫ φ, inferInstance, Category.assoc _ _ _⟩
  haveI : IsLocallyNoetherian (clos z) := by
    obtain ⟨N, ι, _, -⟩ := hp'
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str F N)
  have hd : topologicalKrullDim (clos z) = ((e : ℕ) : WithBot ℕ∞) := hdimeq.trans hdim
  have H1 := GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F (clos z) (closι z ≫ p) σ e hp' hd (fun i => (L i).pull (closι z) rfl)
  have hpre : ∀ U : X.Opens, ptMap (closι z) rfl σ ⁻¹' ptsIn p σ U = ptsIn (closι z ≫ p) σ (closι z ⁻¹ᵁ U) := by
    intro U
    ext y
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  refine ⟨H1.1, fun f hf => H1.2 _ (hf.comp (PtsOver.continuous_map _ _ _)), ?_, ?_⟩
  · intro U hU ε
    have hgU : genericPoint (clos z) ∈ closι z ⁻¹ᵁ U := by
      show closι z (genericPoint (clos z)) ∈ U
      rw [hgen]; exact hU
    rw [hpre U]
    exact GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F (clos z) (closι z ≫ p) σ σ.injective hp' e _ ε _ hgU
  · intro M s hs
    obtain ⟨s', hnz, hnsq, -⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X (clos z) p (closι z ≫ p) σ (closι z) rfl M s
    have hgs : genericPoint (clos z) ∈ nonzeroLocus s' := by
      rw [hnz]
      show closι z (genericPoint (clos z)) ∈ nonzeroLocus s
      rw [hgen]; exact hs
    have H := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F (clos z) (closι z ≫ p) σ e hp' hd (fun i => (L i).pull (closι z) rfl)
      (M.pull (closι z) rfl) s' hgs
    have he : (M.pull (closι z) rfl).logSec s' = fun y => M.logSec s (ptMap (closι z) rfl σ y) := by
      funext y
      simp only [MLine.logSec, hnsq]
    unfold CycIntg
    rw [← he]
    exact H

end GlobalTheory.CycFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosureStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (z : X), topologicalKrullDim (closure ({z} : Set X)) = e → (∀ ε : ℤˣ, IsFiniteMeasure (part (fun i => (L i).pull (closι z) rfl) ε)) ∧ (∀ f : CxPts p σ → ℝ, Continuous f → CycIntg L f z) ∧ (∀ (U : X.Opens), z ∈ U → ∀ ε : ℤˣ, part (fun i => (L i).pull (closι z) rfl) ε (ptMap (closι z) rfl σ ⁻¹' ptsIn p σ U)ᶜ = 0) ∧ ∀ (M : MLine p σ) (s : M.B.Sec), z ∈ nonzeroLocus s → CycIntg L (M.logSec s) z := by
  first | exact @GlobalTheory.CycFin.cycle_facts | exact GlobalTheory.CycFin.cycle_facts | (intros; apply GlobalTheory.CycFin.cycle_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridAlphaBetaRestrictQuadraticPowRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridAlphaBetaRestrictQuadraticPowRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareResChars

theorem resEta_mul_pow {D : D7} {c η : (AE D)ˣ →* Circle} (hc : ResEta D c 0) (hη : ResEta D η 1) {n k : ℕ}
    (h : n % 2 = k % 2) : ResEta D (c * η ^ (n % 2)) k := by
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · rw [e, pow_zero, mul_one]
    exact resEta_parity hc (by omega)
  · rw [e, pow_one]
    exact resEta_parity (resEta_mul hc hη) (by omega)

theorem resEta_alpha_beta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), GlobalTheory.LFun.ResEta D.host.F D.host.E (alpha G t i j) (spW₁ G i j).rank ∧
      GlobalTheory.LFun.ResEta D.host.F D.host.E (beta G i j) (spW G i j).rank := by
  intro D T L sc G μ₀ hL t i j
  have hi := i.2
  have hj := j.2
  have hη := GlobalTheory.HeckeCharacterRestriction.resEta_eta hL
  have hμ := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hχ : ResEta D (G.ch.chi (D.R.m - i)) 0 := ⟨hη.1, fun η _ a => by
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (G.ch.chi_eq _ (by omega) (by omega)) (G.ch.triv _ (by omega) (by omega)) a⟩
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hpar : (spW₁ G i j).rank % 2 = (spW G i j).rank % 2 := by
    have e : (spW G i j).rank = (spW₁ G i j).rank + D.R.t + sLen D := by
      show (G.V (.grid (i + 1) (j + 1))).rank = (G.V (.grid i j)).rank + _ + _
      rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
      simp only [rankV]
      ring
    obtain ⟨p, hp⟩ := D.R.t_odd
    obtain ⟨q, hq⟩ := odd_sLen D
    omega
  have h1 : ResEta D (alpha G t i j) (spW₁ G i j).rank := resEta_mul_pow hμ hη rfl
  have h2 : ResEta D (beta G i j) (spW G i j).rank := resEta_mul_pow hχ hη hpar
  exact ⟨h1, h2⟩

end GlobalTheory.SquareResChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridAlphaBetaRestrictQuadraticPowRankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), GlobalTheory.LFun.ResEta D.host.F D.host.E (alpha G t i j) (spW₁ G i j).rank ∧
      GlobalTheory.LFun.ResEta D.host.F D.host.E (beta G i j) (spW G i j).rank := by
  first | exact @GlobalTheory.SquareResChars.resEta_alpha_beta | exact GlobalTheory.SquareResChars.resEta_alpha_beta | (intros; apply GlobalTheory.SquareResChars.resEta_alpha_beta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModel
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AffModel

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (g : X.functionField), 0 < e → g ∈ P.H e 0 → g ≠ 0 → ∃ (U : X.Opens) (h : genericPoint X ∈ U), (U : Set X) = NV P e 0 g ∧ IsAffineOpen U ∧ (∀ w : X.functionField, (∀ z ∈ U, RegAt z w) ↔ w ∈ (fnOf U h).range) ∧ Algebra.FiniteType ℤ (fnOf U h).range ∧ (∀ w : X.functionField, ∃ a ∈ (fnOf U h).range, ∃ b ∈ (fnOf U h).range, b ≠ 0 ∧ w = a / b) ∧ ∀ φ : (fnOf U h).range →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ U ∧ ∀ w : (fnOf U h).range, ratVal (w : X.functionField) y = φ w := by
  intro k _ X _ p D hV P hA e g he hg hg0
  obtain ⟨u, hu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P e).2 g hg
  have hN := GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P (e : ℤ) 0 g hg
  have : IsProper p := GlobalTheory.ProperFamily.isProper_of_isProjOver hV.isProjOver
  have hU : IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) := IsAmpleLB.isAffineOpen_nonzeroLocus p hA he u
  have hgen : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
    have := hN.2.1.2 hg0
    rw [hu] at this
    exact this
  set U := ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u with hUdef
  have : Nonempty U := ⟨⟨_, hgen⟩⟩
  have hfr := functionField_isFractionRing_of_isAffineOpen X U hU
  refine ⟨U, hgen, hu.symm, hU, ?_, ?_, ?_, ?_⟩
  · intro w
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hgen h
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩ z hz
      exact regAt_fnOf hz hgen a
  · have h1 : (algebraMap ℤ k).FiniteType := by
      have := hV.finite
      exact RingHom.finiteType_algebraMap.2 inferInstance
    have h2 : (p.appLE ⊤ U le_top).hom.FiniteType :=
      p.finiteType_appLE (isAffineOpen_top _) hU _
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x, by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩)
    have h4 : (fnOf U hgen).rangeRestrict.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fnOf U hgen).rangeRestrict_surjective
    have h5 := h4.comp (h2.comp (h3.comp h1))
    rw [← RingHom.finiteType_algebraMap]
    convert h5
    exact RingHom.ext_int _ _
  · intro w
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) w
    refine ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, ?_, ?_⟩
    · exact fun h0 => nonZeroDivisors.ne_zero hb (fnOf_injective U hgen (h0.trans (map_zero _).symm))
    · exact hab.symm
  · intro φ
    let ψ : Γ(X, U) →+* ℂ := φ.comp (fnOf U hgen).rangeRestrict
    refine ⟨ψ.comp (algX p U), CxPts.ofHom hU ψ (fun _ => rfl), mem_ptsIn.1 (CxPts.ofHom_mem hU ψ _), ?_⟩
    rintro ⟨_, a, rfl⟩
    rw [ratVal_fnOf (CxPts.ofHom_mem hU ψ _) hgen a, CxPts.ev_ofHom]
    rfl

end GlobalTheory.AffModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (g : X.functionField), 0 < e → g ∈ P.H e 0 → g ≠ 0 → ∃ (U : X.Opens) (h : genericPoint X ∈ U), (U : Set X) = NV P e 0 g ∧ IsAffineOpen U ∧ (∀ w : X.functionField, (∀ z ∈ U, RegAt z w) ↔ w ∈ (fnOf U h).range) ∧ Algebra.FiniteType ℤ (fnOf U h).range ∧ (∀ w : X.functionField, ∃ a ∈ (fnOf U h).range, ∃ b ∈ (fnOf U h).range, b ≠ 0 ∧ w = a / b) ∧ ∀ φ : (fnOf U h).range →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ U ∧ ∀ w : (fnOf U h).range, ratVal (w : X.functionField) y = φ w := by
  first | exact @GlobalTheory.AffModel.main | exact GlobalTheory.AffModel.main | (intros; apply GlobalTheory.AffModel.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutPoly
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace GlobalTheory.PolynomialPushoutEquivalence

theorem eqv_iso (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n

  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp (R : Type) [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n

  have e : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext (pull_comp R f g F n)
  rw [e]
  exact (hf n).comp (hg n)

theorem isPushout_poly {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPushout (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (Polynomial.mapRingHom φ)) (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) := by

  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra (Polynomial A) (Polynomial B) := Polynomial.algebra A B
  exact CommRingCat.isPushout_of_isPushout A (Polynomial A) B (Polynomial B)

theorem main (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv (ZMod q) (E := sp (Polynomial A')) (spMap Polynomial.C) (tw q i)) :
    Eqv (ZMod q) (sch.map (pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp))) (tw q i) := by

  set φ : A →+* A' := (Spec.preimage s).hom with hφ
  have hs : s = Spec.map (CommRingCat.ofHom φ) := by simp [φ]

  have sq : IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s := by
    rw [Category.comp_id, hs]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_poly φ)

  have e : pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp) =
      sq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')) ≫
        inv (pullback.snd (𝟙 (Spec (CommRingCat.of A))) s) := by
    rw [← Category.assoc, IsIso.eq_comp_inv, sq.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp _ _ _ _ (eqv_iso _ _ _) (eqv_comp _ _ _ _ h (eqv_iso _ _ _))

end GlobalTheory.PolynomialPushoutEquivalence

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtale
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomotopyInv

variable {R : Type} [CommRing R]

attribute [local instance] Polynomial.algebra

theorem eqv_baseChange (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv _ (spMap (Polynomial.C : A' →+* Polynomial A')) (tw q i)) :
    Eqv _ (sch.map (pullback.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 _) s (𝟙 _) s
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) := by
  first
  | exact @_root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | (apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main ..)

theorem homotopy_invariance_etale : GlobalTheory.EtC.C4 := by
  intro q _ A _ hq i
  have hqΓ : IsUnit ((q : ℕ) : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  refine GlobalTheory.T.etC_b3 q (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
    (𝟙 (Spec (CommRingCat.of A))) hqΓ i ?_
  intro A' _ s hA'
  refine eqv_baseChange q A i A' s ?_
  have hq' : IsUnit (q : A') := by simpa using hq.map (Spec.preimage s).hom
  exact GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian q A' hA' hq' i

end GlobalTheory.EtC.HomotopyInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopy_invariance_etale_alt : GlobalTheory.EtC.C4 := by
  first | (exact @GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale) | (exact GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale) | (intros; apply GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ)
    (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  intro p k _ h d G c μ hμ b hb
  obtain ⟨hres, -, huniq⟩ := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  let B : G.funs := ⟨fun n => c.ev n b, fun n => hres n b⟩
  have hB : G.cob B = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    change cobOne k (G.A n) (c.ev n b) = 0
    rw [← (hlaw n b).2, hb, map_zero]
  have hB0 := G.eq_zero_of_cob_eq_zero h hB
  have hb0 : ∀ n, c.ev n b = 0 := fun n => congrArg (fun B : G.funs => B.1 n) hB0
  obtain ⟨f, -, hf⟩ := huniq (fun _ => 0) (fun n => map_zero _)
  exact (hf b hb0).trans (hf 0 fun n => map_zero _).symm

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZeroStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ) (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  first | exact @GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | exact GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.Katz.eq_zero_of_cob1_eq_zero <;> assumption)
end
end

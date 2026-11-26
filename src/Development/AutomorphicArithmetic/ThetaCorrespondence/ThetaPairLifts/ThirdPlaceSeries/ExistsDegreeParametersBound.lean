module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsDegreeParametersBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermitianPairingBilinearOnPair

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShortVectorWeightBound
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace GlobalTheory.HSShortRoad
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem short_vector_weight_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => 0 ≤ PP * kap p i ∧ ∀ Z, ∀ j ≤ lenT p i PP, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j) 0) σ (v q).1 ≤ Real.exp (PP * kap p i) := by
  intro h2 _hDG hSz hF
  have hcomp := _root_.GlobalTheory.T.short_generator_norm_comparison h2
  obtain ⟨C₂, c₂, H₂⟩ := hcomp
  have H₄ := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  refine Closed.imp (Closed.and (Closed.and _root_.GlobalTheory.HSApp.wtBig_run_alt (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz))
    (Closed.and (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz) (Closed.and hSz hF))) ?_
  intro eps Fm CH heps h
  obtain ⟨⟨⟨_, -, a₁⟩, ⟨_, -, a₂⟩⟩, ⟨_, -, a₃⟩, ⟨_, -, a₄⟩, ⟨_, -, a₅⟩⟩ := h
  have e₆ : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x _ ι _ => 6 * C₂ ≤ (Fm.L x ι).sc.L := by
    refine ⟨(6 * C₂) ^ eps⁻¹, fun x hx hle ι p _ => ?_⟩
    have hx1 := Fm.L_x x ι hx
    have he := Fm.L_eps x ι
    have h0 : (0 : ℝ) ≤ 6 * C₂ := by positivity
    show _ ≤ (Fm.L x ι).sc.x ^ (Fm.L x ι).sc.eps
    rw [hx1, he]
    calc 6 * C₂ = ((6 * C₂) ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h0 heps.ne').symm
      _ ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hle heps.le
  obtain ⟨x0, a⟩ := ((((a₁.and a₂).and a₃).and a₄).and a₅).and e₆
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨⟨b₁, b₂⟩, b₃⟩, b₄⟩, b₅⟩, hCL⟩ := a x hx hle ι p hp
  clear a a₁ a₂ a₃ a₄ a₅ e₆
  have hW := b₁ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := b₂ i hi
  obtain ⟨hLaw, hIn, hL, hM, hFs, hfr, -, -, hf8, hr, hc₁, hκ2, hPP, -, -, -, -, hwt⟩ := b₃ i hi Y hY
  have s1 : 1 ≤ (Fm.L x ι).sc.b := (b₄ i).1
  have s2 : (Fm.L x ι).sc.b ≤ (Fm.parT x hx ι).PP * kap p i := (b₄ i).2.2.2.2.2.1
  have hFl := b₅ i hi Y hY
  have hdim := (GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi).2.1
  clear b₁ b₂ b₃ b₄ b₅
  unfold zBase at hPP hwt
  have hY' : Y.Good _ (391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2) := hY.1
  replace H₂ := fun la a b c Z => H₂ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY' _ hL hM hFs hfr le_rfl _ hFl
    (by rwa [abs_neg]) la a b c Z
  replace H₄ := H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY'
  have hfr1 : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hgap : ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ FlagTan.dimFlag (dat p i) + 1 := by
    have : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ FlagTan.dimFlag (dat p i) + 1 := by
      rw [hdim]
      generalize (Fm.D x ι).R.f = f at hf8 ⊢
      generalize (Fm.D x ι).R.r = r at hr ⊢
      have : 9 * r ≤ r.choose 2 := by
        rw [Nat.choose_two_right]
        exact (Nat.le_div_iff_mul_le two_pos).2 (by nlinarith [Nat.mul_le_mul_left r (show 18 ≤ r - 1 by omega)])
      nlinarith [Nat.mul_le_mul_left f this, Nat.mul_le_mul hf8 hr]
    exact_mod_cast this
  have hLZ : (Fm.L x ι).sc.L ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) := le_mul_of_one_le_left (by linarith) hfr1
  have hZ : 1 ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) := hL.trans hLZ
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hPk : 1 ≤ (Fm.parT x hx ι).PP * kap p i := s1.trans s2
  have hκpos : 0 < kap p i := by
    by_contra hneg
    have h0 : (Fm.parT x hx ι).PP * kap p i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hPP0 (not_lt.1 hneg)
    exact absurd (hPk.trans h0) (by norm_num)
  have hκ : 1 ≤ kap p i := one_le_sz hκpos
  have hZ3 : 0 ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 := by positivity
  refine ⟨zero_le_one.trans hPk, fun Z j hj => ?_⟩
  have hg := gapGe_wt hW j
  have ha := antitone_of_gapGe (by positivity) hg
  have hb : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j τ) ((dat p i).p - 1) :=
    fun τ => hgap.trans (hg τ ((dat p i).p - 1) (by omega))
  have hs := hwt j hj
  have h1 := hs.trans (le_mul_of_one_le_left (by positivity) one_le_two)
  have hX := H₂ ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j) ha hb
    (log_size_le (by positivity) hL hfr hκ hκ2 (by positivity) (le_trans (le_of_eq (sum_univ_inst _)) h1)) Z
  obtain ⟨n, w, Λ, hSG, hΛ, _hn⟩ := hX
  have hY4 := H₄ ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j) ha (fun τ => le_trans (by omega) (hb τ))
  obtain ⟨_hGA, hGO⟩ := hY4
  have hsp := span_of_shortGen hSG (hGO Z).2.2
  obtain ⟨hmem, hspan⟩ := hsp
  refine ⟨n, w, hmem, hspan, fun q σ => ?_⟩
  have hΛ' : Real.log Λ ≤ (Fm.parT x hx ι).PP * kap p i := by
    refine hΛ.trans (le_trans ?_ (bound_le c₂ hZ (hCL.trans hLZ) hPP hκ))
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left ?_ hZ3) le_rfl) c₂
    exact le_trans (le_of_eq (sum_univ_inst _)) hs
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hSG.one_le
  calc _ ≤ Λ := hSG.le q σ
    _ = Real.exp (Real.log Λ) := (Real.exp_log hΛ0).symm
    _ ≤ _ := Real.exp_le_exp.2 hΛ'
end GlobalTheory.HSShortRoad
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_path_weight_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => 0 ≤ PP * kap p i ∧ ∀ Z, ∀ j ≤ lenT p i PP, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j) 0) σ (v q).1 ≤ Real.exp (PP * kap p i) := by
  first | exact @_root_.GlobalTheory.HSShortRoad.short_vector_weight_bound_alt | exact _root_.GlobalTheory.HSShortRoad.short_vector_weight_bound_alt | (intros; apply _root_.GlobalTheory.HSShortRoad.short_vector_weight_bound_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelBergmanFrameBound
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameBerg
end GlobalTheory.FrameBerg
namespace GlobalTheory.FrameBerg
set_option maxHeartbeats 2000000 in
theorem bergman_frames_of_short_range_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  intro hP2 _hDG hS hFD
  obtain ⟨C1, hC1, H1⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP2
  obtain ⟨C2, hC2, H2⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP2
  have H0 := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP2
  refine (((_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and (_root_.GlobalTheory.HSApp.wtBig_run_alt.and hFD)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨_, _, a, ha⟩, ⟨_, _, b, hb⟩⟩, ⟨⟨_, _, c, hc⟩, ⟨_, _, d, hd⟩⟩⟩ := hh
  obtain ⟨e, he⟩ := GlobalTheory.family_sizes_eventually_large _ Fm (2 * C1 + C2 + 1)
  refine ⟨0, le_rfl, max (max a b) (max (max c d) e), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hA := ha x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi
  have hB := hb x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY
  have hW := hc x hx ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi
  have hF := hd x hx ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi Y hY
  have hLM := (he x ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι).2.2.1
  clear ha hb hc hd he
  obtain ⟨h1p, h1q, hfin, -, hanti, -⟩ := hA
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, h8f, h100r, hflat, hkap, hZ12, -, -, -, hsum, -⟩ := hB
  obtain ⟨hr, hdim, -⟩ := GlobalTheory.RecGaps.gaps p (Fm.params x hx ι) i hi
  intro Zc
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ with hPdef
  have hq : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
  have hg1 : ∀ τ, 1 ≤ gap (P.u₁ τ) ((dat p i).p - 1) := fun τ => one_le_gap_of_strictAnti (hanti τ).1 hq
  have ha1 : ∀ τ, Antitone (P.u₁ τ) := fun τ => (hanti τ).1.antitone
  have hgap2 : ∀ τ k, k + 1 < (dat p i).p + (dat p i).q → 1 ≤ gap (P.u₂ τ) k := by
    intro τ k hk
    have e : P.u₂ τ = P.u₁ τ + P.rem τ := rfl
    rw [e, gap_add]
    have := one_le_gap_of_strictAnti (hanti τ).1 hk
    have := (P.gap_rem τ k).1
    omega
  have ha2 : ∀ τ, Antitone (P.u₂ τ) := fun τ =>
    antitone_of_gap_nonneg fun k hk => (zero_lt_one.le).trans (hgap2 τ k hk)
  have hG := H0 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
  refine ⟨nonempty_cuspFrame ((hG P.u₂ ha2 fun τ => hgap2 τ _ hq).2 Zc), ?_⟩
  have hgapBig : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := by
    intro τ
    refine le_trans ?_ (hW.gaps τ ((dat p i).p - 1) hq)
    have h9 : 9 * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.r.choose 2 := by
      rw [Nat.choose_two_right]
      apply (Nat.le_div_iff_mul_le two_pos).2
      have : 100 ≤ (Fm.D x ι).R.r := h100r
      have : 99 ≤ (Fm.D x ι).R.r - 1 := by omega
      nlinarith
    rw [hdim, hr]
    generalize (Fm.D x ι).R.r.choose 2 = c at h9 ⊢
    generalize ((Fm.D x ι).R.f * c + 1).choose 2 = B
    have h1 : 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.f * c := by
      rw [mul_assoc, mul_comm 9, mul_assoc, mul_comm (Fm.D x ι).R.r]; exact Nat.mul_le_mul_left _ h9
    have h2 : B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3 ≤
        ((Fm.D x ι).R.f * c + 3) * (B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 8 ≤ (Fm.D x ι).R.f := h8f
    have h4 : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r := by
      have : 10 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    exact_mod_cast (h4.trans (h1.trans (by omega))).trans h2
  have hL1' : (1 : ℝ) ≤ (Fm.L x ι).sc.L := hL1
  have hZdef : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L = zBase (Fm.L x ι) := rfl
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast h8f
  have hr100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast h100r
  have hfrpos : (0 : ℝ) < ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by positivity
  have hE2 : (2 : ℝ) ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hfrE : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r ≤ Real.exp (Fm.L x ι).sc.L := by
    have := Real.exp_le_exp.2 hfr
    rwa [Real.exp_log (by exact_mod_cast hfrpos)] at this
  have hLE : (Fm.L x ι).sc.L ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hZE : zBase (Fm.L x ι) ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rw [← hZdef, sq]; exact mul_le_mul hfrE hLE (by linarith) (Real.exp_pos _).le
  have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    rw [← hZdef]
    have : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := hL1'.trans hZL
  have hkap0 : 0 ≤ kap p i := by unfold CovTop.kap sizeK; positivity
  have hkapE : kap p i ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rcases hkap0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have := Real.exp_le_exp.2 hkap
      rw [Real.exp_log h0] at this
      rw [← Real.exp_nat_mul]; push_cast; linarith
  have hK1 : (1 : ℝ) ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
    have : 0 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP := div_nonneg hkap0 (Nat.cast_nonneg _)
    linarith
  have hKle : kap p i / lenT p i (Fm.parT x hx ι).PP ≤ kap p i := by
    rcases Nat.eq_zero_or_pos (lenT p i (Fm.parT x hx ι).PP) with h0 | h0
    · rw [h0]; simp [hkap0]
    · exact div_le_self hkap0 (by exact_mod_cast h0)
  have hS := hsum P.u₁ (by simp)
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by positivity
  have hSE : ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤ Real.exp (7 * (Fm.L x ι).sc.L) := by
    have e7 : Real.exp (7 * (Fm.L x ι).sc.L) = Real.exp (Fm.L x ι).sc.L ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e7]
    refine hS.trans ?_
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ Real.exp (Fm.L x ι).sc.L ^ 4 := by
      calc zBase (Fm.L x ι) ^ 2 ≤ (Real.exp (Fm.L x ι).sc.L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hZE 2
        _ = _ := by ring
    have hK3 : kap p i / lenT p i (Fm.parT x hx ι).PP + 1 ≤ Real.exp (Fm.L x ι).sc.L ^ 3 := by
      nlinarith
    calc zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)
        ≤ Real.exp (Fm.L x ι).sc.L ^ 4 * Real.exp (Fm.L x ι).sc.L ^ 3 :=
          mul_le_mul hZ2 hK3 (by linarith) (by positivity)
      _ = _ := by ring
  have hlogS : Real.log (∑ τ, ∑ k, |(P.u₁ τ k : ℝ)|) ≤ 7 * (Fm.L x ι).sc.L := by
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h0).2 hSE
  have ho : 391 * zBase (Fm.L x ι) ^ 2 ≤ 391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2 := by
    rw [hZdef]
  have hc₁ : |-GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by rw [abs_neg]; exact hflat
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := H1 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho _ hF hc₁ P.u₁ ha1 hgapBig (by linarith) Zc
  obtain ⟨f, hfn, -, hfN⟩ := exists_latFrame_of_isShortGen _ _ _ _ n w abelian₂
    (nonempty_cuspFrame ((hG P.u₁ ha1 hg1).2 Zc)) hsg
  have hb := (H2 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho P.u₁ ha1 (by linarith) Zc).1
  rw [hZdef] at hLam hn hb
  have hMZ : 2 * C1 + C2 + 1 ≤ zBase (Fm.L x ι) := hLM.trans hZL
  have hZ35 : zBase (Fm.L x ι) ^ 3 ≤ zBase (Fm.L x ι) ^ 5 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ612 : zBase (Fm.L x ι) ^ 6 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ5 : 0 ≤ zBase (Fm.L x ι) ^ 5 := by positivity
  have hkey : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) ^ 12 := by
    have : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) * zBase (Fm.L x ι) ^ 5 :=
      mul_le_mul_of_nonneg_right (by linarith) hZ5
    nlinarith
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ12
  have hC1Z : C1 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  have hC2Z : C2 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  refine ⟨f, max abelian₂ 1, Real.exp (C2 * zBase (Fm.L x ι) ^ 3), le_max_right _ _,
    Real.one_le_exp (by positivity), ?_, ?_, ?_, fun q σ => (hfN q σ).trans (le_max_left _ _), hb⟩
  · rw [hfn]; exact hn.trans hC1Z
  · rw [Real.log_exp]; exact hC2Z
  · rcases le_total abelian₂ 1 with hl | hl
    · rw [max_eq_right hl, Real.log_one]; positivity
    · rw [max_eq_left hl]
      refine hLam.trans ?_
      have h3 : zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤
          zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ zBase (Fm.L x ι) ^ 3)
        nlinarith
      have h4 : C1 * (zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| + zBase (Fm.L x ι) ^ 5) ≤
          (2 * C1 * zBase (Fm.L x ι) ^ 5) * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have h6 := mul_le_mul_of_nonneg_left h3 hC1
        have h5 : C1 * zBase (Fm.L x ι) ^ 5 ≤ C1 * zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) :=
          le_mul_of_one_le_right (by positivity) hK1
        linarith [h6, h5]
      refine h4.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
      nlinarith
end GlobalTheory.FrameBerg
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_bergman_frame_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  first | exact @_root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt | exact _root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt | (intros; apply _root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShortVectorsSpanCuspLattice
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.ShortSpanUnitCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
end GlobalTheory.CovTop.ShortSpanUnitCover
namespace GlobalTheory.CovTop.ShortSpanUnitCover
end GlobalTheory.CovTop.ShortSpanUnitCover
namespace GlobalTheory.CovTop.ShortSpanUnitCover
set_option maxHeartbeats 1000000 in
theorem short_vectors_span_uc_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  intro hP2 _hDG hSz hFD
  have hshort := _root_.GlobalTheory.T.short_generator_norm_comparison hP2
  obtain ⟨C, hC0, hH3⟩ := hshort
  have hGd := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP2
  refine ((((((_root_.GlobalTheory.T.size_bounds_for_family_alt hSz).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz)).and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt (4 * C + 1))).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).and
    _root_.GlobalTheory.HSApp.wtBig_run_alt).and hFD).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨⟨⟨⟨C1, -, a1, h1⟩, ⟨C2, -, a2, h2⟩⟩, ⟨C3, -, a3, h3⟩⟩, ⟨C4, -, a4, h4⟩⟩, ⟨C5, -, a5, h5⟩⟩, ⟨C6, -, a6, h6⟩⟩ := hh
  refine ⟨0, le_rfl, max a1 (max a2 (max a3 (max a4 (max a5 a6)))), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have s1 := h1 x hx (le_trans (by simp) hle) ι p hp i hi Y hY
  have s2 := h2 x hx (le_trans (by simp) hle) ι p hp i hi
  have s3 := h3 x hx (le_trans (by simp) hle) ι p hp i
  have s4 := h4 x hx (le_trans (by simp) hle) ι p hp i
  have s5 := h5 x hx (le_trans (by simp) hle) ι p hp i hi
  have s6 := h6 x hx (le_trans (by simp) hle) ι p hp i hi Y hY
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, hkap, hPP, -, -, -, hu12, hwt⟩ := s1
  obtain ⟨hp1, hq1, hfin, -, hsa, -⟩ := s2
  intro Z
  set P : WtPar (dat p i) := (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ :
    WtPar (dat p i)) with hP
  have hpq : (dat p i).p + (dat p i).q = (Fm.D x ι).R.r := s4.sig.2.2
  have hr2 : 0 < (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
  have hDf : (Fm.D x ι).R.f ≤ FlagTan.dimFlag (dat p i) := by
    rw [← GlobalTheory.CompHS.dimFlag_eq, s4.dim]; exact Nat.le_mul_of_pos_right _ hr2
  have hD2 : 2 ≤ FlagTan.dimFlag (dat p i) + 0 := by omega
  have hAnt := fun τ => GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P 0 (fun τ => (hsa τ).1) hD2 hp1 hq1 τ
  have hgap : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.wt 0 τ) ((dat p i).p - 1) := by
    intro τ
    have hk : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
    obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (FlagTan.dimFlag (dat p i) + 3) * ((FlagTan.dimFlag (dat p i) + 1).choose 2 +
        4 * ((dat p i).p + (dat p i).q) + FlagTan.dimFlag (dat p i) + 3) := ⟨_, rfl⟩
    have hg : (G : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := hG ▸ s5.gaps τ _ hk
    have h1 := consecutiveGap_weightZero_ge (dat p i) P τ hk _ hg
    have hG12 : 12 * (Fm.D x ι).R.r ≤ G := by
      rw [hG, hpq]
      have := Nat.mul_le_mul (show 3 ≤ FlagTan.dimFlag (dat p i) + 3 by omega)
        (show 4 * (Fm.D x ι).R.r ≤ (FlagTan.dimFlag (dat p i) + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          FlagTan.dimFlag (dat p i) + 3 by omega)
      omega
    have hN : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 ≤ (FlagTan.dimFlag (dat p i) + 1) * G := by
      have := Nat.mul_le_mul (show (Fm.D x ι).R.f + 1 ≤ FlagTan.dimFlag (dat p i) + 1 by omega) hG12
      nlinarith
    have hN' : ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 : ℕ) : ℤ) ≤ (((FlagTan.dimFlag (dat p i) + 1) * G : ℕ) : ℤ) := by
      exact_mod_cast hN
    push_cast at hN' ⊢
    linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hfr1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| := by positivity
  have hw0 := hwt 0 (Nat.zero_le _)
  have hlog := log_sum_le hS0 hw0 hkap hfr hL1 hfr1
  obtain ⟨n, w, abelian₂, hSG, hLam, -⟩ := hH3 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 _ hL1 hM hfs
    hfr le_rfl _ s6 (by rw [abs_neg]; exact hflat) (P.wt 0) (fun τ => (hAnt τ).1) hgap hlog Z
  refine ⟨n, w, fun q => (hSG.gen _).2 (Submodule.subset_span ⟨q, rfl⟩), ?_, fun q σ => ?_⟩
  · have hGO := ((hGd (Fm.D x ι) p.T hLaws _ hp1 hq1 hfin hInR Y _ _ hY.1 (P.wt 0) (fun τ => (hAnt τ).1)
      (fun τ => (hAnt τ).2)).2 Z).2.2
    rw [eq_top_iff, ← hGO]
    exact Submodule.span_le.2 fun y hy => Submodule.span_le_restrictScalars ℤ _ _ ((hSG.gen y).1 hy)
  · refine (hSG.le q σ).trans ?_
    rw [← Real.exp_log (lt_of_lt_of_le one_pos hSG.one_le), GlobalTheory.CompHS.dimFlag_eq]
    refine Real.exp_le_exp.2 ?_
    have hZ : 0 < zBase (Fm.L x ι) := by unfold zBase; positivity
    have hkap0 : 0 ≤ kap p i := by
      have : 0 ≤ zBase (Fm.L x ι) ^ 2 * kap p i := hS0.trans hw0
      exact (mul_nonneg_iff_of_pos_left (by positivity)).1 this
    have hX : 1 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
      have := div_nonneg hkap0 (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP)); linarith
    have hW : 0 ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by positivity
    have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := by rw [← Nat.card_eq_fintype_card]; exact s4.card
    have hK : ∑ τ, ∑ k, |(FlagTan.kap (dat p i) τ k : ℝ)| ≤
        zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
      refine (sum_abs_kap_le (dat p i)).trans ?_
      rw [hcard, hpq]
      have a : 1 ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2 := by nlinarith
      have b : ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 ≤ zBase (Fm.L x ι) ^ 2 := by
        unfold zBase
        calc ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * 1 :=
              (mul_one _).symm
          _ ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * (((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2) :=
              mul_le_mul_of_nonneg_left a (by positivity)
          _ = _ := by ring
      calc _ ≤ zBase (Fm.L x ι) ^ 2 := by push_cast; exact b
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hX
    have hDc : (1 : ℝ) ≤ (FlagTan.dimFlag (dat p i) : ℝ) := by exact_mod_cast (by omega : 1 ≤ FlagTan.dimFlag (dat p i))
    have hSs := sum_le (sum_abs_weightZero_le_components (dat p i) P) hK (hu12 _ (Set.mem_insert _ _))
      (hu12 _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hDc hW
    have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := le_mul_of_one_le_left (by linarith) hfr1
    exact final_le hC0 s3.big.1 hZL hPP hDc hX (by linarith) hLam
end GlobalTheory.CovTop.ShortSpanUnitCover
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_vectors_span_cusp_lattice_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  first | exact @_root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt | exact _root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt | (intros; apply _root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogDegreeLeOfCoveringRange
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogTopDimensionBoundCovering
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DimLogTop
theorem log_top_dimension_le_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  intro hP hSz
  have hBex := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  obtain ⟨Cb, -, hB⟩ := hBex
  have hG := _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain hP
  have hQ := _root_.GlobalTheory.QuoWt.weights_at_point_alt hSz
  have hS := _root_.GlobalTheory.CovTop.CovSz.size_rows_alt hSz
  have hW := _root_.GlobalTheory.HSApp.wtBig_run_alt
  refine Closed.imp (Closed.and (Closed.and hQ hS) hW) ?_
  intro eps Fm CH heps hh
  obtain ⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩ := hh
  refine ⟨0, le_rfl, max (max (max x1 x2) x3) ((max Cb 1) ^ eps⁻¹), ?_⟩
  intro x hx hle ι p hp i hi Y hY Z
  have hle1 : max (max x1 x2) x3 ≤ x := (le_max_left _ _).trans hle
  have hq := h1 x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi
  have hs := h2 x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi Y hY
  have hwb := h3 x hx ((le_max_right _ _).trans hle1) ι p hp i hi
  obtain ⟨hp1, hq1, hE, -, hstr, -, -⟩ := hq
  obtain ⟨hLJ, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, -, hkap, hZ12, -, -, -, -, hwt⟩ := hs
  set PP := (Fm.parT x hx ι).PP with hPP
  have hx1 : Fm.x1 < x := hx
  have hLx : (Fm.L x ι).sc.L = x ^ eps := by
    unfold Scale.L; rw [Fm.L_x x ι hx1, Fm.L_eps x ι]
  have hLC : max Cb 1 ≤ (Fm.L x ι).sc.L := by
    rw [hLx]
    have h0 : (0 : ℝ) ≤ (max Cb 1) ^ eps⁻¹ := Real.rpow_nonneg (by positivity) _
    calc max Cb 1 = ((max Cb 1) ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow (by positivity) heps.ne').symm
      _ ≤ x ^ eps := Real.rpow_le_rpow h0 ((le_max_right _ _).trans hle) heps.le
  have hT2 : 2 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) + lenT p i PP := by
    have hT1 := hwb.le_T
    have hD1 := hwb.one_le
    change 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) at hD1
    change GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i PP at hT1
    omega
  have hanti := GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i)
    (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) (lenT p i PP)
    (fun τ => (hstr τ).1) hT2 hp1 hq1
  have hsum := hwt (lenT p i PP) le_rfl
  have hsize : Real.log (∑ τ, ∑ k, |(((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) τ k : ℝ)|) ≤ 20 * (Fm.L x ι).sc.L := by
    refine GlobalTheory.CovTop.DimLogTop.log_size_le ((Fm.D x ι).R.f : ℝ) ((Fm.D x ι).R.r : ℝ) (Fm.L x ι).sc.L (kap p i) _
      (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)) (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r))
      hL1 (sizeK_nonneg _ _ _) hkap hfr (by positivity) ?_
    have : (0 : ℝ) ≤ 6 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 := by positivity
    have e : zBase (Fm.L x ι) = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) * (Fm.L x ι).sc.L := by unfold zBase; ring
    rw [← e]; linarith
  have hBr := (hB (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 (Fm.L x ι).sc.L hL1 hM hfs hfr (by unfold zBase; exact le_rfl)
    _ (fun τ => (hanti τ).1) hsize Z).2.2
  have hGd := (hG (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 _ (fun τ => (hanti τ).1) (fun τ => (hanti τ).2)).2 Z
  have hrk : Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) Z = (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i)
      ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt
      (lenT p i PP)) 0)) : ℝ) := by
    show ((rankOn Y.U Z _ : ℕ) : ℝ) = _
    unfold rankOn
    rw [rkK_eq_finrank_of_span_top _ hGd.2.2]
  rw [← hrk]
  have hfr1 : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) := by
    have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hLZ : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase; nlinarith
  have hcube := GlobalTheory.CovTop.DimLogTop.cube_le Cb (Fm.L x ι).sc.L (zBase (Fm.L x ι)) ((le_max_left _ _).trans hLC) hL1 hLZ
  have h2 : Cb * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 = Cb * zBase (Fm.L x ι) ^ 3 := by
    unfold zBase; ring
  linarith
end GlobalTheory.CovTop.DimLogTop
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_finrank_cuspOn_le : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  first | exact @_root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt | exact _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt | (intros; apply _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BinomialFlagDimensionDegreeBound
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftsAndAltAlt
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DgShare
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem lifts_and_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop} (h : _root_.GlobalTheory.CovTop.LiftsCondition Q) (h' : _root_.GlobalTheory.CovTop.LiftsCondition Q') :
    _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP _ => (∃ C, Q Fm x hx ι p i PP C) ∧ ∃ C, Q' Fm x hx ι p i PP C :=
  Closed.imp (Closed.and h h') fun _ _ _ ⟨⟨C, _, a⟩, C', _, b⟩ => ⟨0, le_rfl, (a.and b).imp fun _ h x hx hle ι p hp i =>
    ⟨⟨C, (h x hx hle ι p hp).1 i⟩, C', (h x hx hle ι p hp).2 i⟩⟩
end GlobalTheory.CovTop.DgShare
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DgShare
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem choose_mul_compDeg_le_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition →
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) *
      GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
        WtPar (dat p i)).u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2,
        lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) := by
  intro hX hP hG hQ hSi hKS hSA _ hS _
  have hFa := hKS.toroidalChartsForFan
  have h4 := _root_.GlobalTheory.T.size_bounds_for_family_alt hS
  have h5 := _root_.GlobalTheory.T.birOn_weightPair_both_components_alt hX hG hQ hSi hP hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition at h4 h5
  have all := _root_.GlobalTheory.CovTop.DgShare.lifts_and_alt (_root_.GlobalTheory.CovTop.DgShare.lifts_and_alt (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS) _root_.GlobalTheory.HSApp.wtBig_run_alt) (_root_.GlobalTheory.CovTop.DgShare.lifts_and_alt h4 h5)
  clear h4 h5
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨_, ⟨_, hq⟩, _, hB⟩, _, ⟨_, hz⟩, _, hb⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, -⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  exact _root_.GlobalTheory.CovTop.DgShare.nef_share_lower_bound hP hG hQ hSi hFa hSA hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hb hi Y hY Z).1
end GlobalTheory.CovTop.DgShare
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.binomial_flag_dimension_degree_bound_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) * GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ≤ Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) := by
  first | exact @_root_.GlobalTheory.CovTop.DgShare.choose_mul_compDeg_le_alt_alt | exact _root_.GlobalTheory.CovTop.DgShare.choose_mul_compDeg_le_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.DgShare.choose_mul_compDeg_le_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DgLog
end GlobalTheory.CovTop.DgLog
namespace GlobalTheory.CovTop.DgLog
end GlobalTheory.CovTop.DgLog
namespace GlobalTheory.CovTop.DgLog
theorem log_degree_le_of_covering_range_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
  intro hX hP hG hQ hSg hFan hSA hDG hSz hFD
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.T.binomial_flag_dimension_degree_bound_alt_alt hX hP hG hQ hSg hFan hSA hDG hSz hFD) (_root_.GlobalTheory.T.log_finrank_cuspOn_le hP hSz)) hSz) ?_
  intro eps Fm CH heps hh
  obtain ⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩ := hh
  refine ⟨0, le_rfl, max (max x1 x2) x3, ?_⟩
  intro x hx hle ι p hp i hi Y hY Z
  have hA := h1 x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY Z
  have hB := h2 x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY Z
  have hz := h3 x hx ((le_max_right _ _).trans hle) ι p hp i
  set PP := (Fm.parT x hx ι).PP with hPP
  obtain ⟨⟨u1, hu1⟩, hqq⟩ := hz.2.2.2.2.2.2 hi
  have hT := (hqq _ hu1).1
  have hbin : 1 ≤ (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) := Nat.choose_pos (by omega)
  have hle' : GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) :=
    (Nat.le_mul_of_pos_left _ hbin).trans hA
  have hdg0 : (0 : ℝ) ≤ Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z := Nat.cast_nonneg _
  rcases hdg0.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    exact (Real.log_natCast_nonneg _).trans hB
  · have h1 : Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z ≤ (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) := by
      exact_mod_cast hle'
    exact (Real.log_le_log h0 h1).trans hB
end GlobalTheory.CovTop.DgLog
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_dg_u1_le_of_flatDeg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
  first | exact @_root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt | exact _root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt | (intros; apply _root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
namespace GlobalTheory.HSShortRun
open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}
set_option maxHeartbeats 1000000 in
theorem hsClaim_short_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  intro hX h2 hG hQ hS hK hL hDG hSz hF
  have hP := _root_.GlobalTheory.T.covering_topology_refinement h2
  have H₄ := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  have H₃ : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg
      (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
    apply _root_.GlobalTheory.T.log_dg_u1_le_of_flatDeg <;> assumption
  refine Closed.imp (Closed.and (Closed.and (Closed.and (_root_.GlobalTheory.T.hilbertSamuel_bergman_frame_bound_alt h2 hDG hSz hF) (_root_.GlobalTheory.T.birOn_weightPair_both_components_alt hX hG hQ hS h2 hSz))
    (Closed.and H₃ _root_.GlobalTheory.HSApp.wtBig_run_alt)) (Closed.and (Closed.and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz) (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz))
    (Closed.and (_root_.GlobalTheory.T.short_vectors_span_cusp_lattice_alt h2 hDG hSz hF) (_root_.GlobalTheory.T.short_path_weight_bound_alt h2 hDG hSz hF)))) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨_, -, a₃⟩, _, -, a₄⟩, ⟨⟨_, -, a₅⟩, _, -, a₆⟩, ⟨_, -, a₇⟩, _, -, a₈⟩
  obtain ⟨x0, a⟩ := (((a₁.and a₂).and (a₃.and a₄)).and ((a₅.and a₆).and (a₇.and a₈)))
  clear a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨⟨a₁, a₂⟩, a₃, a₄⟩, ⟨a₅, a₆⟩, a₇, a₈⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨⟨f₂⟩, f₁, Λ, β, hΛ, hβ, hn, hlβ, hlΛ, hfr, hberg⟩ := a₁ i hi Y hY Z
  have hW := a₄ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := a₅ i hi
  obtain ⟨hLaw, hIn, -, -, -, -, -, -, -, -, -, -, hPP, -⟩ := a₆ i hi Y hY
  obtain ⟨hPk, hsh⟩ := a₈ i hi Y hY
  have hg := gapGe_wt_of_wtBig hW
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hκ0 : 0 ≤ kap p i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c₁, c₂⟩ := _root_.GlobalTheory.HSShortRun.hilbertSamuel_estimate_at_level hP hG hQ h2.q15 h2.q16 hS hK.toroidalChartsForFan hL hY.1 hE Z hW
    (fun j _ => (H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1 _ (fun τ => antitone_of_gapGe (by positivity) (hg j) τ)
      (fun τ => le_trans (by omega) (hg j τ ((dat p i).p - 1) (by omega)))).1)
    hPP0 hκ0 f₂ f₁ hΛ hβ hfr hberg (a₂ i hi Y hY Z) (a₇ i hi Y hY Z) (hsh Z)
  refine ⟨f₁.n, Λ, β, _, _, _, c₁, hΛ, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk, hn, hlβ, a₃ i hi Y hY Z, hlΛ,
    (Real.log_exp _).le, (Real.log_exp _).le, ?_, c₂⟩
  have e₁ : 0 ≤ CompHt.dimFlag (dat p i) * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
    positivity
  have e₂ : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP := by positivity
  have e₃ : 0 ≤ 2 * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP) * CompHt.dimFlag (dat p i) := by
    positivity
  linarith
end GlobalTheory.HSShortRun
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degree_parameters_bound_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  first | exact @_root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt | exact _root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt | (intros; apply _root_.GlobalTheory.HSShortRun.hsClaim_short_alt_alt <;> assumption)
end
end

module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightHodgeBundleGenerated
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleSandwichBound
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp.Sandwich
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {TF : TorFlag Xo c} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {P : WtPar Dw} (R : Choice TF.X Z U P)
end GlobalTheory.HSApp.Sandwich
open GlobalTheory.HSApp.Sandwich in
theorem GlobalTheory.HSApp.hodge_bundle_sandwich_bound : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P)
    (ω : CanId R.toModif), FnAlgClosed (Xo := Xo) (c := c) → ∀ h₁ : FreeOnOpen TF.X Z U P.u₁,
    (∀ j, CuspIso TF.X Z U (P.wt j) → adjGlobal R j ≤ LinearMap.range (adjSec R ω h₁ j)) ∧
    (CuspIso TF.X Z U (P.wt 0) → LinearMap.range (adjSec R ω h₁ 0) ≤ adjGlobal R 0) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U P R ω hF h₁
  have key := fun (j : ℕ) m => _root_.GlobalTheory.T.log_canonical_criterion_boundary hP hG E H Dw l Xo c TF Z hF R.toModif ω _ _ (P.kap_add j) m
  refine ⟨fun j hj => ?_, fun hj => ?_⟩
  · rintro _ ⟨f, rfl⟩
    let e := R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)
    obtain ⟨m, hm⟩ := (R.bijective_pullOff (isLB_L₀ TF.X Z (P.wt j))).2 (e.symm (H0.restr le_top f))
    have hmul : H0.restr le_top (R.mulPole j ⊤ f) =
        (((common₀ TF.X Z).pull R.σ).canChart R.K.isLB (P.kap_add j)).mul ω.ω (R.pullOff m) := by
      rw [restr_mulPole, hm]
      have := R.mulPole_adjEquiv ω.ω ω.unit h₁ j (P.kap_add j) (e.symm (H0.restr le_top f))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨g, hg, hgm⟩ := (key j m).2 ⟨R.mulPole j ⊤ f, hmul⟩
    obtain ⟨c', hc'⟩ := hj.2 hg
    refine ⟨c', ?_⟩
    show e (R.pullOff (cuspSec TF.X Z U _ c')) = _
    rw [hc', hgm, hm, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨c', rfl⟩
    obtain ⟨s, hs, hsr⟩ := hj.1 c'
    obtain ⟨g, hg⟩ := (key 0 _).1 ⟨s, hs, hsr⟩
    obtain ⟨f, hf⟩ := ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (nowhereZero_pow_zero R)).surjective g
    refine ⟨f, mulPole_injective R h₁ 0 ?_⟩
    rw [← restr_mulPole, mulPole_adjSec]
    exact (congrArg (H0.restr le_top) hf).trans hg
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_bundle_degree_squeeze : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif), FnAlgClosed (Xo := Xo) (c := c) → ∀ h₁ : FreeOnOpen TF.X Z U P.u₁, (∀ j, CuspIso TF.X Z U (P.wt j) → adjGlobal R j ≤ LinearMap.range (adjSec R ω h₁ j)) ∧ (CuspIso TF.X Z U (P.wt 0) → LinearMap.range (adjSec R ω h₁ 0) ≤ adjGlobal R 0) := by
  first | exact @_root_.GlobalTheory.HSApp.hodge_bundle_sandwich_bound | exact _root_.GlobalTheory.HSApp.hodge_bundle_sandwich_bound | (intros; apply _root_.GlobalTheory.HSApp.hodge_bundle_sandwich_bound <;> assumption)
end
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
private theorem gap_add' {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp
private theorem gap_sub' {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v - w) k = gap v k - gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.sub_apply]; ring
  · simp
private theorem gap_nsmul' {N : ℕ} (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = n * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]; ring
  · simp
private theorem gap_kap_le' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (FlagTan.kap Dw τ) k ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 := by
  unfold FlagTan.kap gap; simp only [dif_pos h]; split_ifs <;> push_cast <;> omega
private theorem div_le_sub_mul_div' (g : ℤ) {n : ℤ} (hn : 0 < n) : g / n ≤ g - (n - 1) * (g / n) := by
  have h₁ : n * (g / n) ≤ g := Int.mul_ediv_self_le hn.ne'
  linarith
private theorem gaps_of_wtBig' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (P : WtPar Dw), WtBig P → ∀ la ∈ [P.u₁, P.u₂, P.ub, P.u₁ - FlagTan.kap Dw - (dimFlag Dw + 2) • P.ub], GapGe 1 la ∧ GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) := by
  intro E _ _ _ H Dw P hP la hla
  have hD3 : (0 : ℤ) < (dimFlag Dw : ℤ) + 3 := by positivity
  have hmain : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q →
      (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) + 4 * ((Dw.p : ℤ) + Dw.q) + dimFlag Dw + 3 ≤ gap (P.ub τ) k ∧
      gap (P.ub τ) k ≤ gap (P.u₁ τ) k - ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k ∧
      gap (P.u₁ τ) k ≤ gap (P.u₂ τ) k := by
    intro τ k h
    have hg := hP.gaps τ k h
    push_cast at hg
    rw [P.gap_ub τ h]
    refine ⟨?_, ?_, ?_⟩
    · apply Int.le_ediv_of_mul_le hD3
      linarith
    · have := div_le_sub_mul_div' (gap (P.u₁ τ) k) hD3
      linarith
    · rw [show P.u₂ τ = P.u₁ τ + P.rem τ from rfl, gap_add']
      linarith [(P.gap_rem τ k).1]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hla
  rcases hla with rfl | rfl | rfl | rfl <;> constructor <;> intro τ k h <;>
  · obtain ⟨h₁, h₂, h₃⟩ := hmain τ k h
    have h₄ := gap_kap_le' τ h
    push_cast at h₄
    have hC : (0 : ℤ) ≤ (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := by positivity
    have hD : (0 : ℤ) ≤ (dimFlag Dw : ℤ) := by positivity
    have hN : (2 : ℤ) ≤ (Dw.p : ℤ) + Dw.q := by omega
    have hb : (0 : ℤ) ≤ ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k := by
      apply mul_nonneg <;> linarith
    try simp only [Pi.sub_apply, Pi.smul_apply, gap_sub', gap_nsmul']
    try push_cast
    linarith
private theorem nonempty_cartier_of_locally_principal' : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData),
    (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧
      I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  intro Y I h
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq (I := I) h
  have hLB : D.lb.IsLB := by
    refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (one_mul _).symm).symm
    · intro i j k
      have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
      have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
      have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
      refine Units.ext (D.eq_trans_on i k hi hk ?_)
      rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← mul_assoc]
      rfl
  refine ⟨{ P := D.lb, isLB := hLB, t := D.canonical, reg := fun i y hi => ?_, cut := ?_ }⟩
  · exact GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) y hi
  · refine ideal_ext_stalk fun y => ?_
    obtain ⟨i, hi⟩ := D.exists_mem y
    rw [stalkId_cutIdeal hLB _ i y hi, ← hD, D.stalkId_idealSheaf i y hi, Set.range_const]
    rfl

private def cartierPullOfInt' {Y T : Scheme.{0}} [IsIntegral T] {I : Y.IdealSheafData} (Δ : Cartier I) (r : T ⟶ Y) {z₀ : T}
    (hz : r z₀ ∉ I.support) : Cartier (I.comap r) :=
  { GlobalTheory.CompHS.Cartier.ofSec (LB.isLB_pull Δ.isLB r) (GlobalTheory.secPull Δ.t r) (y₀ := z₀)
      (by rw [GlobalTheory.nonzeroLocus_secPull]; exact (Δ.mem_nonzeroLocus _).2 hz) with
    cut := (GlobalTheory.Vanishing.eq_comap_of_stalk
      (fun z => GlobalTheory.Vanishing.stalkId_cutIdeal_secPull Δ.isLB (fun _ : Unit => Δ.t) z)).trans (by rw [Δ.cut]) }

private theorem ne_bot_of_notMem' {Y : Scheme.{0}} {I : Y.IdealSheafData} {y : Y} (h : y ∉ I.support) : I ≠ ⊥ := fun e => by
  rw [e, Scheme.IdealSheafData.support_bot] at h
  exact h trivial

private theorem nonempty_resol' (hPr : GlobalTheory.Published.Principalisation) {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}}
    {p : Y ⟶ Sp F} {D : ℕ} (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hc : GeometricallyConnected p)
    {U : Y.Opens} (hU : (U : Set Y).Nonempty) {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) {a₁ a₂ : Λ}
    {W₁ : Submodule F (H0 p (B a₁) ⊤)} {W₂ : Submodule F (H0 p (B a₂) ⊤)}
    (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) : Nonempty (Resol C U D W₁ W₂) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres p
  have hY : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral (f := p) (K := F) (𝟙 _) (𝟙 Y) p IsPullback.of_id_fst
  obtain ⟨u, hu⟩ := hU
  obtain ⟨Y₁, s₁, hi₁, hs₁, hp₁, hb₁, -, hc₁, -⟩ :=
    hPr F D Y p hY hs hp (baseIdeal (C.isLB a₁) W₁) (ne_bot_of_notMem' (h₁ u hu))
  have iso₁ : IsIso (s₁ ∣_ U) := hb₁.isIso_restrict U h₁
  obtain ⟨z₁, hz₁⟩ : ∃ z : Y₁, z ∈ s₁ ⁻¹ᵁ U :=
    let z := inv (s₁ ∣_ U) ⟨u, hu⟩
    ⟨z.1, z.2⟩
  let M₁ : Modif p U D := ⟨Y₁, s₁, hs₁, hp₁, iso₁, (s₁ ⁻¹ᵁ U).isOpen.dense ⟨z₁, hz₁⟩⟩
  have off₂ : ∀ y ∈ s₁ ⁻¹ᵁ U, y ∉ ((baseIdeal (C.isLB a₂) W₂).comap s₁).support := fun y hy h => by
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h₂ _ hy h
  obtain ⟨Y₂, s₂, hi₂, hs₂, hp₂, hb₂, -, hc₂, -⟩ :=
    hPr F D Y₁ (s₁ ≫ p) hi₁ hs₁ hp₁ _ (ne_bot_of_notMem' (off₂ z₁ hz₁))
  have iso₂ : IsIso (s₂ ∣_ (s₁ ⁻¹ᵁ U)) := hb₂.isIso_restrict _ off₂
  obtain ⟨z₂, hz₂⟩ : ∃ z : Y₂, z ∈ s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U) :=
    let z := inv (s₂ ∣_ (s₁ ⁻¹ᵁ U)) ⟨z₁, hz₁⟩
    ⟨z.1, z.2⟩
  let M₂ : Modif M₁.str M₁.opn D := ⟨Y₂, s₂, hs₂, hp₂, iso₂, (s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U)).isOpen.dense ⟨z₂, hz₂⟩⟩
  have Δ₂ : Cartier ((baseIdeal (C.isLB a₂) W₂).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]; exact (nonempty_cartier_of_locally_principal' _ _ hc₂).some
  have Δ₁ : Cartier ((baseIdeal (C.isLB a₁) W₁).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact cartierPullOfInt' (nonempty_cartier_of_locally_principal' _ _ hc₁).some s₂ (z₀ := z₂) (by
      rw [Scheme.IdealSheafData.support_comap]; exact h₁ _ hz₂)
  exact ⟨{ toModif := M₁.trans M₂, Δ₁ := Δ₁, Δ₂ := Δ₂ }⟩

private theorem nonempty_choice' : GlobalTheory.Published.Principalisation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw), IsVariety₀ TF.X Z → FreeOnOpen TF.X Z U P.u₁ → FreeOnOpen TF.X Z U P.u₂ → Nonempty (Choice TF.X Z U P) := by
  intro hPr E _ _ _ H Dw l Xo c TF Z r U P hv h₁ h₂
  obtain ⟨hs, hp, hc⟩ := hv
  have : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  exact nonempty_resol' hPr hs hp hc (dense_U₀ TF.X Z).nonempty (common₀ TF.X Z) h₁ h₂

theorem exists_weight_sections_nonvanishing : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)), WtBig P → (∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) → ∃ (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif), Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict := by
  intro hP hGD hQ hN hPr hS hT hL D T j Y e o hY hf Z P hB hG
  have hD := hB.one_le
  obtain ⟨TF⟩ := @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ _ _ _ TF Z hY.geo
  have hC : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T j Y e o hY hf Z TF la, @GlobalTheory.HSApp.vanBd_le_space D T j Y e o hY hf Z TF la⟩
  have hW := GlobalTheory.HSApp.gaps_of_wtBig' _ _ _ P hB
  have h₁ : FreeOnOpen TF.X Z Y.U P.u₁ :=
    _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hN hPr hS hT hL _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (hW _ (by simp)).2 (hC _)
  have h₂ : FreeOnOpen TF.X Z Y.U P.u₂ :=
    _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hN hPr hS hT hL _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (hW _ (by simp)).2 (hC _)
  obtain ⟨R⟩ := nonempty_choice' hPr _ _ _ _ _ _ TF Z _ Y.U P hV h₁ h₂
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    by_contra h
    have h0 : (T.Q.Dw j).p + (T.Q.Dw j).q = 0 := by omega
    have : dimFlag (T.Q.Dw j) = 0 := by simp [dimFlag, h0]
    omega
  obtain ⟨ω⟩ := @GlobalTheory.CompHS.canId_nonempty hP.p5 _ _ _ _ _ _ _ _ _ TF.Y TF.X Z R.toModif
    (fun K _ _ y => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso hP hGD _ _ _ _ _ _ K y hpq)
  obtain ⟨w₁, w₂⟩ := _root_.GlobalTheory.T.hodge_bundle_degree_squeeze hP hGD _ _ _ _ _ _ TF Z _ Y.U P R ω hY.geo h₁
  exact ⟨TF, R, ω,
    { conn := GlobalTheory.CompHS.Modif.geometricallyConnected_str _ _ _ _ _ R.toModif hV.1 hV.2.2 (dense_U₀ _ _)
      one_le := hD
      le_T := hB.le_T
      ext₁ := (hC _).1
      ext₂ := (hC _).1
      free₁ := h₁
      free₂ := h₂
      good := fun i hi => GlobalTheory.HSApp.goodOn_of_goodAt D T j Y e o hY hf Z _ (hG i hi)
      global_le := fun i _ => w₁ i (hC _)
      le_global := w₂ (hC _) }⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)), WtBig P → (∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) → ∃ (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif), Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict := by
  first | exact @_root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing | exact _root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing | (intros; apply _root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspValueNeZeroLowLevel
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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.LowNonzero
theorem exists_cusp_value_ne_zero_low_level (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hT : GlobalTheory.Published.ToroidalChartsForFan)
    (hN : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j))
    (hla : GapGe (((FlagTan.dimFlag (T.Q.Dw j) + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap (T.Q.Dw j))) :
    ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0), f ≠ 0 := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨TF⟩ := _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag hP1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hfree := _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP1 hG hQ hP.q15 hP.q16 hS hT hN _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ hla
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY hf Z TF _⟩
  haveI := (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hY.geo).2.2
  haveI : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  obtain ⟨s, hs, hs0⟩ := ne_zero_of_noBase hfree (dense_U₀ TF.X Z).nonempty
  refine ⟨(ofSpace TF.X Z Y.U _ ⟨s, hs⟩).1, (ofSpace TF.X Z Y.U _ ⟨s, hs⟩).2, fun h0 => hs0 ?_⟩
  have h1 : ofSpace TF.X Z Y.U _ ⟨s, hs⟩ = 0 := Subtype.ext h0
  exact congrArg Subtype.val (ofSpace_injective TF.X Z Y.U _ (h1.trans (map_zero _).symm))
end GlobalTheory.CovTop.LowNonzero
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
end
end

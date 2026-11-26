module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.RealTrue

theorem ontoUni_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (h : a = b)
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) :
    OntoUni fun k τ => (r k τ).reindex (finCongr h) (finCongr h) := by
  subst h; simpa using hr

theorem ontoUni_one {ι K : Type} [Group K] [TopologicalSpace K] {a : ℕ}
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm := hr.mul 1 1 τ
  rw [mul_one] at hm
  have hu := Matrix.mem_unitaryGroup_iff'.1 (hr.uni 1 τ)
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, Matrix.one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := Matrix.mul_assoc _ _ _
    _ = 1 := by rw [← hm, hu]

theorem inN_one {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    inN θ V (fun _ => 1) hn g τ = infM θ V hn g τ := by
  simp [inN, GlobalTheory.SeeSaw.inB, infM]

theorem valC_transport {ι : Type} [Fintype ι] {n : ℕ} {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (h : G = G')
    (lam : ι → DomWeight n) (f : Formalism.L2.Forms.Frames G → ℂ) (hf : f ∈ ValC G lam) :
    (fun z : Formalism.L2.Forms.Frames G' => f ⟨z.1, z.2⟩) ∈ ValC G' lam := by
  subst h; exact hf

end GlobalTheory.RealTrue


open GlobalTheory.RealTrue in
theorem GlobalTheory.AdForm.realOf_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hJ hJO hEmb
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hOk hPins l Z R.ψ R.θ hX.std hX.inf
  have hm2 : 2 ≤ B.R.m := B.R.two_le_m
  have hgX : ∀ i, i ≤ B.R.m → ((I.rec7 l Z).sp.X i).gram = 1 := by
    intro i hi
    rcases Nat.lt_or_ge i B.R.m with h | h
    · exact (hstd.1 i h).gS
    · obtain rfl : i = B.R.m := le_antisymm hi h
      have := (hstd.1 (B.R.m - 1) (by omega)).gT
      rwa [show B.R.m - 1 + 1 = B.R.m by omega] at this
  have hrk : ∀ i, i < B.R.m → 0 < B.R.N i ∧ B.R.N i ≤ B.R.N (i + 1) := by
    intro i hi
    have h := (hstd.1 i hi).rk
    rw [rankN (I.rec7 l Z) i hi.le, rankN (I.rec7 l Z) (i + 1) hi] at h
    exact ⟨h.1, h.2.1.le⟩
  have huni : ∀ i (hi : i ≤ B.R.m), OntoUni fun k : GinfC ((I.rec7 l Z).sp.X i) => (realOf u R g s J).r i hi k.1 := by
    intro i hi
    have hB := (hX.xs i hi).2.1
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ ((I.rec7 l Z).sp.X i) (g.x i).B hX.inf (fun τ => by
      rw [hB]; simp [gramAt, hgX i hi])
    exact ontoUni_reindex (rankN (I.rec7 l Z) i hi) this
  have huniT : OntoUni fun k : GinfC (I.rec7 l Z).sp.X' => (realOf u R g s J).rT k.1 := by
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ (I.rec7 l Z).sp.X' (fun _ => 1) hX.inf (fun τ => by
      simp [gramAt, hstd.2.1])
    exact ontoUni_reindex (rankP (I.rec7 l Z)) this
  have hrT : ∀ k, (realOf u R g s J).rT k = infM R.θ _ (rankP (I.rec7 l Z)) k := fun k => funext fun τ => inN_one _ _ _ _ _
  have hone : ∀ τ, infM R.θ _ (rankP (I.rec7 l Z)) 1 τ = 1 := by
    intro τ
    have := ontoUni_one huniT τ
    rw [← hrT]; exact this
  have htr1 : ∀ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) 1) z z := by
    intro z τ; rw [hone, Matrix.one_mul]
  have hJ1 : ∀ v, J v 1 = fun z => j v ⟨z.1, z.2⟩ := fun v => funext fun z => hJO v 1 (Subgroup.one_mem _) z z (htr1 z)
  have hG : gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) = fun _ => 1 := by
    funext τ; simp [gramC, gramP, hstd.2.1]
  refine ⟨huni, ?_, hrk, ?_, ?_, ?_, ?_⟩
  · exact huniT
  · intro i τ
    simp only [realOf]
    split_ifs with h
    · exact one_ne_zero
    · exact div_ne_zero h (hstd.2.2.2.1 τ)
  · intro i hi τ
    obtain ⟨Ch, _, A, hA, -⟩ := GlobalTheory.T.exists_tupleChain_adelicData I hOk hPins l Z u I.mu0
    obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u I.mu0 Ch A hA i hi
    exact Int.toNat_of_nonneg (he τ).2.2
  · intro v
    refine ⟨?_, fun k hk z z' hz => ?_⟩
    · show J v 1 ∈ ValC _ (sgT (D := I.rec7 l Z) u)
      rw [hJ1 v]
      have hm : j v ∈ ValC (gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z))) (sgT (D := I.rec7 l Z) u) := by
        rw [← hJ.range]; exact LinearMap.mem_range_self j v
      exact valC_transport hG _ _ hm
    · rw [hrT] at hz
      show J v k z' = J v 1 z
      rw [hJO v k hk z z' hz, hJO v 1 (Subgroup.one_mem _) z z (htr1 z)]
  · intro n hn
    subst hn
    have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := by
      have := hrk (B.R.m - 1) (by omega)
      rw [show B.R.m - 1 + 1 = B.R.m by omega] at this
      omega
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common I hOk hPins l Z u hN
    refine ⟨hN, h1, h2, h3, ?_⟩
    intro k hk τ
    have hb := GlobalTheory.T.lastGroup_embedding_real_components_block_form I hOk hPins l Z u R.θ hX.inf _ hN hEmb k τ
    have hB := (hX.xs B.R.m le_rfl).2.1
    show GlobalTheory.BranchFormula.IsBlock hN (inN R.θ _ (g.x B.R.m).B (rankN (I.rec7 l Z) B.R.m le_rfl) ((g.oT B.R.m rfl).emb (k, 1)) τ) (inN R.θ _ (fun _ => 1) (rankP (I.rec7 l Z)) k τ) 1
    rw [hB]
    first
      | simpa only [inN_one] using hb
      | simpa [inN, GlobalTheory.SeeSaw.inB, infM] using hb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpecStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_realData_spec : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  first | exact @GlobalTheory.AdForm.realOf_is | exact GlobalTheory.AdForm.realOf_is | (intros; apply GlobalTheory.AdForm.realOf_is <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembers
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberFrame


open Formalism.MainNotions.S in
theorem member_frame_of_standing_hypotheses_window_three {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Formalism.BasicNotions.Ties D) (hR : LocalBesselAndTopKernel.FamilyMidVolume D)
    (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3) (h29 : 29 ≤ C') (h40 : 40 ≤ Cl)
    (hCu : Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1) : Formalism.L2.SG.RowsConc.TFrameAt D := by
  have hH := h.1
  have hyp : LocalBesselAndTopKernel.hyp D large₂ 3 C' Cl Cg cb Cu cT CT := ⟨h.2.1, h.1, h.2.2⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_scale_log large₂
  have hG := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) h29
  have hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
    intro τ
    have hgap := Formalism.L2.SG.Pf.WuBL.gapAtLeast_of D.R (D.hc τ) (hG.2 τ)
    have hds := GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.L2.Col.lamSH_isHCParam (D.hc τ)) hgap
      (GlobalTheory.Core.Deg.CritVand.thrE_add_one_lt D.R hG.1)
    have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
    have hSF : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
      Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
    unfold VV
    rw [hds, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
    field_simp
  have hg : LocalBesselAndTopKernel.MidVolumeChain D large₂ (1 / 3) 0 := by
    intro τ
    rw [hVV τ]
    have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
    have h1 : 1 ≤ Real.exp ((0 : ℝ) * D.R.k * D.R.m * large₂.sc.L) := Real.one_le_exp (by simp)
    constructor
    · nlinarith
    · nlinarith
  have hD : UnitaryVolumeMass.cTvD D 1 :=
    Formalism.MainNotions.BridgeLemma.critical_level_lower_bound (C3' := 1) h40 (by norm_num) le_rfl hyp hg
  have hA : UnitaryVolumeMass.cTvA D :=
    Formalism.MainNotions.BridgeLemma.degree_ratio_product_formula D (Formalism.MainNotions.BridgeLemma.stMassRatio_of_siegel GlobalTheory.Mass.siegelMassRatio_holds D) hR
      (Formalism.MainNotions.BridgeLemma.sza_spl_of_data h.2.1) (Formalism.MainNotions.BridgeLemma.sza_g_ge hH)
  have F := Formalism.MainNotions.BridgeLemma.tfFacts_of h
  have hm : 2 * (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; norm_num; exact_mod_cast this
  have hm40 : (40 : ℝ) ≤ D.R.m := le_trans h40 hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk : 3 * Real.exp 8 ≤ (D.R.k : ℝ) := by
    have e8 : Real.exp 8 ≤ 3 ^ 8 := by
      have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      calc Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 8 := pow_le_pow_left₀ (Real.exp_pos _).le h3 8
    have hf := Formalism.MainNotions.BridgeLemma.two_le_degree_bis D
    have h5 : (40 : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hm40 5
    have hk' : 29 * (40 : ℝ) ^ 5 * 2 * 1 ≤ C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have : 0 ≤ C' := by linarith
      gcongr
    have := F.hk
    linarith
  exact fun w => F.tframe (by linarith) hm hCu hA hD hk w

theorem three_L_le {s : Scale} {R : Ranks} (h : RankVal s R) (he : s.eps < 1 / 52) (hx : 256 ≤ s.x) :
    3 * s.L ≤ (R.m : ℝ) - 1 := by
  have h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) := h.2.1.1
  have hx0 : 0 < s.x := by linarith
  have hx1 : 1 ≤ s.x := by linarith
  have he0 := s.eps_pos
  have hL : 1 ≤ s.x ^ s.eps := Real.one_le_rpow hx1 he0.le
  have h4 : (4 : ℝ) ≤ s.x ^ ((1 : ℝ) / 4) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ))⁻¹ := (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ = (256 : ℝ) ^ ((1 : ℝ) / 4) := by norm_num
      _ ≤ s.x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hs : s.x ^ s.eps * s.x ^ ((1 : ℝ) / 4) ≤ Real.sqrt (s.x * s.delta1) := by
    have e : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      unfold Scale.delta1
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [e, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  show 3 * s.x ^ s.eps ≤ (R.m : ℝ) - 1
  nlinarith

theorem Dstar_eq_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar = StandardLattice.massI X.toD7 X.toD7.R.r * StandardLattice.idxSig X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) *
      ∏ τ, X.toD7.dsig τ := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem admissible_ranks_of_mass_formula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.massI D D.R.r * StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ) :
    LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
      (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL)

end GlobalTheory.Fam.MemberFrame

end
end

module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthAllRun
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharacters
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UnramifiedCompanionChartCharacters
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullDataExtension
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTopOfCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleChar
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsXiOKNotTwistCond
noncomputable section

namespace GlobalTheory.TwistFieldCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open GlobalTheory.FinalJoin
open scoped TensorProduct

variable {D : D7}

theorem cF_eq (a : D.host.E) : GlobalTheory.Member.cF D a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [GlobalTheory.XiCounterexample.conj_emb]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

end GlobalTheory.TwistFieldCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleChar
noncomputable section

namespace GlobalTheory.FinalJoin2.ReadTwist

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val (D : D7) (y : (AfE D)ˣ) :
    ((cjFin D y : (AfE D)ˣ) : AfE D) = GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin
  rw [h]
  rfl

theorem normOne_iff {D : D7} (x : (AfE D)ˣ) :
    NormOne x ↔ (x : AfE D) * GlobalTheory.NormOneChar.bar (cF D) (x : AfE D) = 1 := Iff.rfl

theorem congOne_iff {D : D7} (N : ℕ) (x : (AfE D)ˣ) :
    x ∈ GlobalTheory.NormOneChar.congOne (cF D) N ↔ CongOne N x ∧ NormOne x := by
  unfold CongOne
  simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
  exact Iff.rfl

theorem cF_cF (D : D7) (y : D.host.E) : cF D (cF D y) = y := star_star y

theorem exists_rat {D : D7} (x : (AfE D)ˣ) (a : D.host.E) (h : (x : AfE D) = 1 ⊗ₜ a) (hn : NormOne x) :
    ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := by
  have key : ∀ b : D.host.E, b ≠ 0 → (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D b) =
      GlobalTheory.NormOneChar.diag D.host.F D.host.E b →
      ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := fun b hb e => by
    refine ⟨(GlobalTheory.NormOneChar.isUnit_diag D.host.F D.host.E hb).unit, b, rfl, eq_div_iff_mul_eq'.2 (Units.ext ?_)⟩
    rw [Units.val_mul, cjFin_val]
    exact e
  have hx : (x : AfE D) = GlobalTheory.NormOneChar.diag D.host.F D.host.E a := h
  by_cases ha : 1 + a = 0
  · have hc : cF D ≠ 1 := by
      have : cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [this]
      exact IsCMField.complexConj_ne_one _
    obtain ⟨z, hz⟩ : ∃ z, cF D z ≠ z := by
      by_contra h0
      push_neg at h0
      exact hc (AlgEquiv.ext h0)
    refine key (z - cF D z) (sub_ne_zero.2 hz.symm) ?_
    rw [hx, ← map_mul, map_sub, cF_cF]
    congr 1
    linear_combination (cF D z - z) * ha
  · refine key (1 + a) ha ?_
    have h1 : (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D a) = 1 := by
      have := (normOne_iff x).1 hn
      rw [h] at this
      rw [h]
      exact this
    rw [map_add (f := _), map_one, map_add (f := _), map_add (f := _), map_one, mul_add, h1, ← hx, mul_one, add_comm]

theorem cong_div {D : D7} (N : ℕ) (y : (AfE D)ˣ) (hu : IntUnit y) (hy : CongOne N y) :
    CongOne N (y / cjFin D y) ∧ NormOne (y / cjFin D y) := by
  have hv : ((y / cjFin D y : (AfE D)ˣ) : AfE D) =
      (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
    rw [div_eq_mul_inv, ← map_inv, Units.val_mul, cjFin_val]
  have h1 : (y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := Units.mul_inv y
  have h2 : GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := by
    rw [← map_mul, h1, map_one]
  rw [← congOne_iff]
  obtain ⟨-, hi⟩ := hu
  obtain ⟨w, hw, e⟩ := hy
  rw [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers] at hi hw
  rw [nsmul_eq_mul] at e
  have e' := congrArg (GlobalTheory.NormOneChar.bar (cF D)) e
  rw [map_sub, map_one, map_mul, map_natCast] at e'
  have hi' := GlobalTheory.NormOneChar.bar_mem (cF D) hi
  have hw' := GlobalTheory.NormOneChar.bar_mem (cF D) hw
  refine ⟨⟨(w - GlobalTheory.NormOneChar.bar (cF D) w) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D),
    mul_mem (sub_mem hw hw') hi', ?_⟩, ?_⟩
  · rw [hv]
    linear_combination (GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D)) * (e - e') + h2
  · rw [hv, map_mul, GlobalTheory.NormOneChar.bar_bar _ (cF_cF D)]
    linear_combination ((y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D)) * h2 + h1

theorem exists_xiOK_xiTilde : ∀ (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ), (p = D.host.pde ∨ p = D.host.pde') → XiRec D p de → ∃ xi, XiOK D p xi ∧ XiTilde xi de := by
  intro D p de hp h
  obtain ⟨h90, hfix, hcong⟩ := GlobalTheory.T.finiteIdeles_normOne_eq_div_conj_of_congOne D
  have hpp : p.Prime ∧ p % 15 = 1 := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hpp.2 (by norm_num)
  let q : (AfE D)ˣ →* (AfE D)ˣ := MonoidHom.id _ / cjFin D
  obtain ⟨xi, hxi⟩ := GlobalTheory.PrimaryCharacter.exists_factor_of_ker_le q de fun x hx => by
    have h1 : x = cjFin D x := div_eq_one.1 hx
    obtain ⟨a, ha⟩ := hfix x h1.symm
    exact h.real x a ha
  have ht : XiTilde xi de := hxi
  refine ⟨xi, ⟨fun x a ha hn => ?_, fun x hn hc => ?_, ?_, ?_, fun x hn => ?_⟩, ht⟩
  · obtain ⟨y, b, hb, rfl⟩ := exists_rat x a ha hn
    rw [ht, h.rat y b hb]
  · obtain ⟨y, hy, hyc, rfl⟩ := hcong p _ x hpp.1 hp2 (Dvd.intro_left _ rfl)
      (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hpp.1.pos) hn hc
    rw [ht, h.tame y hy hyc]
  · obtain ⟨y, hy, hyc, hne⟩ := h.ram
    obtain ⟨c1, c2⟩ := cong_div _ y hy hyc
    exact ⟨_, c2, c1, by rwa [ht]⟩
  · obtain ⟨m, hm, hf⟩ := h.fin
    refine ⟨m, hm, fun x hn => ?_⟩
    obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht, hf]
  · obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht]
    exact h.val y

end GlobalTheory.FinalJoin2.ReadTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleCharStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shortSeriesTwistChar_of_twistingIdeleChar : ∀ (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ), (p = D.host.pde ∨ p = D.host.pde') → XiRec D p de → ∃ xi, XiOK D p xi ∧ XiTilde xi de := by
  first | exact @GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde | exact GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde | (intros; apply GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullOfXiRec
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_full_of_xiRec : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ de, XiRec D p de → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ XiTilde TF.xi de ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hcan p hp P hP de hde
  obtain ⟨xi, hxi, ht⟩ := GlobalTheory.T.exists_shortSeriesTwistChar_of_twistingIdeleChar D p de hp.own hde
  obtain ⟨dd, TF, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol D J T hJ hT hc hcan p hp P hP xi hxi
  exact ⟨dd, TF, h1, h2, h3, h4 ▸ ht, h5⟩

end GlobalTheory.FinalJoin2.FullExt
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.RunOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val_eq (D : D7) (y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
    ((cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  have h : D.conjF = D.sp.cm.sig :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin sigR
  rw [h]
  rfl

theorem xi_det_of_isDetRoot {D : D7} {xi de : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} (h : XiTilde xi de)
    (V : Formalism.BasicNotions.TH.HSp D) (g : Formalism.L2.Theta.GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.IsDetRoot V g x) :
    xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom V g)) =
      de (Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x) := by
  rw [← GlobalTheory.AntiCycRead.quo_of_isDetRoot D V g x hx, ← h]
  congr 1
  apply GlobalTheory.AntiCycRead.quo_eq_of
  have e : (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) =
      ((Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) := rfl
  rw [e, ← cjFin_val_eq, ← Units.val_mul, div_mul_cancel]

theorem exists_run_pins : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ hC l hl

  obtain ⟨δ, hδdef⟩ : ∃ δ : Formalism.L2.Host.HChar D.host.E, δ = if l = D.host.pde then (R2 p).C.del else (R2 p).C.del' :=
    ⟨_, rfl⟩
  have hδ : Formalism.L2.Host.IsDelta (H := D.host) l δ := by
    rcases hl with rfl | rfl
    · rw [hδdef, if_pos rfl]; exact (R2 p).C.isDel
    · rw [hδdef, if_neg D.host.pde_ne.symm]; exact (R2 p).C.isDel'
  have hδv : ∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D := by
    intro x
    by_cases h : l = D.host.pde
    · rw [hδdef, if_pos h]; exact hC.delVal x
    · rw [hδdef, if_neg h]; exact hC.delVal' x
  obtain ⟨χ, de, hχ, hd, hfin⟩ := GlobalTheory.TameFinitePart.exists_xiRec D l δ hl hδ hδv
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D l := by
    rcases hl with rfl | rfl
    exacts [hC.field₁, hC.field₂]

  obtain ⟨Pk, hPk⟩ := hC.oneHalf
  obtain ⟨P, hP, hPv⟩ : ∃ P : HeightOneSpectrum (𝓞 D.host.K), ((l : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal ∧
      ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ PP ∈ placesOver (R2 p) ((R2 p).mu v) (ownAt D v),
        P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
    by_cases hex : ∃ v ∈ (R2 p).twPl, ownAt D v = l
    · obtain ⟨v, hv, hvl⟩ := hex
      refine ⟨Pk l, by rw [← hvl]; exact (hPk v hv).1, fun w hw hwl PP hPP => ?_⟩
      have := (hPk w hw).2 PP hPP
      rwa [hwl] at this
    · have hlp : l.Prime := by
        rcases hl with rfl | rfl
        exacts [D.host.pde_prime, D.host.pde'_prime]
      obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hlp
      exact ⟨P, hP, fun w hw hwl => absurd ⟨w, hw, hwl⟩ hex⟩

  have hJ : LawsJ p.T := (fw2 p).laws
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.FinalJoin.exists_top_of_core D p.T.toCore hC.laws hC.rank hF.kpsi
  have hcan : T.Q.Canon := by
    have e : T.toCore.Q = p.T.toCore.Q := congrArg (fun C => C.Q) hTc
    rw [show T.Q = p.T.Q from e]
    exact hC.canon
  obtain ⟨dd, TF, hTF, -, hJ', hxi, hh, hcov⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiRec D p.T T hJ hT hTc hcan l hF P hP de hd
  obtain ⟨r, rfl⟩ : ∃ r : GlobalTheory.RealIndexBound.RunData p.T, r.full = TF := by
    rw [← hJ']
    exact ⟨GlobalTheory.RealIndexBound.RunData.of TF, rfl⟩
  have hInR : ∀ i : Fin D.R.m, InR D ((i : ℕ) + 1) := fun i => ⟨Nat.le_add_left _ _, i.2⟩
  refine ⟨r, hTF, fun i => (hcov _ (hInR i)).1, fun j n hj => (hcov j hj).2 n, ?_, ?_⟩
  · intro i γ₀ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D _).2.2.1 γ₀ hγ
    rw [xi_det_of_isDetRoot hxi _ _ _ hx]
    exact hd.rat _ x rfl
  · intro v hv hvl i
    letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hvl]
      exact (hcov _ (hInR i)).2 _
    · intro PP hPP
      rw [hh]
      exact hPv v hv hvl PP hPP
    · have hδv' : (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = δ := by
        unfold ownAt at hvl
        unfold Formalism.L2.Host.CharFrame.delAt
        by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
        · rw [if_pos h] at hvl ⊢
          rw [hδdef, ← hvl, if_neg D.host.pde_ne.symm]
        · rw [if_neg h] at hvl ⊢
          rw [hδdef, ← hvl, if_pos rfl]
      refine ⟨χ, hδv' ▸ hχ, fun g x hx => ?_⟩
      rw [xi_det_of_isDetRoot hxi _ _ _ hx]
      exact hfin x _ rfl

end GlobalTheory.RunOnto

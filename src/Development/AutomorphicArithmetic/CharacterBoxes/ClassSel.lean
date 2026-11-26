module

public import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProof
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwGoodOneSetDiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.EX.DQ NumberField IsDedekindDomain

namespace GlobalTheory.EX.DQ


set_option maxHeartbeats 2000000 in
theorem twGoodOne_setDiv (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b))
    (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (p : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (H : TwGoodOne D ⟨twEOf O.xd, N0, S⟩ i b Q k p) :
    TwGoodOne (setDiv D N h) ⟨twEOf (O.tr N h).xd, N0, S⟩ i b Q k p := by
  unfold TwGoodOne at H ⊢
  have e1 : AvRec (setDiv D N h) = AvRec D := rfl
  have e2 : twEps (setDiv D N h) i = twEps D i := rfl
  rw [e1, e2]
  unfold IntegralHeckeForms.GoodTw at H ⊢
  obtain ⟨h1, ⟨eB, h2, h3, h4⟩, h5, h6, h7, h8⟩ := H
  exact ⟨h1, ⟨eB, h2, h3, h4⟩, fun j hj c => ⟨(h5 j hj c).1, (h5 j hj c).2⟩, h6, h7, h8⟩

theorem qd_setDiv : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    QD D O → QD (setDiv D N h) (O.tr N h) := by
  rintro D O N h ⟨h1, ⟨hc, N0, S, hS⟩, h3⟩
  refine ⟨h1, ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, fun a ha => ?_⟩⟩, h3⟩
  exact twGoodOne_setDiv D O N h N0 S _ _ _ _ _ ((hS w hw).2 a ha)

end GlobalTheory.EX.DQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberTopFinalContextParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContexts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContexts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem recExP_of_recAtG : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  intro hconds Q' QO h hq
  obtain ⟨ε0, hε0, h⟩ := h
  obtain ⟨ε1, hε1, hq⟩ := hq
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps C8 C5 c6 Cb he he0 he52 hC8 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb he (he0.trans (min_le_left _ _)) he52 hC8
  obtain ⟨K1, hq⟩ := hq eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he52 hC8
  refine ⟨K0.sup K1, fun C hstd hC hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hstd hC (large_of_sup hL).1
  obtain ⟨c1', hq⟩ := hq C hstd hC (large_of_sup hL).2
  refine ⟨max (max c1 c1') 0, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2q, hq⟩ := hq cD (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2', hlow⟩ := GlobalTheory.EX.WinLow.window_lower hconds eps C he he52 hstd cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max (max c2 c2q) c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hch)
  have hq := hq ch (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hch)
  obtain ⟨x1, hlow⟩ := hlow ch (le_trans (le_max_right _ _) hch)
  obtain ⟨x2, hint⟩ := exists_du_nat eps he he52
  have hq' : ∃ x3 : ℝ, Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩ → ∀ K : Ctx, Par.Of ⟨eps, C, cD, ch, C5, c6, Cb⟩ K → x3 ≤ K.s.x →
      ∀ β : BPt K, β.Is Q' → QO ⟨eps, C, cD, ch, C5, c6, Cb⟩ β.D β.O := by
    by_cases hp : Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩
    · obtain ⟨x3, h3⟩ := hq hp
      exact ⟨x3, fun _ => h3⟩
    · exact ⟨0, fun hp' => absurd hp' hp⟩
  obtain ⟨x3, hq'⟩ := hq'
  refine ⟨1, max (max x0 x3) (max x1 x2), one_pos, fun s P a b c hs hx d3 => ?_⟩
  have hok := d3.ok
  have hx0 : x0 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨du, hpos, hdu⟩ := hint s C cD ch P _ a b c hs hx2 hok
  obtain ⟨hD, hDle⟩ := GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P
  refine ⟨du, DsP P, hpos, hD, fun u => ?_, fun Lv h1 h2 h3 => ?_⟩
  · rw [one_mul]
    exact hlow s P _ a b c du (DsP P) hs hx1 hok hdu hDle u
  · let K : Ctx := ⟨s, C, cD, ch, P, _, a, b, c, hstd, hok, Lv, fun u => by rw [h1]; exact hdu u, h2, h3⟩
    obtain ⟨D, Y, g1, g2, g3, g4, ⟨X, f, T, co, hQ, he⟩, u1, u2, u3⟩ := h K rfl rfl rfl hs hx0 d3
    refine ⟨D, Y, g1, g2, g3, g4, fun p p1 p2 p3 p4 => ⟨fun hp => ?_, ?_⟩⟩
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj he
      exact hq' hp K ⟨rfl, rfl, rfl, hs, d3⟩ hx3
        ⟨X, f, T, co, Y, eq_of_heq he, p, p1, p2, p3, p4, ⟨C5, c6, Cb, d3⟩, g2, g3, u1, u2⟩ hQ
    · exact DQ.qd_setDiv D (Y.obj p) (nPrime p.L) p.ht ⟨u1, u2, u3⟩

end GlobalTheory.Fc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContextsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsLayeredData_of_goodScaleContexts : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  first | exact @GlobalTheory.Fc.recExP_of_recAtG | exact GlobalTheory.Fc.recExP_of_recAtG | (intros; apply GlobalTheory.Fc.recExP_of_recAtG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPasses
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem untw_set_eq (B : Base) (pl : Finset ℕ) (f : Fr B.toPre) :
    (TwDat.untw B pl).set f = {1, f.del, f.del'} := by
  refine Set.union_eq_left.2 ?_
  rintro _ ⟨w, rfl⟩
  change (if _ then f.del' else f.del) * 1 ∈ _
  rw [mul_one]
  split_ifs
  · exact .inr (.inr rfl)
  · exact .inr (.inl rfl)

theorem recAtG_of_two_passes : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  intro h2v KP Q Q' hK hF hX hS
  have hL := EvG.imp (EvG.inter hF (EvG.inter hX hS)) fun K _ _ _ _ H =>
    (large₂.inter (large₂.inter H.1 (lg_forced K)) (large₂.inter H.2.1 H.2.2))
  refine EvG.imp (EvG.inter (EvG.inter hK.ex hL) (evG_of_ev GlobalTheory.Mem.Top.LayOfCore.lay_of_core)) ?_
  rintro K _ _ _ _ ⟨⟨⟨P, f₀, hO, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩, hlay⟩
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks (S₁ P f₀) (fun F F₀ => S₂ P f₀ F F₀ {1, f₀.del, f₀.del'}) (a₁ _ _)
    (fun F F₀ => a₂ _ _ F F₀ _)
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨⟨h1, hfo⟩, h2, h3⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hO
    ⟨hH₁, by rw [untw_set_eq]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _))
  obtain ⟨C, W, V, S, N, G, c, hQ⟩ := h1 hKP hfo rfl
  obtain ⟨B', f', T', -, -, -, -, -, C', W', V', S', N', G', c', -, hTw, hQ'⟩ :=
    h3 hKP rfl C W V S N G c hQ (h2 hKP rfl C W V S N G c hQ) (fun _ => ∅) (fun _ _ _ => ∅) (by simp)
  obtain ⟨Y, hY, k1, k2, k3, k4⟩ := hlay ⟨B', C', W', V', S', N', G'⟩ f' T' c' (h2v _ c'.real.vol)
  have hTw' : DQ.TwAllAt (Stages.toD7 ⟨B', C', W', V', S', N', G'⟩) Y.nch Y.xd := by
    have e1 : Y.nch = c'.O.nch := by rw [← hY]; rfl
    have e2 : Y.xd = c'.O.xd := by rw [← hY]; rfl
    rw [e1, e2]
    exact hTw
  exact ⟨_, Y, k1, k2, k3, hTw'.twAt, ⟨_, f', T', c', hQ', by rw [hY]⟩, k4, hTw', c'.mtStable⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPassesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) → ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' → RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  first | exact @GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | exact GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | (intros; apply GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem memberTop_final_contextParameters :
    StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop),
      GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) →
      RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) :=
  fun hAll hU KP Q Q' QO hB hF hE hS hEv =>
    GlobalTheory.T.existsLayeredData_of_goodScaleContexts hAll Q' QO
      (GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold hU) KP Q Q' hB hF hE hS)
      hEv

end GlobalTheory.Fc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_pair_form {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

theorem normPrimes_unconditional : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.normPrimesN UpperTheory.T3.shortNorm eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d (hs ▸ hq) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_pair_form h4⟩

theorem levelPrime_unconditional : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.levelPrimeN UpperTheory.T3.shortNorm eps he0 he1 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := R.toFrame.ord_pos
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m (hs ▸ hq)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_pair_form hT4⟩

theorem normPrimes_and_levelPrime_unconditional : NormPrimes ∧ LevelPrime :=
  ⟨normPrimes_unconditional, levelPrime_unconditional⟩

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem kit_of_points : ∀ (Q : PtProp) (C : FC) (cD ch : ℝ) (s : Scale) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool), (∀ u0 : ℕ, u0 < R.n → ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q) → ∃ k : Kit C cD ch s, ∀ i, (∃ u0, (k.pt i).From H a b c u0) ∧ CanonInst (k.pt i).ta.Gx ∧ (k.pt i).Has Q := by
  intro Q C cD ch s R H a b M c hObj
  have hn : 0 < R.n := by unfold Ranks.n; exact R.ord_pos
  choose pt hsc hval har hfrom hcan hhas using fun i : Fin R.n => hObj i.1 i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ⟨⟨i.1, hfrom i⟩, hcan i, hhas i⟩⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩

end GlobalTheory.EX.DC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

theorem weightWindowRequirement_host_of_point : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → Formalism.MainNotions.AuxBlock8.WeightVectorExists p.D p.L p.ta.Gx C.GK → ∃ a' b' : R.A → ℤ, (∀ t, t ∉ H.TT → a' t = 0 ∧ b' t = 0) ∧ WinOK p.L.sc C.GK H a' b' ∧ WOK p.L.sc cD ch C.GK H a' b' := by
  intro C cD ch p R H a b M c u0 _ hV hF hC hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, -, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  obtain ⟨a', ha, b', hb, hW⟩ := hW
  have ha' := Fintype.mem_piFinset.1 ha
  have hb' := Fintype.mem_piFinset.1 hb
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  refine ⟨a', b', fun t ht => ?_, fun t ht => ?_, ?_⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_false, Finset.mem_singleton] at h1 h2
    exact ⟨h1, h2⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_true, G.winA, G.winB, Finset.mem_Icc, Int.ceil_le, Int.le_floor, G.Nstar] at h1 h2
    exact ⟨h1, h2⟩
  · have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
        p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
        (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
         open Classical in
         ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
          (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l then (1 : ℝ) else 0) +
            4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) := by
      intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6
      obtain rfl : G.hP p.D = hf := funext e6
      subst e1 e2 e0 e3 e4 e5
      unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands at hW
      simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1] at hW
      exact hW
    exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh'

end GlobalTheory.EX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfPrimesRel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem smallPrimeOne_of_primesRel : GlobalTheory.Lin.PrimesRel → SmallPrimeOne := by
  intro h
  obtain ⟨C₀, Cr, cr, c, h0, h1, h2, h3, H⟩ := GlobalTheory.Lin.primesAPInterval_of_primesRel h
  obtain ⟨s, hsC, hs21, hsr⟩ : ∃ s : ℝ, C₀ ≤ s ∧ 21 ≤ s ∧ 200 * Cr / cr ≤ s :=
    ⟨max C₀ (max 21 (200 * Cr / cr)), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hss : s ≤ s ^ 2 := by nlinarith
  have hexp : Cr * Real.exp (-cr * s) ≤ 1 / 200 := by
    have e1 : 200 * Cr ≤ cr * s := by
      rw [div_le_iff₀ h2] at hsr; linarith
    have e2 := Real.add_one_le_exp (cr * s)
    have e3 : 0 < Real.exp (cr * s) := Real.exp_pos _
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ e3 (by norm_num)]
    linarith
  refine ⟨3 * s ^ 2 + 1, by nlinarith, ?_⟩
  intro M hM
  rcases Nat.eq_or_lt_of_le hM with rfl | hM3
  · refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have e1 : ((2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (3 * s ^ 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    refine le_trans ?_ e1
    norm_num
  have hm3 : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hB0 : (0 : ℝ) < 4 * (M : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ 4 * (M : ℝ) := by linarith
  have hlB : 1 ≤ Real.log (4 * (M : ℝ)) := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set Y : ℝ := (4 * (M : ℝ)) ^ (s ^ 2) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hB0 _
  have hlY : Real.log Y = s ^ 2 * Real.log (4 * (M : ℝ)) := Real.log_rpow hB0 _
  have hlY2 : s ^ 2 ≤ Real.log Y := by rw [hlY]; nlinarith [sq_nonneg s]
  have hlY0 : 0 < Real.log Y := by linarith
  have hrho : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * M) Y ≤ 1 / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have a1 : Real.exp (-cr * Real.log Y / Real.log (4 * (M : ℝ))) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      rw [hlY, ← mul_assoc, mul_div_assoc, div_self (by linarith), mul_one]
      nlinarith
    have a2 : Real.exp (-cr * Real.sqrt (Real.log Y)) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      have : s ≤ Real.sqrt (Real.log Y) := Real.le_sqrt_of_sq_le hlY2
      nlinarith
    have b1 := mul_le_mul_of_nonneg_left a1 h1.le
    have b2 := mul_le_mul_of_nonneg_left a2 h1.le
    linarith
  have h7 : (4 * (M : ℝ)) ^ (7 : ℝ) ≤ 1 * Y ^ ((1 : ℝ) / 3) := by
    rw [one_mul, hY, ← Real.rpow_mul hB0.le]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hc := H M 1 hM3 (Nat.coprime_one_left M) Y 1
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) le_rfl hrho h7
  have hpos : 0 < c * 1 * (4 * (M : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y := by
    have := Real.rpow_pos_of_pos hB0 (-6 : ℝ)
    positivity
  have hcard := lt_of_lt_of_le hpos hc
  rw [Nat.cast_pos, Finset.card_pos] at hcard
  obtain ⟨p, hp⟩ := hcard
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨-, hp2⟩, hpp, hpm⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · have : p % M = 1 % M := hpm
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  · have e1 : (p : ℝ) ≤ Y * (1 + 1) :=
      le_trans (Nat.cast_le.2 hp2) (Nat.floor_le (by positivity))
    have hM0 : (0 : ℝ) < M := by linarith
    have e2 : Y ≤ (M : ℝ) ^ (3 * s ^ 2) := by
      rw [Real.rpow_mul hM0.le]
      apply Real.rpow_le_rpow hB0.le _ (by positivity)
      have : (M : ℝ) ^ (3 : ℝ) = (M : ℝ) ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (M : ℝ) 3
      rw [this]
      have : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      nlinarith
    rw [Real.rpow_add hM0, Real.rpow_one]
    nlinarith

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasWithDutyWallAndChoices
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem has_withDuty_wall_and_choices {Q : PtProp} {C : FC} {cD ch C8 C5 c6 Cb : ℝ} (p : Pt C) {R : Ranks} {H : Host R} {q0 : ℕ}
    {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (hC : Std C) (hT : H.CT2 = C.CT2)
    (hH : HostGood p.L.sc C8 C5 c6 Cb H q0) (hq : (q0 : ℝ) < p.L.sc.X')
    (h0 : ∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) (hW : WOK p.L.sc cD ch C.GK H a b)
    (hV : Val C cD ch p.L) (hF : p.From H a b c u0) (hI : CanonInst p.ta.Gx) (hQ : p.Has Q) :
    p.Has ((withDuty Q).and WallPt) ∧ ThickSetLowerBound p.L ∧ ChBad_at p.ta.Gx Cb ∧ ChQD_at p.D p.L.sc.x p.L.sc.eps C5 := by
  have hw := GlobalTheory.EX.wreq_of_wok C cD ch p R H a b M c u0 hC hV hF hI h0 hW
  obtain ⟨hv, -, hT2, -, hQD, hBox, -, -, hBad, -, -, -, ⟨hp, hmod, -, hne, hne'⟩, hlev⟩ := hH
  have hb := GlobalTheory.EX.chBad_of_from C p R H a b M c u0 Cb hF hI hBad
  have eS := hF.QS_eq
  have hBW := hF.boxesW hBox
  have hQW := hF.qdRowsW hBox
  obtain ⟨eR, -, eT2, eq, ed, eg, ep, ep', hsub, -⟩ := hF
  subst eR
  have hq0 : (0 : ℝ) < q0 := by exact_mod_cast hp.pos
  have hXb := X'_le_b p.L.sc
  refine ⟨⟨⟨hQ, hw, ?_, ?_, q0, hsub (by rw [hlev]; simp), hp, ?_, ?_, hq, ?_, ?_, ?_⟩,
    ⟨hV.mem_box.1, hV.mem_box.2, hw⟩⟩, ?_, hb, ?_⟩
  · exact hBW
  · exact hQW
  · rw [eS, eq, ed]; exact hmod
  · rw [Real.log_le_iff_le_exp hq0]
    exact hq.le.trans hXb
  · rw [ep]; exact hne
  · rw [ep']; exact hne'
  · intro i hi
    have hg := (hv.2.2.2.2.1 i).1
    rw [← eg, ← hi] at hg
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  · unfold ThickSetLowerBound Host.secondSet_card_lower_bound
    rw [eT2, hV.secondConstant_eq, hV.host.2.2.2.2.2.1, ← hT, ← hv.2.2.2.2.2.1]
    exact hT2
  · unfold ChQD_at
    rw [eq, ed]
    exact hQD

end GlobalTheory.EX.DC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FixAndWinOfNumAt
namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem fix_and_win_of_numAt (eps : ℝ) (C : FC) (Fm : FamP eps) (hS : Std C) (hO : Fm.cOut = C.cOut)
    (hN : ∀ x (i : Fm.Ix x), Nonempty (NumAt C (Fm.L x i))) : DC.PageFix Fm ∧ DC.PageWin Fm := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, sCt⟩, sCc, -, -, scw, sCYL, -, sCp, seP, scTO, -, sCe, -⟩ := hS
  simp only [FamP.cOut, FC.cOut, List.cons.injEq] at hO
  obtain ⟨oCt, oCc, -, -, -, ocw, oCYL, -, -, -, oCp, oeP, ocTO, -, oCe, -⟩ := hO
  refine ⟨⟨oCp.trans sCp, oeP.trans seP, ?_, ?_, oCe.trans sCe, oCc.trans sCc, ocw.trans scw, oCYL.trans sCYL,
    fun x hx i => ?_⟩, fun x hx i => ?_⟩
  · rw [ocTO, oeP, scTO, seP]; norm_num
  · rw [ocTO, oCt, scTO, sCt]; norm_num
  · obtain ⟨N⟩ := hN x i
    refine ⟨N.ccK_top, N.cloud1, N.g_le, N.pde_lt.1, N.pde_lt.2, N.logFiveDepth_eq, ?_, ?_⟩
    · have h := N.Lw_eq
      rw [Fm.L_x x i hx, Fm.L_eps x i, ← oCt] at h
      exact h
    · have h := (Fm.parT x hx i).TO_eq
      rw [Fm.parT_cTO, Fm.L_x x i hx] at h
      exact h
  · obtain ⟨N⟩ := hN x i
    have h := N.win
    rw [Fm.L_x x i hx, Fm.L_eps x i] at h
    exact h

end GlobalTheory.EX.DC
end

section -- merged from Development.AutomorphicArithmetic.CharacterBoxes.ObjCTrue
section -- merged from Development.AutomorphicArithmetic.CharacterBoxes.DesignS
noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.DC GlobalTheory.Fc NumberField

theorem designS : ∀ (Q : Par → PtProp) (cT : ℝ → ℝ → ℝ) (la : ℝ) (G : FReq), 1 < la → DC.MinkDiv →
    KitCPW la (fun κ => ((withDuty (DC.withObj (Q κ))).and DC.WallPt).and G.pt) →
    DC.DesignChoices (DC.WithTw fun Fm => (∃ κ : Par, Link κ Fm ∧ DC.cls (Q κ) Fm) ∧ G.cls la Fm) 3 cT := by
  rintro Q cT la G hla hM ⟨ε0, hε0, hK⟩
  refine ⟨min ε0 (1 / 53), lt_min hε0 (by norm_num), fun eps he hle K => ?_⟩
  have he52 : eps < 1 / 52 := lt_of_le_of_lt (hle.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨CT2, C8, C5, c6, Cb, K0, hC8, hC5, hc6, hCb, hK⟩ := hK eps he (hle.trans (min_le_left _ _)) he52
  obtain ⟨C, hStd, hCT2, hCp, hLK, hLK0, hGK⟩ := exists_std_large (thrTu K (cT eps 9)) K0 CT2 C8 hC8
  obtain ⟨c1, hK⟩ := hK C hStd hCT2 hCp hLK0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  obtain ⟨c2, hK⟩ := hK (max c1 c1') (le_max_left _ _)
  obtain ⟨c2', hN⟩ := hN (max c1 c1') (le_max_right _ _)
  obtain ⟨x0, S, hK⟩ := hK (max c2 c2') (le_max_left _ _)
  obtain ⟨x0', hN⟩ := hN (max c2 c2') (le_max_right _ _)
  have hx1 : (1 : ℝ) < max 2 (max x0 x0') := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  have hK' : ∀ s : Scale, s.eps = eps → max 2 (max x0 x0') ≤ s.x → S.Mem s →
      ∃ k : Kit C (max c1 c1') (max c2 c2') s, ∀ i, (k.pt i).Has (((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt).and G.pt) ∧
        ThickSetLowerBound (k.pt i).L ∧ ChBad_at (k.pt i).ta.Gx Cb ∧ ChQD_at (k.pt i).D (k.pt i).L.sc.x (k.pt i).L.sc.eps C5 :=
    fun s hs hx hm => hK s hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hm
  choose k hk using hK'
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) ∧ ChTT_at ((k s h h' h'').pt i).L ∧
      ChCode_at ((k s h h' h'').pt i).L 3 C.P.CF := by
    intro s h h' h'' i
    refine hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, hTu, hQ, hR, -, hWn, -⟩ :=
    exists_famP_of_kits eps C _ _ _ la S he he52 hx1 hla.le hStd hGK k (fun s h h' h'' i => (hnum s h h' h'' i).1)
  replace hOut : Fm.cOut = C.cOut := hOut
  have hall := hR (fun D L Gx => (ThickSetLowerBound L ∧ ChBad_at Gx Cb ∧ ChQD_at D L.sc.x L.sc.eps C5) ∧
      (Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) ∧
      Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊)
    (fun s h h' h'' i => ⟨(hk s h h' h'' i).2, hnum s h h' h'' i, ((k s h h' h'').val i).words⟩)
  have hCF : (1 : ℝ) ≤ C.P.CF := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hc := hQ ((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt) (fun s h h' h'' i => (hk s h h' h'' i).1.1)
  have hGc : G.cls la Fm := ⟨fun y => by
      obtain ⟨Y, a, b⟩ := S.windows y
      exact ⟨Y, a, fun x c d => hWn ▸ b x c d⟩,
    hQ G.pt (fun s h h' h'' i => (hk s h h' h'' i).1.2)⟩
  obtain ⟨hFix, hWin⟩ := fix_and_win_of_numAt eps C Fm hStd hOut (fun x i => (hall x i).2.1.1)
  have hCYL : Fm.CYL = 9 := hFix.2.2.2.2.2.2.2.1
  have hlt : ∀ x, x ≥ Fm.x1 + 1 → Fm.x1 < x := fun x hx => by linarith
  have hLarge : Fm.Large (thrTu K (cT eps 9)) C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hLK
  have hTw : TwGood Fm := classOf_twPt Fm fun x hx i => (hc x hx i).1.1.2.2.2
  have hQD : ChosenQD Fm C5 := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have := (hall x i).1.2.2
    rwa [Fm.L_x x i (hlt x hx), Fm.L_eps x i] at this
  have hreq := classOf_reqPt Fm fun x hx i => ⟨(hc x hx i).2, (hc x hx i).1.2.2.1, (hc x hx i).1.2.2.2.1⟩
  have hDG : Formalism.MainNotions.DGamDvdF Fm := ⟨Fm.x1 + 1, fun x hx i u => (hc x (hlt x hx) i).1.1.2.2.1 _ (hM _) u⟩
  have hTame : Formalism.MainNotions.TameDistinctF Fm := ⟨Fm.x1 + 1, fun x hx i => (hc x (hlt x hx) i).1.1.2.1⟩
  have hCFeq : Fm.CF = C.P.CF := by
    have := congrArg (fun f : ℝ → List ℝ => (f 0).getD 9 0) hMid
    simpa [FamP.cMid, FC.cMid] using this
  have hUp : Formalism.MainNotions.CodeUpF Fm 3 C.P.CF := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h := (hall x i).2.2
    rw [Fm.L_x x i (hlt x hx)] at h
    have hx0 : (0 : ℝ) ≤ x := by have := Fm.one_lt_family_threshold; linarith
    rw [h]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hT2 : ThickSetEventually Fm := ⟨0, fun x _ i => (hall x i).1.1⟩
  have hTT : ChosenTT Fm := ⟨0, fun x _ i => (hall x i).2.1.2.1⟩
  have hBad : ChosenBad Fm Cb := ⟨0, fun x _ i => (hall x i).1.2.1⟩
  have hCode : ChosenCode Fm 3 C.P.CF := ⟨0, fun x _ i => (hall x i).2.1.2.2⟩
  have hLink : Link ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩ (setTu Fm (cT eps 9)) := by
    refine ⟨rfl, ⟨hC5, hc6, hCb⟩, hStd, hPre, ?_, hMid, hLast⟩
    show (setTu Fm C.CTu).cOut = _
    rw [← hTu]
    exact hOut
  refine ⟨setTu Fm (cT eps 9), C.P.CF, C5, Cb, ⟨⟨⟨_, hLink, (setTu_cls _ Fm _).2 ⟨hc, hFix, hWin⟩⟩, hGc⟩, hTw⟩, zero_le_one.trans hCF,
    (setTu_large Fm K _ _).2 hLarge, hC5, hCb, hT2, hTT, hBad, hQD, hCode, hreq.2.1, hreq.2.2, hDG, ?_, hTame, hCFeq, hUp,
    hCYL.le⟩
  show cT eps Fm.CYL ≤ cT eps 9
  rw [hCYL]

end UpperTheory.Top

end
end

section -- merged from Development.AutomorphicArithmetic.CharacterBoxes.KitS
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

open GlobalTheory.Fc

theorem kitS : ∀ (Q : Par → PtProp) (la : ℝ) (G : FReq), DC.HostWW la G.req → ObjCP Q →
    KitCPW la (fun κ => ((withDuty (Q κ)).and DC.WallPt).and G.pt) := by
  intro Q la G hHost hObj
  obtain ⟨εH, hεH, hHost⟩ := hHost
  obtain ⟨εO, hεO, hObj⟩ := hObj
  refine ⟨min εH εO, lt_min hεH hεO, fun eps he he0 he1 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, KW, h8, h5, h6, hb, hHost⟩ := hHost eps he (he0.trans (min_le_left _ _)) he1
  obtain ⟨KO, hObj⟩ := hObj eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he1 h8
  refine ⟨CT2, C8, C5, c6, Cb, KW.sup KO, h8, h5, h6, hb, fun C hC hT hP hL => ?_⟩
  obtain ⟨hLW, hLO⟩ := GlobalTheory.EX.fc_large_of_sup hL
  obtain ⟨c1, hObj⟩ := hObj C hC hP hLO
  obtain ⟨c1', hHost⟩ := hHost C hC hT hP hLW
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hObj⟩ := hObj cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hHost⟩ := hHost cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hObj⟩ := hObj ch ((le_max_left _ _).trans hch)
  obtain ⟨xH, S, hHost⟩ := hHost ch ((le_max_right _ _).trans hch)
  have hmid := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG : 0 ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hF : 0 ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xC, hCode⟩ := exists_injective_words eps C.CGam C.P.CF he he1 hG hF
  obtain ⟨xq, hq⟩ := small_prime_lt eps C8 he h8
  refine ⟨max (max xH xO) (max xC xq), S, fun s hs hx hmem => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxH, hxO⟩, hxC, hxq⟩ := hx
  obtain ⟨R, H, q0, a, b, hRV, hHT, hH, hqH, h0, hWin, hW, hGq⟩ := hHost s hs hxH hmem
  obtain ⟨c, hc, -⟩ := hCode s R hs hxC hRV
  have hHT' : H.CT2 = C.CT2 := hHT.trans hT.symm
  have hn : 0 < R.n := R.toFrame.ord_pos
  have hq0 : (q0 : ℝ) < s.X' := by
    have hqp : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    have hn' : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    exact hq s _ q0 hs hxq (by positivity) hH.1.log_cond_le hH.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  choose pt hsc hval har hfrom hcan hhas using
    fun i : Fin R.n => hObj s R H q0 a b _ c i.1 hs hxO hRV hHT' (by show HostGood s C.P.Cpde C5 c6 Cb H q0; rw [hP]; exact hH) hqH hWin rfl hc i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ?_⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩
  · have hd := DC.has_withDuty_wall_and_choices (C8 := C8) (c6 := c6) (q0 := q0) (pt i) hC hHT' (by rw [hsc i]; exact hH)
      (by rw [hsc i]; exact hq0) h0 (by rw [hsc i]; exact hW) (hval i) (hfrom i) (hcan i) (hhas i)
    exact ⟨⟨hd.1, G.at_of_from (hfrom i) (by rw [hsc i]; exact hGq)⟩, hd.2⟩

end UpperTheory.Top
end

section -- merged from Development.AutomorphicArithmetic.CharacterBoxes.HostWW
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

private theorem gk_nonneg {C : FC} (h : Std C) : C.GK.Nonneg := by
  obtain ⟨⟨f1, f2, f3, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hm, hl⟩ := h
  have hm' : ∀ c ∈ C.cMid C.P.CF, 0 ≤ c := fun c hc => zero_le_one.trans (hm c hc)
  have hl' : ∀ c ∈ C.cLast, 0 ≤ c := fun c hc => zero_le_one.trans (hl c hc)
  refine ⟨hm' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_,
    by rw [f2]; norm_num, by rw [f3]; norm_num, by rw [f1]; norm_num, hl' _ ?_⟩ <;> simp [FC.cMid, FC.cLast]

private theorem large_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
   ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

private theorem scale_ext {s s' : Scale} (h1 : s.x = s'.x) (h2 : s.eps = s'.eps) (h3 : s.J = s'.J) : s = s' := by
  cases s; cases s'; simp_all

theorem UpperTheory.Top.hostWW :
    ∀ (Q : PtProp) (la : ℝ) (P : HostReq), 1 < la → DC.HostExQW la P → DC.ObjC Q → DC.WClosed → DC.HostWW la P := by
  rintro Q la P hla hH ⟨ε0, hε0, hO⟩ ⟨ε1, hε1, hW⟩
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps he hle he52 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, h5, h6, hb, S, hH⟩ := hH eps he he52
  obtain ⟨K0, hO⟩ := hO eps C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) he52 h8
  obtain ⟨K1, hW⟩ := hW eps he (hle.trans (min_le_right _ _))
  refine ⟨CT2, C8, C5, c6, Cb, K0.sup K1, h8, h5, h6, hb, fun C hStd hCT2 hCp hL => ?_⟩
  obtain ⟨hL0, hL1⟩ := large_sup hL
  obtain ⟨c1, hO⟩ := hO C hStd hCp hL0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hO⟩ := hO cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hN⟩ := hN cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hO⟩ := hO ch ((le_max_left _ _).trans hch)
  obtain ⟨xN, hN⟩ := hN ch ((le_max_right _ _).trans hch)
  have hmid := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCF : (0 : ℝ) ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hCG : (0 : ℝ) ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xw, hw⟩ := exists_weights_in_windows eps C he he52 hStd
  obtain ⟨xc, hc⟩ := exists_injective_words eps C.CGam C.P.CF he he52 hCG hCF
  obtain ⟨x1, hx1, a1, a2, a3, a5, a6⟩ : ∃ x1 : ℝ, 1 < x1 ∧ xH ≤ x1 ∧ xO ≤ x1 ∧ xN ≤ x1 ∧ xw ≤ x1 ∧ xc ≤ x1 :=
    ⟨max 2 (max xH (max xO (max xN (max xw xc)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  let G : Scale → Prop := fun s => ∃ (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ),
    RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ q0 = DC.q0H H ∧ (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) ∧
      WinOK s C.GK H a b ∧ WOK s cD ch C.GK H a b ∧ P C5 s R H q0
  let Q' : PtProp := fun D L _ Gx _ K _ _ _ => AuxBlock8.WeightVectorExists D L Gx K → G L.sc
  have hK : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q' := by
    intro s hs hx hm
    obtain ⟨R, H, q0, hRV, hHT, hHG, hq, hP⟩ := hH s hs (a1.trans hx) hm
    obtain ⟨a, b, hab⟩ := hw s R H hs (a5.trans hx) hRV
    obtain ⟨c, hci, -⟩ := hc s R hs (a6.trans hx) hRV
    obtain ⟨k, hk⟩ := DC.kit_of_points Q C cD ch s R H a b _ c fun u0 hu =>
      hO s R H q0 a b _ c u0 hs (a2.trans hx) hRV (hHT.trans hCT2.symm) hHG hq hab rfl hci hu
    refine ⟨k, fun i hp => ?_⟩
    obtain ⟨⟨u0, hF⟩, hI, -⟩ := hk i
    obtain ⟨a', b', e1, e2, e3⟩ := weightWindowRequirement_host_of_point C cD ch (k.pt i) R H a b _ c u0 hStd (k.val i) hF hI hp
    rw [k.sc_eq i] at e2 e3 ⊢
    exact ⟨R, H, q0, a', b', hRV, hHT, hHG, hq, e1, e2, e3, hP⟩
  choose k hk using hK
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) := by
    intro s h h' h'' i
    refine (hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)).1
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact a3.trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, -, hQ, -, hJ, hWin, -⟩ :=
    exists_famP_of_kits eps C cD ch x1 la S he he52 hx1 hla.le hStd (gk_nonneg hStd) k hnum
  have hFL : Fm.Large K1 C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hL1
  obtain ⟨xW, hW⟩ := hW Fm C.P.CF trivial hFL
  refine ⟨max (Fm.x1 + 1) xW, S, fun s hs hx hm => ?_⟩
  have hx' : Fm.x1 < s.x := by have := (le_max_left _ _).trans hx; linarith
  obtain ⟨i⟩ := Fm.Ix_win s.x (by rw [hWin]; exact hm.2)
  have hG : G (Fm.L s.x i).sc := hQ Q' hk s.x hx' i (hW s.x ((le_max_right _ _).trans hx) i)
  have e : (Fm.L s.x i).sc = s :=
    scale_ext (Fm.L_x _ i hx') ((Fm.L_eps _ i).trans hs.symm) ((Fm.L_J _ i).trans (hJ.trans hm.1.symm))
  rw [e] at hG
  exact hG
end

section -- merged from Development.AutomorphicArithmetic.CharacterBoxes.SmallestPrimePolynomialBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

namespace UpperTheory.Top.PolynomialHostPrimeBound

open GlobalTheory.EX.DC

private theorem smallest_prime_polynomial_bound {A C : ℝ} (hA : 1 ≤ A)
    (hS : ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A)
    {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (h1 : (H.pde : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C)
    (h2 : (H.pde' : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C) :
    (q0H H : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ ((3 + 2 * C) * A) := by
  obtain ⟨p, hp, hm, hle⟩ := hS _ (one_lt_rPrH_mul H)
  have hq : (q0H H : ℝ) ≤ p := by exact_mod_cast globalTwisting_le_fact H hc hp hm
  have hN : 2 ≤ H.QS * H.q * H.d :=
    H.hyp.2.1.one_lt.trans_le (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))
  have e : ((H.QS : ℝ) * H.q * H.d) = ((H.QS * H.q * H.d : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h1 h2 ⊢
  have a2 : 0 < H.pde - 1 := Nat.sub_pos_of_lt H.pde_prime.one_lt
  have a3 : 0 < H.pde' - 1 := Nat.sub_pos_of_lt H.pde'_prime.one_lt
  have hr : rPrH H ≤ 2 * (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1)) := by
    have hM : 0 < H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) a2) a3
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul _ hM.ne'
    refine (rPrH_le H hr ?_).trans hr2
    rw [hc, Ideal.absNorm_top, mul_one]
    exact Nat.not_dvd_of_pos_of_lt hM hr1
  generalize H.QS * H.q * H.d = N at *
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr' : rPrH H ≤ N * (N * H.pde * H.pde') := hr.trans (by gcongr <;> omega)
  have hr'' : (rPrH H : ℝ) ≤ N * (N * H.pde * H.pde') := by exact_mod_cast hr'
  have hb : ((rPrH H * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (3 + 2 * C) := by
    have : (N : ℝ) ^ (3 + 2 * C) = N * (N * N ^ C * N ^ C) * N := by
      rw [show 3 + 2 * C = ((3 : ℕ) : ℝ) + C + C by push_cast; ring, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
      ring
    rw [this, Nat.cast_mul]
    refine mul_le_mul_of_nonneg_right (hr''.trans ?_) hN0.le
    gcongr
  rw [Real.rpow_mul hN0.le]
  exact hq.trans (hle.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by linarith)))

private noncomputable def DC.relevel {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (q0 : ℕ) (h0 : Nat.Coprime q0 H.QS) : Host R :=
  { H with
    levelPrimes := {H.g 0, H.g 1, H.pde, H.pde', q0}
    g_level := by intro i; fin_cases i <;> simp
    pde_level := by simp
    level_coprimeS := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h | h <;> rw [h]
      · exact H.level_coprimeS _ (H.g_level 0)
      · exact H.level_coprimeS _ (H.g_level 1)
      · exact H.level_coprimeS _ H.pde_level.1
      · exact H.level_coprimeS _ H.pde_level.2
      · exact h0
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p }

end UpperTheory.Top.PolynomialHostPrimeBound

open GlobalTheory.EX.DC UpperTheory.Top.PolynomialHostPrimeBound in
theorem UpperTheory.Top.hostQ :
    SmallPrimeOne → ∀ (la : ℝ) (G : FReq), HostExW la G.req → DC.HostExQW la G.req := by
  intro hS la G hH
  obtain ⟨A, hA, hS⟩ := hS
  intro eps he he'
  obtain ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, hH⟩ := hH eps he he'
  have hC : C8 ≤ (3 + 2 * C8) * A := by nlinarith
  refine ⟨CT2, (3 + 2 * C8) * A, C5, c6, Cb, x0, h8.trans hC, h5, h6, hb, S, fun s hs hx hm => ?_⟩
  obtain ⟨R, H, q0, hR, hT, ⟨hv, har, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -, -⟩, hG⟩ := hH s hs hx hm
  have hc : H.ccK = ⊤ := hv.2.2.2.2.2.2.1
  have h0 : Nat.Coprime (q0H H) H.QS := by
    have h1 : q0H H ≡ 1 [MOD H.QS * H.q * H.d] := by
      have := mod_cond H
      have h2 : 1 < H.QS * H.q * H.d := by
        by_contra h3
        have h4 : H.QS * H.q * H.d = 1 := by have := cond_pos H; omega
        rw [h4] at this
        omega
      unfold Nat.ModEq
      rw [this, Nat.mod_eq_of_lt h2]
    have h5 : Nat.Coprime (q0H H) (H.QS * H.q * H.d) := by
      rw [Nat.Coprime, h1.gcd_eq]
      simp
    exact Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) h5
  have hv' : HostVal s ((3 + 2 * C8) * A) (GlobalTheory.EX.DC.relevel H hc (q0H H) h0) := (hv.mono hC :)
  have hq := smallest_prime_polynomial_bound hA hS H hc hv.2.2.2.1.1 hv.2.2.2.1.2
  have har' : HostArith (GlobalTheory.EX.DC.relevel H hc (q0H H) h0) := by
    refine ⟨har.1, har.2.1, har.2.2.1, fun l hl => ?_⟩
    have hl' : l ∈ ({H.g 0, H.g 1, H.pde, H.pde', q0H H} : Finset ℕ) := hl
    show H.cls l = .splitK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with h | h | h | h | h <;> rw [h]
    · exact har.2.2.2 _ (H.g_level 0)
    · exact har.2.2.2 _ (H.g_level 1)
    · exact har.2.2.2 _ H.pde_level.1
    · exact har.2.2.2 _ H.pde_level.2
    · exact (GlobalTheory.HostSplit.split_of_one_mod R H _ (globalTwisting_spec_fact H).1 (mod_cond H)).2
  exact ⟨R, GlobalTheory.EX.DC.relevel H hc (q0H H) h0, q0H H, hR, hT, ⟨hv', har', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
    ⟨(globalTwisting_spec_fact H).1, mod_cond H, hq, q0H_ne_pde_and_ne_pde' H⟩, rfl⟩, globalTwisting_congr_fact _ rfl rfl rfl rfl rfl rfl, hG⟩
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

theorem objC_true {Q : Par → PtProp} (h : ObjCP Q) : DC.ObjC (fun _ _ _ _ _ _ _ _ _ => True) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  refine ⟨x0, fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  obtain ⟨p, e1, e2, e3, e4, e5, -⟩ := h s R H q0 a b M c u0 d1 d2 d3 d4 (by rw [← b2] at d5; exact d5) d0 d6 d7 d8 d9
  exact ⟨p, e1, e2, e3, e4, e5, trivial⟩

theorem recS (QO : Par → ∀ D : D7, Obj D → Prop) (cT : ℝ → ℝ → ℝ) (hR : DC.MinkDiv → RecExP (fun κ => DQ.withQD (QO κ)))
    (hM : DC.MinkDiv) : ExD (clsP QO) cT := by
  intro la G hla hH
  have hS : SmallPrimeOne := GlobalTheory.EX.smallPrimeOne_of_primesRel GlobalTheory.Lin.primesRel_holds
  have hO := GlobalTheory.T.existsObjects_of_admissibleTwistDatum _ GlobalTheory.EX.normPrimes_and_levelPrime_unconditional.2 (hR hM)
  have hW : DC.HostWW la G.req := hostWW _ la _ hla (hostQ hS la G hH) (objC_true hO) GlobalTheory.T.windowShareRequirementClosedForm_proof
  exact designS (fun κ => ptO (DQ.withQD (QO κ))) cT la G hla hM (kitS _ la G hW hO)

end UpperTheory.Top
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem isSel_of_sAnd {Bd : BdT} {Q R : V4.Slot} {Lk : LkT Bd} {E : Par → BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜}
    (s : IsSel (sAnd Q R) Lk E 𝒜 σ) : IsSel Q Lk E 𝒜 σ := by
  intro eps Fm hc
  obtain ⟨κ, h1, h2, h3⟩ := s Fm hc
  refine ⟨κ, h1, h2, fun x hx i => ⟨?_, (h3 x hx i).2⟩⟩
  obtain ⟨K, β, b, a0, a1, a2, a3⟩ := (h3 x hx i).1
  exact ⟨K, β, b, a0, a1.1, a2, a3⟩

end GlobalTheory.Fc

namespace UpperTheory.Top

theorem classSel : StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Bd : BdT) (Lk : LkT Bd) (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') → ExBL KP Q Q' Lk → RowL KP Q Q' Lk H → ∃ (𝒜 : FamClass) (σ : RawSel Bd 𝒜), (DC.MinkDiv → ExD 𝒜 cT) ∧ (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → DQ.Duty7 Fm ∧ DQ.MtStableF Fm) ∧ IsSel Q' Lk (fun _ _ _ _ _ => True) 𝒜 σ ∧ H 𝒜 σ := by
  intro h1 h2 KP Q Q' Bd Lk H cT hc hx hr
  obtain ⟨R, r, hx', hr'⟩ := RowL.elim hx hr
  obtain ⟨E, hE, hH⟩ := Row.elim hx' hr'
  have hs : IsSel (sAnd Q' R) Lk (fun _ _ _ _ _ => True) (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) :=
    IsSel.mono (fun _ _ _ _ _ _ => trivial) (pick_isSel (sAnd Q' R) Lk E)
  refine ⟨cls (sAnd Q' R) Lk E, pick (sAnd Q' R) Lk E, ?_, fun _ _ h => sevenDuties_of_class h,
    @isSel_of_sAnd Bd Q' R Lk _ (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) hs, hH⟩
  refine recS (QOf (sAnd Q' R) Lk E) cT fun hm => ?_
  obtain ⟨a, b, c, d⟩ := hc hm
  have d' := GlobalTheory.T.secondG_sAnd_of_largeBase KP Q Q' R a (evG_of_ev r) d
  have h := memberTop_final_contextParameters h1 h2 KP Q (sAnd Q' R) (QOf (sAnd Q' R) Lk E) a b c d' hE
  have e : ∀ κ : Par, (fun D O => κ.Pos → QOf (sAnd Q' R) Lk E κ D O) = QOf (sAnd Q' R) Lk E κ :=
    fun κ => funext fun _ => funext fun _ => propext ⟨fun h' h0 => h' h0 h0, fun h' _ => h'⟩
  simpa only [e] using h

end UpperTheory.Top

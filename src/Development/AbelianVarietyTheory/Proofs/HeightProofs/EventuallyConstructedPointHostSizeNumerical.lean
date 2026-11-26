module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
public import Development.AutomorphicArithmetic.ThickFrames.ThickFrame2Large
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivLeRpowThreeQuarters
public import Development.AutomorphicArithmetic.CharacterBoxes.RealSplit
public import Development.AutomorphicArithmetic.CharacterBoxes.ThinChoice
public import Development.AutomorphicArithmetic.ThickFrames.topsBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem hostArith_of_over {K : Ctx} {B : Pre} (h : K.Over B) : HostArith B.host := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  exact ⟨K.ok.arith.1, K.ok.arith.2.1, K.ok.arith.2.2.1, (Pre.ofCh K.P K.Lv sp hT hY hA hV hz).level_split⟩

theorem hostArith_bpt {K : Ctx} (β : BPt K) : HostArith β.D.host := hostArith_of_over β.c.isOver

theorem eventually_hostSize_and_numAt : EvP fun _ K => ∀ β : BPt K, GlobalTheory.FieldSize.HostSz β.D.host β.O.L.sc.L ∧
    ∀ C, FieldTies β.D C → NumAtL β.O.L K.s.x := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨max x0 (max (C.T.CP ^ 20) ((10 : ℝ) ^ 60)), fun K h1 h2 h3 h4 hx β => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hy0, hyP, hy60⟩ := hx
  have hsc : β.O.L.sc = K.s := β.sc
  have hsx : β.O.L.sc.x = K.s.x := by rw [hsc]
  have hse : β.O.L.sc.eps = eps := by rw [hsc, h4]
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy0.trans hsx.ge) hv (hostArith_bpt β)
  have hCP : N.parT.CP = C.T.CP := (List.cons.inj N.parT_K).1
  have hg : ∀ j, Real.log (β.D.host.g j) ≤ 9 * β.O.L.sc.L + 1 := by
    intro j
    have hlo : 0 < ((β.D.host.g j : ℕ) : ℝ) := by
      exact_mod_cast (β.D.host.g_prime j).pos
    have := (Real.log_le_iff_le_exp hlo).2 (N.g_le j)
    linarith
  obtain ⟨hH, hS⟩ := GlobalTheory.FieldSize.hostSz_of_sizes β.D β.O.L N.params N.parT N.sizes hg (hy60.trans hsx.ge)
  refine ⟨hH, fun Cf hT => ⟨β.O.ex.kap_def, ⟨N.params, N.parT, N.sizes, N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1, hg, ?_, ?_,
    hsx.ge⟩, hS (hT.small _ hH)⟩⟩
  · rw [hCP]; exact hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hCP]
    exact hyP.trans (hsx.ge.trans (x_le_zBase_of_pow_le_n β.O.L N.win.1.1))

end GlobalTheory.Plug
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Plug.wPt_frame : ∀ (𝒮 : Slots) (K : Ctx) (p : WPt 𝒮 K), p.x.what₂.r.z.R.C = Fr.at (p.w.st p.Z) p.f ∧ GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z = Fr.at (p.w.st p.Z) p.f ∧ ∃ μ0, p.x.what₂.r.z.R.toRealDat.toLevCh.Is μ0 := by
  intro 𝒮 K p
  have hC : Fr.at (p.w.st p.Z) p.w.I.C = Fr.at (p.w.st p.Z) p.f := congrArg (Fr.at (p.w.st p.Z)) p.w.C_eq
  refine ⟨?_, ?_, ⟨_, p.x.what₂.r.z.lev.is⟩⟩
  · exact p.x.what₂.r.z.lev.C.trans hC
  · exact (rfl : GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z = Fr.at (p.w.st p.Z) p.w.I.C).trans hC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreTiesOfTied
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreTiesOfHyp
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem level_of_is {T : Core D} (hT : LawsM T) {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) (hO : T.pb = Lc.C.P.pb) :
    T.Q.l.Mb = ∏ PP ∈ Lc.Pg, PP.asIdeal := by
  have hprod := T.Q.l.prod
  refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
  · rw [hT.pins.2.1.1] at hprod
    exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
  · rw [hL.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
    rfl

theorem exists_half_of_is {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) {p : ℕ} (hp : p = D.host.pde ∨ p = D.host.pde') :
    ∃ P : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ P.asIdeal ∧ ∀ t, ∀ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal →
      P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  obtain ⟨P, hP⟩ := hL.Q_de p hp
  by_cases h : ∃ t, ∃ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨t, PP, h1, h2⟩ := h
    refine ⟨P, ?_, fun t PP h1 h2 => ?_⟩
    · rw [← hP t PP h1 h2]
      change algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (p : 𝓞 D.host.K) ∈ PP.asIdeal
      rwa [map_natCast]
    · rw [← hP t PP h1 h2]
      exact Ideal.map_comap_le
  · have hpp : p.Prime := by
      rcases hp with rfl | rfl
      exacts [D.host.pde_prime, D.host.pde'_prime]
    obtain ⟨P', hP'⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hpp
    exact ⟨P', hP', fun t PP h1 h2 => absurd ⟨t, PP, h1, h2⟩ h⟩

theorem ownAt_special (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ownAt D v = D.host.pde ∨ ownAt D v = D.host.pde' := by
  unfold ownAt
  split_ifs
  exacts [Or.inr rfl, Or.inl rfl]

theorem oneHalf_of_is {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {μ0 : T0}
    (hL : R.toLevCh.Is μ0) : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v,
      ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧ ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
        (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  classical
  choose P h1 h2 using fun (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde') => exists_half_of_is hL hp
  refine ⟨fun p => if hp : p = D.host.pde ∨ p = D.host.pde' then P p hp else R.C.P.pb 0, fun v => ?_⟩
  simp only [dif_pos (ownAt_special v)]
  refine ⟨h1 _ _, fun PP hPP => ?_⟩
  have h3 := Finset.mem_filter.1 hPP
  exact h2 _ _ _ PP h3.1 h3.2

theorem level_and_oneHalf (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (μ0 : T0) (hL : R.toLevCh.Is μ0)
    (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) :
    J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
      ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
        ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
          (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal :=
  ⟨level_of_is hc.toLawsM hL hO, (oneHalf_of_is R hL).imp fun _ h v _ => h v⟩

theorem coreTies_of_is {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {μ0 : T0}
    (hL : R.toLevCh.Is μ0) (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) (hcan : J.Q.Canon)
    (hr : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) (hE : HalfEX J.toCore EX) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L) (hd : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D)
    (hd' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) : CoreTies L EX J R :=
  ⟨hc, hcan, hr, hE, h₁, h₂, hs, (level_and_oneHalf J R μ0 hL hO hc).1, (level_and_oneHalf J R μ0 hL hO hc).2, hd, hd'⟩

end GlobalTheory.BigOn

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Plug.coreTies_of_tied : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A J.Q.c.F) (μ0 : T0), Tied EX J R.C → R.toLevCh.Is μ0 → FieldSmall D L → GlobalTheory.BigOn.CoreTies L EX J R := by
  intro D G _ _ Pl0 T0 A L EX J _ R μ0 hT hL hs
  have hH : HalfEX J.toCore EX := fun i => by
    show barE D (EX.piG i) ∈ (J.pb i).asIdeal.map _
    rw [hT.core.pb]
    exact hT.half i
  exact GlobalTheory.BigOn.coreTies_of_is hL hT.core.pb hT.core.laws hT.core.canon hT.core.rank hH hT.field.one hT.field.two hs
    hT.field.del hT.field.del'
end

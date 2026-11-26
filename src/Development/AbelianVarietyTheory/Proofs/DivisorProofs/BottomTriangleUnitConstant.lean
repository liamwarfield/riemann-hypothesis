module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorReadsAsTranslateCurveTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuConductorExponentsPosProdEqModulus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuConductorExponentsPosProdEqModulus
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.NuExpModulus

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop

theorem levelLe_mono {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hv =>
  h x hx (hv.trans (WithZero.exp_le_exp.2 (by omega)))

theorem exp_eq {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt χ w c) (h1 : χ.LevelLe w (n + 1)) (h2 : ¬ χ.LevelLe w n) : c = n + 1 := by
  have a := (hc _).1 h1
  have b := (hc n).not.1 h2
  omega

theorem exp_div {E : Type} [Field E] [NumberField E] {a b : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt (a / b) w c) (ha : a.LevelLe w n) (h1 : b.LevelLe w (n + 1)) (h2 : ¬ b.LevelLe w n) :
    c = n + 1 := by
  refine exp_eq hc ?_ fun h => h2 ?_
  · rw [div_eq_mul_inv]
    exact Formalism.L2.Host.HChar.LevelLe.mul (levelLe_mono ha (Nat.le_succ n)) (Formalism.L2.Host.HChar.LevelLe.inv h1)
  · have e : b = a * (a / b)⁻¹ := by rw [inv_div, mul_div_cancel]
    rw [e]
    exact Formalism.L2.Host.HChar.LevelLe.mul ha (Formalism.L2.Host.HChar.LevelLe.inv h)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem gridBaseCharacter_unramified_off_badPlaces (j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)} (hS : P.under (𝓞 D.host.F) ∉ S1 D) :
    (L.C.mu0 j).UnrAt P := by
  refine (L.C.isMu0 j).unr P fun k hk => hS ((S1_mem_OmF D).2 ?_)
  have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
    rw [map_natCast]; exact hk
  fin_cases k
  · exact Or.inl this
  · exact Or.inr (Or.inl this)

theorem exp_w (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ G.pl.S0) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) c) : c = condExp G.pl v := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hu := G.pl.under_w hv
  by_cases h0 : v = G.pl.v0
  · rw [condExp, if_pos h0]
    have hu0 : (G.pl.w v).under (𝓞 D.host.F) = G.pl.v0 := hu.trans h0
    obtain ⟨l1, l2⟩ := G.ch.lev0 _ a1 a2 _ hu0
    have hmu : (L.C.mu0 j).UnrAt (G.pl.w v) := gridBaseCharacter_unramified_off_badPlaces j (by rw [hu0]; exact G.ch.basePlace_not_mem_chiGridBadPlaces)
    have hxi : (L.xiH t).UnrAt (G.pl.w v) := by
      by_contra hn
      rcases (hL.Q_ram t _).1 hn with hq | ⟨PP', hq, hcj⟩
      · exact G.pl.levelPlace_ne_basePlace t _ hq hu0
      · exact G.pl.levelPlace_ne_basePlace t _ hq ((GlobalTheory.BadPlaceExp.under_eq_of_isConjPl hcj).trans hu0)
    exact exp_div (n := 0) hc (Formalism.L2.Host.HChar.UnrAt.levelLe (hmu.mul hxi) 0) l1
      (fun h => l2 ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h))
  · rw [condExp, if_neg h0]
    have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
    obtain ⟨l1, l2⟩ := G.ch.lev1 _ a1 a2 (G.pl.w v) (by rw [hu]; exact h1)
    exact exp_div (n := 1) hc (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _)) l1 l2

theorem exp_twPl (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ twPl G t) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) P c) : c = 1 := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  refine exp_eq (n := 0) hc ?_ fun h => nuH_not_unrAt_twPl G hL t i j P hP ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  rw [nuH, div_eq_mul_inv]
  exact Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _))
    (Formalism.L2.Host.HChar.LevelLe.inv (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ a1 a2 P hS0) _))

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ →
  ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ),
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, GlobalTheory.CMVal.ExpAt (GlobalTheory.FunObj.SqNum.nuH G t i j) w (c w)) →
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, 0 < c w) ∧ ∏ w ∈ GlobalTheory.FunObj.locPl G t, w.asIdeal ^ c w = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have hW : ∀ v ∈ G.pl.S0, G.pl.w v ∈ locPl G t := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  have hT : ∀ P ∈ twPl G t, P ∈ locPl G t := fun P hP => (Finset.mem_filter.1 hP).1
  have h1 : ∀ v ∈ G.pl.S0, c (G.pl.w v) = condExp G.pl v := fun v hv => exp_w G hL t i j hv (hc _ (hW v hv))
  have h2 : ∀ P ∈ twPl G t, c P = 1 := fun P hP => exp_twPl G hL t i j hP (hc _ (hT P hP))
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [h1 v hv, condExp]
      split_ifs <;> omega
    · rw [h2 w (Finset.mem_filter.2 ⟨hw, h⟩)]
      omega
  · rw [← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0), modT]
    congr 1
    · have e : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.S0.image G.pl.w := by
        ext w
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_union_left _ h, h⟩⟩
      rw [e, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv')), condE]
      exact Finset.prod_congr rfl fun v hv => by rw [h1 v hv]
    · refine Finset.prod_congr ?_ fun P hP => by rw [h2 P hP, pow_one]
      ext w
      simp only [twPl, Finset.mem_filter]

end GlobalTheory.NuExpModulus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuConductorExponentsPosProdEqModulusStatement
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNuConductorExponents_pos_prod_eq_modulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ →
  ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ),
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, GlobalTheory.CMVal.ExpAt (GlobalTheory.FunObj.SqNum.nuH G t i j) w (c w)) →
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, 0 < c w) ∧ ∏ w ∈ GlobalTheory.FunObj.locPl G t, w.asIdeal ^ c w = GlobalTheory.SqTop.modT G t := by
  first | exact @GlobalTheory.NuExpModulus.main | exact GlobalTheory.NuExpModulus.main | (intros; apply GlobalTheory.NuExpModulus.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumStandardLatticesReadsTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumStandardLatticesReadsTheta
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacRead

theorem vacuum_reads_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∃ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), G ≠ 0 ∧ Reads ψ θ hS hT ⊤ δ 1 G v := by
  intro D ψ θ S T a d hS hT δ hcc hSet v hv
  subst hS hT
  have hδ : δ ≠ 0 := GlobalTheory.NormExact.delta_ne_zero hSet.crv
  have h1 : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) D.host.E), M = 1 →
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ((1 : GL (Fin k) D.host.E) : Matrix (Fin k) (Fin k) D.host.E) * M *
        ((1 : GL (Fin k) D.host.E) : Matrix (Fin k) (Fin k) D.host.E) = 1 := by
    intro k M hM
    subst hM
    simp [Formalism.UG.cT]
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ (h1 _ hSet.gS) (h1 _ hSet.gT) v hv
  have hinV : ∀ {k : ℕ} (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)),
      GlobalTheory.MovedDict.inV (D := D) 1 L = (L : Set (Fin k → D.host.E)) := by
    intro k L
    simp [GlobalTheory.MovedDict.inV]
  have hv' := hv
  rw [← hinV (stdL D S.rank), ← hinV (stdL D T.rank)] at hv'
  have hC : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ := by rw [hcc]; exact hSet.crv
  have hTh := GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved ψ θ S T 1 1 (h1 _ hSet.gS) (h1 _ hSet.gT) δ hC hδ
    (stdL D S.rank) (stdL D T.rank) (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) v hv' Φ hΦd hΦ
  rw [hcc] at hTh
  refine ⟨fun Y => Φ (δ⁻¹ • Y), hTh, ?_, ?_⟩
  · intro hG
    have h0 : v = 0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hv.2.theta (fun w hw => by
      rw [hΦ w hw]
      have e := congrFun hG (δ • GlobalTheory.FockPos.zCo θ 1 1 w)
      simp only [smul_smul, inv_mul_cancel₀ hδ, one_smul, Pi.zero_apply] at e
      rw [e, mul_zero])
    obtain ⟨⟨p, hp⟩, hq⟩ := hv.2.norm
    have e := hq p hp
    rw [h0] at e
    simp [nrm2] at e
  · rw [GlobalTheory.NormExact.reads_iff hSet.crv hSet.scale]
    refine ⟨hv.2.theta, fun w hw => ?_⟩
    rw [hΦ w hw]
    congr 2
    funext τ i j
    simp [smul_eq_mul, map_one, mul_one, inv_mul_cancel_left₀ hδ]

end GlobalTheory.VacRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumStandardLatticesReadsThetaStatement
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicVacuum_standardLattices_readsTheta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∃ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), G ≠ 0 ∧ Reads ψ θ hS hT ⊤ δ 1 G v := by
  first | exact @GlobalTheory.VacRead.vacuum_reads_theta | exact GlobalTheory.VacRead.vacuum_reads_theta | (intros; apply GlobalTheory.VacRead.vacuum_reads_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionIntegralPointCosetVectorEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionIntegralPointCosetVectorEq
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.Move

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem eig_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    {g' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) (hH : H ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) : P.W.Om k 1 H = s • H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) = k := mul_one k
  have f2 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = s • P.W.Om 1 g' P.e0 := by
    rw [← e1, e2, he, P.W.smul _ _ _ _ hT]
  rw [hc', P.W.smul _ _ _ _ hH, smul_comm s c H] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_eig (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) :
    P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      s • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact eig_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)
    (GlobalTheory.FunObj.CosetFix.iop_facts hI P h𝔪).1 k s he

theorem exists_close {𝔪 : Ideal (𝓞 D.host.E)} (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a)
    (z : Matrix (Fin d) (Fin a) D.host.E) (hz : Approx 𝔪 o k z) (m : ℕ) (hm : 0 < m) :
    ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧
      CloseTo D ⊤ m (k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
        (unitBlock D o a d) (z + w) := by
  choose b hb y hy hby using fun i j => GlobalTheory.CongApprox.exists_mem_approx D 𝔪 m hm _ (neg_mem (hz i j))
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have e1 : (((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := by
    simp
  unfold CloseTo
  refine fun i j => ⟨y i j, hy i j, Eq.trans ?_ (hby i j)⟩
  rw [e1, Matrix.one_mul, Matrix.map_add _ (map_add (inc D))]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply]
  ring

theorem wd_smul (δ : ℂ) {a d : ℕ} (x : VC D a d) (c : ℂ) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
  funext y
  simp only [Wd, Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_cosetVec : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
  ∀ (o : ℕ) (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a), k ∈ intG D P.a → ∀ c : ℂ, P.W.Om k 1 P.e0 = c • P.e0 →
  ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, IsIntE z → Approx 𝔪 o k z →
  P.W.Om k 1 (cosetVec P 𝔪 o) = c • cosV δ 𝔪 z P.e0 := by
  intro D hD δ t0 Q P 𝔪 h𝔪 o k hk c hc z hzi hz
  have h1 := hD.g1
  have he := P.vac.1
  have hIT := (GlobalTheory.FunObj.CosetFix.iop_facts hD P h𝔪).1
  have hfix := iop_eig hD P h𝔪 k c hc
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) :=
    VacMove.klat _ (VacMove.moves_one D P.a) (VacMove.moves_one D P.d)
  have kB : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D P.a), GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d, rfl⟩
  have hHB := (hD.uni ⊤ δ P.crv P.a P.d _ _ k0 kB P.e0 he).2.1
  obtain ⟨m, hm, hl⟩ := P.W.lift k 1 (unitBlock D o P.a P.d) _ hIT
  obtain ⟨w, hw, hclose⟩ := exists_close o k z hz m hm
  have hmain := hl _ hclose
  rw [hfix, wd_smul] at hmain
  obtain ⟨hw0, hwB⟩ := GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ 𝔪 w hw
  have hx0 := (GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ ⊤ z
    (fun i j => (hzi i j).imp fun b hb => ⟨Submodule.mem_top, hb⟩)).1
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hφ1 : φ = 1 := by
    have h2 := hφ P.e0
    rw [VacMove.wd_fix h1 P.crv k0 he hw0, VacMove.wd_fix h1 P.crv k0 he hx0,
      VacMove.wd_fix h1 P.crv k0 he (add_mem hx0 hw0)] at h2
    by_contra hne
    apply P.W.nz
    have : (φ - 1) • P.e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h3 := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)
  rw [VacMove.wd_fix h1 P.crv kB hHB hwB, hφ1, one_smul, ← VacMove.pt_add] at h3
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hIT
  unfold cosetVec cosV
  rw [P.W.smul _ _ _ _ hWT, hmain, ← h3, smul_comm]

end GlobalTheory.StdRead.Move
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionIntegralPointCosetVectorEqStatement
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_integralPoint_cosetVector_eq : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
  ∀ (o : ℕ) (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a), k ∈ intG D P.a → ∀ c : ℂ, P.W.Om k 1 P.e0 = c • P.e0 →
  ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, IsIntE z → Approx 𝔪 o k z →
  P.W.Om k 1 (cosetVec P 𝔪 o) = c • cosV δ 𝔪 z P.e0 := by
  first | exact @GlobalTheory.StdRead.Move.om_cosetVec | exact GlobalTheory.StdRead.Move.om_cosetVec | (intros; apply GlobalTheory.StdRead.Move.om_cosetVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLattice
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

open scoped TensorProduct

namespace GlobalTheory.StdRead

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_of_mem_hatL_pi {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) (i : Fin n) :
    z i ∈ Formalism.L2.Herm.intAf F E := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hy i (Set.mem_univ i))
    exact Subring.subset_closure (Or.inl ⟨⟨y i, b, hb⟩, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact mul_mem a.2 hx

theorem single_mem_hatL_pi (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  refine Submodule.subset_span ⟨Pi.single j 1, fun i _ => ?_, funext fun i => ?_⟩
  · by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  · by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same, map_one]
    · simp only [Pi.single_eq_of_ne h, map_zero]

theorem entries_int_of_isFrame_pi (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hβ : Formalism.L2.DIV.IsFrame β (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) :
    (∀ i j, β.val i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (β⁻¹).val i j ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h1 : Matrix.mulVec β.1 (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
        Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      refine (hβ _).2 fun l => ?_
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact int_of_mem_hatL_pi (single_mem_hatL_pi j) l
    have h2 := int_of_mem_hatL_pi h1 i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hβ _).1 (single_mem_hatL_pi j) i
    rwa [Matrix.mulVec_single_one] at h2

end Gen

theorem isIntM_of_isFrame_stdL : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)),
    Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val :=
  fun β hβ => entries_int_of_isFrame_pi β hβ

end GlobalTheory.StdRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLatticeStatement
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)), Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val := by
  first | exact @GlobalTheory.StdRead.isIntM_of_isFrame_stdL | exact GlobalTheory.StdRead.isIntM_of_isFrame_stdL | (intros; apply GlobalTheory.StdRead.isIntM_of_isFrame_stdL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEisensteinRatioAlgebraicUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapRingOfIntegersLeOne
namespace GlobalTheory.RingOfIntegersNormBound

theorem norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, hq, hqx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hqx
  have hlead : q.coeff q.natDegree = 1 := hq
  rw [hlead, map_one, one_mul] at hqx
  have hpow : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ F (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hqx
  have hpos : 0 < ‖x‖ := lt_trans one_pos hlt
  have key : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, algebraMap ℤ F (q.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ‖x‖ ^ n < ‖x‖ ^ (n + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ih.trans h1) ?_)
      rw [norm_mul, norm_pow]
      have h2 : ‖algebraMap ℤ F (q.coeff n)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one F (q.coeff n)
      calc ‖algebraMap ℤ F (q.coeff n)‖ * ‖x‖ ^ n ≤ 1 * ‖x‖ ^ n :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ‖x‖ ^ n := one_mul _
        _ < _ := h1
  have := key q.natDegree
  rw [← norm_neg, ← hpow, norm_pow] at this
  exact lt_irrefl _ this

theorem norm_map_ringOfIntegers_le_one {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) :=
  norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))

end GlobalTheory.RingOfIntegersNormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEisensteinRatioAlgebraicUnit
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacUnit

open Formalism.MainNotions.TaylorLogMetric (hYY LocBasis YYl)
open Formalism.MainNotions.StandardLatticesGL3 (OnB LaB pullB KLat)

theorem mem_Qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact h.of_pow hn

theorem norm_int_le {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p]) (c : 𝓞 K) :
    ‖f (c : K)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | (apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one ..)

theorem norm_nat_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem norm_det_le {p : ℕ} [Fact p.Prime] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ_[p]) (h : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _

variable {D : D7} {N N' r : ℕ}

theorem hYY_comb (c : Fin r → D.host.K) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (∑ k, c k • b k) y = ∑ k, c k * hYY D (b k) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hYY, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.smul_sum, smul_eq_mul, Finset.sum_mul, smul_mul_assoc]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

theorem exists_coord {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') (j : Fin r) :
    ∃ a : Fin r → D.host.K, (∀ i, ‖f (a i)‖ ≤ 1) ∧ b' j = ∑ i, a i • b i := by
  obtain ⟨s, hs, hY⟩ := hl'.2.1 j
  obtain ⟨t, ht, c, hc⟩ := hl.2.2 _ hY
  have hst : Nat.Coprime (t * s) p := Nat.Coprime.mul_left ht hs
  have h0 : ((t * s : ℕ) : D.host.K) ≠ 0 := by
    intro h
    have h1 := norm_nat_coprime hst
    rw [← map_natCast f, h] at h1
    simp at h1
  refine ⟨fun i => ((t * s : ℕ) : D.host.K)⁻¹ * (c i : D.host.K), fun i => ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, norm_nat_coprime hst, inv_one, one_mul]
    exact norm_int_le f _
  · have h2 : ((t * s : ℕ) : D.host.K) • b' j = ∑ i, (c i : D.host.K) • b i := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul] at hc
      rw [Nat.cast_smul_eq_nsmul, hc]
      rfl
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h2, smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem norm_det_eq_one {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
    (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') :
    ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ = 1 := by
  choose a ha hab using exists_coord f hl hl'
  choose a' ha' hab' using exists_coord f hl' hl
  have hM : ∀ i j, hYY D (b' j) (b i) = a j i := by
    intro i j
    rw [hab j, hYY_comb]
    simp [hb.1 _ i]
  have hMM : (Matrix.of fun i j => hYY D (b' j) (b i)) * (Matrix.of fun j k => a' k j) = 1 := by
    ext i k
    have h1 := hb.1 k i
    conv_lhs at h1 => rw [hab' k, hYY_comb]
    rw [Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, ← h1]
    simp [mul_comm]
  have hd := congrArg (fun A => ‖f (Matrix.det A)‖) hMM
  simp only [Matrix.det_mul, map_mul, norm_mul, Matrix.det_one, map_one, norm_one] at hd
  have h1 : ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa [hM] using ha j i
  have h2 : ‖f (Matrix.of fun j k => a' k j).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa using ha' j i
  refine le_antisymm h1 ?_
  rw [← hd]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

noncomputable def phiK (D : D7) : D.host.K →+* Qbar :=
  (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring fun x => by
    change _ ∈ Qbar
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toRatAlgHom

theorem at_place (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ) (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0)
    {e₁ e₂ : VC D N N' → ℂ} (h₁ : oddE0 D ⊤ δ t0 N N' e₁) (h₂ : oddE0 D ⊤ δ t0 N N' e₂) (hne : e₁ ≠ 0) {κ : ℂ}
    (hκ : e₂ = κ • e₁) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hSD : ∀ n, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h2 ▸ (h1 1).2
  obtain ⟨b, ε, hb, hl, hε, hεn, -, he⟩ := h₁.2.2.2.2 p lam (by simp)
  obtain ⟨b', ε', hb', hl', hε', hεn', -, he'⟩ := h₂.2.2.2.2 p lam (by simp)
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht N N' _ b b' hb hb'
  obtain ⟨μ, hμ, hI3⟩ := hI.mu ⊤ δ hC N N' _ _ (La0 D (tor0 D ⊤ δ) N N') (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inl ⟨_, b', hb', rfl⟩) (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩) _
    (GlobalTheory.UnitaryTheta.pullB_mem D ⊤ δ hC t0 ht N N' _ b hb).1
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have e2 := congrFun hκ z
  rw [he', hpull, Pi.smul_apply, smul_eq_mul] at e2
  rw [he] at e2 hz
  simp only [GlobalTheory.UnitaryTheta.iop_smul, hI3] at e2
  have hz' := right_ne_zero_of_mul hz
  have key : κ * ε = ε' * c * μ := by
    apply mul_right_cancel₀ hz'
    linear_combination -e2
  have hζQ : ζ ∈ Qbar := mem_Qbar_of_pow hm (hζ ▸ one_mem _)
  have hμQ : μ ∈ Qbar := mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)
  set u := phiK D (Matrix.of fun i j => hYY D (b' j) (b i)).det with hu
  have hun : ‖lam u‖ = 1 := norm_det_eq_one (lam.comp (phiK D)) hb hl hl'
  change c ^ 2 = ζ * (u : ℂ) at hc
  have hcQ : c ∈ Qbar := mem_Qbar_of_pow (n := 2) (by norm_num) (hc ▸ mul_mem hζQ u.2)
  rw [lamC, dite_eq_left hε] at hεn
  rw [lamC, dite_eq_left hε'] at hεn'
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul hz
  have hκQ : κ ∈ Qbar := by
    rw [eq_div_of_mul_eq hε0 key]
    exact div_mem (mul_mem (mul_mem hε' hcQ) hμQ) hε
  refine ⟨hκQ, ?_⟩
  rw [lamC, dite_eq_left hκQ]
  have root : ∀ (x : Qbar) (n : ℕ), 0 < n → (x : ℂ) ^ n = 1 → ‖lam x‖ = 1 := by
    intro x n hn hx
    have : x ^ n = 1 := Subtype.ext (by simpa using hx)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  have hcn : ‖lam ⟨c, hcQ⟩‖ = 1 := by
    have : (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u := Subtype.ext (by simpa using hc)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_mul, norm_mul, hun, root ⟨ζ, hζQ⟩ m hm hζ, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have : (⟨κ, hκQ⟩ : Qbar) * ⟨ε, hε⟩ = ⟨ε', hε'⟩ * ⟨c, hcQ⟩ * ⟨μ, hμQ⟩ := Subtype.ext key
  have h := congrArg (fun y => ‖lam y‖) this
  simpa only [map_mul, norm_mul, hεn, hεn', hcn, root ⟨μ, hμQ⟩ 8 (by norm_num) hμ, mul_one] using h

theorem vac_unit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ},
  oddE0 D ⊤ δ t0 N N' e₁ → oddE0 D ⊤ δ t0 N N' e₂ → e₁ ≠ 0 → ∀ κ : ℂ, e₂ = κ • e₁ →
  κ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam κ‖ = 1 := by
  intro D hI δ t0 hC ht N N' e₁ e₂ h₁ h₂ hne κ hκ
  refine ⟨?_, fun p _ lam => (at_place hI hC ht h₁ h₂ hne hκ p lam).2⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  exact (at_place hI hC ht h₁ h₂ hne hκ 2 (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom).1

end GlobalTheory.VacUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEisensteinRatioAlgebraicUnitStatement
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.odd_eisenstein_ratio_algebraic_unit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ},
  oddE0 D ⊤ δ t0 N N' e₁ → oddE0 D ⊤ δ t0 N N' e₂ → e₁ ≠ 0 → ∀ κ : ℂ, e₂ = κ • e₁ →
  κ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam κ‖ = 1 := by
  first | exact @GlobalTheory.VacUnit.vac_unit | exact GlobalTheory.VacUnit.vac_unit | (intros; apply GlobalTheory.VacUnit.vac_unit <;> assumption)
end
end

noncomputable section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem xiN_eq {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {δ : ℂ} {ι : Type} (R : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ r ∈ R, Reads ψ θ hS hT ⊤ δ 1 (G r) (f r)) : Reads ψ θ hS hT ⊤ δ 1 (∑ r ∈ R, G r) (∑ r ∈ R, f r) := by
  induction R using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

def IsPh (u : ℂ) : Prop := ‖u‖ = 1 ∧ u ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam u‖ = 1

theorem IsPh.mul {u v : ℂ} (hu : IsPh u) (hv : IsPh v) : IsPh (u * v) :=
  ⟨by rw [norm_mul, hu.1, hv.1, mul_one], mul_mem hu.2.1 hv.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam hu.2.1 hv.2.1, norm_mul, hu.2.2, hv.2.2, mul_one]⟩

theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  unfold lamC
  rw [dite_eq_left (one_mem _)]
  exact map_one lam

theorem IsPh.conj {u : ℂ} (hu : IsPh u) : IsPh (starRingEnd ℂ u) := by
  have h0 : u ≠ 0 := fun h => by simpa [h] using hu.1
  have e : starRingEnd ℂ u = u⁻¹ := (Complex.inv_eq_conj hu.1).symm
  refine ⟨by rw [Complex.norm_conj, hu.1], e ▸ inv_mem hu.2.1, fun p _ lam => ?_⟩
  have h := GlobalTheory.BotFormula.lamC_mul lam hu.2.1 (inv_mem hu.2.1)
  rw [mul_inv_cancel₀ h0, lamC_one] at h
  have h2 := congrArg norm h
  rw [norm_mul, hu.2.2, norm_one, one_mul] at h2
  rw [e, ← h2]

theorem isPh_of_pow {u : ℂ} {m : ℕ} (hm : 0 < m) (h : u ^ m = 1) : IsPh u := by
  have hQ : u ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow hm (h ▸ isIntegral_one)).isAlgebraic
  refine ⟨(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, h, norm_one]), hQ, fun p _ lam => ?_⟩
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_
  unfold lamC
  rw [dite_eq_left hQ, ← norm_pow, ← map_pow, show (⟨u, hQ⟩ : Qbar) ^ m = 1 from Subtype.ext h, map_one, norm_one]

theorem exists_const (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) {a d : ℕ} (G : VC D a d → ℂ)
    (hG : G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (h0 : G ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e0, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 →
      ∃ u, IsPh u ∧ G = (κ * u) • e0 := by
  by_cases hex : ∃ e1, Crv D ⊤ δ ∧ oddE0 D ⊤ δ t0 a d e1 ∧ e1 ≠ 0
  · obtain ⟨e1, hC, h1, hne⟩ := hex
    have k0 := GlobalTheory.NormSum.VacMove.klat (D := D) (tor0 D ⊤ δ) (GlobalTheory.NormSum.VacMove.moves_one D a)
      (GlobalTheory.NormSum.VacMove.moves_one D d)
    obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _ k0
    obtain ⟨κ, hκ⟩ := hline G hG e1 h1.1 hne
    refine ⟨κ, fun h => h0 (by rw [hκ, h, zero_smul]), fun e0 _ ht he hn => ?_⟩
    obtain ⟨u, hu, e⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC he h1 hn
    obtain ⟨a1, a2⟩ := GlobalTheory.T.odd_eisenstein_ratio_algebraic_unit hI hC ht he h1 hn u e
    exact ⟨u, ⟨hu, a1, a2⟩, by rw [hκ, e, smul_smul]⟩
  · exact ⟨1, one_ne_zero, fun e0 hC _ he hn => absurd ⟨e0, hC, he, hn⟩ hex⟩

theorem reads_std (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} (hS : S.rank = P.a) (hT : T.rank = P.d) (hcc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {v f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) v)
    {c : ℂ} (hc : c • P.e0 ∈ Th D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d)) (hr : Reads ψ θ hS hT ⊤ δ 1 (c • P.e0) v)
    {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hm : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hν : HasFinPart ν⁻¹ P.W.chV' P.W.ep')
    (hk : KillsCong ν 𝔪) {β : GL (Fin S.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β (stdL D S.rank))
    (hstd : GlobalTheory.FunObj.SqNum.IsStdDatum P 𝔪 0) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm)
    (hf : f = Tm fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) :
    ∃ u, IsPh u ∧ Reads ψ θ hS hT ⊤ δ 1 ((c * u) • P.F) f := by
  obtain ⟨R, hR1, hR2, hF⟩ := hstd
  obtain ⟨b1, b2⟩ := GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice β hβ
  obtain ⟨m, hm0, hpow⟩ := GlobalTheory.T.unitDetCharacter_integralFrame_pow_eq_one e 𝔪 hm ν hk β b1 b2
  choose! z hz using fun (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (hk : k ∈ intG D P.a) => exists_approx hm.ne_bot 0 P.d hk
  have hz' : ∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r) := fun r hr => hz r (hR1 r hr)
  have h0 := GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm
  have h1 := GlobalTheory.T.cosetIndicator_reads_as_translate_curveTheta ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm h0
  refine ⟨_, (isPh_of_pow hm0 hpow).conj, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators S T hS hT P.a_le e 𝔪 hm ν hk β b1 b2 R hR1 hR2 z hz', map_smul, map_sum, mul_comm c, mul_smul, hF,
    Finset.smul_sum]
  refine Reads.smul (reads_sum R _ _ fun r hr => ?_) _
  rw [GlobalTheory.T.weilAction_integralPoint_cosetVector_eq hI P hm.ne_bot 0 r (hR1 r hr) _ (GlobalTheory.T.integral_action_unit_character_eigen hI P e 𝔪 hm ν hν hk r (hR1 r hr)) (z r) (hz' r hr).1 (hz' r hr).2,
    map_smul, smul_comm c, ← cosV_smul]
  exact (h1 (z r) (hz' r hr).1).smul _

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}


open GlobalTheory.FunObj.SqNum GlobalTheory.FunObj.StdDatum GlobalTheory.Mem.Col2.SplitChar in
theorem killsCong {μ₀ : T} (hL : L.Is μ₀) (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) (i j : Fin D.R.m) :
    KillsCong (G.nu t i (j + 1)) (GlobalTheory.SqTop.modT G t) := by
  intro x u hxu hu hm
  have hle := Ideal.mul_mono (TwBig.modT_le_condE G t) (TwBig.conj_smul_mono (TwBig.modT_le_condE G t))
  have h1 := TwBig.nuInv_base_eq_one hL G i j u hu (TwBig.hatId_mono hle hm)
  have h2 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu hm
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    show L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) * L.xiH t
    rw [hL.xi_base, mul_one, mul_div_right_comm]
  have h3 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G t i j hL) x u hxu
  have e1 : (nuH G μ₀ i j * L.xiH t).1 (finIdl D u) = (nuH G μ₀ i j).1 (finIdl D u) * (L.xiH t).1 (finIdl D u) := rfl
  have e2 : (nuH G μ₀ i j).1 (finIdl D u) = 1 := inv_eq_one.1 h1
  rw [e, e1, e2, h2, mul_one] at h3
  exact Circle.coe_injective (by simpa using h3)

end GlobalTheory.StdRead

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

end GlobalTheory.StdRead

end

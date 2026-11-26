module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyReal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyReal
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr
theorem restage_copy_real_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)), ∃ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) ∧ HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ ∧ HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) ∧ HEq x'.m.z.cG x.m.z.cG ∧ HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) := by
  intro hL K B f T w P x l N
  obtain ⟨m, hm, hc, hh⟩ := GlobalTheory.T.exists_movedData_laterStagesWithNewTwist x N
  obtain ⟨r, hp, hrep, hj, he⟩ := GlobalTheory.T.exists_normalisedReading_transported_newTwist x N m hm hc hh
  obtain ⟨l', h1, h2, h3, h4, h5, h6, h7⟩ := _root_.GlobalTheory.T.read_package_twist_heq_alt hL x l N m hm hc hh r hp hrep hj he
  refine ⟨stTw x N m hc hh r hp, l', rfl, ?_, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, ?_⟩
  · show HEq m.z.R.toRealDat.toLevCh _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).R.toRealDat.toLevCh) :))
  · show HEq m.z.R _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).R) :))
  · show HEq m.z.cG _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).cG) :))
  · show HEq m.z.geo _
    rw [hm]
    exact (by with_unfolding_all exact ((HEq.refl (datTw x N).geo) :))
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyRealStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_state_transport_heq_levels' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)), ∃ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) ∧ HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ ∧ HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) ∧ HEq x'.m.z.cG x.m.z.cG ∧ HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.restage_copy_real_alt | exact _root_.GlobalTheory.HeightCounting.Up.restage_copy_real_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.restage_copy_real_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Facts
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Facts
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section
namespace GlobalTheory.HeightCounting.FirstFacts
theorem facts_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T}, K.Over B.toPre → GlobalTheory.Mem.Top.Bl.Start K B f T w → ∀ {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x), IsChoice (D := GlobalTheory.HeightCounting.Up.Dof x) (Set.range l.Pq) ∧ (∀ t, ∀ Q ∈ x.m.z.R.Q t, Q ∈ Set.range l.Pq) ∧ (∀ j, FWT.VStd (GlobalTheory.HeightCounting.Up.Dof x) j) ∧ x.m.z.R.C = GlobalTheory.HeightCounting.Up.cfOf x ∧ ∀ (k : Fin 2) (z : ℂ), z ^ ((GlobalTheory.HeightCounting.Up.Dof x).host.g k * ((GlobalTheory.HeightCounting.Up.Dof x).host.g k - 1)) = 1 → z ∈ (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)).fieldRange := by
  intro hL K B f T w hK hS P x l
  obtain ⟨⟨c⟩, -⟩ := hS
  refine ⟨⟨pair_of_over _ l.Pq_over, ?_⟩, ?_, vstd_of_over (w.st x.o.Z) hK, x.m.z.lev.C, fun k z hz => ?_⟩
  · rw [l.sel]
    rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩ ⟨p, hp, h1, h2⟩
    have key : ∀ u : HeightOneSpectrum (𝓞 B.host.F), (p : 𝓞 B.host.E) ∈ (w.I.sel u).asIdeal → (p : 𝓞 B.host.F) ∈ u.asIdeal := by
      intro u hu
      have e : (w.I.sel u).asIdeal.under (𝓞 B.host.F) = u.asIdeal := w.ok.sel_ok u
      rw [← e, Ideal.mem_comap, map_natCast]
      exact hu
    exact congrArg HeightOneSpectrum.asIdeal (c.half v v' p hp (key v h1) (key v' h2))
  · intro t Q hQ
    rw [x.m.z.lev.Q] at hQ
    rw [l.sel]
    exact mem_range_of_mem_QE hQ
  · have h0 : B.host.g k * (B.host.g k - 1) ≠ 0 :=
      mul_ne_zero (B.host.g_prime k).ne_zero (by have := (B.host.g_prime k).two_le; omega)
    obtain ⟨y, hy, e⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
    obtain ⟨u, hu⟩ := GlobalTheory.Mem.Col2.InEx.root_mem (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)) h0 ⟨⟨y, B.Ks_le hy⟩, e⟩ hz
    exact ⟨u, hu⟩
end GlobalTheory.HeightCounting.FirstFacts
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FactsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isChoice_of_start_of_over : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T}, K.Over B.toPre → GlobalTheory.Mem.Top.Bl.Start K B f T w → ∀ {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x), IsChoice (D := GlobalTheory.HeightCounting.Up.Dof x) (Set.range l.Pq) ∧ (∀ t, ∀ Q ∈ x.m.z.R.Q t, Q ∈ Set.range l.Pq) ∧ (∀ j, FWT.VStd (GlobalTheory.HeightCounting.Up.Dof x) j) ∧ x.m.z.R.C = GlobalTheory.HeightCounting.Up.cfOf x ∧ ∀ (k : Fin 2) (z : ℂ), z ^ ((GlobalTheory.HeightCounting.Up.Dof x).host.g k * ((GlobalTheory.HeightCounting.Up.Dof x).host.g k - 1)) = 1 → z ∈ (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)).fieldRange := by
  first | exact @_root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt | exact _root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesCopyEmbeddingOfCmDatum
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesStateB1OfGeometry
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.SerCopy
theorem series_state_b1_of_geometry_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
    {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {cf cf' : CharFrame D} (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG)
    (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {Rw : RowSide D} {kKs hk}
    {hk' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)} {eig θ}
    (Bs : SideB D cf' Rw (lowAll D) Pq' (ratDatR R cG kKs hk) hk' eig θ) (YS : NExpRealS R cG (ratDatR R cG kKs hk))
    (eF : YS.eF = Bs.eF) (fi : ∀ i x, HEq ((YS.fi i).e x) x) (ser : SerAt YS g.v₀ Bs.exp PV cf' Pq') (tau : TauTrue Bs.exp)
    (e1 : cf' = cf) (e2 : Rw = a.A.row) (e3 : Pq' = Pq) (e4 : HEq hk' n.In.hL) (e5 : eig = n.In.eig) (e6 : θ = n.In.θ)
    (h1 : ∀ i, n.In.Sb ⊆ D.ntw.S0 i) (h2 : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))) :
    Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData g a n PV Pq) := by
  obtain rfl : kKs = n.kKs := RingHom.ext fun y => Subtype.ext ((hk y).trans (n.hk y).symm)
  subst e1 e2 e3 e5 e6
  cases e4
  exact ⟨{ Bs := Bs, Sb_le := h1, rootsOfUnityRing_le_wittIntegers := h2, lam := ⟨ser.lam, ser.lam_ok, ser.lam_teich, ser.lam_C, ser.lam_q, ser.lam_tie⟩
           YS := YS, eF := eF, fi := fi, ser := ser, tau := tau }⟩
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem pre_at_of_side_b_tau_true_lam_ok (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x)
    (hB : ∃ Bs : SideB (Dof x) (cfOf x) l.a.A.row (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ (Dof x).ntw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (Dof x), Z.Ok) :
    PreAt (P := P) x.m.z l.a.A.row l.Pq l.rat.In.hL l.rat.In.eig l.rat.In.θ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := _root_.GlobalTheory.T.isChoice_of_start_of_over hL hK hS x l.toLA
  obtain ⟨Bs, hτ⟩ := sideB_tau_congr h4.symm rfl rfl HEq.rfl hB
  exact ⟨h4, l.rat.kKs, l.rat.hk, l.rat.In.hL, HEq.rfl, Bs, x.r.Y.hF, hτ,
    GlobalTheory.T.exists_newThetaData_series_classSums_lattices hA (Dof x) _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG l.rat.kKs l.rat.hk _ _ _ _ _ Bs l.rat.In.Sb x.m.z.geo.v₀ x.r.Y.hF
      x.m.z.pins x.m.intersectionNumber_baseChange (fun j => x.m.z.geo.fw.hv₀ j _) x.m.z.geo.fw.ks l.rat.rat.hecke hSb hτ (h4 ▸ l.a.A.chr) (h4 ▸ l.a.val)
      l.a.elem.split l.Pq_over h1 h2 hZ h3⟩

private theorem charFrame_heq_of_fields {D D' : D7} (hD : D = D')
    {c : CharFrame D} {c' : CharFrame D'}
    (hP : HEq c.P c'.P) (hW : HEq c.W c'.W) (hmu : HEq c.mu0 c'.mu0)
    (heta : HEq c.eta c'.eta) (hchi : HEq c.chiPsi c'.chiPsi)
    (hdel : HEq c.del c'.del) (hdel' : HEq c.del' c'.del') : HEq c c' := by
  subst D'
  cases c
  cases c'
  cases eq_of_heq hP
  cases eq_of_heq hW
  cases eq_of_heq hmu
  cases eq_of_heq heta
  cases eq_of_heq hchi
  cases eq_of_heq hdel
  cases eq_of_heq hdel'
  rfl

private theorem sideB_tau_reindex {D D' : D7} {cf cf' Rw Rw' low low' Pq Pq' S S' hL hL' eig eig' θ θ'}
    (hD : D = D') (hc : HEq cf cf') (hr : HEq Rw Rw') (hlow : low = low')
    (hq : HEq Pq Pq') (hs : HEq S S') (hh : HEq hL hL') (he : HEq eig eig') (hθ : HEq θ θ')
    (h : ∃ Bs : SideB D cf Rw low Pq S hL eig θ, TauTrue Bs.exp) :
    ∃ Bs : SideB D' cf' Rw' low' Pq' S' hL' eig' θ', TauTrue Bs.exp := by
  subst D' low'
  cases eq_of_heq hc
  cases eq_of_heq hr
  cases eq_of_heq hq
  cases eq_of_heq hs
  cases eq_of_heq hh
  cases eq_of_heq he
  cases eq_of_heq hθ
  exact h

theorem pre_at_twisted_copy_of_side_b_tau_true (hA : GlobalTheory.Published.GlobalArtinReciprocity) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hK : K.Over B.toPre)
    (hS : Start K B f T w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x))
    (hB : ∃ Bs : SideB N.toD7 (N.cf (cfOf x)) (N.row l.a.A.row) (lowAll (Dof x)) l.Pq (N.rat l.rat.S) l.rat.In.hL l.rat.In.eig
      l.rat.In.θ, TauTrue Bs.exp)
    (hSb : ∀ i, l.rat.In.Sb ⊆ N.tw.S0 i) (hZ : ∃ Z : GlobalTheory.LamTie.LamDat N.toD7, Z.Ok) :
    PreAt (P := P) (Z := (oTw x N).Z) (datTw x N)
      (cast (congrArg RowSide (dof_oTw x N).symm) (N.row l.a.A.row))
      (by with_unfolding_all exact l.Pq) l.rat.In.hL
      (by with_unfolding_all exact l.rat.In.eig) (by with_unfolding_all exact l.rat.In.θ) := by
  obtain ⟨x', l', ho, -, hrow, hPq, hS', hSb', hhL, heig, hθ, hR, hcG, hgeo⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq_levels' hL x l N
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  have hz : m'.z = datTw x N := moved_eq_datTw x N m' copy' hR hcG hgeo
  have hc : HEq (N.cf (cfOf x)) (TC.cf w.I w.l (oTw x N).Z) := by
    with_unfolding_all
      apply charFrame_heq_of_fields (dof_oTw x N).symm <;> rfl
  have hZ' : ∃ Z : GlobalTheory.LamTie.LamDat (DN x N), Z.Ok :=
    Eq.mpr (congrArg (fun D => ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok) (dof_oTw x N)) hZ
  have e2 : l'.Pq = (by with_unfolding_all exact (l.Pq :)) := (by with_unfolding_all exact ((eq_of_heq hPq) :))
  have e4 : l'.rat.In.Sb = (by with_unfolding_all exact (l.rat.In.Sb :)) := (by with_unfolding_all exact ((eq_of_heq hSb') :))
  have e5 : l'.rat.In.eig = (by with_unfolding_all exact (l.rat.In.eig :)) := (by with_unfolding_all exact ((eq_of_heq heig) :))
  have e6 : l'.rat.In.θ = (by with_unfolding_all exact (l.rat.In.θ :)) := (by with_unfolding_all exact ((eq_of_heq hθ) :))
  have h := pre_at_of_side_b_tau_true_lam_ok hA hK hS _ l'
    (sideB_tau_reindex (dof_oTw x N).symm hc hrow.symm (by with_unfolding_all rfl)
      hPq.symm hS'.symm hhL.symm heig.symm hθ.symm hB)
    (by rw [e4]; with_unfolding_all exact hSb) hZ'
  have hrow' := hrow.trans (cast_heq (congrArg RowSide (dof_oTw x N).symm) (N.row l.a.A.row)).symm
  exact preAt_congr hz (eq_of_heq hrow') e2 hhL e5 e6 h
section Install
variable {x : St P} {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host} {hf eig θ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) hf eig θ} {hF}
  (p : PreTie (ysOf Bs) (datTw x N₁).geo.v₀ Bs.exp hF Pq)
theorem series_state_b1_twist_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hτ : TauTrue Bs.exp) (hC : cf = TC.cf w.I w.l (oTw x N₁).Z)
    (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) (ho : NoOff (DN x N₁))
    (z : Dat (w.st (oTw x (nP p)).Z) w.I P.hX T P.Wt) (hz : z = datTw x (nP p)) {X0 : BaseLevelRowSide (DN x (nP p))}
    (Y : R3.Read z.R.toRealDat z.F.lv2 X0) (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL (DN x (nP p)) (TC.cf w.I w.l (oTw x (nP p)).Z) (repOf Y)) (n : InRat Y z.cG)
    (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) {hF'}
    (hPV : ∀ j, GlobalTheory.MtRead.IdFrame hF' (PV j))
    (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x (nP p)).host.E)) → PlE (DN x (nP p)).host)
    (hZ : ∃ Z : GlobalTheory.LamTie.LamDat (DN x (nP p)), Z.Ok ∧ Z.Teich ∧ Z.C = TC.cf w.I w.l (oTw x (nP p)).Z ∧
      Z.q0 = AbsolutelyIrreducibleSpan.q0 (DN x (nP p)) ∧ GlobalTheory.LamTie.IsLamTieFull (DN x (nP p)).ntw Z)
    (e2 : HEq a.A.row ((kwP p).row Rw)) (e3 : HEq Pq' Pq) (e4 : HEq n.In.hL hf) (e5 : HEq n.In.eig eig) (e6 : HEq n.In.θ θ)
    (h1 : ∀ i, n.In.Sb ⊆ (DN x (nP p)).ntw.S0 i)
    (h2 : ∀ i, OverSet (DN x (nP p)) ((DN x (nP p)).ntw.S0 i) (insert ((DN x (nP p)).ntw.l i) (lowAll (DN x (nP p))))) :
    Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData z.geo a n PV Pq') := by
  subst hz
  obtain ⟨Z, z1, z2, z3, z4, z5⟩ := hZ
  have e1 : ((by with_unfolding_all exact (((kwP p).cf cf) :)) : CharFrame (DN x (nP p))) = TC.cf w.I w.l (oTw x (nP p)).Z := (by with_unfolding_all exact ((congrArg (kwP p).cf hC) :))
  exact _root_.GlobalTheory.HeightCounting.SerCopy.series_state_b1_of_geometry_alt _ a n PV (bsP p) (ysP p) ((by with_unfolding_all exact ((Eq.refl Bs.eF) :))) ((by with_unfolding_all exact ((ysOf_fi Bs) :)))
    ((by with_unfolding_all exact ((serP p hu ho Bs.bsup PV hPV Z ⟨z1, z2, z3.trans e1.symm, z4, z5⟩) :))) ((by with_unfolding_all exact (hτ :))) e1 ((by with_unfolding_all exact ((eq_of_heq e2).symm :)))
    ((by with_unfolding_all exact ((eq_of_heq e3).symm :))) ((by with_unfolding_all exact (e4.symm :))) ((by with_unfolding_all exact ((eq_of_heq e5).symm :))) ((by with_unfolding_all exact ((eq_of_heq e6).symm :))) h1 h2
end Install
end GlobalTheory.HeightCounting.SerCopy
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.SerCopy
open GlobalTheory.Mem.Top.GroupRetwisting in
theorem series_copy_embedding_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}, K.Over B.toPre → Forced K B T → Start K B f T w → ∀ {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x), ∃ N : TwNew (Dof x), (∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ ∀ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N → HEq l'.a.A.row (N.row l.a.A.row) → HEq l'.Pq l.Pq → HEq l'.rat.S (N.rat l.rat.S) → HEq l'.rat.In.Sb l.rat.In.Sb → HEq l'.rat.In.hL l.rat.In.hL → HEq l'.rat.In.eig l.rat.In.eig → HEq l'.rat.In.θ l.rat.In.θ → HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq x'.m.z.cG x.m.z.cG → HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → ∀ m : InMt x'.r.Y (cfOf x') w.I.xi (QOf P), (∀ i, GlobalTheory.MtRead.IdFrame x'.r.Y.hF (m.ad.PV i)) → Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData x'.m.z.geo l'.a l'.rat m.ad.PV l'.Pq) := by
  intro hPr _ hL K B f T w hK _ hS P x l
  obtain ⟨-, -, -, -, hr⟩ := _root_.GlobalTheory.T.isChoice_of_start_of_over hL hK hS x l.toLA
  obtain ⟨N, h1, h2, h3, h4, hB⟩ := exists_prepared hPr.what₂.art l.b.Bs l.a.val hr
  obtain ⟨Z, z1, z2, z3, z4, z5⟩ := l.b.lam
  have hSb : ∀ i, l.rat.In.Sb ⊆ N.tw.S0 i := fun i => by
    obtain ⟨i₀, e, -⟩ := h2 i
    rewrite [e]
    exact l.b.Sb_le i₀
  have hS0 : ∀ i, OverSet (Dof x) (N.tw.S0 i) (insert (N.tw.l i) (lowAll (Dof x))) := fun i => by
    obtain ⟨i₀, e, e'⟩ := h2 i
    rewrite [e, e']
    exact l.b.rootsOfUnityRing_le_wittIntegers i₀
  obtain ⟨hC, kKs, hk, hf, g, Bs, hF, hτ, ⟨p⟩⟩ := _root_.GlobalTheory.HeightCounting.SerCopy.pre_at_twisted_copy_of_side_b_tau_true hPr.what₂.art hK hS x l.toLI N hB hSb
    ⟨_, (lamT_spec N ⟨z1, z2, z3, z4, h1 Z z5⟩).1⟩
  refine ⟨nP p, h1, fun x' l' ho hrow hPq _ hSb' hhL heig hθ hR hcG hgeo m hm => ?_⟩
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  have e4 : l'.rat.In.Sb = (by with_unfolding_all exact (l.rat.In.Sb :)) := (by with_unfolding_all exact ((eq_of_heq hSb') :))
  exact _root_.GlobalTheory.HeightCounting.SerCopy.series_state_b1_twist_alt p hτ hC ((by with_unfolding_all exact (h4 :))) ((by with_unfolding_all exact (h3 :))) m'.z (moved_eq_datTw x _ m' copy' hR hcG hgeo) r'.Y l'.a l'.rat m.ad.PV hm l'.Pq
    ⟨(by with_unfolding_all exact ((lamT (nP p) Z) :)), (by with_unfolding_all exact ((lamT_spec (nP p) ⟨z1, z2, z3, z4, h1 Z z5⟩) :))⟩ ((by with_unfolding_all exact (hrow :))) ((by with_unfolding_all exact (hPq :))) (hhL.trans g.symm) ((by with_unfolding_all exact (heig :))) ((by with_unfolding_all exact (hθ :)))
    (by rewrite [e4]; exact (by with_unfolding_all exact (hSb :))) ((by with_unfolding_all exact (hS0 :)))
end GlobalTheory.HeightCounting.SerCopy
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_copy_embedding_of_cmDatum_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}, K.Over B.toPre → Forced K B T → Start K B f T w → ∀ {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x), ∃ N : TwNew (Dof x), (∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ ∀ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N → HEq l'.a.A.row (N.row l.a.A.row) → HEq l'.Pq l.Pq → HEq l'.rat.S (N.rat l.rat.S) → HEq l'.rat.In.Sb l.rat.In.Sb → HEq l'.rat.In.hL l.rat.In.hL → HEq l'.rat.In.eig l.rat.In.eig → HEq l'.rat.In.θ l.rat.In.θ → HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq x'.m.z.cG x.m.z.cG → HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → ∀ m : InMt x'.r.Y (cfOf x') w.I.xi (QOf P), (∀ i, GlobalTheory.MtRead.IdFrame x'.r.Y.hF (m.ad.PV i)) → Nonempty (_root_.GlobalTheory.HeightCounting.SeriesData x'.m.z.geo l'.a l'.rat m.ad.PV l'.Pq) := by
  first | exact @_root_.GlobalTheory.HeightCounting.SerCopy.series_copy_embedding_alt | exact _root_.GlobalTheory.HeightCounting.SerCopy.series_copy_embedding_alt | (intros; apply _root_.GlobalTheory.HeightCounting.SerCopy.series_copy_embedding_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemMatrixGroupIdentityFrame
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000
namespace GlobalTheory.MtId
variable {D : D7}
section Fam
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
variable {I0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Fam
section Asm
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Asm
section Cols
open GlobalTheory.Mem.Col2
variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)
end Cols
section State
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
variable {P : Pre2 K w} (x : St P)
theorem exists_matrix_input_identity_frame_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ w P x =>
    ∃ m : InMt x.r.Y (cfOf x) w.I.xi (QOf P), ∀ i, GlobalTheory.MtRead.IdFrame x.r.Y.hF (m.ad.PV i) :=
  fun _ => by
    unfold AllSt
    exact StepW.of_all fun _ _ _ _ _ _ _ hs _ x => hs.1.elim fun pin => inMt_state x pin
end State
end GlobalTheory.MtId
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SeriesStep
open GlobalTheory.Mem.R3.Tr
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem sb1l_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep := by
  intro hPr hSer hL cDep
  refine (StepW.and (_root_.GlobalTheory.MtId.exists_matrix_input_identity_frame_of_inputs hPr) (StepW.of_all fun _ _ _ _ _ _ _ h => h)).trans
    (StepW.of_all (q := fun K B f T w => ∀ (P : Pre2 K w) (x : St P),
      FirstIntermediateLevel hL x → ∃ x' : St P, Nonempty (SecondIntermediateLevel hL x') ∧
        (ListSt cDep x → ListSt cDep x')) fun K B f T w hK hF H P x l => ?_)
  obtain ⟨N, hN, hser⟩ := _root_.GlobalTheory.T.series_copy_embedding_of_cmDatum_alt hPr hSer hL hK hF H.2 x l
  obtain ⟨x', l', ho, hLc, hrow, hPq, hS, hSb, hhL, heig, hθ, hR, hcG, hgeo⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq_levels' hL x l.toLI N
  obtain ⟨m, hm⟩ := H.1 P x'
  obtain ⟨b⟩ := hser x' l' ho hrow hPq hS hSb hhL heig hθ hR hcG hgeo m hm
  exact ⟨x', ⟨{ toLI := { l' with mt := m }, b := b }⟩, listSt_oTw cDep x N hN x' ho hLc⟩
end GlobalTheory.HeightCounting.Up.SeriesStep
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesExistList_of_inputs_serN : (_root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt | exact _root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt <;> assumption)
end
end

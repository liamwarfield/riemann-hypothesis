module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevUIffInLevG
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevAtGEmbAIff
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevAtGEmbAIff
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TraceAtG
end GlobalTheory.TraceAtG
end
noncomputable section
open GlobalTheory.FamTrace
theorem GlobalTheory.TraceAtG.levAtG_embA_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (_root_.GlobalTheory.FamTrace.LevelAtElement a (embA a.d.B.d a.d.B.o κ) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∈ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.TraceAtElement a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ
  have hmi : ∀ i, 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := fun i => by
    have h1 := (a.G i).hs
    have h2 := (a.G i).S.odd
    unfold Ranks.rS; omega
  have hbes : ∀ i, (ofSplit (a.G i).q).IsBesFrame a.d.B.lev ((a.G i).sc 0) ((a.G i).FX 0 (Nat.zero_le _))
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) := by
    intro i
    have hm := hmi i
    have key : ∀ Bl : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, Bl = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ hm →
        ∀ (FA : Frame (a.G i).k Bl.A.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0))
          (F : Frame (a.G i).k Bl.V.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1))), HEq FA ((a.G i).FX 0 (Nat.zero_le _)) →
          HEq F ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) → (ofSplit (a.G i).q).IsBesFrame Bl ((a.G i).sc 0) FA F := by
      rintro Bl rfl FA F h1 h2
      cases h1; cases h2
      exact (a.G i).bes 0 _ hm _ _
    exact key _ (ha.bot.1 hm) _ _ HEq.rfl HEq.rfl
  have hmat : ∀ i g, IsMatrixInFrameOfXZero (a.G i) κ g → (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) (embA a.d.B.d a.d.B.o κ)
      (GlobalTheory.RootEx.embX ((a.G i).s + 1) g) := fun i g hg =>
    GlobalTheory.TraceAtG.mat_embA_besFrame (ofSplit (a.G i).q) a.d.B.lev _ _ _ (hbes i) κ g hg
  have huniq : ∀ i x m m', (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m →
      (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m' → m = m' := by
    intro i x m m' h1 h2
    unfold GLoc.Mat at h1 h2
    rw [h1] at h2
    refine Units.ext ?_
    have := congrArg (fun M => ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).γ * M *
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β) h2
    simp only [← Matrix.mul_assoc, Frame.γβ, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, Frame.γβ, Matrix.mul_one] using this
  have hex : ∀ i, ∃ g, IsMatrixInFrameOfXZero (a.G i) κ g := fun i =>
    ⟨coordHom _ (a.G i).q.pr _ _ ((a.G i).FX 0 (Nat.zero_le _)).βγ ((a.G i).FX 0 (Nat.zero_le _)).γβ κ,
      (eq_coordHom_iff _ _ _ _ _ _ κ _).2 rfl⟩
  constructor
  · intro hlev
    have htr : _root_.GlobalTheory.FamTrace.TraceAtElement a κ := fun i g hg => hlev i _ (hmat i g hg)
    refine ⟨?_, htr⟩
    have hsd := (ha.x 0 (Nat.zero_le _)).sd
    have hloc : ∀ i, GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = (a.G i).q.v) := by
      intro i
      obtain ⟨g, hg⟩ := hex i
      have hlev0 := htr i g hg
      let β := GlobalTheory.SplitLat.frameOf (a.G i).q ((I.rec7 l Z).sp.X 0) _ ((a.G i).FX 0 (Nat.zero_le _))
      have hIs : β.IsLat (a.g.x 0).L (GlobalTheory.SplitLat.stdLat (a.G i).k _) := fun x => by
        rw [GlobalTheory.SplitLat.mem_std]; exact (a.G i).latX 0 (Nat.zero_le _) x
      have key := GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes _ (a.G i).k (a.G i).q ((I.rec7 l Z).sp.X 0) _ β (a.g.x 0).L _ hsd hIs κ
      refine key.2 ?_
      have hreg := ((Chain.ofType_regular _ _ _ _ _ : ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).Regular).2.2 0
        ((a.G i).s + 1) (Nat.zero_add _)).2.2
      have hst := hreg hlev0
      have hK := GlobalTheory.LevX.mem_KO_of_embX_mem_stabLat (a.G i).S.ϖ
        (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) (l := (a.G i).s + 1) 0 ((a.G i).s + 1) (Nat.zero_add _)) hst
      have hcoord : coordHom ((I.rec7 l Z).sp.X 0) (a.G i).q.pr β.b β.b' β.bb' β.b'b κ = g :=
        ((eq_coordHom_iff _ _ _ _ _ _ κ g).1 hg).symm
      rw [hcoord]
      exact GlobalTheory.LevX.smul_stdLat_of_mem_KO hK
    intro y hy
    have hlat := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua (I.rec7 l Z) (fun p => p ∈ a.v.gP)).2 ((I.rec7 l Z).sp.X 0)).2.2.2 (a.g.x 0).L
    have hy' : ∀ j, (mt ((I.rec7 l Z).sp.X 0) κ *ᵥ y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (fun p => p ∈ a.v.gP) := fun j => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ (hy t)
    have hey : ∀ v e, e ∈ GlobalTheory.FinPl.intAt (I.rec7 l Z) (· = v) → ∀ j, (e • y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (· = v) :=
      fun v e he j => by simpa [smul_eq_mul] using Ideal.mul_mem_right (y j) _ he.1
    rw [hlat y hsd.1, hlat _ hsd.1]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ hv e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      have := h2 _ hv e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · rintro ⟨-, htr⟩ i m hm'
    obtain ⟨g, hg⟩ := hex i
    rw [huniq i _ _ _ hm' (hmat i g hg)]
    exact htr i g hg
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevAtGEmbAIffStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (_root_.GlobalTheory.FamTrace.LevelAtElement a (embA a.d.B.d a.d.B.o κ) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∈ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.TraceAtElement a κ) := by
  first | exact @_root_.GlobalTheory.TraceAtG.levAtG_embA_iff_alt | exact _root_.GlobalTheory.TraceAtG.levAtG_embA_iff_alt | (intros; apply _root_.GlobalTheory.TraceAtG.levAtG_embA_iff_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbAMovesOffLevelIff
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbAMovesOffLevelIff
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.OffTrace
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise
end GlobalTheory.OffTrace
open GlobalTheory.LatPair GlobalTheory.FinPl in
open scoped Pointwise in
theorem GlobalTheory.OffTrace.embA_moves_off_level_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (GlobalTheory.FinPl.Moves (Yc (I.rec7 l Z) 0) (embA a.d.B.d a.d.B.o κ) (a.v.N 0) (a.v.N 0) (fun p => p ∉ a.v.gP) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∉ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  have h0 : 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := by
    have := Formalism.BasicNotions.Ranks.rS_two (I.rec7 l Z).R; omega
  have hB := ha.bot.1 h0
  have key : ∀ B' : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, B' = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0 →
      HEq (embA B'.d B'.o) (embA ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o) := by
    rintro _ rfl; rfl
  have hE := eq_of_heq (key a.d.B.lev hB)
  have hE' : embA a.d.B.d a.d.B.o κ = ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1)) :=
    DFunLike.congr_fun hE κ
  rw [hE']
  have hm : 0 < (I.rec7 l Z).R.m := by omega
  have hN : Submodule.IsLattice (I.rec7 l Z).host.E (a.v.N 0) := (ha.vis.sd 0 hm).1
  have hL : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x 0).L := (ha.x 0 (Nat.zero_le _)).sd.1
  rw [GlobalTheory.T.carriesLatticeCompletion_iff_forall_place _ _ _ hN, GlobalTheory.T.carriesLatticeCompletion_iff_forall_place _ _ _ hL]
  have hA : ∀ v, Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).V 0)
      (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0) (· = v) ↔
      Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).V₀ (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1)) (a.o.M 0 _ h0)
        (a.o.M 0 _ h0) (· = v) := fun v =>
    GlobalTheory.OffTrace.carriesLattice_wittEmbedding_iff_core _ _ _ v ((ha.shape.good v).bf 0 _ h0).monoV _
  have hoff : ∀ v, v ∉ a.v.tP → (Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).V 0)
      (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0) (· = v) ↔
      Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = v)) := by
    intro v hv
    obtain ⟨LL, -, hO⟩ := (ha.shape.split v hv).core 0 _ h0
    exact (hA v).trans (GlobalTheory.OffTrace.moves_emb_iff _ _ _ _ v hO κ)
  have hcore : ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X 0).rank) a.k),
      (mt ((I.rec7 l Z).sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
      (Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).V 0)
        (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0)
        (· = (a.o.p i).v) ↔ g • a.o.Q 0 i = a.o.Q 0 i) := by
    intro i g hg
    have hgl := ha.shape.glued 0 _ h0 i
    exact (hA _).trans ((GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff (a.o.β₀ 0 _ h0 i) (a.o.M 0 _ h0) _
      ((ha.shape.good (a.o.p i).v).bf 0 _ h0).sdV₀ hgl.lat _ _
      (GlobalTheory.T.splitPlace_besselCore_matrix_eq_blockDiagonal_one _ _ _ hgl.sum κ g hg)).trans (GlobalTheory.OffTrace.glued_stab_iff _ _ _))
  have hX : ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X 0).rank) a.k),
      (mt ((I.rec7 l Z).sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
      (Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = (a.o.p i).v) ↔ g • (a.o.Q 0 i).lat = (a.o.Q 0 i).lat) :=
    fun i g hg => GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff (a.o.β 0 i) (a.g.x 0).L _ (ha.x 0 (Nat.zero_le _)).sd
      (ha.shape.pre.latT 0 (Nat.zero_le _) i) κ g hg
  have hTg : ∀ i, (a.o.p i).v ∉ a.v.gP := fun i hg' =>
    Finset.disjoint_left.1 ha.vis.disj hg' ((ha.shape.pre.tP _).2 ⟨i, rfl⟩)
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun i g hg => (hcore i g hg).1 (h _ (hTg i))⟩
    by_cases hT : v ∈ a.v.tP
    · obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 hT
      obtain ⟨g, hg⟩ := GlobalTheory.OffTrace.exists_gl_frame (a.o.β 0 i) κ
      have h1 := (hcore i g hg).1 (h _ hv)
      exact (hX i g hg).2 (by rw [← Pair.smul_lat, h1])
    · exact (hoff v hT).1 (h v hv)
  · rintro ⟨h1, h2⟩ v hv
    by_cases hT : v ∈ a.v.tP
    · obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 hT
      obtain ⟨g, hg⟩ := GlobalTheory.OffTrace.exists_gl_frame (a.o.β 0 i) κ
      exact (hcore i g hg).2 (h2 i g hg)
    · exact (hoff v hT).2 (h1 v hv)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbAMovesOffLevelIffStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (GlobalTheory.FinPl.Moves (Yc (I.rec7 l Z) 0) (embA a.d.B.d a.d.B.o κ) (a.v.N 0) (a.v.N 0) (fun p => p ∉ a.v.gP) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∉ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ) := by
  first | exact @_root_.GlobalTheory.OffTrace.embA_moves_off_level_iff_alt | exact _root_.GlobalTheory.OffTrace.embA_moves_off_level_iff_alt | (intros; apply _root_.GlobalTheory.OffTrace.embA_moves_off_level_iff_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTraceMem
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace
theorem levTrace_mem_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hT' row col hc κ hκ y e
  have hx : embA a.d.B.d a.d.B.o κ ∈ GfC ((I.rec7 l Z).sp.Y 0) := GlobalTheory.Corev.EmbAGfC.embA_mem_GfC_fin _ _ _ _ _ _ _ _ κ hκ
  rw [_root_.GlobalTheory.T.true_geometry_final_identity_alt W hA u a ha hT' row col hc κ hκ y e, _root_.GlobalTheory.T.true_geometry_final_value_alt W hA u a ha hT' row col hc _ hx]
  unfold _root_.GlobalTheory.FamTrace.InLevelGroupOfY _root_.GlobalTheory.FamTrace.InLevelGroup
  rw [_root_.GlobalTheory.T.true_geometry_final_relation_alt W hA u a ha hT' row col hc κ hκ, _root_.GlobalTheory.T.true_geometry_final_property_alt W hA u a ha hT' row col hc κ hκ,
    ← GlobalTheory.T.carriesLatticeCompletion_on_off_iff_all_finitePlaces _ κ _ (fun p => p ∈ a.v.gP)]
  tauto
end GlobalTheory.FamTrace
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTraceMemStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_local_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W) := by
  first | exact @_root_.GlobalTheory.FamTrace.levTrace_mem_alt | exact _root_.GlobalTheory.FamTrace.levTrace_mem_alt | (intros; apply _root_.GlobalTheory.FamTrace.levTrace_mem_alt <;> assumption)
end
end

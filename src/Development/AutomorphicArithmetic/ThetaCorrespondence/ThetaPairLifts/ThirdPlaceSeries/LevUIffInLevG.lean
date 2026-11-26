module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeForward
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemUlocBadG
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InJRed
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InJRed
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace.RedAt
section Split
variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
include hq
end Split
end GlobalTheory.FamTrace.RedAt
namespace GlobalTheory.FamTrace.RedAt
set_option maxHeartbeats 1000000 in
theorem inJ_red_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ (i : Fin a.n) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (i0 : Fin 2) (h : ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), (a.G i).q.v = v → (∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1)) → Formalism.L2.Forms.InJ (I.rec7 l Z).R.k (I.rec7 l Z).R.t ((I.rec7 l Z).R.N 0) false (Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy i v i0 h hv hM
  have hstd := hA.tr.std.some u
  obtain ⟨w, hw, ρ, hu, hres⟩ := GlobalTheory.Mem.Col2.TC.GLev0.exists_w (_root_.GlobalTheory.MiTop.formsAtZero W u).gl hstd.gl.piG i0 v h
  have hid := (ha.tie row col).2.idem i
  have hPg : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  have hwe : w = (a.pl i).1 := GlobalTheory.Mem.Col2.TC.GLev0.vGs_inj (X := X) hPg
    (GlobalTheory.Mem.Col2.TC.GLev0.mem_vGs.2 ⟨i0, hw⟩) (hu.trans (hv.symm.trans hid.2))
  subst hwe
  have hn : (I.rec7 l Z).R.N 0 = (I.rec7 l Z).R.k := by simp [Ranks.N]
  have hr := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  have key : ∀ r c : Fin ((I.rec7 l Z).R.N 0), c ≤ r →
      Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1)) r c =
        if r = c then 1 else 0 := by
    intro r c hcr
    obtain ⟨r', rfl⟩ : ∃ r', r = finCongr hr r' := ⟨(finCongr hr).symm r, by simp⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = finCongr hr c' := ⟨(finCongr hr).symm c, by simp⟩
    have hcr' : c' ≤ r' := hcr
    have hsm := (hM r' c').2 hcr'
    have hinj : (finCongr hr r' = finCongr hr c') ↔ r' = c' := (finCongr hr).injective.eq_iff
    have e1 : (a.G i).q.pr (incA (I.rec7 l Z) (((if r' = c' then 1 else 0 : 𝓞 (I.rec7 l Z).host.E)) : (I.rec7 l Z).host.E)) =
        (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r' c' := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have hR := hasRes_of_pr (a.G i).q hid.1 (z := mt ((I.rec7 l Z).sp.X 0) κ r' c') (if r' = c' then 1 else 0) (by
      rw [e1]
      exact hsm)
    have hyrc : y.1.1 (finCongr hr r') (finCongr hr c') = toEAf (I.rec7 l Z) (mt ((I.rec7 l Z).sp.X 0) κ r' c') := by
      rw [← hy]
      rfl
    rw [← hyrc] at hR
    obtain ⟨hh, e⟩ := hres _ _ hR
    rw [GlobalTheory.Mem.Col2.TC.GLev0.mat_one]
    unfold Formalism.L2.Forms.redM
    refine (dif_pos hh).trans (e.trans ?_)
    by_cases hrc : r' = c'
    · subst hrc
      rw [if_pos rfl, if_pos rfl, map_one]
      exact map_one ρ
    · rw [if_neg hrc, if_neg (fun e => hrc (hinj.1 e)), map_zero]
      exact map_zero ρ
  have hlt : ∀ x : Fin ((I.rec7 l Z).R.N 0), (x : ℕ) < (I.rec7 l Z).R.k := fun x => hn ▸ x.2
  have hb : ∀ x : Fin ((I.rec7 l Z).R.N 0), Formalism.L2.Forms.blkOf (I.rec7 l Z).R.k (I.rec7 l Z).R.t x = x :=
    fun x => if_pos (hlt x)
  refine ⟨fun x z hxz => ?_, fun x _ => ?_, fun x z hz => absurd hz (ne_of_lt z.2), fun h' => absurd h' (by simp)⟩
  · rw [hb, hb] at hxz
    rw [key x z (le_of_lt (show z < x from hxz)), if_neg (fun e => by subst e; exact lt_irrefl _ hxz)]
  · rw [key x x le_rfl, if_pos rfl]
end GlobalTheory.FamTrace.RedAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InJRedStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_index_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ (i : Fin a.n) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (i0 : Fin 2) (h : ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), (a.G i).q.v = v → (∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1)) → Formalism.L2.Forms.InJ (I.rec7 l Z).R.k (I.rec7 l Z).R.t ((I.rec7 l Z).R.N 0) false (Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1))) := by
  first | exact @_root_.GlobalTheory.FamTrace.RedAt.inJ_red_alt | exact _root_.GlobalTheory.FamTrace.RedAt.inJ_red_alt | (intros; apply _root_.GlobalTheory.FamTrace.RedAt.inJ_red_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevelVLBase
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevelVLBase
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FinPl.AwayLevel.mem_levelVL_base_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a hat κ hκ y hy hmv v hv
  have hL := (hat.pinX.xs 0 (Nat.zero_le _)).2.2
  have hint := (GlobalTheory.SeeSaw.LevMem.moves_iff hL _ hy).1 hmv
  obtain ⟨k, hR⟩ := (hA.tr.std.some u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb : ∀ x, x ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb ↔ x ∈ TC.baseL B (B.R.N 0) (X.piT u) := hR.lb ()
  have hv' : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := hv
  have h1 : ∀ x ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb, ∀ j, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = r := fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have h2 : ∀ j, (Pi.single j ((B.T u : ℕ) : (I.rec7 l Z).host.E) : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb := fun j =>
    (hLb _).2 fun b => by
      have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
      refine ⟨if b = j then (B.T u : 𝓞 B.host.E) else 0, ?_, fun _ => ?_⟩
      · exact GlobalTheory.FinPl.AwayLevel.single_natCast_eq (K := B.host.E) (B.T u) j b
      · split_ifs
        · refine ⟨B.fields.conjO ((B.primes X).piT u), ?_⟩
          rw [hPr.piT_norm u]
        · exact dvd_zero _
  have hS := fun x => GlobalTheory.Mem.Col2.LevRead.mem_latS_iff hv' h1 h2 x
  have hmul : ∀ (N : GL (Fin ((I.rec7 l Z).R.N 0)) (Formalism.L2.DIV.AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), (∀ i j, N.1 i j ∈ Formalism.L2.DIV.RInt (I.rec7 l Z).host.F (I.rec7 l Z).host.E) →
      ∀ x : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F, (∀ b, x b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) →
        ∀ b, ((Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) N).1 *ᵥ x) b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v := fun N hN x hx b => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (Formalism.UG.P.afsplit_prV_int v _ (hN b j)) (hx j)
  refine Subgroup.mem_inf.2 ⟨GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2, fun x => ?_⟩
  rw [hS, hS]
  refine ⟨hmul _ hint.1 x, fun h b => ?_⟩
  have := hmul _ hint.2 _ h b
  rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevelVLBaseStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_compact_level_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb := by
  first | exact @_root_.GlobalTheory.FinPl.AwayLevel.mem_levelVL_base_alt | exact _root_.GlobalTheory.FinPl.AwayLevel.mem_levelVL_base_alt | (intros; apply _root_.GlobalTheory.FinPl.AwayLevel.mem_levelVL_base_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PatternOfTraceAtG
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PatternOfTraceAtG
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace.TraceBwd
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
set_option maxHeartbeats 1000000 in
theorem pattern_of_traceAtG_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ κ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X 0), _root_.GlobalTheory.FamTrace.TraceAtElement a κ → ∀ i : Fin a.n, ∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ κ hκ i r c
  obtain ⟨e, he, hβ⟩ := (ha.stdG i).1 0 (Nat.zero_le _)
  obtain ⟨g, hg, hgM⟩ := exists_mat (a.G i).q ((I.rec7 l Z).sp.X 0) _ e hβ κ
  obtain ⟨r, rfl⟩ := e.surjective r
  obtain ⟨c, rfl⟩ := e.surjective c
  have h := entries_of_colGroup e he g (colGroup_of_embX (a.G i).S g (hκ i g hg)) r c
  rw [hgM] at h
  refine ⟨h.1, fun hcr => ?_⟩
  have h1 : (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) (e r) (e c) =
      (1 : Matrix _ _ (a.G i).k) r c := by
    simp only [Matrix.one_apply, e.injective.eq_iff]
  rw [h1]
  exact h.2 hcr
end GlobalTheory.FamTrace.TraceBwd
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PatternOfTraceAtGStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_measure_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ κ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X 0), _root_.GlobalTheory.FamTrace.TraceAtElement a κ → ∀ i : Fin a.n, ∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1) := by
  first | exact @_root_.GlobalTheory.FamTrace.TraceBwd.pattern_of_traceAtG_alt | exact _root_.GlobalTheory.FamTrace.TraceBwd.pattern_of_traceAtG_alt | (intros; apply _root_.GlobalTheory.FamTrace.TraceBwd.pattern_of_traceAtG_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemUlocBadG
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace.AtG
set_option maxHeartbeats 1000000 in
theorem mem_Uloc_badG_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hIn v hv
  have hstd := hA.tr.std.some u
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 2, ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
    rcases hv with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨w, hw, -, hu, -⟩ := GlobalTheory.Mem.Col2.TC.GLev0.exists_w (_root_.GlobalTheory.MiTop.formsAtZero W u).gl hstd.gl.piG i0 v hi0
  have hwP : w ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg := (hA.lev.2.1 w).2 (GlobalTheory.Mem.Col2.TC.GLev0.mem_vGs.2 ⟨i0, hw⟩)
  obtain ⟨i, hi⟩ := a.pl.surjective ⟨w, hwP⟩
  have hqv : (a.G i).q.v = v := by
    rw [((ha.tie row col).2.idem i).2, hi]
    exact hu
  have hTv : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal :=
    GlobalTheory.Mem.Col2.TC.GLev0.T_notMem X u i0 hi0
  have hx := _root_.GlobalTheory.T.true_geometry_compact_level_property_alt W hA u a hat κ hκ y hy hIn.1 v hTv
  have hfr : (_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.fr i0 v hi0 = 1 := hstd.fr0 i0 v hi0
  refine ((_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.mem i0 v hi0 _ hx).2 ?_
  rw [hfr]
  exact _root_.GlobalTheory.T.true_geometry_final_index_alt W hA u a ha hat row col hc κ hκ y hy i v i0 hi0 hqv (_root_.GlobalTheory.T.true_geometry_final_measure_alt W hA u a ha hat κ hIn.2.2 i)
end GlobalTheory.FamTrace.AtG
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemUlocBadGStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_measure_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  first | exact @_root_.GlobalTheory.FamTrace.AtG.mem_Uloc_badG_alt | exact _root_.GlobalTheory.FamTrace.AtG.mem_Uloc_badG_alt | (intros; apply _root_.GlobalTheory.FamTrace.AtG.mem_Uloc_badG_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocTOfInLevG
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastRowCongOfKeepsPairs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastRowCongOfKeepsPairs
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.LastRow
end GlobalTheory.FamTrace.LastRow
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.FamTrace.lastRow_cong_of_keepsPairs_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ → (∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r s : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r s) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ s : Fin ((I.rec7 l Z).R.N 0), ∃ c ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v, Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ (Formalism.L2.Col.lastIdx _) s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N 0)) (Fin ((I.rec7 l Z).R.N 0)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (Formalism.L2.Col.lastIdx _) s = Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)) * c := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat κ hκ hkp hint v hv s
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have htP : ∀ p, p ∈ a.v.tP ↔ ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.asIdeal := by
    have hψ := hat.pinX.std
    let row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t := fun t =>
      { vP := fun _ => 0, vT := fun _ _ => 0,
        sBF := fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
        sFB := fun j σ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some,
        io := fun _ => 0, ioT := fun _ _ => 0 }
    exact (ha.tie row (fun t =>
      { kom := fun _ => 1, Ch := fun _ => Unit, fin := fun _ => inferInstance, dd := fun _ _ _ => 0, e := fun _ _ => 0,
        eT := fun _ _ _ => 0, Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1,
        cK := fun _ => 1, cP := 1 })).1.tP
  obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 ((htP v).2 hv)
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  obtain ⟨e, he⟩ := hat.std.1
  have hpi : X.piT u ∈ (e i).1.asIdeal := by
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    exact (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have hn := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  set r₀ : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm (Formalism.L2.Col.lastIdx _) with hr₀def
  set s' : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm s with hs'def
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X 0).rank := by
    have h1 : (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 = (I.rec7 l Z).R.N 0 - 1 := rfl
    have h2 : r₀.1 = (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 := rfl
    have h3 := NeZero.ne ((I.rec7 l Z).R.N 0)
    omega
  have hQ := GlobalTheory.AdForm.stdT_pair_coords I l Z u a.k a.ι a.o.p a.o.β a.o.Q _ hat.std 0 (Nat.zero_le _) i r₀ hr₀
  obtain ⟨g, hg⟩ := GlobalTheory.FamTrace.LastRow.exists_gl (a.o.β 0 i) κ
  have hl := GlobalTheory.FamTrace.LastRow.row_lt_of_smul_pair_eq _ _ _ _ (a.o.β 0 i).bb' _ r₀ hQ g hg (hkp i g hg) s'
  exact GlobalTheory.FamTrace.LastRow.entry_cong (I.rec7 l Z) a.k (a.o.p i) (e i).1 (he i) ((I.rec7 l Z).mem u).A.T (X.piT u)
    (B.fields.conjO (X.piT u)) ((B.fields_conjO_coe _).trans (GlobalTheory.RankOneLine.star_eq_hostConj (I.rec7 l Z) _).symm)
    (hPr.piT_norm u) (hPr.piT_cop u) hpi hv (GlobalTheory.LevelUnif.T_notMem_sq (I.rec7 l Z) u (W.R.T.cols.forms u).atT _ hv)
    _ hn κ _ s (hint _ _ s) hl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastRowCongOfKeepsPairsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_character_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ → (∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r s : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r s) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ s : Fin ((I.rec7 l Z).R.N 0), ∃ c ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v, Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ (Formalism.L2.Col.lastIdx _) s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N 0)) (Fin ((I.rec7 l Z).R.N 0)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (Formalism.L2.Col.lastIdx _) s = Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)) * c := by
  first | exact @_root_.GlobalTheory.FamTrace.lastRow_cong_of_keepsPairs_alt | exact _root_.GlobalTheory.FamTrace.lastRow_cong_of_keepsPairs_alt | (intros; apply _root_.GlobalTheory.FamTrace.lastRow_cong_of_keepsPairs_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocTOfInLevG
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.FamTrace.uloc_T_of_inLevG_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hIn v hv
  have hF := hA.tr.std.some u
  have hI := hA.tr.ok
  have hP := hA.tr.pins.some
  obtain ⟨kk, R⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hgram : Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have hlb := R.lb ()
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s (W.R.T.cols.forms u).atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact (W.R.T.cols.forms u).atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N 0) ((((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ (W.R.T.cols.forms u).atT.piU hp0 _ ?_
    rw [hF.piU]; exact hlb
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) := by
    have h1 := hPr.piT_cop u
    have e : s (W.R.T.cols.forms u).atT.piU = B.fields.conjO ((B.primes X).piT u) := by
      apply RingOfIntegers.ext (K := (I.rec7 l Z).host.E)
      rw [hsc, hF.piU]
      exact (B.fields_conjO_coe _).symm
    rw [e, hF.piU]
    exact h1
  have hint : ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r t : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) w (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r t) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E w :=
    GlobalTheory.T.finiteMatrix_entry_integral_of_keeps_standardLattice (I.rec7 l Z) ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (a.g.x 0).L
      ((hat.std.2 0 (Nat.zero_le _)).1) κ hIn.1
  refine GlobalTheory.T.unitary_lastRow_congr_one_mem_localLevel_levelPrime (Formalism.L2.Forms.sigD (I.rec7 l Z)) (fun x => star_star x) hgram (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) rfl hpq hcop hTp.ne_zero hL v hv _ (GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2) ?_ ?_
  · intro r t
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 r t) ∈ _
    rw [← hy]
    exact hint v r t
  · intro t
    obtain ⟨c, hc, he⟩ := _root_.GlobalTheory.T.true_geometry_final_character_alt W hA u a ha hat κ hκ hIn.2.1 hint v hv t
    refine ⟨c, hc, ?_⟩
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 _ t) - _ = _
    rw [← hy, he, hF.piU]
    rfl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocTOfInLevGStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_index_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  first | exact @_root_.GlobalTheory.FamTrace.uloc_T_of_inLevG_alt | exact _root_.GlobalTheory.FamTrace.uloc_T_of_inLevG_alt | (intros; apply _root_.GlobalTheory.FamTrace.uloc_T_of_inLevG_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairsOfMemLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairsOfMemLevel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.PairsFwd
end GlobalTheory.FamTrace.PairsFwd
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.FamTrace.keepsPairs_of_mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a _ hat row col _ κ _ y hy hU i g hg
  obtain ⟨hP⟩ := hA.tr.pins
  obtain ⟨hC⟩ := hA.tr.std
  have hF := hC u
  obtain ⟨k₀, hR⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  exact @GlobalTheory.FamTrace.PairsFwd.stdPair_fixed B X I hA.tr.ok hP l Z u _ _ _ hF 0 (Nat.zero_le _) (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev
    (fun x => hR.lb () x) a.k a.fld a.val a.top a.loc a.ι _ _ _ _ hat.std κ y.1 hy hU i g hg
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairsOfMemLevelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_image_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ := by
  first | exact @_root_.GlobalTheory.FamTrace.keepsPairs_of_mem_level_alt | exact _root_.GlobalTheory.FamTrace.keepsPairs_of_mem_level_alt | (intros; apply _root_.GlobalTheory.FamTrace.keepsPairs_of_mem_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcPrVMemUlocOff
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcPrVMemUlocOff
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace
set_option maxHeartbeats 4000000 in
theorem bc_prV_mem_Uloc_off_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Formalism.L2.Forms.badG (I.rec7 l Z) → (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hin v hbad hTv
  obtain ⟨Fstd⟩ := hA.tr.std
  obtain ⟨k, hR⟩ := (Fstd u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb : ∀ x, x ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb ↔ x ∈ TC.baseL B _ (X.piT u) := fun x => hR.lb () x
  rw [(_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc_hyp v hbad hTv]
  have hx0 := (hat.pinX.xs 0 (Nat.zero_le _)).2.2
  have hsd := GlobalTheory.AdForm.intVec_isSelfDualC I hA.tr.ok l Z 0 (Nat.zero_le _) (a.g.x 0).L hx0
  have hmv := ((GlobalTheory.FinPl.movesLocal _ _ _ hsd κ).1 hin.1) v
  haveI : Submodule.IsLattice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (a.g.x 0).L := hsd.1
  have hfg : (a.g.x 0).L.FG := Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x 0).L
  have hn := Formalism.L2.Forms.rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) 0 (Nat.zero_le _)
  let Λ : Submodule (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) :=
    (a.g.x 0).L.comap (LinearMap.funLeft (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (finCongr hn))
  have hb := bc_prV_mem_levelVL_of_moves (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X 0) _ hn (a.g.x 0).L Λ hfg (fun x => Iff.rfl) κ y.1 hy v hmv
  let s : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E :=
    RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)
  have hsc : ∀ x, (s x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.conj (x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) :=
    fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hTdvd : X.piT u ∣ ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.E) := by
    refine ⟨s (X.piT u), ?_⟩
    have hsc' : ∀ x, algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E (s x) =
        (I.rec7 l Z).host.conj (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E x) := hsc
    apply RingOfIntegers.coe_injective
    push_cast
    erw [map_mul, hsc', ← (Fstd u).piU]
    exact (W.R.T.cols.forms u).atT.piU_norm.symm
  have hint : ∀ (j i : Fin ((I.rec7 l Z).R.N 0)), ∃ r : 𝓞 (I.rec7 l Z).host.E,
      (Pi.single j ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) : Fin _ → _) i = (r : (I.rec7 l Z).host.E) ∧
        (i.1 + 1 = (I.rec7 l Z).R.N 0 → X.piT u ∣ r) := by
    intro j i
    by_cases h : i = j
    · subst h
      exact ⟨((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.E), by simp, fun _ => hTdvd⟩
    · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
  have e : Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v
      (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb =
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v Λ := by
    refine levelVL_eq_of_std _ _ hTv (fun x hx j => ?_) (fun j => (hLb _).2 fun i => hint j i) (fun x hx j => ?_) (fun j => ?_)
    · obtain ⟨r, e, -⟩ := (hLb x).1 hx j
      exact ⟨r, e⟩
    · have h := (hx0 _).1 hx ((finCongr hn).symm j)
      simp only [LinearMap.funLeft_apply, Function.comp_apply, Equiv.apply_symm_apply] at h
      exact ⟨⟨x j, h⟩, rfl⟩
    · refine (hx0 _).2 fun i => ?_
      obtain ⟨r, hr, -⟩ := hint j (finCongr hn i)
      show IsIntegral ℤ ((Pi.single j _ : Fin _ → _) (finCongr hn i))
      rw [hr]
      exact r.isIntegral_coe
  rw [e]
  exact hb
end GlobalTheory.FamTrace
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcPrVMemUlocOffStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_volume_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Formalism.L2.Forms.badG (I.rec7 l Z) → (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  first | exact @_root_.GlobalTheory.FamTrace.bc_prV_mem_Uloc_off_alt | exact _root_.GlobalTheory.FamTrace.bc_prV_mem_Uloc_off_alt | (intros; apply _root_.GlobalTheory.FamTrace.bc_prV_mem_Uloc_off_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceAtGOfMem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceAtGOfMem
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace.TraceFwd
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
set_option maxHeartbeats 1000000 in
theorem traceAtG_of_mem_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → _root_.GlobalTheory.FamTrace.TraceAtElement a κ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ κ _ y hκy hy i g hg
  obtain ⟨hS⟩ := hA.tr.std
  obtain ⟨hP⟩ := hA.tr.pins
  obtain ⟨k₀, hR⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨A, hU, hA'⟩ := exists_red I hA.tr.ok ((TC.spaces_in_coordinates I hA.tr.ok hP l Z).2.2.2 0 (Nat.zero_le _)).1
    ((W.R.T.cols.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev hR ⟨_, hy⟩ (a.pl i).1 ((hA.lev.2.1 _).1 (a.pl i).2)
  letI := (a.G i).fld; letI := (a.G i).val; letI := (a.G i).top; letI := (a.G i).loc
  exact embX_mem (a.G i).S g (colGroup_of_red (a.G i).q ((ha.tie row col).2.idem i).1 ((I.rec7 l Z).sp.X 0)
    (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (show B.R.N 0 = B.R.k by simp [Ranks.N]) _
    ((ha.stdG i).1 0 (Nat.zero_le _)) hκy hA' hU g hg)
end GlobalTheory.FamTrace.TraceFwd
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceAtGOfMemStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_kernel_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → _root_.GlobalTheory.FamTrace.TraceAtElement a κ := by
  first | exact @_root_.GlobalTheory.FamTrace.TraceFwd.traceAtG_of_mem_alt | exact _root_.GlobalTheory.FamTrace.TraceFwd.traceAtG_of_mem_alt | (intros; apply _root_.GlobalTheory.FamTrace.TraceFwd.traceAtG_of_mem_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeForwardPreservesBase
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeForwardPreservesBase
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.LatFwd
end GlobalTheory.FamTrace.LatFwd
namespace GlobalTheory.FamTrace.LatFwd
set_option maxHeartbeats 4000000 in
theorem lattice_forward_preserves_base_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hU
  have hs := hA.tr.std.some u
  obtain ⟨k, hk⟩ := hs.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hlb := hk.lb ()
  have hg : Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hA.tr.ok hA.tr.pins.some l Z).2.2.2 0 (Nat.zero_le _)).1
  have hfg : ((a.g.x 0).L).FG := by
    haveI : Submodule.IsLattice _ (a.g.x 0).L := (ha.x 0 (Nat.zero_le _)).sd.1
    exact Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x 0).L
  have hne : X.piT u ≠ 0 := by
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hne' : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h => hne (by exact_mod_cast h)
  have hσ : ∀ x, Formalism.L2.Forms.sigD (I.rec7 l Z) (Formalism.L2.Forms.sigD (I.rec7 l Z) x) = x := fun x => star_star x
  have hΛ : ∀ x, x ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb ↔ ∀ j : Fin _, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = _ → X.piT u ∣ r) :=
    fun x => hlb x
  have hloc : ∀ v, ∀ g ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v, ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (Formalism.UG.intOE (I.rec7 l Z).host.E) (v.adicCompletionIntegers (I.rec7 l Z).host.F).toSubring :=
    fun v g hgv => GlobalTheory.T.unitFormUnitary_integralEntries_of_levelLattice _ _ _ hσ _ _ hg _ hne' _ hΛ v g ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc_lev v hgv)
  have hyv := (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U_eq y.1).1 hU).2
  have hyinv := finM_inv_eq _ _ κ y.1 hy
  refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen _ _ hfg _ ?_
  clear hs hk hlb row col hc
  have hL : (a.g.x 0).L = GlobalTheory.AdelicU.stdLattice (I.rec7 l Z).host.E ((I.rec7 l Z).sp.X 0).rank := by
    ext z
    rw [(hat.pinX.xs 0 (Nat.zero_le _)).2.2 z]
    simp only [GlobalTheory.AdForm.intVec, Set.mem_setOf_eq, GlobalTheory.AdelicU.stdLattice, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, LinearMap.mem_range, Algebra.linearMap_apply]
    exact forall_congr' fun k => ⟨fun hk => ⟨⟨_, hk⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩
  rw [GlobalTheory.AdelicU.levelOpen, Subgroup.mem_iInf]
  intro v
  rw [Subgroup.mem_comap, hL]
  have e2 : ∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y.1)⁻¹).1 i j ∈ Formalism.UG.tensInt (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (Formalism.UG.intOE (I.rec7 l Z).host.E) (v.adicCompletionIntegers (I.rec7 l Z).host.F).toSubring := by
    rw [map_inv]; exact hloc v _ (inv_mem (hyv v))
  exact proj_mem_stabLoc_std _ κ v (GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral _ _ _ _ κ y.1 hy v (hloc v _ (hyv v)))
    (GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral _ _ _ _ κ⁻¹ (y.1)⁻¹ hyinv v e2)
end GlobalTheory.FamTrace.LatFwd
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeForwardPreservesBaseStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_forward_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) := by
  first | exact @_root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt | exact _root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt | (intros; apply _root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevUIffInLevG
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace
theorem levU_iff_inLevG_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ _root_.GlobalTheory.FamTrace.InLevelGroup a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy
  constructor
  · intro h
    exact ⟨_root_.GlobalTheory.T.true_geometry_lattice_forward_alt W hA u a ha hat row col hc κ hκ y hy h, _root_.GlobalTheory.T.true_geometry_lattice_image_alt W hA u a ha hat row col hc κ hκ y hy h, _root_.GlobalTheory.T.true_geometry_lattice_kernel_alt W hA u a ha hat row col hc κ hκ y hy h⟩
  · intro h
    refine ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U_eq _).2 ⟨y.2, fun v => ?_⟩
    by_cases hv : (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal)
    · exact _root_.GlobalTheory.T.true_geometry_lattice_index_alt W hA u a ha hat row col hc κ hκ y hy h v hv
    · by_cases hb : v ∈ Formalism.L2.Forms.badG (I.rec7 l Z)
      · exact _root_.GlobalTheory.T.true_geometry_lattice_measure_alt W hA u a ha hat row col hc κ hκ y hy h v hb
      · exact _root_.GlobalTheory.T.true_geometry_lattice_volume_alt W hA u a ha hat row col hc κ hκ y hy h v hb hv
end GlobalTheory.FamTrace
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevUIffInLevGStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ _root_.GlobalTheory.FamTrace.InLevelGroup a κ) := by
  first | exact @_root_.GlobalTheory.FamTrace.levU_iff_inLevG_alt | exact _root_.GlobalTheory.FamTrace.levU_iff_inLevG_alt | (intros; apply _root_.GlobalTheory.FamTrace.levU_iff_inLevG_alt <;> assumption)
end
end

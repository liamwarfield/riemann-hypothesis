module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.MovedJoin
open GlobalTheory.AdForm
end GlobalTheory.Fam.MovedJoin
namespace GlobalTheory.Fam
open GlobalTheory.AdForm GlobalTheory.Fam.MovedJoin
set_option maxHeartbeats 1000000 in
theorem QuadraticExtensionData.Reads.movedAt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha t J hJ i
  refine { toReadsAt := ⟨hJ.eq i, hJ.tw i, hJ.M i, hJ.rep i⟩, rk := fun _ => rfl, low := ?_, pen := ?_ }
  · intro k hk hm β e he r b
    have hs : (a.Q (J.pl i) ⟨t, J.mem i⟩).s + 1 + 1 = B.R.m := (a.Q (J.pl i) ⟨t, J.mem i⟩).hs
    have hstd := hJ.std k (by omega) β
    have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
    obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 k (Nat.le_succ_of_le hk)
    rw [hF]
    have key : ∀ r' b' : Fin (B.R.N k), Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 k β).1.1 (J.P i) (Pi.single b' 1) r' =
        if r' = b' then (1 : B.host.E) else 0 := by
      intro r' b'
      apply (algebraMap B.host.E ((J.P i).1.adicCompletion B.host.E)).injective
      rw [← adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn k hm β r' b', hstd, adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ r' b']
    unfold QTw.baseFr
    refine (congrArg _ (key _ _)).trans ?_
    have hiff : ((finCongr (rankN (I.rec7 l Z) k hm)) (Fin.cast rfl r) = e b) ↔ (r = e' b) := by
      constructor
      · intro h
        exact Fin.ext ((congrArg Fin.val h).trans ((he b).trans (he' b).symm))
      · intro h
        exact Fin.ext ((congrArg Fin.val h).trans ((he' b).trans (he b).symm))
    have hR : ∀ x : (a.Q (J.pl i) ⟨t, J.mem i⟩).k, x = (if r = e' b then 1 else 0) →
        x = Matrix.submatrix (1 : Matrix (Fin ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).X k).rank) (Fin ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).X k).rank) (a.Q (J.pl i) ⟨t, J.mem i⟩).k) id e' r b := by
      intro x hx
      rw [hx]
      rfl
    apply hR
    split_ifs with h1 h2 h2
    · simp only [GlobalTheory.LocMod.Place.pr]
      exact (congrArg _ (map_one _)).trans (map_one _)
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · simp only [GlobalTheory.LocMod.Place.pr]
      exact (congrArg _ (map_zero _)).trans (map_zero _)
  · intro hm β e he
    have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
    have hidem : Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := by rw [hJ.eq i]; exact (J.G i).idem
    obtain ⟨k₀, h, hk₀, hfin, hkA, hh, hg⟩ := hJ.pen ((J.G i).s + 1) (by omega) β
    obtain ⟨g, hgJ, hgm⟩ := hg i rfl
    obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 ((J.G i).s + 1) le_rfl
    have hkb := (hJ.is.kA ((J.G i).s + 1) hm β).2.1
    have hent : ∀ (y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1))) (c d : Fin ((I.rec7 l Z).sp.X ((J.G i).s + 1)).rank),
        finM _ (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) y (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c)
          (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d) = toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ y c d) := by
      intro y c d
      simp [finM, Matrix.reindex_apply]
    have hent' : ∀ (y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1))) (c d : Fin (B.R.N ((J.G i).s + 1))),
        finM _ (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) y c d = toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ y
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm c) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm d)) := by
      intro y c d
      rfl
    have hk0 : (Formalism.L2.Theta.mt _ k₀).map (J.G i).q.pr = 1 := by
      refine map_eq_one_of_pr _ _ fun c d => GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq _ _ hidem _ _ ?_
      have h1 := congrFun (congrFun hfin (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c))
        (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d)
      rw [hent] at h1
      refine (congrArg (adAt B.host.F (J.P i).1) h1).trans ((adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ _ _).trans ?_)
      have hite : (if finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c = finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d
          then (1 : B.host.E) else 0) = if c = d then 1 else 0 := by
        by_cases hcd : c = d
        · subst hcd
          simp
        · rw [if_neg (fun h' => hcd ((finCongr _).injective h')), if_neg hcd]
      exact congrArg _ hite
    have hkAm : (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)).map (J.G i).q.pr =
        ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ := by
      rw [hkA, GlobalTheory.AdForm.CongAtIdem.mt_mul', Matrix.map_mul, hk0, Matrix.one_mul]
      exact hgm
    have hentry : ∀ (x : Fin (B.R.N ((J.G i).s + 1))) (b : StepData.XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1)),
        (ofSplit (J.G i).q).pr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single (e b) 1) x) =
          (((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) b := by
      intro x b
      have h1 := adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn _ hm β x (e b)
      rw [← hkb] at h1
      have h2 : adAt B.host.F (J.P i).1 (toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e b)))) =
          algebraMap B.host.E _ (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single (e b) 1) x) := by
        have h5 := hent' (J.A.kA ((J.G i).s + 1) β) x (e b)
        exact (congrArg (adAt B.host.F (J.P i).1) h5).symm.trans h1
      have h3 := GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq _ _ hidem _ _ h2
      have h4 : (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e b) = e' b := Fin.ext ((he b).trans (he' b).symm)
      refine h3.symm.trans ?_
      refine (congrArg (fun c => (J.G i).q.pr (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) c)) h4).trans ?_
      refine (congrFun (congrFun hkAm _) (e' b)).trans ?_
      exact mul_frameγ_std _ e' hF _ _ _
    refine ⟨g, hgJ, fun r b => hentry _ b, ?_⟩
    refine (hJ.cos i β e he).trans (congrArg _ ?_)
    funext r
    have hexp := map_eq_sum_frame ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i))
      (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2) (e r)
    refine hexp.trans ?_
    refine (Equiv.sum_comp e (fun c => ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single c 1) (e r)) *
      ((J.G i).q.pr.comp (incA (I.rec7 l Z))) ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i)).symm
        (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2) c))).symm.trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    have h4 : (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e r) = e' r := Fin.ext ((he r).trans (he' r).symm)
    have H := (hentry (e r) b).trans ((congrArg (fun c => (((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁) c b) h4).trans
      (frameβ_mul_std _ e' hF _ r b))
    exact congrArg₂ (· * ·) H rfl
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiStdEqConstMulLocXi
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section Loc
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.TopCongr GlobalTheory.LocMod
namespace GlobalTheory.Fam.TopFrames
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.Fam.TopFrames
end Loc
section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix
open GlobalTheory.SeeSaw.BaseFrame GlobalTheory.TopStep
namespace GlobalTheory.Fam.TopFrames
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
end GlobalTheory.Fam.TopFrames
end Gen
section World
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
namespace GlobalTheory.Fam.TopFrames
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}
section Tw
variable {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀}
end Tw
variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
set_option maxHeartbeats 1000000 in
theorem valuation_frs_sub_kronecker_lt_one (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.Reads) (P : BadPr I (W.P.I.tup t))
    (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j + 1 = B.R.m) (β : J.Ch₀ j) (r c) :
    HeightOneSpectrum.valuation B.fields.E P.1
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P (Pi.single c 1) r - if r.val = c.val then 1 else 0) < 1 := by
  letI := GlobalTheory.Mem.Col2.starE B
  have hm : j ≤ B.R.m := by omega
  obtain ⟨k₀, h, -, h1, h2, h3, -⟩ := hJ.pen j hj β
  have h4 : ¬ ∃ i, (J.G i).q.v = P.1.under (𝓞 B.host.F) := by
    rintro ⟨i, hi⟩
    rw [(GlobalTheory.LocMod.PinEx.place_facts _ (J.G i).idem).1] at hi
    have h5 := ((TwistPrimes.twist_primes_away I hW.tr.ok).2 u (W.P.I.tup t) (J.pl i) ((hW.tq.Q t _).1 (J.mem i))).1
    rcases (under_eq_iff B.host (J.pl i) P.1).1 hi.symm with h6 | h6
    · exact h5.2.1 (h6 ▸ hP)
    · exact h5.2.2.2.1 (h6 ▸ hP)
  have h5 := finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 h4
  have h6 := (TrueColsTest.kStd_spec X u (B.R.N j)).2.1 (P.1.under (𝓞 B.host.F))
    fun hT => Formalism.L2.Col.rls_T_notUnder l.pr u _ hT ⟨P.1, hP, rfl⟩
  have hk : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (J.A.kb j β) = 1 := by
    refine Units.ext ?_
    have h7 := (hJ.is.kA j hm β).2.1
    rw [h2, GlobalTheory.AdForm.Model.finM_mul, h1] at h7
    have h8 : (J.A.kb j β).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := by
      rw [← h7]
      refine Matrix.map_mul.trans ?_
      have h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := congrArg Units.val h6
      exact (congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j))
        (B.host.E ⊗[B.host.F] (P.1.under (𝓞 B.host.F)).adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)
    exact h8
  have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  have h9 := (hJ.is.base j hm β).1
  rw [e]
  exact GlobalTheory.SeeSaw.BaseFrame.lift_near_one (y := 1) (by rw [one_mul]; exact h9) (by rw [one_mul]; exact h9) h9 (hJ.is.base j hm β).2
    ⟨P.1, hP⟩ hk (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hP⟩) r c
set_option maxHeartbeats 1000000 in
theorem fm_beta_eq {a : _root_.GlobalTheory.Fam.GeometricFamily W u} (hIs : a.Is) (hTr : a.True) (hA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0)
    (n : Fin a.n) (r) : (∀ c, (a.G n).FM.β r (Sum.inl c) = if r.val = GlobalTheory.SymBridge.zPos c then 1 else 0) ∧
      (a.G n).FM.β r (Sum.inr ()) = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) := by
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  have hA' : ∀ j (h : j = (I.rec7 l Z).R.m) r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0 := by
    rintro _ rfl
    exact hA
  have hB' : ∀ j (h : j = (I.rec7 l Z).R.m) r, ((a.g.oT j h).iB *ᵥ a.o.ζ₀) r =
      if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    rintro _ rfl r
    exact hTr.z0 r
  obtain ⟨-, ⟨e, he, hT⟩, hz⟩ := hIs.stdG n
  rw [(a.G n).last]
  refine ⟨fun c => ?_, ?_⟩
  · rw [fromCols_apply_inl, hT, Matrix.mul_apply, Finset.sum_eq_single (e c)]
    · rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, ← he c]
      refine (congrArg (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (hA' _ _ r (e c))).trans ?_
      split_ifs
      exacts [map_one _, map_zero _]
    · intro b _ hb
      rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [fromCols_apply_inr, hz]
    refine Eq.trans ?_ (congrArg (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (hB' _ (a.G n).hs r))
    refine Eq.trans ?_ (map_sum (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (fun b => (a.g.oT _ (a.G n).hs).iB r b * a.o.ζ₀ b) Finset.univ).symm
    show ∑ b, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((a.g.oT _ (a.G n).hs).iB r b) * _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (a.o.ζ₀ b) = _
    exact Finset.sum_congr rfl fun b _ => (map_mul (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) _ _).symm
set_option maxHeartbeats 2000000 in
theorem xiStd_eq_const_mul_locXi_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch ((a.G n).s + 1)) (γ : J.Ch ((a.G n).s + 1 + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ C : ℂ,
  (∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((a.G n).s + 1)) (Fin B.R.t) ((a.G n).s + 2) ⊕ Unit ≃ Fin (B.R.N B.R.m)),
     GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e →
     ∀ (y : Formalism.L2.Col.HomE B.fields.E (B.R.N ((a.G n).s + 1)) (B.R.N B.R.m)) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
       (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) * y' i)) →
       ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
           (Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y' (e' r))) (GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' y) =
         C * B.embLL (GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P y y')) →
  ∀ (hj : (a.G n).s + 1 + 1 ≤ B.R.m) z, _root_.GlobalTheory.Fam.TopLoc.standardXi a n z =
    C * B.embLL (GlobalTheory.QTw.locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (GlobalTheory.QTw.homOf I l Z ((a.G n).s + 1) hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hA n t J hJ α γ P hP C hC hj z
  have hint : ∀ x : B.fields.E, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt P.1 x := by
    have hR := (hIs.tie (fun t => (TopLocFac.nonempty_rowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g hTr.pinX.std t).some)
      fun t => (TopLocFac.nonempty_colCh _ _).some).2
    rw [hP]
    exact (GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hm : (a.G n).s + 1 ≤ B.R.m := Nat.le_of_succ_le hj
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  have hlt := GlobalTheory.SeeSaw.LevelData.val_lt_one_iff hint
  obtain ⟨e', he'⟩ := exists_xOrd B.R ((a.G n).s + 1)
  obtain ⟨e, he⟩ := exists_topOrd B.R (a.G n).s hs
  have hF := _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ P hPv hs (J.ι _ α)
  have hF' := top_near hW.tr.ok hJ.is P hPv hs (J.ι _ γ)
  have hq := intAt_q_mul (A := J.A) P hPv hs (J.ι _ α)
  have hco := hJ.cosG n α e' he'
  have hx : locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (homOf I l Z ((a.G n).s + 1) hj z) =
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P
        (castSp B.fields.E (congrArg B.R.N hs) ∘ₗ Formalism.L2.Col.inFr
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P) (homOf I l Z ((a.G n).s + 1) hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2)) := by
    unfold locXi
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dif_pos hs]
    rfl
  rw [hx]
  clear hx
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P = f at hF hq ⊢
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P = f' at hF' ⊢
  generalize Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g10⟩ := id (GlobalTheory.SeeSaw.LevelData.type_prime hPv)
  have hqv : HeightOneSpectrum.valuation B.fields.E P.1 (Formalism.L2.Col.qOf P.1 : B.fields.E) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨i, g1, -, -, g4, -⟩ := GlobalTheory.SeeSaw.LevelData.type_prime hPv
    exact GlobalTheory.AtTypeExists.valuation_norm P.1 (g1 ▸ g4)
  have hy : (Submodule.Quotient.mk ((a.G n).S.y0 (Fin B.R.t)) :
      (GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) → (a.G n).k) ⧸
        box (GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1)) (1 : (a.G n).kˣ)) =
      Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f.symm y (e' r)) := by
    refine GlobalTheory.SeeSaw.StdMatch.mk_eq_mk_of_int fun c => ?_
    have h1 := (hint _).2 (intAt_sub_of_near hqv hF hq (e' c))
    rw [LinearEquiv.apply_symm_apply, map_sub] at h1
    have h2 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y (e' c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k] := hco c
    have h3 := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at h3
  refine Eq.trans ?_ (hC e' (e.trans (finCongr (congrArg B.R.N hs))) he' (fun r => he r) _ _ hq)
  refine Eq.trans ?_ (congrArg (fun w => ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) w _) hy)
  have e1 := GlobalTheory.SeeSaw.StdMatch.mul_toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (rankN (I.rec7 l Z) _ hm) (rankN (I.rec7 l Z) _ hj) f f' e' e
    (Matrix.of fun r c => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f (Pi.single (e' c) 1) (finCongr (rankN (I.rec7 l Z) _ hm) r)))
    (Matrix.of fun r c => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f' (Pi.single (e c) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)))
    (fun _ _ => rfl) (fun _ _ => rfl) z
  refine xiTop_frames (a.G n).unitVol (a.G n).S (Fin B.R.t) ((a.G n).FX _ le_rfl) (a.G n).FM
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hm).2.2) ((a.G n).latX _ le_rfl))
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hj).2.2) (a.G n).latM) (fun r c => ?_) (fun r c => ?_) _ e1
  · obtain ⟨e₁, h1, h2⟩ := (hIs.stdG n).1 ((a.G n).s + 1) le_rfl
    have h3 := (hlt _).2 (hF (finCongr (rankN (I.rec7 l Z) _ hm) r) (e' c))
    rw [map_sub, apply_ite (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n), map_one, map_zero, (he' c).trans (h1 c).symm] at h3
    have h4 : ((a.G n).FX ((a.G n).s + 1) le_rfl).β r c = if r.val = (e₁ c).val then 1 else 0 :=
      (congrFun (congrFun h2 r) c).trans (Matrix.one_apply.trans (if_congr Fin.ext_iff rfl rfl))
    exact (congrArg (fun w => valuation (a.G n).k (_ - w)) h4).trans_lt h3
  · have h3 := (hlt _).2 (hF' (finCongr (rankN (I.rec7 l Z) _ hj) r) (e c))
    rw [map_sub, apply_ite (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n), map_one, map_zero, he c] at h3
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Fam.TopFrames.fm_beta_eq hIs hTr hA n r
    show valuation (a.G n).k (_ - (a.G n).FM.β r c) < 1
    rcases c with c | c
    · exact (congrArg (fun w => valuation (a.G n).k (_ - w)) (h1 c)).trans_lt h3
    · refine (congrArg (fun w => valuation (a.G n).k (_ - w)) h2).trans_lt ?_
      have h4 := (hlt ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E)).2 ((P.1.valuation_lt_one_iff_mem _).2 (g10 u))
      have h5 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E) = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((X.piT u : 𝓞 B.host.E) : B.host.E) - 1 :=
        ((_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n).map_sub ((X.piT u : 𝓞 B.host.E) : B.host.E) 1).trans (congrArg _ (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n).map_one)
      rw [h5] at h4
      replace h3 : valuation (a.G n).k (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f' (Pi.single (e (Sum.inr c)) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)) -
          if (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 then 1 else 0) < 1 := h3
      have h6 : 0 < B.R.N B.R.m := by
        have := (e (Sum.inr c)).2
        rw [← hs]
        omega
      by_cases hr : r.val + 1 = B.R.N B.R.m
      · rw [if_pos (show (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from Nat.eq_sub_of_add_eq hr)] at h3
        rw [if_pos hr]
        have h7 := Valuation.map_sub_lt _ h3 h4
        rwa [sub_sub_sub_cancel_right] at h7
      · rw [if_neg (show ¬ (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from fun h => hr (by
          have h8 : r.val = B.R.N B.R.m - 1 := h
          omega))] at h3
        rw [if_neg hr, map_zero]
        exact h3
end GlobalTheory.Fam.TopFrames
end World
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHolds
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHolds
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.AnchorRd
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.AnchorRd
namespace GlobalTheory.CovTop
theorem anchor_holds_alt : _root_.GlobalTheory.CovTop.AnchorCondition := by
  refine Closed.imp (Closed.and _root_.GlobalTheory.CovTop.WtShape.wtN_z (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1)) ?_
  rintro eps Fm CH - ⟨⟨C1, -, hW⟩, ⟨A, -, hH⟩⟩
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hW hH
  exact ⟨100, by norm_num, x0, fun x hx hle ι p hp i =>
    AnchorRd.anchorAt_of p i (Fm.params x hx ι) ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i)⟩
end GlobalTheory.CovTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHoldsStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchor_bound : _root_.GlobalTheory.CovTop.AnchorCondition := by
  first | exact @_root_.GlobalTheory.CovTop.anchor_holds_alt | exact _root_.GlobalTheory.CovTop.anchor_holds_alt | (intros; apply _root_.GlobalTheory.CovTop.anchor_holds_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTied
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTied
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigTop.Fun
theorem gBig_atTied_alt : ∀ Q : GlobalTheory.SqTop.GP, _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.SqTop.GBig @Q → _root_.GlobalTheory.BigTop.Fun.LeafConditions (@Fitted @Comparison₂) fun p _ d C _ => Q d.G p.P.A3.A.μ0 C p.Z.x p.Z.b := by
  intro Q hS hD hG
  obtain ⟨CF0, hG⟩ := hG
  refine ⟨CF0, fun CF hCF => (hS.and hD).imp fun {eps} Fm CH he h => ?_⟩
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩ := h
  intro _
  obtain ⟨C0, x₀, hC⟩ := hG eps CF hCF
  refine ⟨C0, fun C hC0 => ⟨max x₀ (max x1 x2), fun x hx hle i p hp d hd => ?_⟩⟩
  obtain ⟨_, a, ht⟩ := hd
  have hset := h1 x hx (le_of_max_le_left (le_of_max_le_right hle)) i p hp ht.ok.eser
  have hdl := h2 x hx (le_of_max_le_right (le_of_max_le_right hle)) i p hp
  have hx0 : x₀ ≤ (Fm.L x i).sc.x := (le_of_max_le_left hle).trans (Fm.L_x x i hx).ge
  exact hC C hC0 _ (Fm.L x i) (Fm.L_eps x i) hx0 ⟨hset.size, hset.host, hset.hF, hdl⟩ _ p.R.toLevCh p.P.A3.A.μ0
    hset.core.lev d.G
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig : ∀ Q : GlobalTheory.SqTop.GP, _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.SqTop.GBig @Q → _root_.GlobalTheory.BigTop.Fun.LeafConditions (@Fitted @Comparison₂) fun p _ d C _ => Q d.G p.P.A3.A.μ0 C p.Z.x p.Z.b := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.gBig_atTied_alt | exact _root_.GlobalTheory.BigTop.Fun.gBig_atTied_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.gBig_atTied_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkFramePlaces
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkFramePlaces
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
namespace GlobalTheory.PkFrame
theorem pk_frame_places_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t → ∀ j, j < (I.rec7 l Z).R.m → (∃ N, IsSDFrame (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) N) ∧ ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW t PP hPP j hj
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.pk.bot.hyp.2.2.2.1.lev
  refine ⟨⟨_, hl.βY j hj⟩, fun PP' hPP' e => ?_⟩
  have hApart := GlobalTheory.StepLifts.places_apart _ hl t
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with hEq | hConj
  · exact Finset.disjoint_left.1 hApart.2 hPP' (hEq ▸ hPP)
  · exact hApart.1 PP' hPP' PP (Or.inr hPP) (GlobalTheory.GoodPrimes.isConjPl_iff.2 hConj)
end GlobalTheory.PkFrame
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkFramePlacesStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_pack_twist_place_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t → ∀ j, j < (I.rec7 l Z).R.m → (∃ N, IsSDFrame (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) N) ∧ ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) := by
  exact @_root_.GlobalTheory.PkFrame.pk_frame_places_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowRRowsOfParts
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.RowsParts
variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}
end GlobalTheory.Fc.RowsParts
namespace GlobalTheory.Fc
open RowsParts
theorem row_rRows_of_parts_alt : ∀ (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), Row Q Lk (fun 𝒜 σ => ∃ τ : _root_.GlobalTheory.Fc.CompatibleSelection σ, Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL3Bound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL6Bound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandFunctionalBound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ)) → Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) → Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) → Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => DR D O c b C CH) → _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition DR Q Lk := by
  intro DR Q Lk h1 h2 h3 h4
  refine (h1.and (h2.and (h3.and h4))).imp fun 𝒜 σ _ H => ?_
  obtain ⟨⟨τ, hS, hL3, hON, hL6, hFUN⟩, hM, hK, hD⟩ := H
  have hw : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm :=
    fun Fm h => (working_classes_frozen.1 𝒜 _ Fm).2.1 h
  have hall := Closed.and hS (Closed.and hL3 (Closed.and hON (Closed.and hL6 (Closed.and hFUN
    (Closed.and hM (Closed.and hK hD))))))
  refine Closed.imp (Pk.Closed.sub hall hw) fun Fm CH _ H hc => ?_
  obtain ⟨hS, hL3, hON, hL6, hFUN, hM, hK, hD⟩ := H
  have hc' := hw Fm hc
  obtain ⟨C1, p1, hS⟩ := hS hc' trivial
  obtain ⟨C2, -, hL3⟩ := hL3 hc' trivial
  obtain ⟨C3, -, hON⟩ := ev_prem (hON hc')
  obtain ⟨C4, -, hL6⟩ := hL6 hc' trivial
  obtain ⟨C5, -, hFUN⟩ := ev_prem (hFUN hc')
  obtain ⟨C6, -, hD⟩ := hD hc' trivial
  obtain ⟨C, k1, k2, k3, k4, k5, k6⟩ : ∃ C : ℝ, C1 ≤ C ∧ C2 ≤ C ∧ C3 ≤ C ∧ C4 ≤ C ∧ C5 ≤ C ∧ C6 ≤ C :=
    ⟨max C1 (max C2 (max C3 (max C4 (max C5 C6)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨x1, hS⟩ := hS C k1
  obtain ⟨x2, hL3⟩ := hL3 C k2
  obtain ⟨x3, hON⟩ := hON C k3
  obtain ⟨x4, hL6⟩ := hL6 C k4
  obtain ⟨x5, hFUN⟩ := hFUN C k5
  obtain ⟨x6, hD⟩ := hD C k6
  obtain ⟨x7, hM⟩ := hM hc'
  obtain ⟨x8, hK⟩ := hK hc'
  obtain ⟨x0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :
      ∃ y : ℝ, x1 ≤ y ∧ x2 ≤ y ∧ x3 ≤ y ∧ x4 ≤ y ∧ x5 ≤ y ∧ x6 ≤ y ∧ x7 ≤ y ∧ x8 ≤ y :=
    ⟨max x1 (max x2 (max x3 (max x4 (max x5 (max x6 (max x7 x8)))))),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨C, p1.trans k1, x0, fun x hx _ hle i => ⟨?_, hD x hx (l6.trans hle) i⟩⟩
  have s := hS x hx (l1.trans hle) i
  exact
    { w1 := s.1
      covol := hL3 x hx (l2.trans hle) i
      onto := hON x hx (l3.trans hle) i
      lamLow := fun _ => hL6 x hx (l4.trans hle) i
      seeIso := s.2.1
      miStar := hM x hx (l7.trans hle) i
      fun0 := hFUN x hx (l5.trans hle) i
      pass := s.2.2
      kap := hK x hx (l8.trans hle) i }
end GlobalTheory.Fc
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunParams
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunParams
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
noncomputable section
namespace GlobalTheory.ThetaSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem run_params_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => (dat p i).q ≤ (Fm.D x ι).R.m ∧ 0 ≤ GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ∧ lenT p i PP * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ C * unitE p ∧ ∀ DF : ℕ, 1 ≤ DF → (DF : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 → GlobalTheory.EtaAn.RunOK (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (Fm.D x ι).R.m ∧ ∀ s : ℝ, (Y.d.l₂.M : ℝ) * s < (Fm.L x ι).sc.b → Real.sqrt s < ReciprocityTheory.ChartRestriction.G.I2.th (E := (Fm.D x ι).host.E) ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) := by
  intro _
  refine (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) _root_.GlobalTheory.CovTop.WtShape.wtN_z).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨A, -, a, ha⟩, ⟨C2, -, b0, hb0⟩⟩ := hh
  refine ⟨200000, by norm_num, max a b0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hW : WtNum p i (Fm.parT x hx ι).PP := hb0 x hx ((le_max_right _ _).trans hle) ι p hp i
  have S := Fm.sizes x hx ι
  have P := Fm.params x hx ι
  have hm4 := Formalism.L2.Pj.host_m_pow_four_le_f S
  have hf2 := Formalism.L2.Pj.host_f_sq_le_rd P
  have hrd16 := Formalism.L2.Pj.host_rd_ge_sixteen P
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have ef := Formalism.L2.Pj.hostSize_f (Fm.D x ι)
  have erd := Formalism.L2.Pj.hostSize_rd (Fm.D x ι)
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hLL := hN.big.2.2.2
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have hmR : (2 : ℝ) ≤ (Fm.D x ι).R.m := by exact_mod_cast a1
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := Real.one_le_exp (by linarith)
  have hb0' : 0 < (Fm.L x ι).sc.b := Real.exp_pos _
  have hq : (1 : ℝ) ≤ (Fm.D x ι).host.q := by exact_mod_cast (Fm.D x ι).host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ (Fm.D x ι).host.d := by exact_mod_cast (Fm.D x ι).host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ (Fm.D x ι).R.n := by exact_mod_cast (Fm.D x ι).R.ord_pos
  have hqd : (1 : ℝ) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by nlinarith
  have hs : Real.sqrt (((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hrdb : (Fm.D x ι).host.rdE ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      hc.trans ((le_self_pow₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have hlogrd : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [erd]
    have := Real.log_le_log (by linarith) hrdb
    unfold Formalism.BasicNotions.Scale.b at this
    rw [Real.log_exp] at this
    linarith
  have hlfr := hN.logfr.1
  have hlf : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [ef]
    have hf0 : (0 : ℝ) < (Fm.D x ι).R.f := by linarith
    have := Real.log_le_log hf0 (le_mul_of_one_le_right hf0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.r))
    linarith
  have hlr : Real.log ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.L := by
    have hr0 : (0 : ℝ) < (Fm.D x ι).R.r := by linarith
    have := Real.log_le_log hr0 (le_mul_of_one_le_left hr0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.f))
    linarith
  have hg0 : ∀ k, (0 : ℝ) < (Fm.D x ι).host.g k := fun k => by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
  have hq1 : 1 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ((Fm.D x ι).host.g_prime 0).ne_zero ((Fm.D x ι).host.g_prime 1).ne_zero)
  have hlq : Real.log (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ 70 * (Fm.L x ι).sc.L := by
    push_cast
    rw [Real.log_mul (hg0 0).ne' (hg0 1).ne']
    linarith [hN.logg 0, hN.logg 1]
  have hP := archimedeanBoundTotalConstant_nonneg_le_bound (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m
    (Fm.L x ι).sc.L (by linarith) (by rw [ef]; omega) (by omega) (by omega) a5.2.1 hq1 (by rw [erd]; exact h1)
    hlogrd hlf hlr hlq
  rw [ef] at hP
  refine ⟨?_, hP.1, ?_, fun DF hDF hDFb => ⟨?_, ?_⟩⟩
  · rw [hW.sig.2.1]; unfold Formalism.BasicNotions.Ranks.sigW; omega
  ·
    have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have := mul_le_mul hfR hrR (by norm_num) (by linarith)
      nlinarith
    have hZ : zBase (Fm.L x ι) ^ 2 ≤ (Fm.parT x hx ι).PP :=
      (pow_le_pow_right₀ hZ1 (by norm_num)).trans hN.ppLow
    have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
      rw [hW.dim]
      have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.choose_pos (by omega)).ne')
      exact_mod_cast this
    have hT0 : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ
    have hrow := hW.what₂.2
    have hTP : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP ≤ (Fm.L x ι).sc.b := by
      revert hrow hD1 hT0 hPP0 hL10
      generalize (lenT p i (Fm.parT x hx ι).PP : ℝ) = T
      generalize (Fm.parT x hx ι).PP = PP
      generalize (dimFlag (dat p i) : ℝ) = Dd
      generalize (Fm.L x ι).sc.L = L
      generalize (Fm.L x ι).sc.b = b
      intro hrow hD1 hT0 hPP0 hL10
      have e0 : 0 ≤ PP * T := mul_nonneg hPP0 hT0
      have e1 : PP * T * 1 ≤ PP * T * Dd ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD1) e0
      have e2 : PP * T * Dd ^ 2 * 1 ≤ PP * T * Dd ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hU : (Fm.L x ι).sc.b ≤ unitE p := by
      rw [hW.unit]
      have e1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m := by nlinarith
      have e2 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x) := by
        have := mul_le_mul e1 (by linarith : (1 : ℝ) ≤ (Fm.L x ι).sc.L) zero_le_one (by linarith)
        have := mul_le_mul this hLL zero_le_one (by linarith)
        linarith
      have : (Fm.L x ι).sc.b * 1 ≤ (Fm.L x ι).sc.b *
          ((Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x)) :=
        mul_le_mul_of_nonneg_left e2 (by linarith)
      nlinarith
    have hPz : GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1)
        (Fm.D x ι).R.m 5 1 ≤ 200000 * zBase (Fm.L x ι) ^ 2 := hP.2
    calc (lenT p i (Fm.parT x hx ι).PP : ℝ) * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r
          ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1
        ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (200000 * (Fm.parT x hx ι).PP) :=
          mul_le_mul_of_nonneg_left (hPz.trans (by linarith)) hT0
      _ = 200000 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP) := by ring
      _ ≤ 200000 * unitE p := by linarith
  ·
    have hDF1 : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
    have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
    have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
      (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
    have key := size_inequality_real (Fm.D x ι).host.rdE (szCond (Fm.L x ι)) (Fm.D x ι).R.t (Fm.L x ι).sc.b (Fm.D x ι).R.f
      (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0) ((Fm.D x ι).host.g 1) h1 hc sC ht (by linarith) hft (by linarith) hrt
      hDF1 hDFb (hg 0) (hg 1)
    have hrun := GlobalTheory.RunParametersOfLower.runOK_of_le (Fm.D x ι).host.E (Fm.D x ι).R.r DF
      ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m hDF (by rw [ef]; nlinarith) (by omega) hm4 hf2 hrd16
      (by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; rw [ef, erd]; push_cast; exact key)
    rw [ef] at hrun
    exact hrun
  ·
    intro s hs
    have hR0 : (1 : ℝ) ≤ Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      have : (0 : ℝ) ≤ DF := Nat.cast_nonneg _
      nlinarith
    have hRR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E) := by
      unfold ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ (by linarith)
    have := sqrt_lt_th_real ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Y.d.l₂.M : ℝ)
      (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)))
      (ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E)) (Fm.L x ι).sc.b s hq1 hb0' (level_ge p i Y hY (by linarith))
      (by rw [ef]; linarith) hR0 hRR hs
    unfold ReciprocityTheory.ChartRestriction.G.I2.th
    exact this
end GlobalTheory.ThetaSizeBounds
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunParamsStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_bound_length_unit_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => (dat p i).q ≤ (Fm.D x ι).R.m ∧ 0 ≤ GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ∧ lenT p i PP * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ C * unitE p ∧ ∀ DF : ℕ, 1 ≤ DF → (DF : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 → GlobalTheory.EtaAn.RunOK (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (Fm.D x ι).R.m ∧ ∀ s : ℝ, (Y.d.l₂.M : ℝ) * s < (Fm.L x ι).sc.b → Real.sqrt s < ReciprocityTheory.ChartRestriction.G.I2.th (E := (Fm.D x ι).host.E) ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) := by
  first | exact @_root_.GlobalTheory.ThetaSizeBounds.run_params_alt | exact _root_.GlobalTheory.ThetaSizeBounds.run_params_alt | (intros; apply _root_.GlobalTheory.ThetaSizeBounds.run_params_alt <;> assumption)
end
end
end

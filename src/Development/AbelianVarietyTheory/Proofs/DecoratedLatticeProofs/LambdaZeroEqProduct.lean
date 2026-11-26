module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

section Red
variable {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

end Red

section Grp
variable (G : ∀ PP : d.c.Pg, GAt d τ PP.1)

end Grp

end GlobalTheory.LevelComb

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

section Comb
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}

theorem comb_single_zero (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  funext w
  simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]

end Comb

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

end GlobalTheory.LevelComb

namespace GlobalTheory.LevelComb

end GlobalTheory.LevelComb
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceWeil

theorem vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT P f) {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P) (hh : h ∈ grpOff T P) :
    Vac ψ S T LS LT P (om (g, h) f) := by
  have key : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, heisO ψ S T u f = f →
      heisO ψ S T u (om (g, h) f) = om (g, h) f := by
    intro u hu hfix
    have e := hW.om_heis g h u f hf.1
    rw [hfix, GlobalTheory.DisjComb.actO_off hg hh (GlobalTheory.FinPl.LatMem.latO_mxAt hu)] at e
    exact e.symm
  exact ⟨hW.om_pres _ f hf.1, fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2) (hf.2.1 u hu),
    fun e he u hu hh' => key u hu (hf.2.2 e he u hu hh')⟩

theorem combAt_eg {D : D7} {c : Comm D} {v : VCom c} (Gi : GLoc v) (j : ℕ) (hj : j + 1 < D.R.m) :
    CombAt (· = Gi.q.v) (Gi.eg j) := by
  have hs := Gi.hs
  intro u hu a b
  have h1 := (Gi.eg_is j (Gi.s - j) (by omega)).1 u hu a b
  obtain ⟨ε, hε, hsum⟩ := Gi.q.above
  exact ((GlobalTheory.FinPl.placeIdem_acts D Gi.q.v ε hε).1 _).2 (hsum ▸ h1)

theorem main : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → ∀ (Gi : GLoc v) (j : ℕ), j + 1 < D.R.m → ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ y ∈ grpOff (c.V (j + 1)) (· = Gi.q.v), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) (om (1, y) F) ∧ om (1, y) (comb c.ψ _ _ (Gi.eg j) F) = comb c.ψ _ _ (Gi.eg j) (om (1, y) F) := by
  intro D c v hc _ Gi j hj χS χT om hW F hF y hy
  exact ⟨vac_off hW hF (one_mem _) hy,
    (GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· = Gi.q.v) (fun _ => False) (fun _ _ h => h)).2.2.1 χS χT om hW _
      (combAt_eg Gi j hj) 1 (one_mem _) y hy F hF.1⟩

end GlobalTheory.OffPlaceWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → ∀ (Gi : GLoc v) (j : ℕ), j + 1 < D.R.m → ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ y ∈ grpOff (c.V (j + 1)) (· = Gi.q.v), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) (om (1, y) F) ∧ om (1, y) (comb c.ψ _ _ (Gi.eg j) F) = comb c.ψ _ _ (Gi.eg j) (om (1, y) F) := by
  first | exact @GlobalTheory.OffPlaceWeil.main | exact GlobalTheory.OffPlaceWeil.main | (intros; apply GlobalTheory.OffPlaceWeil.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPattern
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.SymRes

theorem exists_red_iff_isPat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] (I : Ideal O) (π : O →+* k) (h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk I) π)
    {s κ r : ℕ} (hr : r = κ + (s + 1)) (S : GlobalTheory.SymChain.SymData k s κ) (g : GL (Fin r) (O ⧸ I)) :
    (∃ x : S.P.J, ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
      b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O, Ideal.Quotient.mk I z = g.val a' b' →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - π z) < 1) ↔ IsPat S.ρ κ g := by
  subst hr
  let e : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hfree : ∀ a b, FreePos S.ρ κ (e a).val (e b).val ↔ GlobalTheory.SymChain.FreeTop S.ρ a b := by
    intro a b
    rw [he, he]
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl, Sum.elim_inr, GlobalTheory.SymChain.FreeTop, FreePos, Fin.lt_def] <;>
      have := a.2 <;> have := b.2 <;> omega
  choose l hl using fun a b => Ideal.Quotient.mk_surjective (I := I) (g.val (e a) (e b))
  have key : ∀ a b, g.val (e a) (e b) = (1 : Matrix _ _ (O ⧸ I)) (e a) (e b) ↔
      valuation k (π (l a b) - (1 : Matrix _ _ k) a b) < 1 := by
    intro a b
    have h4 := h.ker (l a b - if a = b then 1 else 0)
    rw [map_sub, map_sub, sub_eq_zero, apply_ite (Ideal.Quotient.mk I), apply_ite π, map_one, map_one, map_zero,
      map_zero, hl] at h4
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [e.apply_eq_iff_eq]
    convert h4
  constructor
  · rintro ⟨x, hx⟩ i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have h1 := hx a b _ _ (he a) (he b) _ (hl a b)
    have h2 := ((GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x.1).1 x.2).2 a b (fun h' => hij ((hfree a b).2 h'))
    have h3 := (valuation k).map_sub_lt h2 h1
    rw [sub_sub_sub_cancel_left] at h3
    exact (key a b).2 h3
  · intro hg
    have hM : (Matrix.of l).map (Ideal.Quotient.mk I) = g.val.submatrix e e := Matrix.ext hl
    have hu : IsUnit ((Matrix.of l).map (Ideal.Quotient.mk I)).det := by
      rw [hM, det_submatrix_equiv_self]
      convert (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    obtain ⟨x, hx1, hx2⟩ := (h.isUnit_det_iff _).1 hu
    have hx3 : ∀ a b, x.val a b = π (l a b) := fun a b => congrFun (congrFun hx2 a) b
    refine ⟨⟨x, (GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x).2 ⟨by convert hx1, fun a b hab => ?_⟩⟩, ?_⟩
    · rw [hx3]
      exact (key a b).1 (hg _ _ fun h' => hab ((hfree a b).1 h'))
    · intro a b a' b' ha hb z hz
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      change valuation k (x.val a b - π z) < 1
      rw [hx3, ← map_sub, ← h.ker, map_sub, hl, hz, sub_self]

end GlobalTheory.SymRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GSuppComb

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [List.erase_cons, ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

theorem comb_eq_at_place : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j : ℕ), j + 1 < D.R.m → ∀ (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ → ∀ (i : Fin n), ∃ F, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) F ∧ comb c.ψ _ _ (v.eG j) Ψ = comb c.ψ _ _ ((G i).eg j) F := by
  intro D c v n hc hv G hG j hj Ψ hΨ i
  have hI := GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1))
  have hca : ∀ i', CombAt (· = (G i').q.v) ((G i').eg j) := fun i' =>
    eg_combAt (G i') j (by have := (G i').hs; omega)
  have hdisj : ∀ a b : Fin n, a ≠ b → ∀ p, p = (G a).q.v → ¬ p = (G b).q.v := fun a b hab p ha hb =>
    hab (hG.inj (ha.symm.trans hb))
  let g : Fin n → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((G a).eg j) f
  refine ⟨((List.finRange n).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) Ψ :=
      vac_mono (fun p hp => by rw [hp]; exact (hG.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin n), (∀ a ∈ l, a ≠ i) → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a t ih =>
        intro hl
        exact ((hI (· = (G a).q.v) (· = (G i).q.v) (hdisj a i (hl a (List.mem_cons_self ..)))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange n).mem_erase_iff.1 ha).1
  · rw [hG.eG j hj Ψ hΨ.1]
    exact foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ (List.mem_finRange i)

end GlobalTheory.GSuppComb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j : ℕ), j + 1 < D.R.m → ∀ (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ → ∀ (i : Fin n), ∃ F, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) F ∧ comb c.ψ _ _ (v.eG j) Ψ = comb c.ψ _ _ ((G i).eg j) F := by
  first | exact @GlobalTheory.GSuppComb.comb_eq_at_place | exact GlobalTheory.GSuppComb.comb_eq_at_place | (intros; apply GlobalTheory.GSuppComb.comb_eq_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharConjFixed

theorem nontrivial_AF (D : D7) : Nontrivial (AF D.host.F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem finrank_AE (D : D7) : Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI := nontrivial_AF D
  rw [Module.finrank_baseChange]; exact D.sp.cm.deg2

theorem cA_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl


set_option synthInstance.maxHeartbeats 200000 in
theorem trace_mem (D : D7) (y : AE D) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y + cA D y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), hu, hv, map_add (f := _)]; abel
  | tmul a e =>
    have hfix : star (e + star e) = e + star e := by
      rw [star_add, star_star, add_comm]
    obtain ⟨f, hf⟩ := (D.sp.cm.fixed _).1 hfix
    refine ⟨f • a, ?_⟩
    rw [cA_tmul, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one (A := D.host.E) f,
      ← TensorProduct.smul_tmul]
    rfl

theorem fixed_mem (D : D7) (y : AE D) (hy : cA D y = y) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y := by
  obtain ⟨b, hb⟩ := trace_mem D y
  refine ⟨algebraMap D.host.F (AF D.host.F) (2⁻¹) * b, ?_⟩
  have h2 : algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (2⁻¹)) * 2 = 1 := by
    rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) 2) by rw [map_ofNat, map_ofNat],
      ← map_mul, ← map_mul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), map_one, map_one]
  rw [map_mul, hb, hy, ← two_mul, ← mul_assoc, h2, one_mul]

theorem norm_scalar (D : D7) (b : AF D.host.F) :
    Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) b) = b ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_AE]

theorem fixed_unit (D : D7) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    ∃ a : (AF D.host.F)ˣ, idF D a = x := by
  obtain ⟨b, hb⟩ := fixed_mem D x hx
  have hn : IsUnit (Algebra.norm (AF D.host.F) (x : AE D)) := x.isUnit.map _
  rw [← hb, norm_scalar] at hn
  obtain ⟨a, ha⟩ := (isUnit_pow_iff two_ne_zero).1 hn
  refine ⟨a, Units.ext ?_⟩
  rw [← hb, ← ha]; rfl

end GlobalTheory.CharConjFixed


open GlobalTheory.CharConjFixed in
theorem GlobalTheory.char_conj_fixed_eq_one : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n →
    ∀ (V : HSp D) (x : (AE D)ˣ), IsDetRoot V 1 x → μ x = 1 := by
  intro D μ n hμ hn V x hx
  have hfix : cA D (x : AE D) = x := by
    have h := hx
    simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at h
    exact h.symm
  obtain ⟨a, ha⟩ := fixed_unit D x hfix
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  have hμa : μ (idF D a) = η a ^ n := hall η hη a
  have hsq : η a ^ 2 = 1 := by
    rw [← map_pow]
    have : Units.map (↑(Algebra.norm (AF D.host.F)) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
      ext
      exact norm_scalar D (a : AF D.host.F)
    rw [← this]; exact hη.2.2.1 _
  obtain ⟨k, rfl⟩ := hn
  rw [← ha, hμa, ← two_mul, pow_mul, hsq, one_pow]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_eq_one_of_isDetRoot_of_even : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ), IsDetRoot V 1 x → μ x = 1 := by
  first | exact @GlobalTheory.char_conj_fixed_eq_one | exact GlobalTheory.char_conj_fixed_eq_one | (intros; apply GlobalTheory.char_conj_fixed_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFun
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFun
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.ThetaPin

variable {D : D7}

theorem isFinComb_of_half {S T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (c : WO S T →₀ ℂ)
    (hc : ∀ u ∈ c.support, IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) : IsFinComb c := by
  intro u hu
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    obtain ⟨α, rfl, -, -⟩ := hε
    show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hc u hu i j, map_mul, h0, zero_mul]

theorem aconv_support {G : Type} [AddMonoid G] (P : AddSubmonoid G) :
    ∀ (l : List (G →₀ ℂ)), (∀ e ∈ l, ∀ g ∈ e.support, g ∈ P) → ∀ g ∈ (aconv l).support, g ∈ P
  | [], _, g, hg => by
    have : g = 0 := by
      simpa [aconv] using Finsupp.support_single_subset hg
    rw [this]; exact P.zero_mem
  | e :: l, hl, g, hg => by
    classical
    have ih := aconv_support P l (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    have he := hl e List.mem_cons_self
    change g ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support at hg
    have houter : g ∈ e.support.biUnion
        (fun x => ((aconv l).sum fun y b => Finsupp.single (x + y) (e x * b)).support) :=
      Finsupp.support_sum (f := e)
        (g := fun x a => (aconv l).sum fun y b => Finsupp.single (x + y) (a * b)) hg
    rcases Finset.mem_biUnion.mp houter with ⟨x, hx, hg⟩
    have hinner : g ∈ (aconv l).support.biUnion
        (fun y => (Finsupp.single (x + y) (e x * aconv l y)).support) :=
      Finsupp.support_sum (f := aconv l) (g := fun y b => Finsupp.single (x + y) (e x * b)) hg
    rcases Finset.mem_biUnion.mp hinner with ⟨y, hy, hg⟩
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
    exact P.add_mem (he x hx) (ih y hy)

def finSub (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | u.map (infPart D) = 0}
  zero_mem' := by ext i j; simp
  add_mem' {a b} ha hb := by
    change Matrix.map a (infPart D) = 0 at ha
    change Matrix.map b (infPart D) = 0 at hb
    change Matrix.map (a + b) (infPart D) = 0
    rw [Matrix.map_add (infPart D) (fun x y => RingHom.map_add (infPart D) x y) a b, ha, hb, add_zero]

theorem isFinComb_aconv {S T : HSp D} (l : List (WO S T →₀ ℂ)) (hl : ∀ e ∈ l, IsFinComb e) : IsFinComb (aconv l) :=
  aconv_support (finSub S T) l hl

theorem isFinComb_cast {c : Comm D} {a b : ℕ} (e : a = b) (x : WO (c.V (a + 1)) c.T →₀ ℂ) (hx : IsFinComb x) :
    IsFinComb (e ▸ x : WO (c.V (b + 1)) c.T →₀ ℂ) := by
  subst e; exact hx

end GlobalTheory.QPl.ThetaPin

open GlobalTheory.QPl.ThetaPin in
theorem GlobalTheory.QPl.pins_keep_theta : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) Ψ₁) ∧ IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQT j h) Ψ₂) := by
  intro D c v t w F hc hP j h Ψ₁ Ψ₂ h1 h2
  have hs : ∀ i, (F.Q i).s = j := fun i => by have := (F.Q i).hs; omega
  refine ⟨?_, ?_⟩
  · rw [hP.eQ j (by omega)]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h1 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := ((F.Q i).eL_at j 0 (by have := hs i; omega)).1
    exact isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu
  · rw [hP.eQT j h]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h2 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := (F.Q i).eLT_at.1
    unfold QAt.eT
    exact isFinComb_cast _ _ (isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFunStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_normalisedCombinations_preserve_thetaFunctions : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) Ψ₁) ∧ IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQT j h) Ψ₂) := by
  first | exact @GlobalTheory.QPl.pins_keep_theta | exact GlobalTheory.QPl.pins_keep_theta | (intros; apply GlobalTheory.QPl.pins_keep_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModel
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocModMove

theorem placeIdem_mul_eq_zero {D : D7} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε) (a : AE D)
    (ha : a ∈ GlobalTheory.FinPl.idOff D (· = v)) : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := GlobalTheory.FinPl.placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hav : GlobalTheory.FinPl.compAt D v a = 0 := by
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha
    exact ha v rfl
  apply GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · subst h; rw [hav, mul_zero]
    · rw [hc w, hw w h, TensorProduct.zero_tmul, zero_mul]

theorem ent_of_mem_grpOff {D : D7} {V : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V P) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D P := by
  have hker := MonoidHom.mem_ker.1 hg
  intro i j
  rw [← Ideal.Quotient.eq]
  have h2 := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P) => u.1 i j) hker
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
  have h3 : Ideal.Quotient.mk (GlobalTheory.FinPl.idOff D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P)) i j := by
    by_cases hij : i = j
    · subst hij; simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h3, ← h2]
  rfl

theorem mul_mul_eq_self {D : D7} {m n : ℕ} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (A : Matrix (Fin m) (Fin m) (AE D)) (B : Matrix (Fin n) (Fin n) (AE D)) (y : Matrix (Fin m) (Fin n) (AE D))
    (hA : ∀ i j, A i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hB : ∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hy : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * y i j = y i j) : HMul.hMul (HMul.hMul A y) B = y := by
  have kill : ∀ a ∈ GlobalTheory.FinPl.idOff D (· = v), ∀ b : AE D, b = algebraMap (AF D.host.F) (AE D) ε * b → a * b = 0 := by
    intro a ha b hb
    rw [hb, ← mul_assoc, mul_comm a, placeIdem_mul_eq_zero v ε hε a ha, zero_mul]
  have h1 : HMul.hMul (A - 1) y = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply]
    exact kill _ (hA i l) _ (hy l j).symm
  have h2 : HMul.hMul y (B - 1) = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply, mul_comm]
    exact kill _ (hB l j) _ (hy i l).symm
  have e1 : HMul.hMul A y = y := by
    rw [← sub_eq_zero, ← h1, Matrix.sub_mul, Matrix.one_mul]
  have e2 : HMul.hMul y B = y := by
    rw [← sub_eq_zero, ← h2, Matrix.mul_sub, Matrix.mul_one]
  rw [e1, e2]

theorem actO_eq_self {D : D7} {V W : HSp D} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = v)) {h : GA D W} (hh : h ∈ GlobalTheory.FinPl.grpOff W (· = v))
    (y : WO V W) (hy : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y) : actO V W g h y = y := by
  unfold actO
  exact mul_mul_eq_self v ε hε _ _ _ (ent_of_mem_grpOff hh)
    (ent_of_mem_grpOff ((GlobalTheory.FinPl.grpOff V (· = v)).inv_mem hg)) hy

theorem isModel_weil_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (ω : Om V W), IsWeilDatumO ψ V W χV χW ω →
  ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FV : Frame k V.rank Y') (FW : Frame k W.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO V W → ℂ)), (ofSplit q).IsModel ψ FV FW Tm →
  ∀ g ∈ GlobalTheory.FinPl.grpOff V (· = q.v), ∀ h ∈ GlobalTheory.FinPl.grpOff W (· = q.v), (ofSplit q).IsModel ψ FV FW ((ω (g, h)) ∘ₗ Tm) := by
  intro D k _ _ _ _ q ψ hψ V W χV χW ω hω Y Y' _ _ _ _ FV FW Tm hM g hg h hh
  obtain ⟨ε, hεv, hsum⟩ := q.above
  refine (GlobalTheory.LocModU.localModel_uniq_transport_exist D k (ofSplit q) Y Y' V W FV FW ψ hψ).2.1 Tm hM (ω (g, h))
    (fun f hf => hω.om_pres _ f hf) (fun f hf y hy => ?_)
  have hy' : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y := by
    rw [← hsum]; exact hy
  rw [hω.om_heis g h y f hf, actO_eq_self q.v ε hεv hg hh y hy']

end GlobalTheory.LocModMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_weil_operator_trivialAtPlace_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (ω : Om V W), IsWeilDatumO ψ V W χV χW ω →
  ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FV : Frame k V.rank Y') (FW : Frame k W.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO V W → ℂ)), (ofSplit q).IsModel ψ FV FW Tm →
  ∀ g ∈ GlobalTheory.FinPl.grpOff V (· = q.v), ∀ h ∈ GlobalTheory.FinPl.grpOff W (· = q.v), (ofSplit q).IsModel ψ FV FW ((ω (g, h)) ∘ₗ Tm) := by
  first | exact @GlobalTheory.LocModMove.isModel_weil_off | exact GlobalTheory.LocModMove.isModel_weil_off | (intros; apply GlobalTheory.LocModMove.isModel_weil_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw

variable {D : D7}

theorem finM_rfl (V : HSp D) (g : GA D V) : finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  simp [finM]

theorem infM_eq (θ : InfFam D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V rfl g τ = (Formalism.L2.Theta.mt V g).map ((θ τ).comp (infPart D)) := by
  simp [infM, Formalism.IndefR.Datum.compAt]; rfl

theorem infM_rfl (θ : InfFam D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V rfl g τ = infMat D.sp.cm.sig V.gram (θ τ) g := by
  rw [infM_eq]; rfl

theorem mt_mul (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem finM_mul (V : HSp D) (g h : GA D V) : finM V rfl (g * h) = finM V rfl g * finM V rfl h := by
  simp only [finM_rfl, mt_mul, Matrix.map_mul]

theorem infM_mul (θ : InfFam D) (V : HSp D) (g h : GA D V) (τ) :
    infM θ V rfl (g * h) τ = infM θ V rfl g τ * infM θ V rfl h τ := by
  simp only [infM_eq, mt_mul, Matrix.map_mul]

theorem infM_fin (θ : InfFam D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) (τ) : infM θ V rfl k τ = 1 := by
  have h : (infHom V k) = 1 := hk
  have h2 : (infHom V k).val = 1 := by rw [h]; rfl
  rw [infM_eq]
  have e : (Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)) = (infHom V k).val.map (θ τ) := rfl
  rw [e, h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finM_inf (V : HSp D) (k : GA D V) (hk : k ∈ GinfC V) : finM V rfl k = 1 := by
  have h : (finHom V k) = 1 := hk
  have h2 : (finHom V k).val = 1 := by rw [h]; rfl
  rw [finM_rfl]
  have e : (Formalism.L2.Theta.mt V k).map (toEAf D) = (finHom V k).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e, h2, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem rat_mt (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ γ0 : GL (Fin V.rank) D.host.E, γ0 ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
      Formalism.L2.Theta.mt V γ = γ0.val.map (incA D) := by
  have h : matHom V γ ∈ HFin (AF D.host.F) D.sp.cm.sig V.gram := hγ
  obtain ⟨γ0, h0, e⟩ := Subgroup.mem_map.1 h
  refine ⟨γ0, h0, ?_⟩
  show (matHom V γ).val = _
  rw [← e]; rfl

theorem rat_finM (V : HSp D) (γ0 : GL (Fin V.rank) D.host.E) (γ : GA D V) (e : Formalism.L2.Theta.mt V γ = γ0.val.map (incA D)) :
    finM V rfl γ = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0).val := by
  rw [finM_rfl, e, Matrix.map_map]; rfl

theorem rat_infM (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (γ0 : GL (Fin V.rank) D.host.E) (γ : GA D V)
    (e : Formalism.L2.Theta.mt V γ = γ0.val.map (incA D)) (τ) :
    infM θ V rfl γ τ = atInf (embT D) γ0.val τ := by
  rw [infM_eq, e, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, atInf, Function.comp_apply, RingHom.coe_comp]
  exact (hθ τ).1 _

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

def e0 (D : D7) : AF D.host.F := ((0, 1) : Ainf D.host.F × Af D.host.F)

theorem finiteAdeleIdempotentOfF_mul_self : e0 D * e0 D = e0 D := Prod.ext (zero_mul _) (one_mul _)

def eps (D : D7) : AE D := e0 D ⊗ₜ[D.host.F] (1 : D.host.E)

theorem eps_mul_self : eps D * eps D = eps D := by
  rw [eps, Algebra.TensorProduct.tmul_mul_tmul, mul_one, finiteAdeleIdempotentOfF_mul_self]

theorem eps_mul_one_sub : eps D * (1 - eps D) = 0 := by
  rw [mul_sub, mul_one, eps_mul_self, sub_self]

theorem one_sub_mul_self : (1 - eps D) * (1 - eps D) = 1 - eps D := by
  rw [sub_mul, one_mul, mul_sub, mul_one, eps_mul_self]; abel

theorem sig_eps : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (eps D) = eps D := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig (_ ⊗ₜ _) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem infPart_eps : infPart D (eps D) = 0 := by
  have h1 : infPart D (eps D) = fstA D.host.F (e0 D) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  have : fstA D.host.F (e0 D) = 0 := rfl
  rw [h1, this, TensorProduct.zero_tmul]

set_option synthInstance.maxHeartbeats 400000 in
theorem finPart_eps : finPart D (eps D) = 1 := by
  have h1 : finPart D (eps D) = sndA D.host.F (e0 D) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  have : sndA D.host.F (e0 D) = 1 := rfl
  rw [h1, this]; rfl

theorem toEAf_eps : toEAf D (eps D) = 1 := by
  show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D (eps D)) = 1
  rw [finPart_eps, map_one]

def PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) : Matrix (Fin r) (Fin r) (AE D) :=
  eps D • M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D))

theorem PM_mul {r : ℕ} (M N : Matrix (Fin r) (Fin r) (AE D)) : PM (M * N) = PM M * PM N := by
  simp only [PM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add]

theorem PM_one {r : ℕ} : PM (1 : Matrix (Fin r) (Fin r) (AE D)) = 1 := by
  simp only [PM, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.AdForm.RdLaw
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenFix
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.OneComb

theorem exists_open_fix' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Y : Type} [Fintype Y] [DecidableEq Y]
    (L : Level (GL Y k)) (hL : IsOpen (L.J : Set (GL Y k))) (α : GL Y k) :
    ∃ U : Subgroup (GL Y k), IsOpen (U : Set (GL Y k)) ∧ ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL Y k) A),
      IsSmoothRep σ → ∀ v : A, (∀ j : L.J, σ (j : GL Y k) v = (L.lam j : ℂ) • v) → ∀ u ∈ U, σ u (σ α v) = σ α v := by
  by_cases h : IsOpen ((L.lam.ker.map L.J.subtype : Subgroup (GL Y k)) : Set (GL Y k))
  · refine ⟨(L.lam.ker.map L.J.subtype).comap (MulAut.conj α⁻¹).toMonoidHom,
      h.preimage ((continuous_const.mul continuous_id).mul continuous_const), fun A _ _ σ _ v hv u hu => ?_⟩
    obtain ⟨j, hj, e⟩ := hu
    have e' : u * α = α * j := by
      have e2 : (j : GL Y k) = α⁻¹ * u * α⁻¹⁻¹ := e
      simp [e2, mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply, hv, show L.lam j = 1 from hj, Units.val_one, one_smul]
  · refine ⟨⊤, isOpen_univ, fun A _ _ σ hσ v hv u _ => ?_⟩
    obtain rfl : v = 0 := by
      by_contra v0
      refine h (Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((hL.inter (hσ v)).mem_nhds ⟨L.J.one_mem, by simp⟩) fun g hg => ⟨⟨g, hg.1⟩, Units.ext ?_, rfl⟩))
      exact smul_left_injective ℂ v0 (((hv ⟨g, hg.1⟩).symm.trans hg.2).trans (one_smul ℂ v).symm)
    simp

theorem exists_isOneComb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), IsCO L.J → ∀ α, ∃ e, IsOneComb ψ ν P L α e := by
  intro k _ _ _ _ _ _ n _ _ c P h1 hP ψ hψc hψ1 ν hν L hL α
  obtain ⟨U, hU, h⟩ := exists_open_fix' L hL.1 α
  obtain ⟨e, e', he⟩ := GlobalTheory.T.exchangeToPositionOne_uniform_in_level k n c P h1 hP ψ hψc hψ1 ν hν U hU
  refine ⟨e.mapDomain (· * α), fun A _ _ σ hσ l hl v hv => ?_⟩
  rw [(he A σ hσ l _ hl (h A σ hσ v hv)).1, GlobalTheory.PosOne.comb, GlobalTheory.PosOne.comb,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_mul _ _ _)]
  simp only [map_mul, Module.End.mul_apply]

end GlobalTheory.QPl.OneComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.FinComm

theorem finite_comm_creation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsHol θ S T ψ f → IsHol θ S T ψ (om (g, h) f) ∧ ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) ∧ om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (om (g, h) f) P := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hom g hg h hh f hf
  have hθ : IsInfFam θ := hP.inf
  have hg' : g⁻¹ ∈ GfC S := inv_mem hg
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ z hf.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg', Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨hom.om_pres _ f hf.1, fun τ z => ?_⟩, fun P => ⟨?_, ?_⟩⟩
  · have h0 := hf.2 τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]
  · refine (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) g h ?_ ?_ ?_ ?_ f hf.1 P).1 <;> intro τ
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg, Matrix.one_mul]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh, Matrix.one_mul]
  · exact GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ S T μ μ om hom θ hθ g hg h hh _ _ _ _ f P hf.1

end GlobalTheory.AdForm.FinComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.om_pureTensorO_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsHol θ S T ψ f → IsHol θ S T ψ (om (g, h) f) ∧ ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) ∧ om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (om (g, h) f) P := by
  first | exact @GlobalTheory.AdForm.FinComm.finite_comm_creation | exact GlobalTheory.AdForm.FinComm.finite_comm_creation | (intros; apply GlobalTheory.AdForm.FinComm.finite_comm_creation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordinateWeilTranslateCompactMajorant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordinateWeilTranslateCompactMajorant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section

namespace GlobalTheory.Unf

theorem mixS_om_compact_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  intro D ψ S T χS χT om hω θ hθ S₀ ρ d v f hf Kp hKp
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact D ψ S T χS χT om hω f hf Kp hKp
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.T.mixedCoordinate_thetaFun_le_schwartz_majorant_level D ψ hω.std θ hθ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hKN N
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hω θ hθ N
  obtain ⟨c, hc⟩ := hA f hf
  have hcont : Continuous fun p : GA D S × GA D T =>
      c * (GlobalTheory.Grow.height S p.1 * GlobalTheory.Grow.height T p.2) ^ A :=
    continuous_const.mul ((((GlobalTheory.Grow.continuous_height S).comp continuous_fst).mul
      ((GlobalTheory.Grow.continuous_height T).comp continuous_snd)).pow A)
  obtain ⟨B, hB⟩ := hKp.bddAbove_image hcont.continuousOn
  refine ⟨(C : ℝ) * max B 0, fun p hp x w => ?_⟩
  have h1 := hC (om p f) (hUK p hp) x w
  have h2 : supSob ψ θ N (om p f) ≤ ENNReal.ofReal (max B 0) :=
    (hc p.1 p.2).trans (ENNReal.ofReal_le_ofReal ((hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)))
  have hm := maj_nonneg θ K N x
  have h3 : ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * max B 0 * maj θ K N x) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    gcongr
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordinateWeilTranslateCompactMajorantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittMixedCoordinate_weilTranslate_compact_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  first | exact @GlobalTheory.Unf.mixS_om_compact_maj | exact GlobalTheory.Unf.mixS_om_compact_maj | (intros; apply GlobalTheory.Unf.mixS_om_compact_maj <;> assumption)
end
end

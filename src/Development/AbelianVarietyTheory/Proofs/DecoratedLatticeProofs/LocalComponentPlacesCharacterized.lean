module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLattices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRebase

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem zero_placeModel {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 0 0 := by
  refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, ?_⟩
  · funext w; simp [heisO]
  · funext w; simp [heisO]
  · simp

theorem local_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (p : GlobalTheory.FinPl.Pl D)
    (hsp : ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (hu1 : ∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧
      incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p))
    (hu2 : ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) :
    ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧ (f ≠ 0 → comb ψ S T c f ≠ 0) := by
  obtain ⟨e, ε, he, hε, hs⟩ := hsp
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D p e ε he hε hs
  have hU : q.UnitAA := by
    unfold GlobalTheory.FinPl.SplitPt.UnitAA
    rw [hq]
    exact ⟨hu1, hu2⟩
  rw [← hq]
  obtain ⟨glS, hS1, hS2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q S (Fin S.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  obtain ⟨glT, hT1, hT2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q T (Fin T.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  let α : GlobalTheory.FinPl.Frame q S (Fin S.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T (Fin T.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glT, hT1, hT2⟩
  obtain ⟨ΛS, hl1, hαN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α N hN
  obtain ⟨ΛT, hl2, hβN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β N' hN'
  obtain ⟨ΛSm, hl3, hαM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α M hM
  obtain ⟨ΛTm, hl4, hβM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β M' hM'
  haveI : ΛS.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual α N hN ΛS hαN
  haveI : ΛT.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β N' hN' ΛT hβN
  haveI : ΛSm.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual α M hM ΛSm hαM
  haveI : ΛTm.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β M' hM' ΛTm hβM
  have R := GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D _ q (Fin T.rank) (Fin S.rank) ψ hψ hU S T α β M N M' N' hM hM' hN hN'
  obtain ⟨c, hc, hov⟩ := R.2 (GlobalTheory.LatPair.latInd ΛS ΛT) (GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT)
  refine ⟨c, hc, fun f hf => ?_⟩
  have hO := hov f hf
  have h1 := R.1 ΛS ΛT hαN hβN f _ hO
  refine ⟨h1.1, fun hf0 hg => hf0 ?_⟩
  obtain ⟨⟨Tm, hTm⟩, -⟩ := hO.2.2.2.2
  have hOf : GlobalTheory.FinPl.Over ψ α β M M' f (GlobalTheory.LatPair.latInd ΛSm ΛTm) f := by
    refine ⟨hM, hM', hf, GlobalTheory.LatPair.latInd_mem_SB _ _, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
    rw [GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D _ q _ _ S T α β M M' hM hM' hU ΛSm ΛTm hαM hβM]
    have hv := hT'.vac
    rw [one_smul] at hv
    exact hv.symm
  have hN0 := h1.2 _ _ hOf
  rw [hg] at hN0
  have := hN0.2.2.2.2.2 0 (zero_placeModel ψ S T _ _)
  simpa using this

end GlobalTheory.VacRebase

namespace GlobalTheory.VacRebase

theorem idAt_mono' {D : D7} {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → P' v) :
    GlobalTheory.FinPl.idAt D P ≤ GlobalTheory.FinPl.idAt D P' := by
  unfold GlobalTheory.FinPl.idAt
  exact inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hp => w.2 (h _ hp)⟩ le_rfl)

theorem foldr_vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) (X : GlobalTheory.FinPl.Pl D → Prop) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p)) → (∀ p ∈ l, ¬ X p) → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T LS LT X f → GlobalTheory.FinPl.Vac ψ S T LS LT X (l.foldr (fun p g => comb ψ S T (c p) g) f) := by
  intro l
  induction l with
  | nil => intro _ _ f hf; exact hf
  | cons p l ih =>
    intro hc hX f hf
    rw [List.foldr_cons]
    have hd : ∀ x, x = p → ¬ X x := fun x hx => hx ▸ hX p List.mem_cons_self
    exact ((GlobalTheory.DisjComb.main D ψ hψ S T (· = p) X hd).2.1 (c p) (hc p List.mem_cons_self)).2 LS LT _
      (ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) (fun x hx => hX x (List.mem_cons_of_mem _ hx)) f hf)

theorem foldr_vac_on {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), l.Nodup → (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p) ∧ ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T (c p) f) ∧
        (f ≠ 0 → comb ψ S T (c p) f ≠ 0)) → ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ l) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ l) (l.foldr (fun p g => comb ψ S T (c p) g) f) ∧
        (f ≠ 0 → l.foldr (fun p g => comb ψ S T (c p) g) f ≠ 0) := by
  intro l
  induction l with
  | nil =>
    intro _ _ f hf
    refine ⟨⟨hf.1, ?_⟩, fun h => h⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => absurd hx List.not_mem_nil)]
    exact hf.2
  | cons p l ih =>
    intro hnd hc f hf
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have hd : ∀ x, x = p → ¬ x ∈ l := fun x hx => hx ▸ hpl
    have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· = p) (· ∈ l) hd
    have hfun : (fun x => x ∈ p :: l) = fun x => x = p ∨ x ∈ l := by
      funext x; exact propext List.mem_cons
    rw [hfun] at hf ⊢
    have hf2 := (DC.2.2.2.2 M M' f hM hM').1 hf
    obtain ⟨ihv, ihn⟩ := ih (List.nodup_cons.1 hnd).2 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) f hf2.2
    have hgp := foldr_vac_off hψ c (· = p) M M' l (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).1)
      (fun x hx hxp => hpl (hxp ▸ hx)) f hf2.1
    obtain ⟨hcp, hloc⟩ := hc p List.mem_cons_self
    obtain ⟨hv1, hn1⟩ := hloc _ hgp
    rw [List.foldr_cons]
    refine ⟨(DC.2.2.2.2 N N' _ hN hN').2 ⟨hv1, (DC.2.1 (c p) hcp).2 N N' _ ihv⟩, fun h0 => hn1 (ihn h0)⟩

end GlobalTheory.VacRebase

theorem GlobalTheory.VacRebase.rebase_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  intro D ψ hψ S T M N M' N' Q hM hN hM' hN' hQ hoff
  have hc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ (p ∈ Q → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧
        (f ≠ 0 → comb ψ S T c f ≠ 0)) := by
    intro p
    by_cases hp : p ∈ Q
    · obtain ⟨h1, h2, h3⟩ := hQ p hp
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.VacRebase.local_step hψ hM hN hM' hN' p h1 h2 h3
      exact ⟨c, hc1, fun _ => hc2⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hp⟩
  choose c hc1 hc2 using hc
  let l := Q.toList
  have hmem : ∀ p, p ∈ l ↔ p ∈ Q := fun p => Finset.mem_toList
  refine ⟨convList ψ S T (l.map c), ?_, fun f hf => ?_⟩
  · refine support_convList (p := GlobalTheory.FinPl.MxAt (· ∈ Q)) (fun i j => Ideal.zero_mem _)
      (fun x y hx hy i j => by rw [Matrix.add_apply]; exact Ideal.add_mem _ (hx i j) (hy i j)) ?_
    intro c' hc' x hx i j
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'
    exact GlobalTheory.VacRebase.idAt_mono' (fun v hv => hv ▸ (hmem p).1 hp) (hc1 p x hx i j)
  rw [comb_convList]
  have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· ∈ l) (· ∉ l) (fun x h1 h2 => h2 h1)
  have hfun : (fun x => x ∈ l ∨ x ∉ l) = fun _ => True := by
    funext x; exact propext ⟨fun _ => trivial, fun _ => em _⟩
  have hf' : GlobalTheory.FinPl.Vac ψ S T M M' (fun x => x ∈ l ∨ x ∉ l) f := by rw [hfun]; exact hf
  obtain ⟨hin, hout⟩ := (DC.2.2.2.2 M M' f hM hM').1 hf'
  obtain ⟨v1, n1⟩ := GlobalTheory.VacRebase.foldr_vac_on hψ hM hN hM' hN' c l (Finset.nodup_toList Q)
    (fun p hp => ⟨hc1 p, hc2 p ((hmem p).1 hp)⟩) f hin
  have hout' : GlobalTheory.FinPl.Vac ψ S T N N' (· ∉ l) f := by
    refine ⟨hout.1, ?_⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => by
      obtain ⟨a, b⟩ := hoff x (fun h => hx ((hmem x).2 h)); exact ⟨a.symm, b.symm⟩)]
    exact hout.2
  have v2 := GlobalTheory.VacRebase.foldr_vac_off hψ c (· ∉ l) N N' l (fun p _ => hc1 p) (fun p hp h => h hp) f hout'
  refine ⟨?_, n1⟩
  rw [← hfun]
  exact (DC.2.2.2.2 N N' _ hN hN').2 ⟨v1, v2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  first | exact @GlobalTheory.VacRebase.rebase_vac | exact GlobalTheory.VacRebase.rebase_vac | (intros; apply GlobalTheory.VacRebase.rebase_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentPlacesCharacterized
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommonVac

theorem latV_eq_of_moves {D : D7} {S : HSp D} {g : GA D S} {Λ M N : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : GlobalTheory.FinPl.Moves S g Λ M P) (hN : GlobalTheory.FinPl.Moves S g Λ N P) :
    GlobalTheory.FinPl.latV S M P = GlobalTheory.FinPl.latV S N P := by
  have h1 : GlobalTheory.FinPl.Moves S (g * g⁻¹) M N P := GlobalTheory.StMoves.moves_mul (GlobalTheory.StMoves.moves_inv hM) hN
  rw [mul_inv_cancel] at h1
  have e1 : ∀ y : Fin S.rank → AE D, mt S (1 : GA D S) *ᵥ y = y := fun y => by
    rw [show mt S (1 : GA D S) = 1 from rfl, Matrix.one_mulVec]
  ext y
  constructor
  · intro hy
    have := (h1 y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    rwa [e1] at this
  · intro hy
    have h2 := h1 y (fun i => by
      have := GlobalTheory.FinPl.FrameLat.latV_supp hy i
      exact this)
    rw [e1] at h2
    exact h2.2 hy

end GlobalTheory.CommonVac

namespace GlobalTheory.CommonVac

theorem exists_common_vacua : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (pk W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, VTie (⟨mkGeo m b, j, row, col⟩ : FamCh W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  intro D L hT Gi Gl Kc Yd cX ex W u hpk a y m b v hc hτ hNT hgP hTy hb hbT hLT hmT hN hvb hvbT htP

  have hQ : ∀ p ∈ v.gP, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) := by
    intro p hp
    obtain ⟨PP, hPP, rfl⟩ := (hgP p).1 hp
    exact GlobalTheory.T.type_places_split_idempotents W hpk hTy PP hPP

  have hY : ∀ j, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, j + 1 < D.R.m →
      GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True)
        (comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)))) ∧
      comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (b j, b (j + 1))
        (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1)) ≠ 0 := by
    intro j
    by_cases hj : j + 1 < D.R.m
    · obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk j (by omega) (b j)
      obtain ⟨M', hM', hM'v⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk (j + 1) hj (b (j + 1))
      obtain ⟨hvac, hnz⟩ := GlobalTheory.T.self_dual_lattices_consecutive_step W hpk j hj (b j) (b (j + 1)) (hb j) (hb (j + 1)) M M' hM hM' hMv hM'v
      obtain ⟨o, ho, hoV⟩ := GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective D (pk W).ψ hc.std (Yc D j) (Yc D (j + 1)) M (v.N j) M' (v.N (j + 1)) v.gP hM
        (hN j (by omega)).1 hM' (hN (j + 1) hj).1 hQ (fun p hp =>
          ⟨latV_eq_of_moves (hMv (· = p)) ((hN j (by omega)).2 (· = p) (fun p' hp' => hp' ▸ hp)),
            latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp))⟩)
      have hv1 := hvac 1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      simp only [one_mul] at hv1
      exact ⟨o, fun _ => ⟨ho, fun P x hx x' hx' => (hoV _ (hvac P x hx x' hx')).1, (hoV _ hv1).2 hnz⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose O hO using hY

  have hTs : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ o : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True)
        (comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)))) ∧
      comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1)) ≠ 0 := by
    intro j h
    have hj : j + 1 < D.R.m := by omega
    obtain ⟨M', hM', hM'v⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk (j + 1) hj (b (j + 1))
    obtain ⟨hvac, hnz⟩ := GlobalTheory.T.self_dual_lattices_top_step W hpk j h (b (j + 1)) a.bT (hb (j + 1)) hbT M' a.LT hM' hLT hM'v hmT
    have hNT' : IsSelfDualC D.sp.X' v.NT := hNT ▸ hLT
    obtain ⟨o, ho, hoV⟩ := GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective D (pk W).ψ hc.std (Yc D (j + 1)) D.sp.X' M' (v.N (j + 1)) a.LT v.NT v.gP hM'
      (hN (j + 1) hj).1 hLT hNT' hQ (fun p hp =>
        ⟨latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp)), by rw [hNT]⟩)
    exact ⟨o, ho, fun P => (hoV _ (hvac P)).1, (hoV _ (hvac 1)).2 hnz⟩
  choose OT hOT using hTs
  refine ⟨fun j P x x' => comb (pk W).ψ _ _ (O j) ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)),
    fun j h P => comb (pk W).ψ _ _ (OT j h) (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)),
    fun j hj P x hx x' hx' => (hO j hj).2.1 P x hx x' hx', fun j h P => (hOT j h).2.1 P, ?_⟩
  intro j' row col
  exact {
    b := fun j => by rw [hvb]
    bT := ⟨hvbT, hNT⟩
    gP := hgP
    tP := htP
    moves := fun j hj P hP => (hN j hj).2 P hP
    movesT := hmT
    Ψ := fun j hj => ⟨O j, (hO j hj).1, fun P x x' => rfl⟩
    ΨT := fun j h => ⟨OT j h, (hOT j h).1, fun P => rfl⟩
    nz := ⟨fun j hj => ⟨1, by simpa only [one_mul] using (hO j hj).2.2⟩, fun j h => ⟨1, (hOT j h).2.2⟩⟩ }

end GlobalTheory.CommonVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentPlacesCharacterizedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_places_characterized : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (pk W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, VTie (⟨mkGeo m b, j, row, col⟩ : FamCh W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  first | exact @GlobalTheory.CommonVac.exists_common_vacua | exact GlobalTheory.CommonVac.exists_common_vacua | (intros; apply GlobalTheory.CommonVac.exists_common_vacua <;> assumption)
end

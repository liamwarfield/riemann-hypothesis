module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryBaseVacuaLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaDifferByTwistValuesLargeDepth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRealSSmulTwoSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Scale

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T →₀ ℂ) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T a (c • f) = c • comb ψ S T a f := by
  simp only [comb, heisO_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S →₀ ℂ) (a' : WO S A' →₀ ℂ) (c : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' a a' (c • C) = c • biComb ψ A S A' a a' C := by
  funext u v
  simp only [biComb]
  have h1 : (fun u' => comb ψ S A' a' ((c • C) u') v) = c • fun u' => comb ψ S A' a' (C u') v := by
    funext u'
    show comb ψ S A' a' (c • C u') v = c * comb ψ S A' a' (C u') v
    rw [comb_smul]; rfl
  rw [h1, comb_smul]; rfl

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul, hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem isLatVac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) : IsLatVac (heisO ψ S T) Λ (c • f) :=
  ⟨fun u hu => by rw [heisO_smul, hf.1 u hu], fun e' he u hu hh => by rw [heisO_smul, hf.2 e' he u hu hh]⟩

theorem isBiVac_smul {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {LA : Set (Fin A.rank → D.host.E)}
    {LS : Set (Fin S.rank → D.host.E)} {LA' : Set (Fin A'.rank → D.host.E)} (c : ℂ) {C : WO A S → WO S A' → ℂ}
    (h : IsBiVac ψ A S A' LA LS LA' C) : IsBiVac ψ A S A' LA LS LA' (c • C) := by
  refine ⟨continuous_const.mul h.cont, ?_, ?_⟩
  · intro v
    have e : (fun u => (c • C) u v) = c • fun u => C u v := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.left v).1, isLatVac_smul c (h.left v).2⟩
  · intro u
    have e : (c • C) u = c • C u := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.right u).1, isLatVac_smul c (h.right u).2⟩

theorem isBiSmooth_smul {A S A' : HSp D} (c : ℂ) {C : WO A S → WO S A' → ℂ} (h : IsBiSmooth C) :
    IsBiSmooth (c • C) :=
  fun n L L' hL hL' h0 h0' u v => by
    show ContDiff ℝ _ fun t => c * C (u + L t) (v + L' t)
    exact ContDiff.mul contDiff_const (h n L L' hL hL' h0 h0' u v)

end GlobalTheory.SeeSaw.Scale

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaRealUpToTwistLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaRealUpToTwistLargeDepth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal.OneVac

theorem isBiVac_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) :
    IsBiVac ψ A S A' LA LS LA' 0 ∧ IsBiSmooth (0 : WO A S → WO S A' → ℂ) := by
  have hz : ∀ (X Y : HSp D) (u : WO X Y), heisO ψ X Y u (0 : WO X Y → ℂ) = 0 := fun X Y u => by
    simpa using GlobalTheory.SeeSaw.Scale.heisO_smul ψ X Y u 0 0
  have h : ∀ (X Y : HSp D) (Λ : AddSubgroup (WO X Y)),
      IsThetaFunO ψ X Y (0 : WO X Y → ℂ) ∧ IsLatVac (heisO ψ X Y) Λ (0 : WO X Y → ℂ) := fun X Y Λ =>
    ⟨⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => hz X Y u⟩, continuous_const, fun k L hL hf w => contDiff_const⟩,
      fun u _ => hz X Y _, fun e _ u _ _ => hz X Y u⟩
  exact ⟨⟨continuous_const, fun v => h A S _, fun u => h S A' _⟩, fun n L L' _ _ _ _ u v => contDiff_const⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem vacAt_of (h₁ : VacReal ch) (h₂ : VacTw ch) : VacAt ch := by
  obtain ⟨hb, z, hz, htw⟩ := h₂
  refine ⟨hb, z, hz, fun P p hp => ?_⟩
  by_cases hex : ∃ (t : T) (M : Vol ch.G), M.Is t
  · obtain ⟨t₀, M₀, hM₀⟩ := hex
    obtain ⟨b₀, hb₀⟩ := hb t₀
    refine ⟨fun j => ((z t₀ j : ℂ)⁻¹) • conAt ch.W hM₀ (fockD ch.W t₀ (fun j => ch.rm.vT D.R.m j) P) (p * b₀) j,
      fun j hj hj' => ?_, fun t M hM b hbt j hj hj' => ?_⟩
    · obtain ⟨hv, hs⟩ := h₁ t₀ M₀ hM₀ b₀ hb₀ P p hp j hj hj'
      exact ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ hv, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ hs⟩
    · have e := htw t t₀ M M₀ hM hM₀ b b₀ hbt hb₀ P p hp j hj hj'
      rw [smul_comm, ← e, smul_smul, inv_mul_cancel₀ (z t₀ j).ne_zero, one_smul]
  · exact ⟨0, fun j _ _ => isBiVac_zero _ _ _ _ _ _ _, fun t M hM => absurd ⟨t, M, hM⟩ hex⟩

theorem big_vacAt : Big fun ch => VacAt ch :=
  GlobalTheory.RowReal.big_mono (Q := fun ch => VacReal ch ∧ VacTw ch) (fun ch h => vacAt_of ch h.1 h.2)
    (Big.and GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth GlobalTheory.T.unfoldedVacua_differ_by_twist_values_largeDepth)

end GlobalTheory.RowVal.OneVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaRealUpToTwistLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth : Big fun ch => VacAt ch := by
  first | exact @GlobalTheory.RowVal.OneVac.big_vacAt | exact GlobalTheory.RowVal.OneVac.big_vacAt | (intros; apply GlobalTheory.RowVal.OneVac.big_vacAt <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFlatAsm

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem evT_combC_smul (c : Combs G) (a : ℕ → ℂ) (C C' : BiFam G) (h : ∀ j, Even j → j < D.R.m → C j = a j • C' j)
    (f : SchRow G) (u : ColPt G) (y : RowPt G) :
    evT (combC W c C) f u y = (∏ k ∈ Finset.range (D.R.m / 2), a (2 * k)) * evT (combC W c C') f u y := by
  simp only [evT]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k < D.R.m := by have := Finset.mem_range.1 hk; omega
  simp only [combC]
  rw [h _ (even_two_mul k) hk', GlobalTheory.SeeSaw.Scale.biComb_smul]
  rfl

theorem isRealFam_smul (a : ℕ → ℂ) {C : BiFam G} (h : IsRealFam W C) : IsRealFam W fun j => a j • C j :=
  fun j hj hm => ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ (h j hj hm).1, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ (h j hj hm).2⟩

theorem prod_ite_zero (κ : ℂ) :
    ∏ k ∈ Finset.range (D.R.m / 2), (if 2 * k = 0 then κ else 1) = κ := by
  have hm : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; exact Finset.mem_range.2 (by omega)
  rw [Finset.prod_eq_single_of_mem 0 hm fun k _ hk => if_neg (by omega)]
  exact if_pos rfl


variable {W} in
theorem isExpansion_zero {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (hβ : β ∉ S.supp t Φ)
    {τ : PureDat G t →₀ ℂ} (h : S.IsExpansion t Φ β τ) : S.IsExpansion t Φ β 0 := by
  obtain ⟨e, he, -, -⟩ := h
  refine ⟨e, he, fun d hd => by simp at hd, fun x y _ _ => ?_⟩
  simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall, unfSupport, not_not] at hβ
  obtain ⟨w, hw⟩ := hβ
  rw [Finsupp.sum_zero_index]
  refine (Finset.prod_eq_zero (Finset.mem_univ w) ?_).symm
  simp only [GridChoice.term]
  rw [hw]
  rfl

end Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem flatAt_of (s : ℤˣ) (hl : LocAt ch s) (hv : VacAt ch) (ho : OneAt ch) : FlatAt ch s := by
  obtain ⟨κ, z₁, hz₁, hl⟩ := hl
  obtain ⟨hb, z₂, hz₂, hv⟩ := hv
  refine ⟨fun t => z₁ t * (∏ k ∈ Finset.range (D.R.m / 2), z₂ t (2 * k))⁻¹,
    fun t => mul_mem (hz₁ t) (inv_mem (prod_mem fun k _ => hz₂ t _)), fun P p hp => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hv P p hp
  refine ⟨fun j => (if j = 0 then κ else 1) • C₀ j, isRealFam_smul ch.W _ hC₀,
    fun t Φ τ hτ M hM β b hβ τ' c hτ' hc => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hb t
  by_cases hs : Stair t β
  · refine ⟨_, fun _ => rfl, fun u y => ?_⟩
    obtain ⟨ζ, hζ, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ τ' c hτ' hc
    rw [e P p hp u y, hζ hs, Finsupp.mul_sum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [evT_combC_smul ch.W (c d) (fun j => (z₂ t j : ℂ)) _ C₀ (hC t M hM b₀ hb₀),
      evT_combC_smul ch.W (c d) (fun j => if j = 0 then κ else 1) _ C₀ (fun _ _ _ => rfl), prod_ite_zero]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_prod, _root_.mul_inv_rev, inv_inv]
    ring
  · refine ⟨0, fun h => absurd h hs, fun u y => ?_⟩
    obtain ⟨ζ, -, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ 0 c
      (isExpansion_zero _ t Φ β (fun h => hs (ho t Φ β h)) hτ') (fun d hd => by simp at hd)
    rw [e P p hp u y, Finsupp.sum_zero_index, mul_zero, zero_mul]

theorem flatAt_big : Big fun ch => ∃ s, FlatAt ch s :=
  big_mono (fun ch ⟨⟨⟨s, hl⟩, hv⟩, ho⟩ => ⟨s, flatAt_of ch s hl hv ho⟩) ((GlobalTheory.T.flat_dictionary_base_vacua_large_depth.and GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth).and GlobalTheory.T.rowTest_support_families_staircase_cosets)

end GlobalTheory.RowFlatAsm

end

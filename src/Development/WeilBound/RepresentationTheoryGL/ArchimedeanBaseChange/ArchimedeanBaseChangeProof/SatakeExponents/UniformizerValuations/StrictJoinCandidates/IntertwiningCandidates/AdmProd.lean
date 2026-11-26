module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FixedMonoBo
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.AdmProd
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

theorem AdmProd_holds : AdmProd := by
  intro E _ _ _ n P w K hKo hKle
  have hadm := GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr (w.adicCompletion E) P.N P.h (fun i => P.σ i w)
  have hKc : IsCompact (K : Set (GLw n w)) :=
    (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n).of_isClosed_subset (K.isClosed_of_isOpen hKo) hKle
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictProd
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

theorem StrictProd_holds : StrictProd := by
  intro E _ _ _ n P P' hS w
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := P
  obtain ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ := P'
  obtain ⟨hF, hc, -⟩ := hS
  simp only at hc
  subst hc
  have key : ∀ i : Fin c, SIso (E := E) ⟨N i, V i⟩ ⟨N' i, V' i⟩ := by
    intro i
    have := (List.forall₂_iff_get.1 hF).2 i.1 (by simp [parts]) (by simp [parts])
    simpa [parts] using this
  have hN : N = N' := funext fun i => (key i).1
  subst hN
  have hσ : ∀ i, Nonempty ((σ i w).ρ.Equiv (σ' i w).ρ) := by
    intro i
    obtain ⟨hNi, hiso⟩ := key i
    have hl : IsLocCompGL (V' i) w (σ i w) := Bo.LocIso_holds E (N i) (V i) (V' i) hiso w (σ i w) (loc i w)
    exact GlobalTheory.LocGL.IrrGL.of_eq_of.1 (Bo.LocUniq_holds E (N i) (V' i) (disc' i) w _ _ hl (loc' i w))
  exact ⟨GlobalTheory.LocGL.multiProdEquiv _ fun i => (hσ i).some⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.CandParts
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem allLeaves_iff (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves Q ↔ ∀ x ∈ t.leafList, Q x.1 x.2
  | _, .leaf V z => by simp [Tr.AllLeaves, Tr.leafList]
  | _, .node t₁ t₂ => by
    rw [Tr.AllLeaves, Tr.leafList, allLeaves_iff Q t₁, allLeaves_iff Q t₂]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h₁, h₂⟩ x (hx | hx)
      · exact h₁ x hx
      · exact h₂ x hx
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩

theorem parts_of_leaves {N : ℕ} (t : Tr E N) (P : Pre E N) (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop)
    (ht : TreeParts t P) (hl : t.AllLeaves fun M V => M = 0 ∨ Q M V) : ∀ j, Q (P.N j) (P.V j) := by
  intro j
  have hmem : (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ t.leafList.filter fun x => 0 < x.1 := by
    rw [← ht]
    exact List.mem_ofFn.2 ⟨j, rfl⟩
  rw [List.mem_filter] at hmem
  obtain ⟨hx, hpos⟩ := hmem
  have h := (allLeaves_iff _ t).1 hl _ hx
  rcases h with h0 | hQ
  · simp only [decide_eq_true_eq] at hpos
    exact absurd h0 (Nat.pos_iff_ne_zero.1 hpos)
  · exact hQ

end PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

theorem CandParts_holds : CandParts := by
  intro hR E _ _ _ n π S F₀ d i s₁ s₂ Pa Pb D hC
  exact ⟨CandidateLeafDecomposition.parts_of_leaves s₁ Pa _ hC.ctx.t₁ hC.leaves₁,
    CandidateLeafDecomposition.parts_of_leaves s₂ Pb _ hC.ctx.t₂ hC.leaves₂⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.IsoInv
noncomputable section

namespace PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

open GlobalTheory.PRep

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}

theorem symm_intertwines (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    ∀ g w, L.symm (ρ' g w) = ρ g (L.symm w) := by
  intro g w
  apply L.injective
  rw [hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem map_fixed_le (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') ≤ fixed ρ' K := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_fixed_iff] at hv
  rw [mem_fixed_iff]
  intro h
  simp only [LinearEquiv.coe_coe]
  rw [← hL, hv h]

theorem map_fixed_eq (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') = fixed ρ' K := by
  refine le_antisymm (map_fixed_le L hL K) ?_
  intro w hw
  have hm : (L.symm : V' →ₗ[ℂ] V) w ∈ (fixed ρ' K).map (L.symm : V' →ₗ[ℂ] V) := ⟨w, hw, rfl⟩
  refine ⟨L.symm w, map_fixed_le L.symm (symm_intertwines L hL) K hm, ?_⟩
  simp

def imap (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) : ρ.IntertwiningMap ρ' :=
  ⟨(L : V →ₗ[ℂ] V'), fun g => by ext v; exact hL g v⟩

theorem isSubquotient_of (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    GlobalTheory.SmGL.IsSubquotient ρ' ρ :=
  GlobalTheory.SmGL.IsSubquotient.of_surjective (imap L hL) (fun w => ⟨L.symm w, L.apply_symm_apply w⟩)

end PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open GlobalTheory.PRep IsoInverse

theorem IsoInv_holds : IsoInv := by
  intro G V V' _ _ _ _ _ ρ ρ' ⟨e⟩ K
  have hL : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining (f := e.toIntertwiningMap) (g := g) (v := v)
  have hL' := symm_intertwines e.toLinearEquiv hL
  let F := e.toLinearEquiv.ofSubmodules _ _ (map_fixed_eq e.toLinearEquiv hL K)
  refine ⟨fun W _ _ τ => ⟨fun h => h.trans (isSubquotient_of e.toLinearEquiv.symm hL'),
    fun h => h.trans (isSubquotient_of e.toLinearEquiv hL)⟩, F.finrank_eq,
    ⟨fun _ => F.finiteDimensional, fun _ => F.symm.finiteDimensional⟩⟩

end PositivityTheory.Rg.BcB.F.FX.Bo
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.LevOpen
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcB.G8
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Rd.LevOC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def LOk (d : LocData E n) : Prop :=
  ∀ a ≤ n, ∀ w ∈ d.S₀ ∪ d.Bad, IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w))

theorem LOk_of_ok (d : LocData E n) (hd : d.Ok) : LOk d := fun a ha w hw => (L_open_le d hd a ha w hw).1

theorem lev_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev
  split_ifs with h1 h2
  · exact iwahori_pair_isOpen a (n - a) w
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem lev₂_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev₂
  split_ifs with h2
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem C_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) {S : Set (Pl E)} (i : Slot S) :
    IsOpen (C d a i) := by
  rcases i with w | w
  · exact lev_open d hd a ha w.1
  · exact lev₂_open d hd a ha w.1

theorem gSet_open' (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (gSet Sec d a) := by
  have hSl' := hSl E a (n - a) Sec hS
  obtain ⟨hKo1, -⟩ := GlobalTheory.T.finite_kernel_compact_open E a
  obtain ⟨hKo2, -⟩ := GlobalTheory.T.finite_kernel_compact_open E (n - a)
  set U : Set (Hf E a (n - a)) := (((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a)))
    with hU
  have hUo : IsOpen U := by
    rw [hU, Subgroup.coe_prod]
    exact hKo1.prod hKo2
  have hF := (Filter.eventually_cofinite.1 (C_cof d a (S := Sec)))
  set V : Set (Hf E a (n - a)) := U ∩ ⋂ i ∈ {i : Slot Sec | ¬ C d a i = (K2 a (n - a) i.pl : Set _)},
    (i.cp a (n - a)) ⁻¹' C d a i with hV
  have hVo : IsOpen V :=
    hUo.inter (hF.isOpen_biInter fun i _ => (C_open d hd a ha i).preimage (hSl'.2.1 i))
  have h1V : (1 : Hf E a (n - a)) ∈ V := by
    refine ⟨one_mem _, Set.mem_iInter₂.2 fun i _ => ?_⟩
    have h1 : (1 : Hf E a (n - a)) ∈ gSet Sec d a := (levSub Sec d a).one_mem
    rw [gSet_eq] at h1
    exact h1 i
  have hVsub : V ⊆ gSet Sec d a := by
    intro x hx
    rw [gSet_eq]
    intro i
    by_cases hi : C d a i = (K2 a (n - a) i.pl : Set _)
    · rw [hi]
      exact (hSl'.2.2.2.2.2.1 x).1 hx.1 i
    · exact Set.mem_iInter₂.1 hx.2 i hi
  exact Subgroup.isOpen_of_mem_nhds (levSub Sec d a) (g := 1) (Filter.mem_of_superset (hVo.mem_nhds h1V) hVsub)

theorem g₁_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₁ Sec d a : Set (GL (Fin a) (Af E))) := by
  rw [g₁_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_id.prodMk continuous_const)

theorem g₂_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) := by
  rw [g₂_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_const.prodMk continuous_id)

theorem loc_LOk {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S)
    (T' : Finset (Pl E)) c e b : LOk (F₀.loc T' c e b) :=
  fun a ha w hw => LOk_of_ok F₀.d₀ F₀.ok₀ a ha w hw

end PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

theorem LevOpen_holds : LevOpen := by
  intro hR E _ _ _ n π S F₀ T' c e b a ha
  have hd := LevelOpenness.loc_LOk F₀ T' c e b
  exact ⟨LevelOpenness.g₁_open slots F₀.hSec _ hd a ha, LevelOpenness.g₂_open slots F₀.hSec _ hd a ha⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

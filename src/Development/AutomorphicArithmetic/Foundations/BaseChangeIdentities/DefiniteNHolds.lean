module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.RunFinChain
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GelfandValueContinuity.ReadLimitOfEfinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFrameOk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.EFinalNEHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameEx0Plug
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PFinFamOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscreteSpectrum
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameBound
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameExOfFin
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.FrameRead
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.USideFree
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinStrictHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.AdmProd

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.BciOf
noncomputable section

namespace PositivityTheory.Rg.BcB.Plug2

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.F5

theorem bci_of (h1 : FrameEx) (h3 : FrameBound)
    (h4 : FrameRead) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  PositivityTheory.Rg.BcB.F.Rig.fieldN_of_run
    (runFin_chain (finFamOf_holds levelFactor GlobalTheory.T.finite_discrete_spectrum) PositivityTheory.Rg.BcB.F.Rig.weightEx PositivityTheory.Rg.BcB.F.Rig.permSat
      GlobalTheory.T.diagonal_algebra_holds (genEx_of (PositivityTheory.Rg.BcB.F.Rd.P.readLimit_of_efinal PositivityTheory.Rg.BcB.SpectralAccumulation.eFinal_holds) GlobalTheory.T.diagonal_algebra_holds PositivityTheory.Rg.BcB.F.Ex0.frameEx0 h1 frameOk₀ h3 h4))

end PositivityTheory.Rg.BcB.Plug2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameEx
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoinHolds
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInf_map {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

theorem isoV_map {a : ℕ} {V V' : Submodule ℂ (Sm E a)} (hV : IsoV V V') (χ : HChar E) :
    IsoV (V.map (mulChi a χ).toLinearMap) (V'.map (mulChi a χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := hV
  let M := mulChi a χ
  refine ⟨((M.submoduleMap V).symm.trans T).trans (M.submoduleMap V'), ?_⟩
  intro o φ ψ hψ
  set φ₀ := (M.submoduleMap V).symm φ with hφ₀
  set ψ₀ := (M.submoduleMap V).symm ψ with hψ₀
  have eφ : φ.1 = M φ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply φ); rw [← this]; rfl
  have eψ : ψ.1 = M ψ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply ψ); rw [← this]; rfl
  have key : ψ₀.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ₀.1 + opAdd χ o • φ₀.1 := by
    apply M.injective
    rw [← eψ, hψ, eφ]
    exact act_mulChi χ o φ₀.1
  have hmem : act o φ₀.1 ∈ V := by
    have : act o φ₀.1 = ((opMul χ o : ℂˣ) : ℂ)⁻¹ • (ψ₀.1 - opAdd χ o • φ₀.1) := by
      rw [key, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    rw [this]
    exact V.smul_mem _ (V.sub_mem ψ₀.2 (V.smul_mem _ φ₀.2))
  have hψ' : ψ₀ = ((opMul χ o : ℂˣ) : ℂ) • (⟨act o φ₀.1, hmem⟩ : V) + opAdd χ o • φ₀ := Subtype.ext key
  have h1 := hT o φ₀ ⟨act o φ₀.1, hmem⟩ rfl
  change (M (T ψ₀).1) = act o (M (T φ₀).1)
  rw [act_mulChi, hψ', map_add (f := _), map_smul, map_smul]
  simp only [Submodule.coe_add, Submodule.coe_smul, h1]
  rfl

theorem sIso_tw {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) (χ : HChar E) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨N, V⟩ := x
  obtain ⟨N', V'⟩ := y
  obtain ⟨e, hi⟩ := h
  dsimp only at e
  subst e
  exact ⟨rfl, isoV_map hi χ⟩

def SInf (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) : Prop :=
  ∀ τ, ∃ m, HasInfCharGL x.2 τ m ∧ HasInfCharGL y.2 τ m

theorem length_parts {n : ℕ} (P : Pre E n) : (parts P).length = P.c := by simp [parts]

theorem sInf_tw {a : ℕ} {P P' : Pre E a} (h : Strict P P') (χ : HChar E) :
    List.Forall₂ SInf ((parts P).map (twPart χ)) ((parts P').map (twPart χ)) := by
  obtain ⟨hc, hm⟩ := h.2
  rw [List.forall₂_iff_get]
  refine ⟨by simp [length_parts, hc], fun i h₁ h₂ => ?_⟩
  intro τ
  have hi : i < P.c := by simpa [length_parts] using h₁
  refine ⟨(P.m ⟨i, hi⟩ τ).map (· + expo χ τ), ?_, ?_⟩
  · have e : ((parts P).map (twPart χ)).get ⟨i, h₁⟩ = twPart χ ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ := by
      simp [parts]
    rw [e]
    exact hasInf_map (P.inf _ τ) χ
  · have e : ((parts P').map (twPart χ)).get ⟨i, h₂⟩ =
        twPart χ ⟨P'.N (Fin.cast hc ⟨i, hi⟩), P'.V (Fin.cast hc ⟨i, hi⟩)⟩ := by
      simp [parts]
    rw [e, hm ⟨i, hi⟩]
    exact hasInf_map (P'.inf _ τ) χ

theorem strict_of {n : ℕ} {P P' : Pre E n} (h₁ : List.Forall₂ SIso (parts P) (parts P'))
    (h₂ : List.Forall₂ SInf (parts P) (parts P')) : Strict P P' := by
  have hc : P.c = P'.c := by rw [← length_parts, ← length_parts]; exact h₂.length_eq
  refine ⟨h₁, hc, fun i => funext fun τ => ?_⟩
  have hi : i.1 < (parts P).length := by rw [length_parts]; exact i.2
  have hi' : i.1 < (parts P').length := by rw [length_parts, ← hc]; exact i.2
  obtain ⟨m, hm, hm'⟩ := (List.forall₂_iff_get.1 h₂).2 i.1 hi hi' τ
  have e : (parts P).get ⟨i.1, hi⟩ = ⟨P.N i, P.V i⟩ := by simp [parts]
  have e' : (parts P').get ⟨i.1, hi'⟩ = ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ := by
    simp only [parts, List.get_ofFn]; rfl
  rw [e] at hm
  rw [e'] at hm'
  have e1 := LemDd.InfUniq_holds E _ _ τ _ _ (P.discrete i).ne_bot (P.inf i τ) hm
  have e2 := LemDd.InfUniq_holds E _ _ τ _ _ (P'.discrete _).ne_bot (P'.inf _ τ) hm'
  rw [e1, e2]

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo StrictJoinAlt

theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  refine strict_of ?_ ?_
  · rw [hJ, hJ']
    exact List.rel_append
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_tw h χ₁)))
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_tw h χ₂)))
  · rw [hJ, hJ']
    exact List.rel_append (sInf_tw ha χ₁) (sInf_tw hb χ₂)

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw

end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinearIndependentEigenvectors
theorem UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {Ξ P : Type}
    (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ),
    Function.Injective ev →
      ∀ (v : Ξ → V),
        (∀ (ξ : Ξ), v ξ ≠ (0 : V)) → (∀ (ξ : Ξ) (p : P), (T p : V → V) (v ξ) = ev ξ p • v ξ) → LinearIndependent ℂ v := by
  intro V _ _ Ξ P T ev hinj v hv hT
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : ev i ≠ ev a := fun h => ha (hinj h ▸ hi)
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
      have h1 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev j p) • v j = 0 := by
        have h := congrArg (T p) hg
        set_option synthInstance.maxHeartbeats 100000 in
          simpa only [map_add (f := _), map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev a p) • v j = 0 := by
        have h := congrArg (fun x => ev a p • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm] using h
      have h3 : ∑ j ∈ s, (g j * (ev j p - ev a p)) • v j = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)
      have h4 := ih (fun j => g j * (ev j p - ev a p)) h3 i hi
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hp)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.SameOfStrict
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.StrictCommon
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem strict_common {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P Q R : Pre E n} (h1 : Strict P R)
    (h2 : Strict Q R) : Strict P Q := by
  obtain ⟨a1, c1, m1⟩ := h1
  obtain ⟨a2, c2, m2⟩ := h2
  refine ⟨?_, c1.trans c2.symm, fun i => ?_⟩
  · refine Tw.FiniteStrictOrder.forall₂_ofFn SIso (c1.trans c2.symm) _ _ fun i => ?_
    have hi : i.val < R.c := c1 ▸ i.isLt
    have e1 := (List.forall₂_iff_get.1 a1).2 i.val (by simp [parts]) (by simpa [parts] using hi)
    have e2 := (List.forall₂_iff_get.1 a2).2 i.val (by simpa [parts, c2] using hi) (by simpa [parts] using hi)
    simp only [parts, List.get_ofFn] at e1 e2
    exact Tw.FiniteStrictOrder.siso_trans (Q.discrete _).stable e1 e2
  · rw [m1 i, m2]
    rfl

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem joins_fin (hSJ : StrictJoin)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (μ : HChar E) {ι : Type} [Finite ι] (a : ι → ℕ) (kA kB : ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - a i)) :
    ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i (Pa : Pre E (a i)) (Pb : Pre E (n - a i)) (D : Pre E n),
      IsJoin (μ ^ (n - a i)) (μ ^ a i) Pa Pb D → (∃ ja, Strict Pa (PA i ja)) → (∃ jb, Strict Pb (PB i jb)) →
      ∃ j, Strict D (Dl j) := by
  let J : Type := {x : Σ i, Fin (kA i) × Fin (kB i) // ∃ D : Pre E n, ∃ (Pa : Pre E (a x.1)) (Pb : Pre E (n - a x.1)),
    IsJoin (μ ^ (n - a x.1)) (μ ^ a x.1) Pa Pb D ∧ Strict Pa (PA x.1 x.2.1) ∧ Strict Pb (PB x.1 x.2.2)}
  haveI : Finite J := Subtype.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  choose Df Paf Pbf hf using fun x : J => x.2
  refine ⟨k, fun j => Df (e.symm j), fun i Pa Pb D hj ⟨ja, ha⟩ ⟨jb, hb⟩ => ?_⟩
  let x : J := ⟨⟨i, ja, jb⟩, D, Pa, Pb, hj, ha, hb⟩
  refine ⟨e x, ?_⟩
  show Strict D (Df (e.symm (e x)))
  rw [e.symm_apply_apply]
  exact hSJ E n _ _ _ _ Pa (Paf x) Pb (Pbf x) D _ hj (hf x).1 (strict_common ha (hf x).2.1) (strict_common hb (hf x).2.2)

theorem same_of_strict (hSPr : StrictProd) (hII : IsoInv) (hAd : AdmProd)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w))
    (ho : IsOpen (K : Set (GLw n w))) (hle : K ≤ GlobalTheory.LFun.KGL w (n := n)) (D D' : Pre E n) (hs : Strict D D') :
    (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
      Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
      FiniteDimensional ℂ ↥(fixed (prodAt D' w) K) := by
  have h := hII (GLw n w) _ _ (prodAt D w) (prodAt D' w) (hSPr E n D D' hs w) K
  exact ⟨fun τ => h.1 τ.V τ.ρ, h.2.1, hAd E n D' w K ho hle⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.EigList
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.EigFin
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.JeigRFinite
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.HeckeLevelFrameExistence.Ev

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Tail

section Gen

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fix_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) {v : V}
    (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

theorem hk_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) (f : G → ℂ) (v : V) :
    φ.toLinearEquiv (hkG ρ K f v) = hkG σ K f (φ.toLinearEquiv v) := by
  unfold hkG
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : G ⧸ K => f q.out • ρ q.out v)).trans (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (f q.out • ρ q.out v) = f q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

theorem hk_lin (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) : ∃ T : V →ₗ[ℂ] V, ∀ v, hkG ρ K f v = T v := by
  by_cases h : (Function.support fun q : G ⧸ K => f q.out).Finite
  · refine ⟨∑ q ∈ h.toFinset, f q.out • ρ q.out, fun v => ?_⟩
    unfold hkG
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset), LinearMap.sum_apply]
    · rfl
    · intro q hq
      rw [Set.Finite.coe_toFinset]
      intro h0
      apply hq
      simp only [h0, zero_smul]
  · refine ⟨0, fun v => ?_⟩
    unfold hkG
    by_cases hv : v = 0
    · simp [hv]
    · refine finsum_of_infinite_support fun hfin => h (hfin.subset fun q hq h0 => ?_)
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact hq h1
      · apply hv
        have := congrArg (ρ q.out⁻¹) h1
        rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

theorem li_eig {Ξ P : Type} (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ) (hinj : Function.Injective ev) (v : Ξ → V)
    (h0 : ∀ ξ, v ξ ≠ 0) (hv : ∀ ξ p, T p (v ξ) = ev ξ p • v ξ) : LinearIndependent ℂ v :=
  _root_.UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig T ev hinj v h0 hv

theorem fin_eig {Ξ P : Type} (U : Submodule ℂ V) [FiniteDimensional ℂ U] (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ)
    (hinj : Function.Injective ev) : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v}.Finite := by
  choose v hU h0 hv using fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ξ.2
  have h := li_eig T (fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ev ξ.1)
    (hinj.comp Subtype.val_injective) v h0 hv
  have h' : LinearIndependent ℂ fun ξ => (⟨v ξ, hU ξ⟩ : U) := LinearIndependent.of_comp U.subtype h
  haveI := h'.finite_of_isNoetherian
  exact Set.toFinite _

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def JEigR {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E) (ρ : Representation ℂ (GLw a w × GLw b w) V)
    (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ fixed ρ (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

theorem jeigR_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {w : Pl E}
    {ρ : Representation ℂ (GLw a w × GLw b w) V} {σ : Representation ℂ (GLw a w × GLw b w) W} (φ : ρ.Equiv σ)
    {ϖ : (w.adicCompletion E)ˣ} {ξa : Fin a → ℂˣ} {ξb : Fin b → ℂˣ} (h : JEigR w ρ ϖ ξa ξb) :
    JEigR w σ ϖ ξa ξb := by
  obtain ⟨v, hv, hv0, he⟩ := h
  refine ⟨φ.toLinearEquiv v, fix_map φ _ hv, fun h0 => hv0 (φ.toLinearEquiv.injective (by rw [h0, map_zero])),
    fun x y hx hy => ?_⟩
  rw [← hk_map, he x y hx hy, map_smul]

theorem qh_ne_zero (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  have hq : qV E w ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero hq

theorem pw_ne_zero {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) : pw y x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => Units.ne_zero _

theorem pw_shift {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) (i : Fin m) :
    pw y (fun j => x j + if j = i then 1 else 0) = pw y x * (y i : ℂ) := by
  have key : ∀ j, (((y j ^ (x j + if j = i then 1 else 0) : ℂˣ)) : ℂ) =
      ((y j ^ x j : ℂˣ) : ℂ) * (if j = i then (y i : ℂ) else 1) := by
    intro j
    by_cases h : j = i
    · subst h
      simp [_root_.zpow_add]
    · simp [h]
  simp only [pw, key, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

def g0 (m : ℕ) : Fin m → ℤ := fun i => 2 * ((m : ℤ) - (i : ℕ))

theorem gap0 (m : ℕ) : Gap (g0 m) := by
  intro i j hij
  have := Fin.lt_def.1 hij
  simp only [g0]
  omega

theorem gap1 (m : ℕ) (i : Fin m) : Gap (fun j => g0 m j + if j = i then 1 else 0) := by
  intro j l hjl
  have := Fin.lt_def.1 hjl
  simp only [g0]
  split_ifs <;> omega

theorem ev2_inj (w : Pl E) : Function.Injective (fun (ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ))
    (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) => ev2 w ξ.1 ξ.2 p.1.1 p.1.2) := by
  rintro ⟨ξa, ξb⟩ ⟨ξa', ξb'⟩ h
  have hx : ∀ (x : Fin a → ℤ) (y : Fin b → ℤ), Gap x → Gap y → ev2 w ξa ξb x y = ev2 w ξa' ξb' x y :=
    fun x y hx hy => congrFun h ⟨(x, y), hx, hy⟩
  have hd : ∀ {N : ℕ} (x : Fin N → ℤ), dl w x ≠ 0 := fun _ => zpow_ne_zero _ (qh_ne_zero w)
  have h0 := hx (g0 a) (g0 b) (gap0 a) (gap0 b)
  simp only [ev2] at h0
  have hM : pw ξa (g0 a) * pw ξb (g0 b) = pw ξa' (g0 a) * pw ξb' (g0 b) := by
    refine mul_left_cancel₀ (mul_ne_zero (hd (g0 a)) (hd (g0 b))) ?_
    linear_combination h0
  have hM0 : pw ξa' (g0 a) * pw ξb' (g0 b) ≠ 0 := mul_ne_zero (pw_ne_zero _ _) (pw_ne_zero _ _)
  refine Prod.ext (funext fun i => Units.ext ?_) (funext fun i => Units.ext ?_)
  · have h1 := hx _ (g0 b) (gap1 a i) (gap0 b)
    simp only [ev2, pw_shift] at h1
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (fun j => g0 a j + if j = i then 1 else 0))
      (hd (g0 b))) hM0) ?_
    linear_combination h1 - (dl w (fun j => g0 a j + if j = i then 1 else 0) * dl w (g0 b) * (ξa i : ℂ)) * hM
  · have h1 := hx (g0 a) _ (gap0 a) (gap1 b i)
    simp only [ev2, pw_shift] at h1
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (g0 a))
      (hd (fun j => g0 b j + if j = i then 1 else 0))) hM0) ?_
    linear_combination h1 - (dl w (g0 a) * dl w (fun j => g0 b j + if j = i then 1 else 0) * (ξb i : ℂ)) * hM

theorem jeigR_finite {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E)
    (ρ : Representation ℂ (GLw a w × GLw b w) V) (ϖ : (w.adicCompletion E)ˣ)
    [FiniteDimensional ℂ (fixed ρ (I2 a b w))] :
    {ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ) | JEigR w ρ ϖ ξ.1 ξ.2}.Finite := by
  choose T hT using fun (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) =>
    hk_lin ρ (I2 a b w) (dc2 w ϖ p.1.1 p.1.2)
  refine (fin_eig (fixed ρ (I2 a b w)) T _ (ev2_inj w)).subset ?_
  rintro ⟨ξa, ξb⟩ ⟨v, hv, hv0, he⟩
  exact ⟨v, hv, hv0, fun p => by rw [← hT]; exact he _ _ p.2.1 p.2.2⟩

end UpperTheory.HeckeLevelFrameExistence.Ev

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical TensorProduct

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem eig_abs (hII : IsoInv) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (w : Pl E)
    (ϖ : (w.adicCompletion E)ˣ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (τ₁ : Representation ℂ (GLw a w) X) (τ₂ : Representation ℂ (GLw b w) Y) (h₁ : IsAdmissible τ₁) (h₂ : IsAdmissible τ₂) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧
      ∀ (X' Y' : Type) [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
        (ρ₁ : Representation ℂ (GLw a w) X') (ρ₂ : Representation ℂ (GLw b w) Y'), Nonempty (ρ₁.Equiv τ₁) → Nonempty (ρ₂.Equiv τ₂) →
        Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) (I2 a b w)) ≤ m ∧
          ∀ ξa ξb, Ev.JEigR w (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  haveI : FiniteDimensional ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)) :=
    GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ τ₁ τ₂ _ _
      (h₁.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
      (h₂.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
  refine ⟨_, Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)), Ev.jeigR_finite w (GlobalTheory.SmGL.extTensor τ₁ τ₂) ϖ, ?_⟩
  rintro X' Y' _ _ _ _ ρ₁ ρ₂ ⟨Φa⟩ ⟨Φb⟩
  have Φ : (GlobalTheory.SmGL.extTensor ρ₁ ρ₂).Equiv (GlobalTheory.SmGL.extTensor τ₁ τ₂) := GlobalTheory.SmGL.RowOneCell.extTensorEquiv Φa Φb
  exact ⟨(hII _ _ _ _ _ ⟨Φ⟩ (I2 a b w)).2.1.le, fun ξa ξb h => Ev.jeigR_equiv Φ h⟩

theorem admissible_hecke_word_product {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (P : Pre E n) (w : Pl E) :
    IsAdmissible (prodAt P w) :=
  ⟨GlobalTheory.SmGL.isSmooth_parInd _ _, fun K ho hc => fixFin E n P w K ho hc⟩

theorem eig_one (hII : IsoInv) (hSPr : StrictProd) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (PA : Pre E a) (PB : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b), Strict Pa PA → Strict Pb PB →
      Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w)) ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  obtain ⟨Z, m, hZ, h⟩ := eig_abs hII w ϖ (prodAt PA w) (prodAt PB w) (admissible_hecke_word_product PA w) (admissible_hecke_word_product PB w)
  refine ⟨Z, m, hZ, fun Pa Pb ha hb => ?_⟩
  have h' := h _ _ (prodAt Pa w) (prodAt Pb w) (hSPr E a Pa PA ha w) (hSPr E b Pb PB hb w)
  exact ⟨h'.1, fun ξa ξb hj => h'.2 ξa ξb hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

def dimI {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) : ℕ :=
  Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w))

theorem eig_fin (hII : IsoInv) (hSPr : StrictProd) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b kA kB : ℕ}
    (PA : Fin kA → Pre E a) (PB : Fin kB → Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b),
      (∃ ja, Strict Pa (PA ja)) → (∃ jb, Strict Pb (PB jb)) →
      dimI Pa Pb w ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  have h0 : ∀ x : Fin kA × Fin kB, ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b),
      Strict Pa (PA x.1) → Strict Pb (PB x.2) → dimI Pa Pb w ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z :=
    fun x => eig_one hII hSPr (PA x.1) (PB x.2) w ϖ
  choose Z mZ hZ using h0
  refine ⟨⋃ x, Z x, Finset.univ.sup mZ, Set.finite_iUnion fun x => (hZ x).1, ?_⟩
  rintro Pa Pb ⟨ja, ha⟩ ⟨jb, hb⟩
  have h := (hZ (ja, jb)).2 Pa Pb ha hb
  exact ⟨le_trans h.1 (Finset.le_sup (Finset.mem_univ (ja, jb))), fun ξa ξb hj => Set.mem_iUnion.2 ⟨(ja, jb), h.2 ξa ξb hj⟩⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.CandOf
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Imports
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem part1 (hII : IsoInv) (hSPr : StrictProd) {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) (T' : Finset (Pl E)) :
    (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
      ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' → ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
    ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T', dimI Pa Pb w ≤ m₀ := by
  choose Z mZ hZ using fun (i : F₀.C.ι) (w : Pl E) => eig_fin hII hSPr (PA i) (PB i) w (F₀.d₀.ϖ w)
  refine ⟨fun i w => ⟨Z i w, (hZ i w).1, fun s₁ s₂ Pa Pb D hc _ => ?_⟩,
    ⟨Finset.univ.sup fun i => T'.sup (mZ i), fun i s₁ s₂ Pa Pb D hc w hw => ?_⟩⟩
  · exact ((hZ i w).2 Pa Pb (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2).2
  · have h1 := ((hZ i w).2 Pa Pb (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2).1
    have h2 : mZ i w ≤ T'.sup (mZ i) := Finset.le_sup hw
    have h3 : T'.sup (mZ i) ≤ Finset.univ.sup fun i => T'.sup (mZ i) :=
      Finset.le_sup (f := fun i => T'.sup (mZ i)) (Finset.mem_univ i)
    exact le_trans h1 (le_trans h2 h3)

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ImportsAlt
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

def Same {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w)) (D D' : Pre E n) : Prop :=
  (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
    Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
    FiniteDimensional ℂ ↥(fixed (prodAt D' w) K)

theorem part2 (hSPr : StrictProd) (hSJ : StrictJoin) (hII : IsoInv) (hAd : AdmProd) {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) :
    ∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j) := by
  intro w hw
  obtain ⟨k, Dl, hD⟩ := joins_fin hSJ F₀.μ F₀.C.a kA kB PA PB
  have hs : ∀ D D' : Pre E n, Strict D D' → Same w (F₀.d₀.K' w) D D' :=
    same_of_strict hSPr hII hAd w _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1
  refine ⟨k, Dl, fun i s₁ s₂ Pa Pb D hc => ?_⟩
  obtain ⟨j, hj⟩ := hD i Pa Pb D hc.ctx.join (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2
  exact ⟨j, hs D (Dl j) hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ClsFin
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem rl_levels (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (h1 : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (h2 : IsOpen (K₂ : Set (GL (Fin b) (Af E)))) :
    Levels E (rlΘ₁ hR E a b Ma Mb K₁ K₂) ∧ Levels E (rlΘ₂ hR E a b Ma Mb K₁ K₂) :=
  (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1 a b Ma Mb K₁ K₂ h1 h2

theorem rl_ktypes (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) : KTypes E (rlΩ₁ hR E a b Ma Mb) ∧ KTypes E (rlΩ₂ hR E a b Ma Mb) :=
  ⟨((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.1,
    ((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.2.1⟩

theorem cls_fin (hFS : FinStrict) (hCP : CandParts)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (i : F₀.C.ι)
    (h1 : IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))))
    (h2 : IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    ∃ (kA kB : ℕ) (PA : Fin kA → Pre E (F₀.C.a i)) (PB : Fin kB → Pre E (n - F₀.C.a i)), ∀ s₁ s₂ Pa Pb D,
      F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA ja)) ∧ ∃ jb, Strict Pb (PB jb) := by
  have hL := rl_levels hR E _ _ (F₀.A i).Ma (F₀.A i).Mb _ _ h1 h2
  have hK := rl_ktypes hR E _ _ (F₀.A i).Ma (F₀.A i).Mb
  obtain ⟨kA, PA, hPA⟩ := hFS E _ _ _ hL.1 hK.1 (mOf (F₀.A i).χa)
  obtain ⟨kB, PB, hPB⟩ := hFS E _ _ _ hL.2 hK.2 (mOf (F₀.A i).χb)
  refine ⟨kA, kB, PA, PB, fun s₁ s₂ Pa Pb D hc => ?_⟩
  have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
  have hm := LemDd.cand_sum hc
  exact ⟨hPA Pa hp.1 hm.1, hPB Pb hp.2 hm.2⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem all_parts (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (T' : Finset (Pl E))
    (hO : ∀ i : F₀.C.ι, IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))) ∧
      IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
      ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' → ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
    (∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j)) ∧
    ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T', dimI Pa Pb w ≤ m₀ := by
  have hfin (i : F₀.C.ι) :
      ∃ (kA kB : ℕ) (PA : Fin kA → Pre E (F₀.C.a i)) (PB : Fin kB → Pre E (n - F₀.C.a i)), ∀ s₁ s₂ Pa Pb D,
        F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA ja)) ∧ ∃ jb, Strict Pb (PB jb) := by
    have hL := rl_levels hR E _ _ (F₀.A i).Ma (F₀.A i).Mb _ _ (hO i).1 (hO i).2
    have hK := rl_ktypes hR E _ _ (F₀.A i).Ma (F₀.A i).Mb
    obtain ⟨kA, PA, hPA⟩ := hFS E _ _ _ hL.1 hK.1 (mOf (F₀.A i).χa)
    obtain ⟨kB, PB, hPB⟩ := hFS E _ _ _ hL.2 hK.2 (mOf (F₀.A i).χb)
    refine ⟨kA, kB, PA, PB, fun s₁ s₂ Pa Pb D hc => ?_⟩
    have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
    have hm := LemDd.cand_sum hc
    exact ⟨hPA Pa hp.1 hm.1, hPB Pb hp.2 hm.2⟩
  choose kA kB PA PB hcls using hfin
  have h1 := part1 hII hSPr F₀ d kA kB PA PB hcls T'
  exact ⟨h1.1, part2 hSPr hSJ hII hAd F₀ d kA kB PA PB hcls, h1.2⟩

theorem candFin_of (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts)
    (hLO : LevOpen) (hII : IsoInv) (hAd : AdmProd) : CandFin := by
  intro hR E _ _ _ hU n hn π hπ S F₀ T' c e b hT'
  have hO := fun i : F₀.C.ι => hLO hR E n π S F₀ T' c e b (F₀.C.a i) (F₀.C.le i)
  exact all_parts hFS hSPr hSJ hCP hII hAd F₀ (F₀.loc T' c e b) T' hO

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

namespace UpperTheory.HeckeLevelFrameExistence

theorem candFin : CandFin :=
  CF.candFin_of Tw.FinStrict_holds StrictProd_holds Tw.StrictJoin_holds CandParts_holds LevOpen_holds
    IsoInv_holds AdmProd_holds

end UpperTheory.HeckeLevelFrameExistence
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FillPre
theorem UpperTheory.BaseChangeIdentities.baseChangeN_of
    (hCF : PositivityTheory.Rg.BcB.F.FX.CandFin) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN := by
  have hFrameEx : PositivityTheory.Rg.BcB.F.FrameEx :=
    UpperTheory.HeckeLevelFrameExistence.frameEx_of_fin UpperTheory.BaseChangeIdentities.uSide hCF
  exact PositivityTheory.Rg.BcB.Plug2.bci_of hFrameEx
    UpperTheory.BaseChangeIdentities.FrameWordIdentity.frameBound
    UpperTheory.BaseChangeIdentities.GelfandReading.frameRead
end

theorem UpperTheory.BaseChangeIdentities.baseChangeN : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  UpperTheory.BaseChangeIdentities.baseChangeN_of UpperTheory.HeckeLevelFrameExistence.candFin

module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
open CategoryTheory Polynomial

noncomputable section
namespace GlobalTheory.GLq.ConstIff

open Formalism.IrreducibleCountingLemmas.TYPES

theorem isConstituent_iff_ip_ne_zero {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G)
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] (ρ : Representation ℂ G V) :
    IsConstituent τ ρ ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ V (ρ x)) ≠ 0 := by
  classical
  let W := FDRep.of ρ
  let H := FDRep.of (Representation.linHom τ.ρ W.ρ)
  let _ : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have havg := FDRep.average_char_eq_finrank_invariants H
  have hH : ∀ g, H.character g = τ.character g⁻¹ * LinearMap.trace ℂ V (ρ g) := fun g =>
    FDRep.char_linHom τ W g
  have hsum : ∑ x, τ.character x * LinearMap.trace ℂ V (ρ x⁻¹) = ∑ g, H.character g := by
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x => ?_
    rw [Equiv.inv_apply, hH, inv_inv]
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key : GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ V (ρ x)) =
      (Module.finrank ℂ (Representation.invariants H.ρ) : ℂ) := by
    rw [← havg, ← hsum, GlobalTheory.GLq.ip, Nat.card_eq_fintype_card]
  rw [key, Ne, Nat.cast_eq_zero, Submodule.finrank_eq_zero, ← Ne, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨φ, hφ, hne⟩
    exact ⟨φ, (PI.SerBridgeGLW.mem_inv_linHom_iff τ.ρ W.ρ φ).mpr hφ, hne⟩
  · rintro ⟨φ, hφ, hne⟩
    exact ⟨φ, (PI.SerBridgeGLW.mem_inv_linHom_iff τ.ρ W.ρ φ).mp hφ, hne⟩

theorem constituent_hcRep_iff : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))),
    CategoryTheory.Simple τ →
      (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔
        GlobalTheory.GLq.ip (fun x => τ.character x)
          (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
            (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0) := by
  intro g _ r s b lam τ _
  have : Module.Finite ℂ (PiTensorProduct ℂ (fun c => (lam c : Type))) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.Free.chooseBasis ℂ (lam c))
  exact isConstituent_iff_ip_ne_zero τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam)

end GlobalTheory.GLq.ConstIff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZeroStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0) := by
  first | exact @GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | exact GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | (intros; apply GlobalTheory.GLq.ConstIff.constituent_hcRep_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfEqMulIntegral
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.NormPrime

variable {R : Ranks}

theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

end GlobalTheory.Mem.NormPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabel
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

theorem hasLabel_of_hasLabelO : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x)) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f := by
  intro g _ L C O h1 h2 h3 r τ f hτ hL
  obtain ⟨s, b, lam, hb, hl, hcon, rfl⟩ := hL
  have hc : ∀ c, 1 ≤ Fintype.card {i // b i = c} := fun c => by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let Q : List ((ZMod g)[X] × GlobalTheory.GLq.Pc g) := (List.finRange s).map fun c =>
    (labO O (lam c), ⟨Fintype.card {i // b i = c},
      fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩)
  have hQ : Q.map Prod.snd = canonList b lam := by
    simp only [Q, canonList, List.map_map]
    rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Q, List.mem_map] at hp
    obtain ⟨c, -, rfl⟩ := hp
    exact h1 _ _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)
  · rw [hQ]
    unfold GlobalTheory.GLq.degL canonList
    rw [List.map_map]
    have e : ((List.finRange s).map ((fun p : GlobalTheory.GLq.Pc g => p.1) ∘ fun c : Fin s =>
        (⟨Fintype.card {i // b i = c},
          fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ : GlobalTheory.GLq.Pc g))).sum =
        ∑ c : Fin s, Fintype.card {i // b i = c} := by
      rw [Fin.sum_univ_def]
      rfl
    rw [e, ← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin]
  · simp only [Q, List.map_map]
    rw [Fin.prod_univ_def]
    rfl
  · rw [hQ]
    have ht : (fun x => LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x)) =
        GlobalTheory.GLq.hcL (canonList b lam) r := funext (h2 r s b lam hb)
    have := (h3 r s b lam τ hτ).1 hcon
    rw [ht] at this
    exact this

end GlobalTheory.SerCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabelStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFunctionLabel_of_labelMap_label : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x)) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f := by
  first | exact @GlobalTheory.SerCmp.hasLabel_of_hasLabelO | exact GlobalTheory.SerCmp.hasLabel_of_hasLabelO | (intros; apply GlobalTheory.SerCmp.hasLabel_of_hasLabelO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmoduleEqSpanOfPowEqSpanPow
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory

theorem fractionalIdeal_eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

theorem submodule_eq_span_of_pow_eq_span_pow :
    ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K) (β : K) (h : ℕ),
      0 < h → β ≠ 0 → I.FG → I ^ h = Submodule.span (𝓞 K) {β ^ h} →
      I = Submodule.span (𝓞 K) {β} := by
  intro K _ _ I β h hh hβ hfg hpow
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hJI : (J : Submodule (𝓞 K) K) = I := rfl
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ β ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ
  have hp : J ^ h = FractionalIdeal.spanSingleton (𝓞 K)⁰ β ^ h := by
    rw [FractionalIdeal.spanSingleton_pow]
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton, hJI, hpow]
  have hJ : J ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne'] at hp
    exact pow_ne_zero h hB hp.symm
  have hJB : J = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    refine fractionalIdeal_eq_of_count_eq hJ hB fun v => ?_
    have := congrArg (FractionalIdeal.count K v) hp
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at this
    exact mul_left_cancel₀ (by exact_mod_cast hh.ne') this
  rw [← hJI, hJB, FractionalIdeal.coe_spanSingleton]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterList
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterList
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem glEquiv_transp_cancel {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {n : ℕ}
    (E : F ≃ Fin n) (x : GL (Fin n) (ZMod g)) :
    (glEquiv (ZMod g) E.symm).symm ((glEquiv (ZMod g) E).symm x) = x := by
  ext i j
  rw [Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv_symm]
  simp

theorem entry_eq {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {d : ℕ}
    (h : Fintype.card F = d) (V : FDRep ℂ (GL (Fin d) (ZMod g))) :
    (⟨Fintype.card F, fun x => (transp (Fintype.equivFin F)
      (transp ((finCongr h.symm).trans (Fintype.equivFin F).symm) V)).character x⟩ : GlobalTheory.GLq.Pc g) =
      ⟨d, fun x => V.character x⟩ := by
  generalize Fintype.equivFin F = E
  subst h
  refine Sigma.ext rfl (heq_of_eq (funext fun x => ?_))
  dsimp only
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp]
  congr 1
  have : (finCongr (rfl : Fintype.card F = Fintype.card F)).trans E.symm = E.symm := by ext; simp
  rw [this, glEquiv_transp_cancel]

theorem exists_blocks (s : ℕ) (d : Fin s → ℕ) (r : ℕ) (hr : ∑ c, d c = r) :
    ∃ b : Fin r → Fin s, ∀ c, Fintype.card {i // b i = c} = d c := by
  subst hr
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun c => ?_⟩
  rw [Fintype.card_congr ((finSigmaFinEquiv.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype c))]
  simp

end GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES in
theorem GlobalTheory.SerCmp.canonList_of_cuspidal_list : ∀ (g : ℕ) [Fact g.Prime] (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q := by
  intro g _ Q hQ
  have H : ∀ c : Fin Q.length, ∃ V : FDRep ℂ (GL (Fin (Q.get c).1) (ZMod g)), 1 ≤ (Q.get c).1 ∧
      CategoryTheory.Simple V ∧ IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = (Q.get c).2 x := by
    intro c
    obtain ⟨h1, V, h2⟩ := hQ _ (List.get_mem Q c)
    exact ⟨V, h1, h2⟩
  choose V hd hVs hVc hVch using H
  have hsum : ∑ c : Fin Q.length, (Q.get c).1 = GlobalTheory.GLq.degL Q := by
    rw [GlobalTheory.GLq.degL]
    rw [← Fin.sum_univ_getElem]
    exact Fintype.sum_equiv (finCongr (List.length_map _).symm) _ _ (fun c => by simp)
  obtain ⟨b, hcard⟩ := GlobalTheory.SerCmp.ListBlocks.exists_blocks Q.length (fun c => (Q.get c).1) _ hsum
  refine ⟨b, fun c => transp ((finCongr (hcard c).symm).trans (Fintype.equivFin _).symm) (V c), ?_, ?_, ?_⟩
  · intro c
    have : 0 < Fintype.card {i // b i = c} := by rw [hcard c]; exact hd c
    obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 this
    exact ⟨i, hi⟩
  · intro c
    exact ⟨Formalism.L2.PT.simple_transp _ (hVs c), Formalism.L2.PT.isCuspidal_transp _ (hVc c)⟩
  · apply List.ext_get (GlobalTheory.SerCmp.canonList_length _ _)
    intro n h1 h2
    simp only [GlobalTheory.SerCmp.canonList, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    rw [GlobalTheory.SerCmp.ListBlocks.entry_eq (hcard _) (V _)]
    have key : ∀ c, (⟨(Q.get c).1, fun x => (V c).character x⟩ : GlobalTheory.GLq.Pc g) = Q.get c := fun c =>
      Sigma.ext rfl (heq_of_eq (_root_.funext fun x => hVch c x))
    rw [key]
    simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterListStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blocks_of_cuspidal_character_list : ∀ (g : ℕ) [Fact g.Prime] (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q := by
  first | exact @GlobalTheory.SerCmp.canonList_of_cuspidal_list | exact GlobalTheory.SerCmp.canonList_of_cuspidal_list | (intros; apply GlobalTheory.SerCmp.canonList_of_cuspidal_list <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimple
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

theorem zOf_character {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) :
    GlobalTheory.GLq.zOf τ.character = Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ := by
  unfold GlobalTheory.GLq.zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  rw [FDRep.char_one]
  rfl

theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (GlobalTheory.GLq.zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  classical
  unfold GlobalTheory.GLq.zOf
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem character_eq_zero_of_finrank {G : Type} [Group G] (τ : FDRep ℂ G)
    (h : Module.finrank ℂ τ.V = 0) (x : G) : τ.character x = 0 := by
  have : Subsingleton τ.V := Module.finrank_zero_iff.mp h
  unfold FDRep.character
  rw [Subsingleton.elim (τ.ρ x) 0]
  exact map_zero _

theorem character_eq_of_zOf_eq {G : Type} [Group G] [Fintype G] (σ τ : FDRep ℂ G)
    (h : GlobalTheory.GLq.zOf σ.character = GlobalTheory.GLq.zOf τ.character) : σ.character = τ.character := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy : ∀ y : G, σ.character 1 * σ.character y = τ.character 1 * τ.character y := by
    intro y
    have h1 := zOf_coeff σ.character y⁻¹
    have h2 := zOf_coeff τ.character y⁻¹
    rw [h, h2, inv_inv] at h1
    field_simp at h1
    first | exact h1.symm | linear_combination (-1 : ℂ) * h1
  have h1 := hy 1
  rw [FDRep.char_one, FDRep.char_one] at h1
  have h2 : Module.finrank ℂ σ.V * Module.finrank ℂ σ.V = Module.finrank ℂ τ.V * Module.finrank ℂ τ.V := by
    exact_mod_cast h1
  have h3 : Module.finrank ℂ σ.V = Module.finrank ℂ τ.V := Nat.mul_self_inj.mp h2
  funext y
  by_cases h0 : Module.finrank ℂ τ.V = 0
  · rw [character_eq_zero_of_finrank τ h0, character_eq_zero_of_finrank σ (h3.trans h0)]
  · have h4 := hy y
    rw [FDRep.char_one, FDRep.char_one, h3] at h4
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr h0) h4

theorem finsum_zOf_eq_finsum_zIdem {G : Type} [Group G] [Fintype G] (Q : (G → ℂ) → Prop) :
    ∑ᶠ χ ∈ {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}, GlobalTheory.GLq.zOf χ =
      ∑ᶠ (z : MonoidAlgebra ℂ G) (_ : ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧
        Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character), z := by
  have hinj : Set.InjOn (GlobalTheory.GLq.zOf (G := G)) {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ} := by
    rintro a ⟨⟨V, -, hV⟩, -⟩ b ⟨⟨U, -, hU⟩, -⟩ hab
    obtain rfl : V.character = a := funext hV
    obtain rfl : U.character = b := funext hU
    exact character_eq_of_zOf_eq V U hab
  rw [← finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) hinj]
  refine finsum_congr fun z => ?_
  have hiff : (z ∈ GlobalTheory.GLq.zOf '' {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}) =
      ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character := by
    apply propext
    constructor
    · rintro ⟨a, ⟨⟨V, hs, hV⟩, hQ⟩, rfl⟩
      obtain rfl : V.character = a := funext hV
      exact ⟨V, hs, (zOf_character V).symm, hQ⟩
    · rintro ⟨V, hs, rfl, hQ⟩
      exact ⟨V.character, ⟨⟨V, hs, fun _ => rfl⟩, hQ⟩, zOf_character V⟩
  rw [hiff]

end GlobalTheory.SerCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimpleStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple : ∀ {G : Type} [Group G] [Fintype G] (Q : (G → ℂ) → Prop), ∑ᶠ χ ∈ {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}, GlobalTheory.GLq.zOf χ = ∑ᶠ (z : MonoidAlgebra ℂ G) (_ : ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character), z := by
  first | exact @GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem | exact GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem | (intros; apply GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderSmulOfFix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.FrobeniusOrbits
open scoped Pointwise

namespace GlobalTheory.PlaceOverPair

theorem under_smul_of_fix {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra K E]
    (σ : E ≃ₐ[ℚ] E) (h : ∀ x : K, σ (algebraMap K E x) = algebraMap K E x) (I : Ideal (𝓞 E)) :
    (σ • I).under (𝓞 K) = I.under (𝓞 K) := by
  ext x
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap (𝓞 K) (𝓞 E) x = algebraMap (𝓞 K) (𝓞 E) x := by
    rw [inv_smul_eq_iff]
    apply Subtype.val_injective
    exact (h x).symm
  rw [this]

theorem exists_over {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra K E]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v := by
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem exists_smul_eq {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime] (hP : (p : 𝓞 E) ∈ P) (hQ : (p : 𝓞 E) ∈ Q) :
    ∃ σ : E ≃ₐ[ℚ] E, σ • P = Q := by
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  have key : ∀ (I : Ideal (𝓞 E)) [I.IsPrime], (p : 𝓞 E) ∈ I → I.LiesOver (Ideal.span {(p : ℤ)}) := by
    intro I _ hI
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hI
  haveI := key P hP
  haveI := key Q hQ
  exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_sqrt : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem fix_of_sqrt (σ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = H.sqrtMinusD) (x : H.K) :
    σ (algebraMap H.K H.E x) = algebraMap H.K H.E x := by
  have : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply IntermediateField.adjoin_simple_le_iff.2
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ H.sqrtMinusD := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (this x.2) σ (Subgroup.mem_zpowers σ)

theorem exists_over_both {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K)) (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 H.E), w.under (𝓞 H.F) = v ∧ w.under (𝓞 H.K) = 𝔭 := by
  haveI := H.hostE_isGalois
  obtain ⟨w, rfl⟩ := exists_over (E := H.E) v
  obtain ⟨u, rfl⟩ := exists_over (E := H.E) 𝔭
  have hu : (p : 𝓞 H.E) ∈ u.asIdeal := by
    have : algebraMap (𝓞 H.K) (𝓞 H.E) (p : 𝓞 H.K) ∈ u.asIdeal := h𝔭
    rwa [map_natCast] at this
  have hw : (p : 𝓞 H.E) ∈ w.asIdeal := by
    have : algebraMap (𝓞 H.F) (𝓞 H.E) (p : 𝓞 H.F) ∈ w.asIdeal := hv
    rwa [map_natCast] at this
  haveI := u.isPrime
  haveI := w.isPrime
  obtain ⟨σ, hσ⟩ := exists_smul_eq hp u.asIdeal w.asIdeal hu hw
  have hs : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, sqrt_sq, map_neg, map_natCast]
  rcases hs with hs | hs
  · refine ⟨w, rfl, HeightOneSpectrum.ext ?_⟩
    show w.asIdeal.under _ = u.asIdeal.under _
    rw [← hσ]
    exact under_smul_of_fix σ (fix_of_sqrt H σ hs) _
  · have hne : H.conj • w.asIdeal ≠ ⊥ := by
      intro h
      apply w.ne_bot
      rw [← inv_smul_smul H.conj w.asIdeal, h, Ideal.smul_bot]
    refine ⟨⟨H.conj • w.asIdeal, inferInstance, hne⟩, HeightOneSpectrum.ext ?_, HeightOneSpectrum.ext ?_⟩
    · exact under_smul_of_fix H.conj (fun x => (H.conjE_mem_hostF_iff _).1 x.2) _
    · show (H.conj • w.asIdeal).under _ = u.asIdeal.under _
      rw [← hσ, smul_smul]
      refine under_smul_of_fix _ (fix_of_sqrt H _ ?_) _
      rw [AlgEquiv.mul_apply, hs, map_neg, conj_sqrt, neg_neg]

end GlobalTheory.PlaceOverPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinear
open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.DefLatBC

section Csd

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem csum_coords (u v : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm u : S.Cl → S.V) (S.basis.equivFun.symm v : S.Cl → S.V) =
      ∑ i, ∑ j, star (u i) * S.H i j * v j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, CSD.csum, CSD.H,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem mem_nabLat_iff (x : Fin S.dim → K) :
    x ∈ S.nabLat ↔ ∀ c, (S.basis.equivFun.symm x : S.Cl → S.V) c ∈ S.Nab c := by
  simp [CSD.nabLat, valLatF, Submodule.mem_pi, CSD.I]

end Csd

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

theorem forms_of_semilinear (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms)
    (hsm : ∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f)
    (hli : LinearIndependent K' (fun k => L (B.S.basis k)))
    (hsp : ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)))
    (hcs : ∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g))
    (hact : ∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f))
    (hnab : ∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔
      f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}))
    (hZ : Z' = Submodule.span K' (L '' (Z : Set B.S.Forms))) :
    ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
      Cᴴ * B'.S.H * C = B.S.H.map φ ∧
      (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
      B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
      B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  classical
  set C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := Matrix.of fun i k => B'.S.basis.repr (L (B.S.basis k)) i with hCdef

  have hcol : ∀ k, B'.S.basis.equivFun.symm (fun i => C i k) = L (B.S.basis k) := by
    intro k
    rw [LinearEquiv.symm_apply_eq]
    ext i
    simp [hCdef]
  have hC : ∀ y, C *ᵥ y = B'.S.basis.equivFun (∑ k, y k • L (B.S.basis k)) := by
    intro y
    ext i
    simp [hCdef, Matrix.mulVec, dotProduct, mul_comm]
  have hLsum : ∀ x : Fin B.S.dim → K, L (B.S.basis.equivFun.symm x) = ∑ k, φ (x k) • L (B.S.basis k) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Basis.equivFun_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _
  have hT : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) = B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x)) := by
    intro x
    rw [hC, hLsum]
  have hTf : ∀ f : B.S.Forms, C *ᵥ (fun k => φ (B.S.basis.repr f k)) = ⇑(B'.S.basis.repr (L f)) := by
    intro f
    have := hT (B.S.basis.equivFun f)
    simpa using this
  refine ⟨C, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro y₁ y₂ h
    have h0 : ∑ k, (y₁ - y₂) k • L (B.S.basis k) = 0 := by
      have : C *ᵥ (y₁ - y₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
      rw [hC] at this
      exact (LinearEquiv.map_eq_zero_iff _).mp this
    have := Fintype.linearIndependent_iff.mp hli _ h0
    funext k
    exact sub_eq_zero.mp (this k)
  ·
    intro y
    have hmem : B'.S.basis.equivFun.symm y ∈ Submodule.span K' (Set.range fun k => L (B.S.basis k)) := hsp trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K').mp hmem
    refine ⟨c, ?_⟩
    rw [hC, hc, LinearEquiv.apply_symm_apply]
  ·
    ext a b
    have h1 := hcs (B.S.basis a) (B.S.basis b)
    rw [← hcol a, ← hcol b, csum_coords] at h1
    simp only [Matrix.map_apply, CSD.H, Matrix.of_apply] at h1 ⊢
    rw [← h1, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Matrix.of_apply]
  ·
    intro g
    have hv : ∀ f : B.S.Forms, (B'.S.actMat B'.r (e g) * C) *ᵥ (fun k => φ (B.S.basis.repr f k)) =
        (C * (B.S.actMat B.r g).map φ) *ᵥ (fun k => φ (B.S.basis.repr f k)) := by
      intro f
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTf]
      have h2 : (B.S.actMat B.r g).map φ *ᵥ (fun k => φ (B.S.basis.repr f k)) =
          fun k => φ (B.S.basis.repr (B.r g f) k) := by
        funext k
        rw [show (fun k => φ (B.S.basis.repr f k)) = φ ∘ (B.S.basis.repr f) from rfl, ← RingHom.map_mulVec φ]
        simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr]
      rw [h2, hTf]
      simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr, hact]
    ext i k
    have hs : (fun j => φ (B.S.basis.repr (B.S.basis k) j)) = Pi.single k 1 := by
      funext j
      by_cases h : j = k
      · subst h; simp
      · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
    have := congrFun (hv (B.S.basis k)) i
    rw [hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    exact this
  ·
    let eO := (B'.S.basis.equivFun).restrictScalars (𝓞 K')
    have himg : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) =
        eO '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨L (B.S.basis.equivFun.symm x), ⟨_, (mem_nabLat_iff _ _).mp hx, rfl⟩, (hT x).symm⟩
      · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        refine ⟨B.S.basis.equivFun f, (mem_nabLat_iff _ _).mpr (by simpa using hf), ?_⟩
        show C *ᵥ (fun k => φ (B.S.basis.equivFun f k)) = _
        rw [hT, LinearEquiv.symm_apply_apply]
        rfl
    ext y
    rw [himg, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv, ← hnab, mem_nabLat_iff]
    rfl
  ·
    rw [hZ, BlockDat.coord, BlockDat.coord, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    refine Set.image_congr fun f _ => ?_
    rw [hT]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.DefLatBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinearStatement
open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_of_semilinear_alt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type} (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms),
  (∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f) →
  LinearIndependent K' (fun k => L (B.S.basis k)) → ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)) →
  (∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g)) →
  (∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f)) →
  (∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔ f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c})) →
  Z' = Submodule.span K' (L '' (Z : Set B.S.Forms)) →
  ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
    Cᴴ * B'.S.H * C = B.S.H.map φ ∧
    (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
    B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
    B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | exact GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | (intros; apply GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProd
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProd
open IsLocalRing TensorProduct

namespace GlobalTheory.CompletionFactor

theorem exists_ringEquiv_prod_of_isIdempotentElem {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) :
    ∃ ε : S ≃+* (S ⧸ Ideal.span {1 - e}) × (S ⧸ Ideal.span {e}),
      ∀ x, (ε x).1 = Ideal.Quotient.mk _ x := by
  have hc : IsCoprime (Ideal.span {1 - e}) (Ideal.span {e} : Ideal S) := by
    rw [Ideal.isCoprime_span_singleton_iff]
    exact ⟨1, 1, by ring⟩
  have hb : (⊥ : Ideal S) = Ideal.span {1 - e} ⊓ Ideal.span {e} := by
    rw [← Ideal.mul_eq_inf_of_isCoprime hc, Ideal.span_singleton_mul_span_singleton, sub_mul,
      one_mul, he.eq, sub_self, Ideal.span_singleton_zero]
  refine ⟨(RingEquiv.quotientBot S).symm.trans ((Ideal.quotEquivOfEq hb).trans
    (Ideal.quotientInfEquivQuotientProd _ _ hc)), fun x => ?_⟩
  rfl

theorem exists_local_factor {B S D : Type*} [CommRing B] [HenselianLocalRing B] [CommRing S]
    [Algebra B S] [Module.Finite B S] [CommRing D] [IsLocalRing D] (φ : S →+* D)
    (hφ : maximalIdeal B ≤ (maximalIdeal D).comap (φ.comp (algebraMap B S))) :
    ∃ e : S, IsIdempotentElem e ∧ IsLocalRing (S ⧸ Ideal.span {1 - e}) ∧
      ∃ ψ : (S ⧸ Ideal.span {1 - e}) →+* D, IsLocalHom ψ ∧
        ∀ x, ψ (Ideal.Quotient.mk _ x) = φ x := by
  have hq : ((maximalIdeal D).comap φ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap B S)
      (fun x => Algebra.IsIntegral.isIntegral x)
    rw [Ideal.comap_comap, ← (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hφ]
    infer_instance
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_of_henselian B ((maximalIdeal D).comap φ)
  have hl := isLocalRing_quotient_one_sub he _ H
  have h1 : φ e = 1 := by
    refine (IsIdempotentElem.iff_eq_one_of_isUnit ?_).1 (he.map φ)
    have := (H _ hq).2 rfl
    rwa [Ideal.mem_comap, notMem_maximalIdeal] at this
  have h0 : ∀ a ∈ Ideal.span {1 - e}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [h1]
  refine ⟨e, he, hl, Ideal.Quotient.lift _ φ h0, ⟨fun r hr => ?_⟩, fun x => rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {1 - e}))
    Ideal.Quotient.mk_surjective (K := maximalIdeal _)
  have h : (maximalIdeal _).comap (Ideal.Quotient.mk (Ideal.span {1 - e})) =
      (maximalIdeal D).comap φ := by
    rw [← H _ hm, ← one_sub_mem_iff_notMem_of_isIdempotentElem he, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    exact zero_mem _
  rw [← notMem_maximalIdeal, ← Ideal.mem_comap, h, Ideal.mem_comap, notMem_maximalIdeal]
  exact hr

theorem bijective_of_complete_quotient {T C A R : Type*} [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] [CommRing C] [Algebra T C] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (h𝔫 : 𝔫.comap (algebraMap T C) = maximalIdeal T)
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (π : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+* R) (hπ : Function.Surjective π)
    (ψ : R →+* AdicCompletion (maximalIdeal A) A) [IsLocalHom ψ]
    (hψ : ∀ c : C, ψ (π (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c)) :
    Function.Bijective ψ := by
  let β₀ : C →+* R := π.comp (Algebra.TensorProduct.includeRight (R := T)).toRingHom
  have hβ₀ : ∀ c, β₀ c = π (1 ⊗ₜ[T] c) := fun c => rfl
  have hu : ∀ s : 𝔫.primeCompl, IsUnit (β₀ s) := fun s => by
    refine IsUnit.of_map ψ _ ?_
    rw [hβ₀, hψ]
    exact (IsLocalization.map_units A s).map _
  let β : A →+* R := IsLocalization.lift hu
  have hβ : ∀ c, β (algebraMap C A c) = π (1 ⊗ₜ[T] c) := fun c => IsLocalization.lift_eq hu c
  have hψβ : ψ.comp β = algebraMap A (AdicCompletion (maximalIdeal A) A) := by
    refine IsLocalization.ringHom_ext 𝔫.primeCompl (RingHom.ext fun c => ?_)
    simp only [RingHom.comp_apply, hβ, hψ]
  have hβm : ∀ a ∈ maximalIdeal A, β a ∈ maximalIdeal R := fun a ha => by
    by_contra h
    rw [notMem_maximalIdeal] at h
    have h2 : IsUnit ((ψ.comp β) a) := h.map ψ
    rw [hψβ] at h2
    exact notMem_maximalIdeal.2 (IsUnit.of_map _ _ h2) ha
  obtain ⟨χ, hχ, -⟩ := exists_extend_adicCompletion β (maximalIdeal A) (maximalIdeal R) (k := 1)
    (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hβm)
  have h₁ : ψ.comp χ = RingHom.id _ := by
    refine adicCompletion_ringHom_ext (maximalIdeal A).fg_of_isNoetherianRing
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (k := 1) ?_ ?_
    · rw [pow_one, RingHom.comp_assoc, hχ, hψβ, AdicCompletion.maximalIdeal_eq_map]
    · rw [RingHom.comp_assoc, hχ, hψβ, RingHom.id_comp]
  have hC : ∀ c : C, χ (ψ (π (1 ⊗ₜ[T] c))) = π (1 ⊗ₜ[T] c) := fun c => by
    rw [hψ, ← RingHom.comp_apply, hχ, hβ]
  have hT : ∀ t : T, (algebraMap T (AdicCompletion (maximalIdeal T) T) t) ⊗ₜ[T] (1 : C) =
      1 ⊗ₜ[T] algebraMap T C t := fun t => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]
  have hL : π.comp Algebra.TensorProduct.includeLeftRingHom =
      ((χ.comp ψ).comp π).comp Algebra.TensorProduct.includeLeftRingHom := by
    refine adicCompletion_ringHom_ext (maximalIdeal T).fg_of_isNoetherianRing
      (maximalIdeal R) (k := 1) ?_ ?_
    · rw [pow_one, Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply, hT, ← hβ]
      apply hβm
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
      exact ht
    · refine RingHom.ext fun t => ?_
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hT, hC]
  have h₂ : ∀ x, χ (ψ (π x)) = π x := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a c =>
      have e1 : a ⊗ₜ[T] c = (a ⊗ₜ[T] (1 : C)) * (1 ⊗ₜ[T] c) := by simp
      have e2 : π (a ⊗ₜ[T] (1 : C)) = χ (ψ (π (a ⊗ₜ[T] (1 : C)))) := congr($hL a)
      rw [e1, map_mul, map_mul, map_mul, ← e2, hC]
  refine Function.bijective_iff_has_inverse.2 ⟨χ, fun r => ?_, fun y => congr($h₁ y)⟩
  obtain ⟨x, rfl⟩ := hπ r
  exact h₂ x

theorem exists_ringEquiv_completion_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by
  intro T C A _ _ _ _ _ _ _ _ _ 𝔫 _ _ h𝔫
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite T C
  have hAn : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔫.primeCompl A hCn
  have hTn := AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  let g : C →+* AdicCompletion (maximalIdeal A) A := (algebraMap A _).comp (algebraMap C A)
  have hg : maximalIdeal T ≤ (maximalIdeal _).comap (g.comp (algebraMap T C)) := by
    intro t ht
    rw [Ideal.mem_comap, AdicCompletion.maximalIdeal_eq_map]
    refine Ideal.mem_map_of_mem _ (?_ : algebraMap C A (algebraMap T C t) ∈ maximalIdeal A)
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
    exact ht
  obtain ⟨α, hα, -⟩ := exists_extend_adicCompletion (g.comp (algebraMap T C)) (maximalIdeal T)
    (maximalIdeal _) (k := 1) (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hg)
  obtain ⟨φ, hφa, hφc⟩ : ∃ φ : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+*
      AdicCompletion (maximalIdeal A) A,
      φ.comp (algebraMap (AdicCompletion (maximalIdeal T) T) _) = α ∧
        ∀ c, φ (1 ⊗ₜ[T] c) = g c := by
    letI : Algebra T (AdicCompletion (maximalIdeal A) A) := (g.comp (algebraMap T C)).toAlgebra
    let α' : AdicCompletion (maximalIdeal T) T →ₐ[T] AdicCompletion (maximalIdeal A) A :=
      { α with commutes' := fun t => congr($hα t) }
    let g' : C →ₐ[T] AdicCompletion (maximalIdeal A) A := { g with commutes' := fun t => rfl }
    refine ⟨(Algebra.TensorProduct.lift α' g' fun _ _ => .all _ _).toRingHom,
      RingHom.ext fun a => ?_, fun c => ?_⟩
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (a ⊗ₜ[T] 1) = α' a
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (1 ⊗ₜ[T] c) = g' c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hH := henselianLocalRing_of_henselianRing (AdicCompletion (maximalIdeal T) T)
  obtain ⟨e, he, hl, ψ, hψl, hψ⟩ := exists_local_factor (B := AdicCompletion (maximalIdeal T) T) φ
    (by
      rw [hφa, AdicCompletion.maximalIdeal_eq_map (R := T), Ideal.map_le_iff_le_comap,
        Ideal.comap_comap, hα]
      exact hg)
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal T) T)
    ((AdicCompletion (maximalIdeal T) T ⊗[T] C) ⧸ Ideal.span {1 - e})
  have hψc : ∀ c : C, ψ (Ideal.Quotient.mk _ (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := fun c => by
    rw [hψ, hφc]; rfl
  have hb := bijective_of_complete_quotient 𝔫 h𝔫 _ Ideal.Quotient.mk_surjective ψ hψc
  obtain ⟨ε, hε⟩ := exists_ringEquiv_prod_of_isIdempotentElem he
  refine ⟨_, inferInstance, ε.trans ((RingEquiv.ofBijective ψ hb).prodCongr (RingEquiv.refl _)),
    fun c => ?_⟩
  rw [← hψc, ← hε]
  rfl

end GlobalTheory.CompletionFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProdStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by
  first | exact @GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod | exact GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod | (intros; apply GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.CrysCoef

open Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {L L' : Type} [Field L] [Algebra Qp L] [Field L'] [Algebra Qp L']

theorem isCrys_mapM [Algebra L L'] [IsScalarTower Qp L L'] [FiniteDimensional L L']
    {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) L) (h : IsCrys PD (matRep M)) :
    IsCrys PD (matRep (mapM (algebraMap L L') M)) := by
  let e := Module.finBasis L L'
  let E : (Fin k → L') ≃ₗ[L] (Fin (finrank L L') → Fin k → L) :=
    { toFun := fun v j i => e.repr (v i) j
      invFun := fun w i => e.equivFun.symm fun j => w j i
      map_add' := fun x y => by funext j i; simp
      map_smul' := fun c x => by funext j i; simp
      left_inv := fun v => by
        funext i
        exact e.equivFun.symm_apply_apply (v i)
      right_inv := fun w => by
        funext j i
        exact congrFun (e.equivFun.apply_symm_apply fun j => w j i) j }
  have : Nonempty (Fin (finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine GlobalTheory.CoeffExt.isCrys_ext PD (E := E) (fun g x j => ?_) (Fintype.card_fin _).symm h
  funext i
  change e.repr (∑ a, algebraMap L L' (M g i a) * x a) j = ∑ a, M g i a * e.repr (x a) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← Algebra.smul_def, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]

end Generic

theorem isCrys_inclusion (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L L' : FinExt l) (h : L.1 ≤ L'.1) (k : ℕ)
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥L.1) (hM : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep (mapM (IntermediateField.inclusion h).toRingHom M)) := by
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 ↥L'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion h).commutes x).symm
  haveI := L'.2
  haveI : FiniteDimensional ↥L.1 ↥L'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  exact isCrys_mapM (P.PD K) M hM

end GlobalTheory.CrysCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlace
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem tameAnyFix_map_primeToPart {M K : Type} [Monoid M] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l]
    (ι : M →* K) (x : M) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  have hl : l.Prime := Fact.out
  unfold Formalism.CyclotomicNorms.primeToPart
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0]
    have e : ∀ n : ℕ, n = 0 → (((1 : ℕ) : ZMod n)⁻¹).val = 1 := by
      intro n hn
      subst hn
      rw [Nat.cast_one, ZMod.inv_one]
      rfl
    have e0 : l ^ (Nat.factorization 0) l = 1 := by simp
    rw [e0, e _ (by simp)]
    simp
  · set a := (orderOf x).factorization l with ha
    set m := orderOf x / l ^ a with hm
    have hmul : l ^ a * m = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : Nat.Coprime (l ^ a) m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
    have hmpos : 0 < m := Nat.ordCompl_pos l hpos.ne'
    haveI : NeZero m := ⟨hmpos.ne'⟩
    have h1 : (ι x ^ m) ^ l ^ a = 1 ^ l ^ a := by
      rw [← pow_mul, mul_comm, hmul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
    have h2 : ι x ^ m = 1 := by
      have := iterateFrobenius_inj K l a
      exact this (by simpa [iterateFrobenius_def] using h1)
    have h3 : l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast [ZMod.natCast_zmod_val]
      have := ZMod.coe_mul_inv_eq_one (l ^ a) hcop
      simpa using this
    rw [map_pow]
    have h4 : ι x ^ (l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val) = ι x ^ 1 := by
      rw [pow_eq_pow_mod _ h2, h3, ← pow_eq_pow_mod _ h2]
    rw [h4, pow_one]

theorem tameAnyFix_isoLoc (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem tameAnyFix_not_over (D : D7) (i : D.nd.Loc) (k : Fin 2) (h : D.nd.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
  intro hl
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hl' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := hl
  have hc : Nat.Coprime (D.nd.l i) (D.host.g k) := (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 h
  have hc' : IsCoprime ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hc
  obtain ⟨a, b, hab⟩ := hc'
  apply (D.naut.plGw k v).isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ hg)

end GlobalTheory.TypeLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.JumpDictRec

open GlobalTheory.JumpDictionaryFoundation

theorem main : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D →
    GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool),
    (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ,
      (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i),
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧
        (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) =
          {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  intro D hW hB hG hC i τ ρ b hτ
  have hs := shift_embOver D ρ b
  refine ⟨shift D (embOver D ρ b), ?_, fun w hw => ?_⟩
  · apply Multiset.map_injective (f := fun q : ℚ => (q : ℂ)) Rat.cast_injective
    rw [Multiset.map_map, Multiset.map_map]
    have e0 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
    rw [hτ] at e0
    have e1 : (D.naut.locAutHodgeTateWeightsLevelZero i τ).map ((fun q : ℚ => (q : ℂ)) ∘ fun n : ℤ => (n : ℚ)) =
        (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ)) :=
      Multiset.map_congr rfl fun n _ => by simp
    rw [e1, e0]
    cases b
    · rw [(hW i ρ).1, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
    · rw [(hW i ρ).2, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
  · have ht : 1 ≤ D.R.t := by
      obtain ⟨u, v, -, hv, -⟩ := exists_halves D.R
      omega
    have hz : ∀ φ, ∃ z : ℤ, (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) φ).map
        (· + (blockExp D 1 : ℂ)) = {(z : ℂ)} := by
      intro φ
      obtain ⟨ρ', b', rfl⟩ := exists_embOver D φ
      obtain ⟨a, ha⟩ := firstJump_int D i ρ' b'
      refine ⟨-a, ?_⟩
      rw [inf_block D hB, ha]
      push_cast
      simp
    choose z hz using hz
    obtain ⟨r, hrc, hrf, hrd, hrj⟩ := hG i _ _ z hz
    have hr : r = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
      have h := eq_of_frob D.nd hC i
        (a := fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)
        (b := fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i))
        ((continuous_apply 0).comp ((continuous_apply 0).comp hrc))
        ((continuous_iotaOQ D i w hw).comp (D.nd.chi_cont i 1)) fun v hv B σ hB' hσ => by
          have e1 := hrf v hv.2.1 (D.naut.chi_mu i v hv).1 B σ hB' hσ
          rw [chi_frob D i 1 le_rfl ht v hv B σ hB' hσ, Multiset.singleton_inj] at e1
          exact ((D.naut.iotaQC i).injective e1).symm
      ext g a c
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine (congrFun h g).trans ?_
      rw [← chiGL_apply D i 1 g 0 0]
      rfl
    subst hr
    refine ⟨hrd w hw, ?_⟩
    have hq : firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1) = ((-z (embOver D ρ b) : ℤ) : ℚ) := by
      have e := (inf_block D hB i 1 ρ b).symm.trans (hz _)
      rw [Multiset.singleton_inj] at e
      have e' : -(firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1)) = (z (embOver D ρ b) : ℚ) := by exact_mod_cast e
      rw [Int.cast_neg, ← e', neg_neg]
    rw [hrj, hτ, Multiset.map_singleton, ← hq, hs]
    congr 1
    cases b
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring

end GlobalTheory.JumpDictRec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D → GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool), (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ, (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧ (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) = {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  first | exact @GlobalTheory.JumpDictRec.main | exact GlobalTheory.JumpDictRec.main | (intros; apply GlobalTheory.JumpDictRec.main <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.BridgeAdmDict

theorem sz_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.liftIdx D i) := by
  have := D.nd.j_range i
  unfold AdmissibleParameterJ.sz
  rw [dite_eq_left (by omega)]
  rfl

theorem PPm_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.PPm D (D.nd.j i) ρ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP D i ρ := by
  unfold AdmissibleParameterJ.PPm GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.param GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.run
  rw [sz_eq, Finset.range_val]

theorem mem_placesOver (D : D7) (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : InducesW D.nd i τ₀ w) :
    w ∈ placesOver D.host.E (D.nd.l i) := by
  have h1 := (h ((D.nd.l i : ℕ) : 𝓞 D.host.E)).1
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  apply h1
  have e : τ₀ (((D.nd.l i : ℕ) : 𝓞 D.host.E) : D.host.E) = algebraMap ℚ_[D.nd.l i] (PadicAlgCl (D.nd.l i)) (D.nd.l i : ℚ_[D.nd.l i]) := by
    simp
  rw [e, PadicAlgCl.norm_extends]
  simpa using (Padic.norm_p_lt_one (p := D.nd.l i))

end GlobalTheory.BridgeAdmDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.PointEigen

theorem genAt_iff_splitOut (D : D7) (i : D.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.nd.l i) (D.nd.Q i) v k ↔ (SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have hS : v ∈ D.nd.S i ↔ v ∈ placesS D (D.nd.l i) := by
    rw [D.nd.S_def]; rfl
  unfold SplitOut GenAt
  rw [hS]
  tauto

theorem ptSys_mem_eigSet : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ (i : D.nd.Loc) (x : D.nd.X i),
    ptSys D i x ∈ EigSet (M.loc i) (D.nd.l i) (D.nd.Q i) := by
  intro D M A i x
  refine ⟨fun v k h => ?_, ?_⟩
  · simp only [ptSys, if_neg h]
  · obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hw, k1, k2⟩ := (genAt_iff_splitOut D i v k).1 hg
    simp only [ptSys, if_pos hg]
    exact (A.ptV i P x).1 hP v k s ϖ hw hc hu k1 k2 y hy

end GlobalTheory.PointEigen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.UnramifiedChar

theorem norm_eq_one_of_compact {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k]
    (d : Γ →* k) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle : ∀ g, ‖d g‖ ≤ 1 := by
    intro g
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have : ‖d (g ^ n)‖ ≤ C := hC ⟨g ^ n, rfl⟩
    rw [map_pow, norm_pow] at this
    linarith
  have h1 : ‖d g‖ * ‖d g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have := hle g; have := hle g⁻¹; have := norm_nonneg (d g); have := norm_nonneg (d g⁻¹)
  nlinarith

variable {l : ℕ} [Fact l.Prime]

theorem val_mem_OL (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) (g : ↥(GK K)) :
    ((μ g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL := by
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  let d : ↥(GK K) →* Om l :=
    ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →* Om l).comp ((Units.coeHom ↥LL.1).comp μ)
  have hd : Continuous d := continuous_subtype_val.comp hμ
  exact (GlobalTheory.Per.Val.mem_OL_iff LL _).2 (norm_eq_one_of_compact d hd g).le

def unitLat (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := ↥LL.1
  ρ := charRep μ
  cont := fun x => hμ.mul continuous_const
  L := GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.charLat Subtype.val_injective μ fun g => ⟨⟨_, val_mem_OL K LL μ hμ g⟩, rfl⟩

theorem isCrys_and_multV_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  intro l _ P AI T K LL μ hμ hI
  obtain ⟨hc, hj⟩ := GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero l P AI T K LL (unitLat K LL μ hμ)
    (fun g hg (x : ↥LL.1) => by
      change ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x = x
      rw [hI g hg, Units.val_one, one_mul])
  change IsCrys (P.PD K) (charRep μ) at hc
  change ∀ τ a, IsJumpV (P.PD K) (charRep μ) τ a → a = 0 at hj
  refine ⟨hc, fun τ b => ?_⟩
  obtain ⟨hcomp, -⟩ := GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)
  obtain ⟨hfd, -, hdr⟩ := hcomp τ
  haveI := hfd
  set_option synthInstance.maxHeartbeats 200000 in
  have hdim : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdr (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL ↥LL.1 (charRep μ) hc).1, finrank_self]
  have hnj : ∀ a, a ≠ 0 → multV (P.PD K) (charRep μ) τ a = 0 := fun a ha =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump (P.PD K) (charRep μ) τ a (fun h => ha (hj τ a h))
  split_ifs with hb
  · subst hb
    obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (charRep μ) τ
    obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (charRep μ) τ
    have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) (charRep μ) τ (min lo 0) (max hi 1) (by omega)
    rw [hlo _ (min_le_left _ _), hhi _ (le_max_left _ _), finrank_bot, Nat.cast_zero, sub_zero, hdim,
      Finset.sum_eq_single (0 : ℤ) (fun a _ ha => hnj a ha)
        (fun h => absurd (Finset.mem_Ico.2 ⟨min_le_right _ _, by omega⟩) h)] at hsum
    exact_mod_cast hsum
  · exact hnj b hb

end GlobalTheory.UnramifiedChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  first | exact @GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | exact GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | (intros; apply GlobalTheory.UnramifiedChar.isCrys_and_multV_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateDualFil

section Linear

variable {G : Type} [Group G] {LL : Type} [Field LL] (L : Type) [Field L] [Algebra LL L]
  {V : Type} [AddCommGroup V] [Module LL V] {V' : Type} [AddCommGroup V'] [Module LL V']

def extRep (ρ : Representation LL G V) : Representation L G (L ⊗[LL] V) where
  toFun g := (ρ g).baseChange L
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem extRep_tmul (ρ : Representation LL G V) (g : G) (a : L) (x : V) :
    extRep L ρ g (a ⊗ₜ[LL] x) = a ⊗ₜ[LL] ρ g x := rfl

theorem exists_ext_pairing [FiniteDimensional LL V] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (hm : Function.Bijective m.flip) :
    ∃ m' : L ⊗[LL] V →ₗ[L] L ⊗[LL] V' →ₗ[L] L, Function.Bijective m' ∧
      ∀ (a b : L) x y, m' (a ⊗ₜ[LL] x) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m x y) := by
  obtain ⟨v, w, hvw⟩ := GlobalTheory.DRFil.exists_dual_bases m hm
  let v' := Algebra.TensorProduct.basis L v
  let w' := Algebra.TensorProduct.basis L w
  let e := v'.equiv w'.dualBasis (Equiv.refl _)
  refine ⟨e.toLinearMap, e.bijective, fun a b x y => ?_⟩
  have h1 : ∀ i, e.toLinearMap (a ⊗ₜ[LL] v i) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m (v i) y) := by
    intro i
    have h2 : a ⊗ₜ[LL] v i = a • v' i := by
      simp [v', Algebra.TensorProduct.basis_apply, smul_tmul']
    have h3 : m (v i) y = w.repr y i := by
      conv_lhs => rw [← w.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hvw, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [h2, map_smul, h3]
    simp only [e, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, LinearMap.smul_apply,
      Basis.dualBasis_apply, w', Algebra.TensorProduct.basis_repr_tmul]
    simp [mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← v.sum_repr x, tmul_sum, map_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h4 : a ⊗ₜ[LL] (v.repr x i • v i) = algebraMap LL L (v.repr x i) • (a ⊗ₜ[LL] v i) := by
    rw [algebraMap_smul, tmul_smul]
  rw [h4, map_smul, LinearMap.smul_apply, h1, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    map_mul]
  ring

end Linear

theorem exists_eq_bot {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ b : ℤ, ∀ a, b ≤ a → F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional k (F a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ∀ a, finrank k (F b) ≤ finrank k (F a) :=
    ⟨Function.argmin fun a => finrank k (F a), fun a => Function.argmin_le (fun a => finrank k (F a)) a⟩
  have h1 : ∀ a, b ≤ a → F a = F b := fun a ha => Submodule.eq_of_le_of_finrank_le (hF ha) (hb a)
  refine ⟨b, fun a ha => ?_⟩
  rw [h1 a ha, eq_bot_iff]
  intro x hx
  refine hsep x fun c => ?_
  rcases le_total b c with h | h
  · rw [h1 c h]; exact hx
  · exact hF h hx

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fil_zero_add (ρ : Representation LL G V) (ρ' : Representation LL G V')
    [FiniteDimensional LL ↥(DdR PD ρ)] [FiniteDimensional LL ↥(DdR PD ρ')] (τ : K →ₐ[Qp] LL)
    (h : ∀ a, multV PD ρ' τ (-a - 1) = multV PD ρ τ a) :
    finrank LL ↥(FildR PD ρ' τ 0) + finrank LL ↥(FildR PD ρ τ 0) = finrank LL ↥(DdRE PD ρ τ) := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := GlobalTheory.Per.FilCount.exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.DRFil.exists_mem_FilV PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  obtain ⟨c, hc⟩ := exists_eq_bot (DdR PD ρ') (FildR PD ρ' τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab))
    (fun a => le_trans inf_le_left inf_le_left)
    (fun x hx => GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV PD (LL := LL) x fun a => (hx a).2)
  let s : ℤ → ℕ := fun a => finrank LL ↥(FildR PD ρ' τ (-a)) + finrank LL ↥(FildR PD ρ τ a)
  have hs : ∀ a, s (a + 1) = s a := fun a => by
    have h1 := h a
    unfold multV at h1
    rw [show -a - 1 + 1 = -a by ring, show -a - 1 = -(a + 1) by ring] at h1
    simp only [s]
    omega
  have hs0 : ∀ a, s a = s 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hs, ih]
    | pred n ih => rw [← hs, sub_add_cancel, ih]
  have h2 := hs0 (min b (-c))
  simp only [s] at h2
  rw [hb _ (min_le_left _ _), hc _ (by omega), finrank_bot, zero_add, neg_zero] at h2
  exact h2.symm

theorem descend (L : Type) [Field L] [Algebra Qp L] [Algebra LL L] [IsScalarTower Qp LL L]
    [FiniteDimensional LL L] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (H : ∀ (W : Type) [AddCommGroup W] [Module L W] [Module Qp W] [IsScalarTower Qp L W]
      [FiniteDimensional L W] (σ : Representation L G W)
      (W' : Type) [AddCommGroup W'] [Module L W'] [Module Qp W'] [IsScalarTower Qp L W']
      [FiniteDimensional L W'] (σ' : Representation L G W') (n : W →ₗ[L] W' →ₗ[L] L),
      Function.Bijective n → (∀ g x y, n (σ g x) (σ' g y) = ((cycLL PD L g : Lˣ) : L) * n x y) →
      IsDR PD σ → IsDR PD σ' ∧
        finrank L ↥(DdR PD σ' ⊓ FilV PD (LL := L) (V := W') 0) +
          finrank L ↥(DdR PD σ ⊓ FilV PD (LL := L) (V := W) 0) = finrank L ↥(DdR PD σ))
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR PD ρ) (hm : IsDual1 PD ρ ρ' m) :
    IsDR PD ρ' ∧
      finrank LL ↥(DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) = finrank LL ↥(DdR PD ρ) := by
  have hbij : Function.Bijective m.flip := by
    have hi : Function.Injective m.flip := (injective_iff_map_eq_zero _).2 fun y hy =>
      hm.2.2.1 y fun x => LinearMap.congr_fun hy x
    refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi⟩
    rw [← hm.2.2.2]
    exact Subspace.dual_finrank_eq.symm
  obtain ⟨m', hm', hm''⟩ := exists_ext_pairing L m hbij
  obtain ⟨a1, -, -, ⟨a2, -⟩, a3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V (L ⊗[LL] V) ρ (extRep L ρ)
    (TensorProduct.mk LL L V 1) (TensorProduct.isBaseChange LL V L) (fun g x => rfl)
  obtain ⟨b1, -, -, ⟨b2, -⟩, b3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V' (L ⊗[LL] V') ρ' (extRep L ρ')
    (TensorProduct.mk LL L V' 1) (TensorProduct.isBaseChange LL V' L) (fun g x => rfl)
  have hχ : ∀ g, ((cycLL PD L g : Lˣ) : L) = algebraMap LL L ((cycLL PD LL g : LLˣ) : LL) := fun g =>
    IsScalarTower.algebraMap_apply Qp LL L _
  have hinv : ∀ g x y, m' (extRep L ρ g x) (extRep L ρ' g y) = ((cycLL PD L g : Lˣ) : L) * m' x y := by
    intro g x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx', mul_add]
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add (f := _), hy, hy', mul_add]
      | tmul b y =>
        rw [extRep_tmul, extRep_tmul, hm'', hm'', hm.1, map_mul, hχ]
        ring
  have hL : IsDR PD (extRep L ρ) := by
    rw [IsDR, a1, a2]; exact h
  obtain ⟨c1, c2⟩ := H _ (extRep L ρ) _ (extRep L ρ') m' hm' hinv hL
  refine ⟨by rw [IsDR, ← b1, ← b2]; exact c1, ?_⟩
  rw [← a2, ← a3, ← b3, c2]

end Period

theorem tateDual_split (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K L : FinExt l) (hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1)
    (W : Type) [AddCommGroup W] [Module ↥L.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥L.1 W]
    [FiniteDimensional ↥L.1 W] (σ : Representation ↥L.1 ↥(GK K) W)
    (W' : Type) [AddCommGroup W'] [Module ↥L.1 W'] [Module ℚ_[l] W'] [IsScalarTower ℚ_[l] ↥L.1 W']
    [FiniteDimensional ↥L.1 W'] (σ' : Representation ↥L.1 ↥(GK K) W') (n : W →ₗ[↥L.1] W' →ₗ[↥L.1] ↥L.1)
    (hn : Function.Bijective n)
    (hinv : ∀ g x y, n (σ g x) (σ' g y) = ((cycLL (P.PD K) ↥L.1 g : (↥L.1)ˣ) : ↥L.1) * n x y)
    (h : IsDR (P.PD K) σ) :
    IsDR (P.PD K) σ' ∧
      finrank ↥L.1 ↥(DdR (P.PD K) σ' ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W') 0) +
        finrank ↥L.1 ↥(DdR (P.PD K) σ ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W) 0) =
          finrank ↥L.1 ↥(DdR (P.PD K) σ) := by
  have := K.2
  obtain ⟨c1, c2⟩ := GlobalTheory.DRDual.twisted_dual_deRham l P AI T K L W σ W' σ' n 1 hn
    (fun g x y => by rw [zpow_one]; exact hinv g x y) h
  refine ⟨c1, ?_⟩
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W σ).1
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W' σ').1
  have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
  obtain ⟨d1, d2⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ
  obtain ⟨-, d3⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ'
  rw [d1, d2, d3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun τ _ =>
    finrank_fil_zero_add (P.PD K) σ σ' τ fun a => c2 τ a hcard

theorem tateDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR (P.PD K) ρ) (hm : IsDual1 (P.PD K) ρ ρ' m) :
    IsDR (P.PD K) ρ' ∧
      finrank LL ↥(DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) 0) =
          finrank LL ↥(DdR (P.PD K) ρ) := by
  obtain ⟨L, ⟨f⟩, hcard, -⟩ := GlobalTheory.exists_finExt_embedding_splitting l K LL
  have := L.2
  letI : Algebra LL ↥L.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥L.1 := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional LL ↥L.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥L.1
  exact descend (P.PD K) ↥L.1 (tateDual_split l P AI T K L hcard) ρ ρ' m h hm

theorem main : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm8 D := by
  intro D l _ K
  refine ⟨fun LL _ _ _ O _ _ hO A A' m h hm => ?_, fun LL _ _ _ O _ _ hO A A' m h hm => ?_⟩
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).1
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).2

end GlobalTheory.TateDualFil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAllStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_deRham_and_filZero_dim_all : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm8 D := by
  first | exact @GlobalTheory.TateDualFil.main | exact GlobalTheory.TateDualFil.main | (intros; apply GlobalTheory.TateDualFil.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.GaloisFromAdm

theorem placesOver_finite (D : D7) (l : ℕ) (hl : l ≠ 0) : (placesOver D.host.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

end GlobalTheory.GaloisFromAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousComplementFamily
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem exists_continuous_complementFamily {D : D7} (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) :
    ∃ ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ π, Continuous
        (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) ∧
      ∀ π ∈ D.nd.Z i, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) (ρ π) := by
  have key : ∀ π : D.nd.X i, ∃ ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
      (π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) ρ) := by
    intro π
    by_cases hπ : π ∈ D.nd.Z i
    · obtain ⟨ρ, hρ⟩ := h i π hπ (r π) (hr π)
      exact ⟨ρ, hρ.cont, fun _ => hρ⟩
    · exact ⟨1, continuous_const, fun h' => absurd h' hπ⟩
  choose ρ h1 h2 using key
  exact ⟨ρ, h1, h2⟩

theorem exists_ptFam : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    (∀ i, ∃ r, GoodR D.nd i r) → ∃ r ρ, PtFam D r ρ := by
  intro hC D hG hr
  choose r hr using hr
  choose ρ h1 h2 using fun i =>
    exists_continuous_complementFamily (GlobalTheory.BlockComplement.complement_at hC D hG) i (r i) (hr i)
  exact ⟨r, ρ, hr, h1, h2⟩

end GlobalTheory.PtCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegular
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem topBasis_disc_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) s F → Function.Injective F := by
  intro l _ K bk A _ s ι TB
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk A s
  refine ⟨(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι TB bk.ρ₀ h0 h1).1, ?_, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hn := (GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl h1).1 y
    rw [mul_comm, hy, norm_zero] at hn
    have hp : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast h0) _
    exact norm_eq_zero.1 ((mul_eq_zero.1 hn.symm).resolve_left hp.ne')
  · have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
    have hF := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
    have hW : ((l : ℕ) : Wq l bk.a) ≠ 0 := by
      intro h
      have h2 := congrArg (fun w : Wq l bk.a => w.coeff 1) h
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h2
      exact one_ne_zero h2
    have hS : ((l : ℕ) : bk.S) ≠ 0 := by
      intro h
      have h2 := congrArg (PowerSeries.constantCoeff) h
      rw [map_natCast, map_zero] at h2
      exact hW h2
    have := hF.2.2.2.2 _ (mem_nonZeroDivisors_of_ne_zero hS)
    rwa [map_natCast] at this
  · intro F hF
    obtain ⟨_, -, -, -, -, -, -, -, hnorm⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ h0 h1 F hF
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hnorm x
    rw [hx, norm_zero] at h
    exact norm_eq_zero.1 h.symm

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) s F → Function.Injective F := by
  first | exact @GlobalTheory.BSP.topBasis_disc_regular | exact GlobalTheory.BSP.topBasis_disc_regular | (intros; apply GlobalTheory.BSP.topBasis_disc_regular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelMulOfConstituent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelMulOfConstituent
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LabelMul

theorem ip_add_right {G : Type} [Group G] [Fintype G] (χ φ ψ : G → ℂ) :
    ip χ (φ + ψ) = ip χ φ + ip χ ψ := by
  simp only [ip, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem ip_sum_eq_count {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (hχ : IsIrr χ) (L : List (G → ℂ))
    (hL : ∀ ρ ∈ L, IsIrr ρ) : ip χ L.sum = (L.count χ : ℕ) := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, ip_add_right, ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ)),
      (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G χ ρ hχ (hL ρ List.mem_cons_self)).2.2, List.count_cons]
    by_cases h : χ = ρ
    · subst h
      simp [add_comm]
    · have h' : ¬ ρ = χ := fun e => h e.symm
      simp [h, h']

theorem ip_nat {G : Type} [Group G] [Fintype G] {χ φ : G → ℂ} (hχ : IsIrr χ) (hφ : IsChar φ) :
    ∃ k : ℕ, ip χ φ = k := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G φ).1 hφ
  exact ⟨_, ip_sum_eq_count hχ L hL⟩

theorem exists_add_of_ip_ne_zero {G : Type} [Group G] [Fintype G] {χ φ : G → ℂ} (hχ : IsIrr χ) (hφ : IsChar φ)
    (h : ip χ φ ≠ 0) : ∃ ψ, IsChar ψ ∧ φ = χ + ψ := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G φ).1 hφ
  rw [ip_sum_eq_count hχ L hL] at h
  have hm : χ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast h))
  refine ⟨(L.erase χ).sum, (GlobalTheory.T.character_decomposition_and_classFunction_expansion G χ).2.2.2.2 _
    (fun ρ hρ => isChar_of_isIrr (hL ρ (List.mem_of_mem_erase hρ))), ?_⟩
  rw [(List.perm_cons_erase hm).sum_eq, List.sum_cons]

variable {g : ℕ} [Fact g.Prime]

theorem hc_add_left (a b n : ℕ) (α α' : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b (α + α') β n = hc a b α β n + hc a b α' β n := by
  funext x
  simp only [hc, hcT, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · ring
  · simp

theorem hc_add_right (a b n : ℕ) (α : Gn g a → ℂ) (β β' : Gn g b → ℂ) :
    hc a b α (β + β') n = hc a b α β n + hc a b α β' n := by
  funext x
  simp only [hc, hcT, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · ring
  · simp

omit [Fact g.Prime] in
theorem degL_append (P Q : List (Pc g)) : degL (P ++ Q) = degL P + degL Q := by
  simp [degL]

theorem hcL_append (P Q : List (Pc g)) (hP : ∀ p ∈ P, IsChar p.2) (hQ : ∀ p ∈ Q, IsChar p.2) :
    ∀ n, n = degL P + degL Q →
      hcL (P ++ Q) n = hc (degL P) (degL Q) (hcL P (degL P)) (hcL Q (degL Q)) n := by
  have cQ : IsClass (hcL Q (degL Q)) :=
    (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g Q Q _ rfl hQ).1
  induction P with
  | nil =>
    intro n hn
    have hn' : n = degL Q := by simpa [degL] using hn
    subst hn'
    exact (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g (degL Q) (degL Q) (degL Q) (degL Q) _ _ _ cQ cQ cQ).2.2.1.symm
  | cons p P ih =>
    intro n hn
    have hP' : ∀ q ∈ P, IsChar q.2 := fun q hq => hP q (List.mem_cons_of_mem _ hq)
    have cP : IsClass (hcL P (degL P)) :=
      (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g P P _ rfl hP').1
    have cp : IsClass p.2 := (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (hP p List.mem_cons_self)
    have key : ∀ m, m = degL P + degL Q → hc p.1 m p.2 (hcL (P ++ Q) m) n =
        hc (p.1 + degL P) (degL Q) (hc p.1 (degL P) p.2 (hcL P (degL P)) (p.1 + degL P)) (hcL Q (degL Q)) n := by
      intro m hm
      subst hm
      rw [ih hP' _ rfl]
      exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g _ _ _ n _ _ _ cp cP cQ).1 hn).symm
    exact key _ (degL_append P Q)

theorem hasLabel_mul : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (a b n : ℕ) (χ : Gn g n → ℂ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (f₁ f₂ : (ZMod g)[X]), n = a + b → IsIrr χ → IsIrr α → IsIrr β → HasLabel L α f₁ → HasLabel L β f₂ → ip χ (hc a b α β n) ≠ 0 → HasLabel L χ (f₁ * f₂) := by
  intro g _ L a b n χ α β f₁ f₂ hn hχ hα hβ h₁ h₂ hip
  obtain ⟨P, hP, rfl, rfl, iP⟩ := h₁
  obtain ⟨Q, hQ, rfl, rfl, iQ⟩ := h₂
  have cP : ∀ p ∈ P.map Prod.snd, IsChar p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact isChar_of_isIrr (hP q hq).2.1.2.1
  have cQ : ∀ p ∈ Q.map Prod.snd, IsChar p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact isChar_of_isIrr (hQ q hq).2.1.2.1
  obtain ⟨A, hA, eA⟩ := exists_add_of_ip_ne_zero hα (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ [] _ rfl cP).1 iP
  obtain ⟨B, hB, eB⟩ := exists_add_of_ip_ne_zero hβ (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ [] _ rfl cQ).1 iQ
  refine ⟨P ++ Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hP p h
    · exact hQ p h
  · rw [List.map_append, degL_append, hn]
  · rw [List.map_append, List.prod_append]
  · rw [List.map_append, hcL_append _ _ cP cQ n hn, eA, eB, hc_add_left, hc_add_right, hc_add_right,
      ip_add_right, ip_add_right, ip_add_right]
    have H := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g _ _ n hn).1
    obtain ⟨k₁, e₁⟩ := ip_nat hχ (H _ _ (isChar_of_isIrr hα) (isChar_of_isIrr hβ))
    obtain ⟨k₂, e₂⟩ := ip_nat hχ (H _ _ (isChar_of_isIrr hα) hB)
    obtain ⟨k₃, e₃⟩ := ip_nat hχ (H _ _ hA (isChar_of_isIrr hβ))
    obtain ⟨k₄, e₄⟩ := ip_nat hχ (H _ _ hA hB)
    rw [e₁] at hip
    rw [e₁, e₂, e₃, e₄]
    have h1 : k₁ ≠ 0 := by exact_mod_cast hip
    have : k₁ + k₂ + (k₃ + k₄) ≠ 0 := by omega
    exact_mod_cast this

end GlobalTheory.GLq.LabelMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelMulOfConstituentStatement
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesLabel_mul_of_constituent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (a b n : ℕ) (χ : Gn g n → ℂ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (f₁ f₂ : (ZMod g)[X]), n = a + b → IsIrr χ → IsIrr α → IsIrr β → HasLabel L α f₁ → HasLabel L β f₂ → ip χ (hc a b α β n) ≠ 0 → HasLabel L χ (f₁ * f₂) := by
  first | exact @GlobalTheory.GLq.LabelMul.hasLabel_mul | exact GlobalTheory.GLq.LabelMul.hasLabel_mul | (intros; apply GlobalTheory.GLq.LabelMul.hasLabel_mul <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.EichlerUnip

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

noncomputable def eich (σ w : S.V) (t : E) : S.V →ₗ[E] S.V :=
  LinearMap.id - (S.hT σ).smulRight w + (S.hT w).smulRight σ - t • (S.hT w).smulRight w

theorem eich_apply (σ w : S.V) (t : E) (x : S.V) :
    eich S σ w t x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  simp only [eich, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, mul_smul]

theorem herm (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← LinearMap.isSymm_def.mp S.herm x y, starRingEnd_apply]

theorem eich_inv (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x : S.V) : eich S (-σ) w (star t) (eich S σ w t x) = x := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add (f := _), map_neg, map_smul,
    LinearMap.neg_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero]
  rw [← ht]
  module

theorem eich_isom (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x y : S.V) :
    S.hT (eich S σ w t x) (eich S σ w t y) = S.hT x y := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add (f := _), map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sub_apply,
    LinearMap.add_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero, starRingEnd_apply,
    star_mul']
  rw [herm S w x, herm S σ x, ← ht]
  ring

noncomputable def eichE (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) : S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (eich S σ w t) (eich S (-σ) w (star t))
    (LinearMap.ext fun x => by
      have := eich_inv S (-σ) w (star t) hw (by simp [hwσ]) (by simp [← ht, add_comm]) x
      simpa using this)
    (LinearMap.ext fun x => eich_inv S σ w t hw hwσ ht x)

theorem integral_of_unimodular {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, (o : E) = S.hT x y := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hΛ
  have h1 : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hΛ]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one] at h1
  obtain ⟨o, ho⟩ := h1 x hx
  exact ⟨o, ho⟩

theorem smul_mem_of {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : ∃ o : 𝓞 E, (o : E) = c) {x : S.V}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := hc
  have h := Λ.smul_mem o hx
  rw [← algebraMap_smul E o x] at h
  exact h

theorem eich_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {σ w : S.V} {t : E}
    (hσ : σ ∈ Λ) (hw : w ∈ Λ) (ht : ∃ o : 𝓞 E, (o : E) = t) {x : S.V} (hx : x ∈ Λ) :
    eich S σ w t x ∈ Λ := by
  rw [eich_apply]
  obtain ⟨a, ha⟩ := integral_of_unimodular S hΛ hσ hx
  obtain ⟨b, hb⟩ := integral_of_unimodular S hΛ hw hx
  obtain ⟨o, ho⟩ := ht
  have hob : ∃ c : 𝓞 E, (c : E) = t * S.hT w x := ⟨o * b, by rw [← ho, ← hb]; rfl⟩
  exact Λ.sub_mem (Λ.add_mem (Λ.sub_mem hx (smul_mem_of S ⟨a, ha⟩ hw)) (smul_mem_of S ⟨b, hb⟩ hσ))
    (smul_mem_of S hob hw)

theorem star_int {t : E} (ht : ∃ o : 𝓞 E, (o : E) = t) : ∃ o : 𝓞 E, (o : E) = star t := by
  obtain ⟨o, rfl⟩ := ht
  exact ⟨⟨star (o : E), (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

theorem iso_X {r : ℕ} {T : E} (F : LFlag S r T) {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) :
    S.hT x y = 0 := by
  have key : ∀ a, ∀ v ∈ Submodule.span E (Set.range F.fl.e), S.hT (F.fl.e a) v = 0 := by
    intro a v hv
    induction hv using Submodule.span_induction with
    | mem u hu => obtain ⟨b, rfl⟩ := hu; exact F.fl.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  have key2 : ∀ u ∈ Submodule.span E (Set.range F.fl.e), S.hT u y = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨a, rfl⟩ := hu; exact key a y hy
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key2 x hx

theorem mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem exists_eichler (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) {r : ℕ} {T : E} (F : LFlag S r T)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (σ : S.V) (hσ : σ ∈ Lrep Λ F)
    (w : S.V) (hw : w ∈ XLam Λ F) :
    ∃ n ∈ NLam Λ F, ∃ t : E, (∀ x ∈ Xsp F, n x = x) ∧
      ∀ x, n x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  obtain ⟨hσΛ, hσX⟩ := Submodule.mem_inf.mp hσ
  obtain ⟨hwΛ, hwX⟩ := Submodule.mem_inf.mp hw
  have hσX' : σ ∈ orth S (Xsp F) := hσX
  have hwX' : w ∈ Xsp F := hwX
  have hww : S.hT w w = 0 := iso_X S F hwX' hwX'
  have hwσ : S.hT w σ = 0 := (mem_orth S).mp hσX' w hwX'
  have hσσ : star (S.hT σ σ) = S.hT σ σ := (herm S σ σ).symm
  obtain ⟨oσ, hoσ⟩ := integral_of_unimodular S hΛ hσΛ hσΛ
  have ht : (θ : E) * S.hT σ σ + star ((θ : E) * S.hT σ σ) = S.hT σ σ := by
    rw [star_mul', hσσ]
    linear_combination (S.hT σ σ) * hθ
  have htI : ∃ o : 𝓞 E, (o : E) = (θ : E) * S.hT σ σ := ⟨θ * oσ, by rw [← hoσ]; rfl⟩
  have hfix : ∀ x ∈ Xsp F, eich S σ w ((θ : E) * S.hT σ σ) x = x := by
    intro x hx
    have h1 : S.hT σ x = 0 := by rw [herm, (mem_orth S).mp hσX' x hx, star_zero]
    have h2 : S.hT w x = 0 := iso_X S F hwX' hx
    rw [eich_apply, h1, h2]
    simp
  refine ⟨eichE S σ w _ hww hwσ ht, ?_, _, hfix, fun x => eich_apply S σ w _ x⟩
  simp only [NLam, Set.mem_setOf_eq, IsAutLam]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · change ∀ x y, S.hT (eich S σ w _ x) (eich S σ w _ y) = S.hT x y
    exact fun x y => eich_isom S σ w _ hww hwσ ht x y
  · apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact eich_mem S hΛ hσΛ hwΛ htI hy
    · intro y hy
      refine ⟨(eichE S σ w _ hww hwσ ht).symm y, ?_, by simp⟩
      exact eich_mem S hΛ (Λ.neg_mem hσΛ) hwΛ (star_int htI) hy
  · intro j x hx
    have hxX : x ∈ Xsp F := Submodule.span_mono (Set.image_subset_range _ _) hx
    change eich S σ w _ x - x ∈ _
    rw [hfix x hxX, sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have h2 : S.hT w x = 0 := (mem_orth S).mp hx w hwX'
    have : eich S σ w ((θ : E) * S.hT σ σ) x - x = -(S.hT σ x • w) := by
      rw [eich_apply, h2]
      module
    change eich S σ w _ x - x ∈ _
    rw [this]
    exact (Xsp F).neg_mem ((Xsp F).smul_mem _ hwX')

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eichler_mem_unipotent : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → ∀ σ ∈ Lrep Λ F, ∀ w ∈ XLam Λ F, ∃ n ∈ NLam Λ F, ∃ t : D.host.E, (∀ x ∈ Xsp F, n x = x) ∧ ∀ x, n x = x - (hS D).hT σ x • w + (hS D).hT w x • σ - (t * (hS D).hT w x) • w := by
  intro D T F Λ hΛ σ hσ w hw
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two
  refine exists_eichler (hS D) θ ?_ F Λ hΛ σ hσ w hw
  have h := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hθ
  simp only [map_add (f := _), map_one, GlobalTheory.InertSign.sgO_coe] at h
  rw [GlobalTheory.NormSum.AdLattice.star_eq_conj D]
  exact h

end GlobalTheory.EichlerUnip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatio
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem exists_isRatioN : ∀ (k r : ℕ), ∃ cN : ℝ, IsRatioN k r cN := by
  intro k r
  have h1 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) 1) :=
    GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top
  have h2 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (D.muN k r) :=
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r (D.muN k r)).2.1).2 (P.nilpotent_measure_is_haar k r)
  obtain ⟨c, c0, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (P.unipotent_radical_closed k r) h1 h2
  exact ⟨c.toReal, ENNReal.toReal_pos c0 c1, by rw [ENNReal.ofReal_toReal c1]; exact e⟩

end GlobalTheory.ThA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatioStatement
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentHaarMeasure_ratio : ∀ (k r : ℕ), ∃ cN : ℝ, IsRatioN k r cN := by
  first | exact @GlobalTheory.ThA.exists_isRatioN | exact GlobalTheory.ThA.exists_isRatioN | (intros; apply GlobalTheory.ThA.exists_isRatioN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
namespace GlobalTheory.SignCount

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

private theorem qEps_eq_star_dotProduct_Jm_mulVec {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    ((GlobalTheory.GaussMean.qEps ε x : ℝ) : ℂ) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  simp only [GlobalTheory.GaussMean.qEps, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]
  split_ifs <;> push_cast <;> ring

private theorem qEps_mulVec_of_conjTranspose_mul_Jm_mul {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x := by
  apply Complex.ofReal_injective
  rw [qEps_eq_star_dotProduct_Jm_mulVec, qEps_eq_star_dotProduct_Jm_mulVec, ← h, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

private theorem qEps_not_eq_neg {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps (fun a => !ε a) x = - GlobalTheory.GaussMean.qEps ε x := by
  simp only [GlobalTheory.GaussMean.qEps, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a = true <;> simp [h]

private theorem card_true_add_card_false_le_of_qEps_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : ∀ x, GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x) :
    Fintype.card {a // η a = true} + Fintype.card {a // ε a = false} ≤ m := by
  classical
  let E₁ : ({a // η a = true} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun u a => if h : η a = true then u ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : η a = true <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : η a = true <;> simp [h] }
  let E₂ : ({a // ε a = false} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun w a => if h : ε a = false then w ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : ε a = false <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : ε a = false <;> simp [h] }
  let Φ := (C.mulVecLin ∘ₗ E₁).coprod E₂
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, w⟩ hp
    have hp' : C *ᵥ E₁ u = -(E₂ w) := by
      have : C *ᵥ E₁ u + E₂ w = 0 := by simpa [Φ] using hp
      exact eq_neg_of_add_eq_zero_left this
    have hnn : ∀ a, 0 ≤ (if η a then (1 : ℝ) else -1) * ‖E₁ u a‖ ^ 2 := by
      intro a
      by_cases h : η a = true
      · simp [h]
      · simp [E₁, h]
    have hnp : GlobalTheory.GaussMean.qEps ε (-(E₂ w)) ≤ 0 := by
      unfold GlobalTheory.GaussMean.qEps
      refine Finset.sum_nonpos fun a _ => ?_
      by_cases h : ε a = false
      · simp [h]
      · simp [E₂, h]
    have hq : GlobalTheory.GaussMean.qEps η (E₁ u) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg fun a _ => hnn a)
      rw [← hC, hp']
      exact hnp
    have hu : u = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hq
      funext b
      have := hz b.1 (Finset.mem_univ _)
      simpa [E₁, b.2] using this
    have hw : w = 0 := by
      have h0 : E₂ w = 0 := by
        have : C *ᵥ E₁ u = 0 := by simp [hu]
        rw [hp'] at this
        exact neg_eq_zero.1 this
      funext b
      have := congrFun h0 b.1
      simpa [E₂, b.2] using this
    simp [hu, hw]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using this

theorem card_true_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) :
    Nat.card {a // ε a = true} = Nat.card {a // η a = true} := by
  classical
  have hC := qEps_mulVec_of_conjTranspose_mul_Jm_mul C h
  have h₁ := card_true_add_card_false_le_of_qEps_eq C hC
  have hC' : ∀ x, GlobalTheory.GaussMean.qEps (fun a => !ε a) (C *ᵥ x) =
      GlobalTheory.GaussMean.qEps (fun a => !η a) x := by
    intro x; rw [qEps_not_eq_neg, qEps_not_eq_neg, hC]
  have h₂ := card_true_add_card_false_le_of_qEps_eq C hC'
  simp only [Fintype.card_subtype] at h₁ h₂
  simp only [Bool.not_eq_true', Bool.not_eq_false'] at h₂
  have hε : (Finset.univ.filter fun a => ε a = true).card +
      (Finset.univ.filter fun a => ε a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases ε a <;> simp
    simp [this]
  have hη : (Finset.univ.filter fun a => η a = true).card +
      (Finset.univ.filter fun a => η a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if η a = true then 1 else 0) + (if η a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases η a <;> simp
    simp [this]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  omega

theorem card_true_cons {n : ℕ} (s : Bool) (ε' : Fin n → Bool) :
    Nat.card {a // (Fin.cons s ε' : Fin (n + 1) → Bool) a = true} =
      (if s = true then 1 else 0) + Nat.card {a // ε' a = true} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

private theorem conjTranspose_mul_Jm_mul_apply {m : ℕ} {ι : Type*} (ε : Fin m → Bool) (M : Matrix (Fin m) ι ℂ)
    (k l : ι) :
    (Mᴴ * Formalism.REAL.Jm ε * M) k l = ∑ i, star (M i k) * ((if ε i then 1 else -1) * M i l) := by
  rw [Matrix.mul_apply]
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, mul_assoc]

theorem gram_cons {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {s : Bool}
    {x₀ : Fin (n + 1) → ℂ} {B : Matrix (Fin (n + 1)) (Fin n) ℂ}
    (h0 : GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s)
    (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ))ᴴ * Formalism.REAL.Jm ε *
      (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ)) =
      Formalism.REAL.Jm (Fin.cons s ε') := by
  have e0 := qEps_eq_star_dotProduct_Jm_mulVec ε x₀
  rw [h0] at e0
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply] at e0
  have e1 : ∀ l, ∑ i, star (x₀ i) * ((if ε i then 1 else -1) * B i l) = 0 := by
    intro l
    have := congrFun h1 l
    simpa [Matrix.vecMul, dotProduct, Formalism.REAL.Jm, Matrix.diagonal_mul] using this
  ext k l
  rw [conjTranspose_mul_Jm_mul_apply]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
  · rw [← e0]
    cases s <;> simp [Formalism.REAL.Jm, GlobalTheory.GaussMean.sgn]
  · rw [e1]
    simp [Formalism.REAL.Jm, (Fin.succ_ne_zero l).symm]
  · have := congrArg star (e1 k)
    rw [star_sum, star_zero] at this
    rw [show (Formalism.REAL.Jm (Fin.cons s ε') : Matrix _ _ ℂ) k.succ 0 = 0 by
      simp [Formalism.REAL.Jm, Fin.succ_ne_zero k]]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp [mul_comm]
  · rw [← conjTranspose_mul_Jm_mul_apply ε B k l, h2]
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply]

theorem exists_signCompat : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  intro n ε ε' s x₀ B h0 h1 h2 P Q P' Q' f f' hf hf'
  have hc := card_true_eq _ (gram_cons h0 h1 h2)
  rw [card_true_cons, hf.card_true, hf'.card_true] at hc
  have hPQ := Sorts.add_eq f
  have hPQ' := Sorts.add_eq f'
  cases s
  · simp at hc
    let eL : Fin P' ≃ Fin P := finCongr (by omega)
    let eR : Option (Fin Q') ≃ Fin Q := (finSuccEquiv Q').symm.trans (finCongr (by omega))
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Fin P' ⊕ Option (Fin Q') :=
      { toFun := fun o => o.elim (Sum.inr none) (Sum.elim Sum.inl (fun b => Sum.inr (some b)))
        invFun := Sum.elim (fun a => some (Sum.inl a)) (fun ob => ob.map Sum.inr)
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro (_ | _ | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]
  · simp at hc
    let eL : Option (Fin P') ≃ Fin P := (finSuccEquiv P').symm.trans (finCongr (by omega))
    let eR : Fin Q' ≃ Fin Q := finCongr (by omega)
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Option (Fin P') ⊕ Fin Q' :=
      { toFun := fun o => o.elim (Sum.inl none) (Sum.elim (fun a => Sum.inl (some a)) Sum.inr)
        invFun := Sum.elim (fun oa => oa.map Sum.inl) (fun b => some (Sum.inr b))
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro ((_ | _) | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]

end GlobalTheory.SignCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrameStatement
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_blocks_of_vector_and_frame : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  first | exact @GlobalTheory.SignCount.exists_signCompat | exact GlobalTheory.SignCount.exists_signCompat | (intros; apply GlobalTheory.SignCount.exists_signCompat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlag
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PerpPos

theorem re_pos {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {k r : ℕ}
    (hA : GlobalTheory.SA.Amb S k r) {T : ℕ} (hT : 0 < T) (F : FlagG S r (T : E)) {x : S.V}
    (hx : x ∈ orth S F.Xplus) (hxX : x ∉ F.X) (τ : E →+* ℂ) : 0 < (τ (S.hT x x)).re := by
  have hsym : ∀ a b : S.V, S.hT a b = 0 → S.hT b a = 0 := fun a b h => by
    rw [← S.herm.eq a b, h, map_zero]
  have hx' : ∀ y ∈ F.Xplus, S.hT y x = 0 := fun y hy => by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx y hy
  have hzP : F.z ∈ F.Xplus := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hXP : ∀ y ∈ F.X, y ∈ F.Xplus := fun y hy => Submodule.mem_sup_left hy
  have hspan : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ y ∈ F.X, S.hT y w = 0 := by
    intro w hw y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hw a
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
  have hXz : ∀ y ∈ F.X, S.hT y F.z = 0 := hspan _ F.z_orth
  have hXX : ∀ y ∈ F.X, ∀ y' ∈ F.X, S.hT y y' = 0 := fun y hy y' hy' =>
    hspan y' (fun a => hsym _ _ (hspan _ (fun b => F.e_iso b a) y' hy')) y hy
  have hTne : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hzX : F.z ∉ F.X := fun h => by
    have := hXz _ h
    rw [F.z_norm, neg_eq_zero] at this
    exact hTne this
  have hxP : x ∉ F.Xplus := fun h => by
    obtain ⟨ξ, hξ, w, hw, hsum⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 := hx' _ hzP
    rw [← hsum, map_add (f := _), map_smul, hsym _ _ (hXz _ hξ), F.z_norm, zero_add, smul_eq_mul, mul_eq_zero,
      neg_eq_zero] at h1
    rcases h1 with h1 | h1
    · apply hxX
      rw [← hsum, h1, zero_smul, add_zero]
      exact hξ
    · exact hTne h1
  have hdX : finrank E F.X = r := by
    have := finrank_span_eq_card F.e_indep
    rwa [Fintype.card_fin] at this
  have hdP : finrank E F.Xplus = r + 1 := by
    have := Submodule.finrank_sup_span_singleton hzX
    rwa [hdX] at this
  have hdU : finrank E (F.Xplus ⊔ Submodule.span E {x} : Submodule E S.V) = r + 2 := by
    have := Submodule.finrank_sup_span_singleton hxP
    rwa [hdP] at this
  by_contra hle
  rw [not_lt] at hle
  have := hA.neg τ (F.Xplus ⊔ Submodule.span E {x}) (by
    intro y hy
    obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨ξ, hξ, w, hw, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have e : S.hT (ξ + a • F.z + c • x) (ξ + a • F.z + c • x) =
        (star a * a) * (-(T : E)) + (star c * c) * S.hT x x := by
      simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
        smul_eq_mul, hXX _ hξ _ hξ, hXz _ hξ, hsym _ _ (hXz _ hξ), hx' _ (hXP _ hξ),
        hsym _ _ (hx' _ (hXP _ hξ)), hx' _ hzP, hsym _ _ (hx' _ hzP), F.z_norm,
        starRingEnd_apply]
      ring
    have n : ∀ b : E, τ (star b * b) = (Complex.normSq (τ b) : ℂ) := fun b => by
      rw [map_mul, hA.cm, Complex.normSq_eq_conj_mul_self]
    rw [e, map_add (f := _), map_mul τ (star a * a), map_mul τ (star c * c), n, n, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, map_neg, map_natCast, Complex.neg_re, Complex.natCast_re]
    have h1 := Complex.normSq_nonneg (τ a)
    have h2 := Complex.normSq_nonneg (τ c)
    have h3 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    nlinarith [mul_nonneg h1 h3, mul_nonneg h2 (neg_nonneg.2 hle)])
  omega

theorem trace_pos {K : Type} [Field K] [NumberField K] (y : K) (hp : ∀ τ : K →+* ℂ, 0 < (τ y).re) :
    0 < Algebra.trace ℚ K y := by
  have e := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := y)
  have e2 : ((Algebra.trace ℚ K y : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ y).re := by
    rw [← Complex.re_sum, ← e]
    simp
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have : (0 : ℝ) < ((Algebra.trace ℚ K y : ℚ) : ℝ) := by
    rw [e2]
    exact Finset.sum_pos (fun σ _ => hp (σ : K →+* ℂ)) Finset.univ_nonempty
  exact_mod_cast this

theorem trace_pos_perp : ∀ (D : D7) (T' : ℕ) (F' : Fg D ((T' : ℕ) : D.host.E)), 0 < T' →
    ∀ x ∈ orth (hS D) (Xplus F'), x ∉ Xsp F' → 0 < Algebra.trace ℚ D.host.E ((hS D).hT x x) := by
  intro D T' F' hT x hx hxX
  have hA : GlobalTheory.SA.Amb (hS D) D.R.k D.R.rS :=
    GlobalTheory.SA.AmbSig.amb_of_sig _ _ _ _ D.sp.cm.cmUnram.2.1 (D.sp.Y_sig 0) D.sp.baseSpace_signature_eq
  exact trace_pos _ (re_pos hA hT F'.fl hx hxX)

end GlobalTheory.LoopC.PerpPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlagStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_form_pos_on_orth_liftedFlag : ∀ (D : D7) (T' : ℕ) (F' : Fg D ((T' : ℕ) : D.host.E)), 0 < T' → ∀ x ∈ orth (hS D) (Xplus F'), x ∉ Xsp F' → 0 < Algebra.trace ℚ D.host.E ((hS D).hT x x) := by
  first | exact @GlobalTheory.LoopC.PerpPos.trace_pos_perp | exact GlobalTheory.LoopC.PerpPos.trace_pos_perp | (intros; apply GlobalTheory.LoopC.PerpPos.trace_pos_perp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSq
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot.BallProd

theorem volume_ball_eq_ballVol {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hd : Module.finrank ℝ F = d) (r : ℝ) :
    (volume : Measure F) (Metric.ball 0 r) = ballVol d r := by
  subst hd
  unfold ballVol
  have h := (stdOrthonormalBasis ℝ F).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem prod_region_eq_ballVol (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ((volume : Measure (ℝ × Sp P Q)).prod
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} = ballVol ((P + Q + 1) ^ 2) r := by
  have h0 := GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).comp
    (WithLp.volume_preserving_ofLp ℝ (EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
  have h2 := (h1.prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
      (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, ← h2.measure_preimage hm.nullMeasurableSet,
    ← volume_ball_eq_ballVol (F := WithLp 2 (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)) ×
      EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))]
  · congr 1
    ext x
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) hr.le, WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    simp
  · rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ (Fin P ⊕ Fin Q → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring

theorem ballVol_succ_sq (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) *
      ((volume : Measure (ℝ × Sp P Q)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
        {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  have h0 : MeasurePreserving (fun y : Sp P Q => (√2 : ℝ) • y) volume
      (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • volume) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_addHaar_smul _ hs, hfin, pow_mul, Real.sq_sqrt (by norm_num),
      abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp
  have hne : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ 0 := by simp
  have hnt : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ ⊤ := by simp
  haveI : SFinite (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • (volume : Measure (Sp P Q))) := inferInstance
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have h2 := h1.measure_preimage hm.nullMeasurableSet
  rw [Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply,
    ← Measure.volume_eq_prod, prod_region_eq_ballVol P Q r hr, smul_eq_mul] at h2
  have h3 : {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} =
      Prod.map (Prod.map id fun y : Sp P Q => (√2 : ℝ) • y) id ⁻¹'
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} := by
    ext p
    simp [tanSq, norm_smul, mul_pow, Finset.mul_sum, mul_add]
  rw [h3, h2, ← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul]

end GlobalTheory.GaugeQuot.BallProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSqStatement
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ballVol_succ_sq_eq_pow_mul_prod : ∀ (P Q : ℕ) (r : ℝ), 0 < r → ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) * ((volume : Measure (ℝ × Sp P Q)).prod (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))) {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  first | exact @GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | exact GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | (intros; apply GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModel
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot

theorem hsDist_equiv_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : hsDist (hf.equiv.symm k) = Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  have h' : Formalism.MainNotions.S.uMat k - 1 = Matrix.reindex f f (UpqT.mat (hf.equiv.symm k) - 1) := by
    rw [show Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.umat k from rfl, h]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  unfold hsDist Formalism.REAL.hs
  rw [h']
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  symm
  rw [← f.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.sum_comp]
  simp

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c) :
    0 < c := by
  have hV : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hneg'
  have hneg : c ≤ 0 := not_lt.1 hneg'
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2)
        ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    exact div_nonpos_iff.2 (Or.inr ⟨mul_nonpos_iff.2 (Or.inr ⟨hneg, ENNReal.toReal_nonneg⟩),
      (pow_pos hr' _).le⟩)
  have := le_of_tendsto hc hle
  linarith

private theorem tendsto_gauge_ratio_volume_ball {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c)
    (hc0 : 0 < c) :
    Tendsto (fun r : ℝ =>
        c * (Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2}).toReal / r ^ (n ^ 2))
      (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  set A : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r} with hAdef
  set B : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2} with hBdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hc' : Tendsto (fun r => c * (A r).toReal / r ^ (n ^ 2)) (𝓝[>] 0) (𝓝 V) := hc
  have hBA : ∀ r : ℝ, 0 < r → B r ≤ A r := by
    intro r hr
    apply measure_mono
    intro g hg
    exact ((Real.sqrt_lt' hr).2 hg).le
  have hAB : ∀ r s : ℝ, 0 < r → s < r → A s ≤ B r := by
    intro r s hr hs
    apply measure_mono
    intro g hg
    exact (Real.sqrt_lt' hr).1 (lt_of_le_of_lt hg hs)
  have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), A r ≠ ⊤ := by
    filter_upwards [hc'.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have h1 : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝 0) (𝓝 ((1 - 0) ^ (n ^ 2))) :=
      ((continuous_const.sub continuous_id).pow _).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝 0) (𝓝 ((1 - 0) * 0)) :=
        ((continuous_const.sub continuous_id).mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact mul_pos (by linarith [hr.2]) hr.1
  have hlow : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2) *
      (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2))) (𝓝[>] 0) (𝓝 V) := by
    simpa using h1.mul (hc'.comp h2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hc' ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hfin] with r hr hAr
    have hr0 : 0 < r := hr.1
    have h1r : 0 < 1 - r := by linarith [hr.2]
    have hBfin : B r ≠ ⊤ := ne_top_of_le_ne_top hAr (hBA r hr0)
    have hle : (A ((1 - r) * r)).toReal ≤ (B r).toReal :=
      ENNReal.toReal_mono hBfin (hAB r _ hr0 (by nlinarith))
    have hne1 : (1 - r) ^ (n ^ 2) ≠ 0 := pow_ne_zero _ h1r.ne'
    have hne2 : r ^ (n ^ 2) ≠ 0 := pow_ne_zero _ hr0.ne'
    have heq : (1 - r) ^ (n ^ 2) * (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2)) =
        c * (A ((1 - r) * r)).toReal / r ^ (n ^ 2) := by
      rw [mul_pow]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hc0.le) (pow_pos hr0 _).le
  · filter_upwards [self_mem_nhdsWithin, hfin] with r hr hAr
    have hr0 : (0 : ℝ) < r := hr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hAr (hBA r hr0)) hc0.le) (pow_pos hr0 _).le

theorem gauge_transport : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  intro n ε c P Q f hf hc
  have hc0 : 0 < c := pos_of_isGauge' hc
  refine ⟨hc0, ?_⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have hPQ : P + Q = n := Sorts.add_eq f
  have hVfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' hVfin
  have hlim := tendsto_gauge_ratio_volume_ball hc hc0
  have key : ∀ r : ℝ, ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) {g | hsDist g < r ^ 2} =
      ENNReal.ofReal c * Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} := by
    intro r
    rw [Measure.map_apply (show Measurable (hf.equiv.symm : Formalism.REAL.UJ ε → UpqT P Q) from
        hf.equiv.symm.continuous.measurable)
      (measurableSet_lt continuous_hsDist.measurable measurable_const), Measure.smul_apply, smul_eq_mul]
    congr 2
    ext k
    simp [hsDist_equiv_symm hf k]
  have hBfin : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} ≠ ⊤ := by
    filter_upwards [hlim.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have hlim' : Tendsto (fun r : ℝ => ENNReal.ofReal
      (c * (Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2}).toReal / r ^ (n ^ 2) / V))
      (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (hlim.div_const V)
    rwa [div_self hV.ne', ENNReal.ofReal_one] at this
  unfold HasEuclDensity
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hBfin] with r hr hB
  have hr0 : (0 : ℝ) < r := hr
  have hball : ballVol ((P + Q) ^ 2) r = ENNReal.ofReal (r ^ (n ^ 2)) * ENNReal.ofReal V := by
    have := ballVol_mul ((P + Q) ^ 2) r 1 hr0 one_pos
    rw [mul_one] at this
    rw [this, hPQ, hVdef, ENNReal.ofReal_toReal hVfin]
    rfl
  rw [key r, hball, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), div_div,
    ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr0 _) hV), ENNReal.ofReal_mul hc0.le,
    ENNReal.ofReal_toReal hB]

end GlobalTheory.GaugeQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModelStatement
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_transport_block_model : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_transport | exact GlobalTheory.GaugeQuot.gauge_transport | (intros; apply GlobalTheory.GaugeQuot.gauge_transport <;> assumption)
end
end

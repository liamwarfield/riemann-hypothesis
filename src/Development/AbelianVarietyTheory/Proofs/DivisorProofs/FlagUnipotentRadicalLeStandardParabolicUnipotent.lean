module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Formalism.UG (cT)
open Matrix

noncomputable section

namespace GlobalTheory.FlagRad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem mulVec_initCols_mem {n r : ℕ} (X : Matrix (Fin n) (Fin r) E) (m : Fin r) (A : Set (Fin r))
    (a : Fin (m.val + 1) → AF F ⊗[F] E) (ha : ∀ l, a l ≠ 0 → Fin.castLE m.2 l ∈ A) :
    adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a ∈ GlobalTheory.StdPar.colSpan F X A := by
  rw [Matrix.mulVec_eq_sum]
  refine sum_mem fun l _ => ?_
  by_cases h : a l = 0
  · simp [h]
  · rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ha l h, rfl⟩)

theorem exists_of_card_lt {r : ℕ} (S : Finset (Fin r)) {a b : ℕ}
    (h : (S.filter fun k => k.val < a).card < (S.filter fun k => k.val < b).card) :
    ∃ k ∈ S, a ≤ k.val ∧ k.val < b := by
  by_contra hc
  push_neg at hc
  refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, not_le.1 fun h' => absurd hk.2 (not_lt.2 (hc k hk.1 h'))⟩


open GlobalTheory.StdPar in
theorem unipFlag_le_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) (m : Fin r) (hmS : m ∈ S)
    (hm : ∀ k ∈ S, k ≤ m) :
    GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) ≤
      GlobalTheory.StdPar.unip σ J X S := by
  set C := initCols X m with hCdef
  set d : Fin (m.val + 1) → ℕ := fun i => (S.filter fun k => k.val < i.val).card with hd
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma h
  have hC : IsIsoCols σ J C := isIsoCols_of_isWittFrame hW hσ hJ m.2
  have memS : ∀ g ∈ unipFlag σ J C d, g ∈ unipSet σ J C d := fun g hg => (mem_unipFlag hJ hσ hC d).1 hg

  have stab : ∀ g ∈ unipSet σ J C d, ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y ∈ colSpan F X A, (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := by
    intro g hg A hA1 hA2 y hy
    have hle : colSpan F X A ≤ (colSpan F X A).comap (matHom _ σ J g).1.mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨a, ha0, ha⟩ := hg.1 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩
      have ha' : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
      have e : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i + ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      show (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i ∈ colSpan F X A
      rw [e, ha']
      refine add_mem (Submodule.subset_span ⟨i, hi, rfl⟩) (GlobalTheory.FlagRad.mulVec_initCols_mem X m A a fun l' hl' => ?_)
      exact hA2 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩ l' hi (not_le.1 fun h' => hl' (ha0 l' h'))
    exact hle hy
  have inv_app : ∀ (g : GAd σ J) y, (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := fun g y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  intro g hg
  have hg1 := memS g hg
  have hg2 := memS g⁻¹ (inv_mem hg)
  have iffPart : ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y, y ∈ colSpan F X A ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := fun A hA1 hA2 y =>
    ⟨stab g hg1 A hA1 hA2 y, fun hy => by
      have := stab g⁻¹ hg2 A hA1 hA2 _ hy
      rwa [inv_app] at this⟩
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (hm k hk), fun hi => ⟨m, hmS, hi⟩⟩
  have hB1 : ∀ i ∈ {i : Fin r | i ≤ m}, i.val ≤ m.val := fun i hi => hi
  have hB2 : ∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ {i : Fin r | i ≤ m} → d l' < d l →
      Fin.castLE m.2 l' ∈ {i : Fin r | i ≤ m} := fun l l' _ _ => Nat.le_of_lt_succ l'.2
  have sub_app : ∀ y, (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1) *ᵥ y := fun y => by
    simp [Matrix.sub_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨iffPart _ ?_ ?_, fun y hy => ?_⟩, ?_⟩
  · rintro i ⟨k, hk, hik, -⟩
    exact hik.trans (hm k hk)
  · rintro l l' ⟨k, hk, hlk, hkj⟩ hdl
    obtain ⟨k', hk', h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S hdl
    refine ⟨k', hk', h1, ?_⟩
    rw [Fin.le_def] at hlk
    rw [Fin.lt_def] at hkj ⊢
    simp only [Fin.coe_castLE] at hlk
    omega
  ·
    have hle : colSpan F X {j} ≤ (colSpan F X {i | ∃ k ∈ S, i ≤ k ∧ k < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi', rfl⟩
      have hij : i = j := hi'
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      by_cases hi : i.val ≤ m.val
      · obtain ⟨a, ha0, ha⟩ := hg1.1 ⟨i.val, Nat.lt_succ_of_le hi⟩
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' hl' => ?_
        obtain ⟨k, hk, h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S (not_le.1 fun h' => hl' (ha0 l' h'))
        refine ⟨k, hk, h1, ?_⟩
        rw [Fin.lt_def, ← hij]
        exact h2
      · have hx : (cT (σ : E →+* E) C * J) *ᵥ (fun k => X k i) = 0 :=
          funext fun l => congrFun (congrFun hW.xx (l.castLE m.2)) i
        obtain ⟨a, ha⟩ := hg1.2 _ hx
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' _ => ⟨m, hmS, Nat.le_of_lt_succ l'.2, ?_⟩
        rw [Fin.lt_def, ← hij]
        omega
    rw [sub_app]
    exact hle hy
  · rw [e1]
    refine ⟨iffPart _ hB1 hB2, fun y hy => ?_⟩
    set T := cT (σ : E →+* E) (initCols X m) * J
    have hT : T * initCols Y m = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hW.xy (i.castLE m.2)) (j.castLE m.2)).trans (by simp [Matrix.one_apply])
    have hQ : T * (1 - initCols Y m * T) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul, Matrix.mul_one, sub_self]
    have hy' : y = adMat F (1 - initCols Y m * T) *ᵥ y := by
      rw [adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, sub_mulVec,
        one_mulVec, ← mulVec_mulVec, mem_colPerp_iff.1 hy, mulVec_zero, sub_zero]
    have : (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1).mulVecLin y := by simp [sub_mulVec]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, hy', mulVec_eq_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [op_smul_eq_smul, map_smul]
    obtain ⟨a, ha⟩ := hg1.2 (fun i => (1 - initCols Y m * T : Matrix (Fin n) (Fin n) E) i j)
      (funext fun i => congrFun (congrFun hQ i) j)
    exact Submodule.smul_mem _ _ (mem_colSpan_iff.2 ⟨a, ha.symm⟩)

end GlobalTheory.FlagRad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotentStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentRadical_le_standardParabolicUnipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) ≤ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.FlagRad.unipFlag_le_unip | exact GlobalTheory.FlagRad.unipFlag_le_unip | (intros; apply GlobalTheory.FlagRad.unipFlag_le_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivRestrictsRealLinearEquivArchimed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivRestrictsRealLinearEquivArchimed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilAdm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infPart (w : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1

theorem infPart_infE (z : κ → mixedEmbedding.mixedSpace F) : infPart (infE F z) = z := by
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem infE_infPart (w : κ → AdeleRing (𝓞 F) F) (h : ∀ i, (w i).2 = 0) : infE F (infPart w) = w := by
  funext i
  refine Prod.ext ?_ (h i).symm
  exact RingEquiv.symm_apply_apply _ _

def eInf : AdeleRing (𝓞 F) F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem eInf_smul_snd (w : κ → AdeleRing (𝓞 F) F) (i : κ) : ((eInf (F := F) • w) i).2 = 0 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = 0
  exact zero_mul _

theorem eInf_smul_infE (z : κ → mixedEmbedding.mixedSpace F) : eInf (F := F) • infE F z = infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (1 : InfiniteAdeleRing F) * _ = _
    exact one_mul _
  · show (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    exact zero_mul _

theorem infE_add (z z' : κ → mixedEmbedding.mixedSpace F) : infE F (z + z') = infE F z + infE F z' := by
  funext i
  refine Prod.ext ?_ ?_
  · exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 + 0
    exact (add_zero _).symm

theorem infPart_add (w w' : κ → AdeleRing (𝓞 F) F) : infPart (w + w') = infPart w + infPart w' := by
  funext i
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (w i).1 (w' i).1

def rAd (t : ℝ) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)), 0)

theorem infE_smul (t : ℝ) (z : κ → mixedEmbedding.mixedSpace F) : infE F (t • z) = rAd (F := F) t • infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • z i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i)
    rw [← map_mul, smul_mul_assoc, one_mul]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    exact (zero_mul _).symm

theorem infPart_smul (t : ℝ) (w : κ → AdeleRing (𝓞 F) F) : infPart (rAd (F := F) t • w) = t • infPart w := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)) * (w i).1) =
    t • InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1
  rw [map_mul, RingEquiv.apply_symm_apply, smul_mul_assoc, one_mul]

def infPart2 (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) := (infPart w.1, infPart w.2)

theorem archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    infPart2 (mixedSpaceVecPairAsAdeles F v) = v := by
  simp only [infPart2, mixedSpaceVecPairAsAdeles, infPart_infE]

theorem archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    eInf (F := F) • mixedSpaceVecPairAsAdeles F v = mixedSpaceVecPairAsAdeles F v := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.smul_mk, eInf_smul_infE]

theorem mixedSpaceVecPair_archimedeanPart_idempotent_smul (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (eInf (F := F) • w)) = eInf (F := F) • w := by
  show (infE F (infPart (eInf (F := F) • w.1)), infE F (infPart (eInf (F := F) • w.2))) =
    (eInf (F := F) • w.1, eInf (F := F) • w.2)
  rw [infE_infPart _ (eInf_smul_snd w.1), infE_infPart _ (eInf_smul_snd w.2)]

theorem mixedSpaceVecPair_archimedeanPart_linearMap_apply (f : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) →ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (f (mixedSpaceVecPairAsAdeles F v))) = f (mixedSpaceVecPairAsAdeles F v) := by
  rw [← archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles v, map_smul]
  exact mixedSpaceVecPair_archimedeanPart_idempotent_smul _

theorem mixedSpaceVecPairAsAdeles_add (v v' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (v + v') = mixedSpaceVecPairAsAdeles F v + mixedSpaceVecPairAsAdeles F v' := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.fst_add, Prod.snd_add, infE_add, Prod.mk_add_mk]

theorem mixedSpaceVecPairAsAdeles_real_smul (t : ℝ) (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (t • v) = rAd (F := F) t • mixedSpaceVecPairAsAdeles F v := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.smul_fst, Prod.smul_snd, infE_smul, Prod.smul_mk]

theorem infPart2_add (w w' : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (w + w') = infPart2 w + infPart2 w' := by
  simp only [infPart2, Prod.fst_add, Prod.snd_add, infPart_add, Prod.mk_add_mk]

theorem infPart2_smul (t : ℝ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (rAd (F := F) t • w) = t • infPart2 w := by
  simp only [infPart2, Prod.smul_fst, Prod.smul_snd, infPart_smul, Prod.smul_mk]

theorem exists_infLin (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∀ v, B (mixedSpaceVecPairAsAdeles F v) = mixedSpaceVecPairAsAdeles F (L v) := by
  refine ⟨{ toFun := fun v => infPart2 (B (mixedSpaceVecPairAsAdeles F v))
            invFun := fun v => infPart2 (B.symm (mixedSpaceVecPairAsAdeles F v))
            map_add' := fun v v' => by simp only [mixedSpaceVecPairAsAdeles_add, map_add (f := _), infPart2_add]
            map_smul' := fun t v => by simp only [mixedSpaceVecPairAsAdeles_real_smul, map_smul, infPart2_smul, RingHom.id_apply]
            left_inv := fun v => by
              show infPart2 (B.symm (mixedSpaceVecPairAsAdeles F (infPart2 (B.toLinearMap (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [mixedSpaceVecPair_archimedeanPart_linearMap_apply]
              simp [archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
            right_inv := fun v => by
              show infPart2 (B (mixedSpaceVecPairAsAdeles F (infPart2 (B.symm.toLinearMap (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [mixedSpaceVecPair_archimedeanPart_linearMap_apply]
              simp [archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles] }, fun v => ?_⟩
  exact (mixedSpaceVecPair_archimedeanPart_linearMap_apply B.toLinearMap v).symm

theorem infLin_main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))),
      ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
        ∀ v, B (GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F v) = GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F (L v) :=
  fun _ _ _ _ _ B => exists_infLin B

end GlobalTheory.WeilAdm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivRestrictsRealLinearEquivArchimedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleLinearEquiv_restricts_realLinearEquiv_archimedean : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))),
      ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
        ∀ v, B (GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F v) = GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F (L v) := by
  first | exact @GlobalTheory.WeilAdm.infLin_main | exact GlobalTheory.WeilAdm.infLin_main | (intros; apply GlobalTheory.WeilAdm.infLin_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearMemSpanImagePartial
namespace GlobalTheory.MultilinearSpanImage

theorem multilinear_mem_span_image_partial {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module ℂ (M i)] {N : Type} [AddCommGroup N]
    [Module ℂ N] (Φ : MultilinearMap (RingHom.id ℂ) M N) (s : (i : ι) → Set (M i)) (t : Finset ι) :
    ∀ f : (i : ι) → M i, (∀ i ∈ t, f i ∈ Submodule.span ℂ (s i)) → (∀ i, i ∉ t → f i ∈ s i) →
      Φ f ∈ Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  refine Finset.induction_on t ?_ ?_
  · intro f _ h
    exact Submodule.subset_span ⟨f, fun i => h i (by simp), rfl⟩
  · intro a t ha ih f h1 h2
    have key : ∀ x ∈ Submodule.span ℂ (s a), Φ (Function.update f a x) ∈
        Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro i hi
          have hne : i ≠ a := by rintro rfl; exact ha hi
          simpa [hne] using h1 i (Finset.mem_insert_of_mem hi)
        · intro i hi
          by_cases h : i = a
          · subst h; simpa using hx
          · simpa [h] using h2 i (by simp [h, hi])
      | zero => rw [Φ.map_update_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Φ.map_update_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Φ.map_update_smul]; exact Submodule.smul_mem _ c hx
    have := key (f a) (h1 a (Finset.mem_insert_self a t))
    simpa using this

theorem multilinear_apply_mem_span_image {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [inst : (i : ι) → AddCommGroup (M i)] [inst_1 : (i : ι) → Module ℂ (M i)] {N : Type}
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N] (Φ : MultilinearMap (RingHom.id ℂ) M N)
    (s : (i : ι) → Set (M i)) (f : (i : ι) → M i) (hf : ∀ (i : ι), f i ∈ Submodule.span ℂ (s i)) :
    (Φ : ((i : ι) → M i) → N) f ∈ Submodule.span ℂ
      {y : N | ∃ (g : (i : ι) → M i), (∀ (i : ι), g i ∈ s i) ∧ y = (Φ : ((i : ι) → M i) → N) g} :=
  multilinear_mem_span_image_partial Φ s Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.MultilinearSpanImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem multilinear_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] {N : Type} [AddCommGroup N] [Module ℂ N]
    (Φ : MultilinearMap (RingHom.id ℂ) M N) (s : ∀ i, Set (M i)) (f : ∀ i, M i)
    (hf : ∀ i, f i ∈ Submodule.span ℂ (s i)) :
    Φ f ∈ Submodule.span ℂ {y | ∃ g : ∀ i, M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  first
  | exact @_root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
  | exact _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
  | (apply _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image ..)

theorem span_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    Submodule.span ℂ (Set.range (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) mu)) = ⊤ :=
  GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem span_wInf (lam : InfinitePlace E → DomWeight n) :
    Submodule.span ℂ (Set.range fun k : infU E n => wInf lam k.1) = ⊤ := by
  rw [eq_top_iff]
  rintro Q -
  obtain ⟨z, rfl⟩ := GlobalTheory.PiTensorCommute.mem_range_piTensorHomMap Q
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.piTensorHomMap_tprod_eq_map]
    refine Submodule.smul_mem _ _ ?_
    have h := multilinear_mem_span
      (PiTensorProduct.mapMultilinear ℂ (fun v => nablaSq ℂ n (lam v)) (fun v => nablaSq ℂ n (lam v)))
      (fun v => Set.range (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) (lam v))) f
      (fun v => by rw [span_smallRep_unitary]; trivial)
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨g, hg, rfl⟩
    choose u hu using hg
    obtain ⟨x, hx, hxc⟩ := GlobalTheory.InfSurj.exists_infU_cAll_eq E n
      (fun v => GlobalTheory.Branching.unitaryIncl n (u v)) (fun v => (u v).2)
    refine Submodule.subset_span ⟨⟨x, hx⟩, ?_⟩
    rw [PiTensorProduct.mapMultilinear_apply]
    change PiTensorProduct.map _ = _
    congr 1
    funext v
    rw [← hu v]
    have h1 := congrFun hxc v
    change cEmb v.embedding x = _ at h1
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x) = GlobalTheory.Branching.sqRep ℂ n (lam v) _
    rw [h1]
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem Phi_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Function.Injective (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  let b := Module.finBasis ℂ (Wsp lam)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := vecM S lam K') b
  have hxe : x = ∑ j, e x j ⊗ₜ b j := by
    conv_lhs => rw [← e.symm_apply_apply x]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype]
    simp
  have hval : ∀ (x₀ : finU (E := E) (n := n)) (k : infU E n), ∑ j, (e x j).1 x₀ (wInf lam k.1 (b j)) = 0 := by
    intro x₀ k
    have h := congrFun hx (x₀.1 * k.1)
    have hw : wInf lam (x₀.1 * k.1) = wInf lam k.1 := by rw [map_mul, wInf_fin, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxe, map_sum] at h
    simpa only [Phi_tmul, phiFun_apply, splitFin_mul, hw, Finset.sum_apply, Pi.zero_apply] using h
  have hall : ∀ (x₀ : finU (E := E) (n := n)) (T : Module.End ℂ (Wsp lam)), ∑ j, (e x j).1 x₀ (T (b j)) = 0 := by
    intro x₀ T
    let Λ : Module.End ℂ (Wsp lam) →ₗ[ℂ] ℂ :=
      { toFun := fun T => ∑ j, (e x j).1 x₀ (T (b j))
        map_add' := fun T T' => by simp [Finset.sum_add_distrib]
        map_smul' := fun c T => by simp [Finset.mul_sum] }
    have hS : Submodule.span ℂ (Set.range fun k : infU E n => wInf lam k.1) ≤ LinearMap.ker Λ := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hval x₀ k
    rw [span_wInf] at hS
    exact hS (Submodule.mem_top (x := T))
  have hc : e x = 0 := by
    refine Finsupp.ext fun j => Subtype.ext (funext fun x₀ => LinearMap.ext fun w => ?_)
    have h := hall x₀ ((b.coord j).smulRight w)
    simp [Finsupp.single_apply] at h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp), if_pos rfl] at h
  exact e.injective (hc.trans e.map_zero.symm)

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjectiveStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_map_phi_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Function.Injective (Phi S lam K') := by
  exact @GlobalTheory.BCT.TrKer.Phi_injective
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLowerBoundPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLowerBoundPrincipalLevel
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

theorem transv_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (Y : Data E r)
    (hX : Xx.toData = Y) (la : Wt Y.Ψ r) (M : ℝ) (hχ : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (htr : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b)) :
    ∀ v ∈ Xx.L', herm Y.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Y.Γ, Y.χ la γ = 1 ∧
        ∀ τ : Y.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Y.flowMat v τ ((M : ℂ) * τ.1 b) := by
  subst hX
  intro v hv hvv b hb hbi
  obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
  exact ⟨γ, hγ, hχ γ hγ, hγ'⟩

theorem lamSup_of_laws : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → F ≠ 0 → -lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U (xiR D) (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  classical
  intro D j H Dw l Xo c U dict h _ χ hχ a n ha F hF hval hF0
  have hσ₀ : GoodEmb c c.F.val.toRingHom := rfl
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hU := h.unf c.F.val.toRingHom hσ₀
  have hpq : Dw.p + Dw.q = D.R.r := hU.1.symm
  have hSD : SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp D.host.E H Dw l Xo c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (h.unf σ hσ)))
  set σ₀ := c.F.val.toRingHom with hσdef
  have hhol : rdU (U σ₀) F ∈ holSub (U σ₀).X (laU (U σ₀) a n) := ((mem_cusp _ _ _ _ _ F).1 hF).2 σ₀ hσ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ₀).X (laU (U σ₀) a n) hhol
  have hfin : supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) ≠ ⊤ := supE_cusp_ne_top hσ₀ hF
  have hpos : 0 < supN (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (hSD a n ha σ₀ hσ₀ F hF heq.symm) hF0
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((U σ₀).X k).dom, ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) x ≤
      2 * ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 := by linarith
  obtain ⟨Xx, hX, hXg, hΛ, -, M, hM, hMk, htr⟩ := GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict h σ₀ hσ₀ k
  have hsp := GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict h σ₀ hσ₀ a n k
  set s : ℝ := ((absA Dw a : ℕ) : ℝ) with hs
  set t : ℝ := ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) with ht
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have hw : (∑ τ, ((U σ₀).X k).spread (laU (U σ₀) a n k) τ) ≤ s + t + 1 := by linarith
  have hw1 : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((U σ₀).X k) hX _ _ z0 M (s + t + 1) (hSS k) hM
    hw hw1 hr (transv_of_eq Xx _ hX _ M (h.chiTriv σ₀ hσ₀ a n ha k) htr) hz0 hhalf hposz
  have hp0 : Xx.p0 = Dw.q := (congrArg Data.p0 hX).trans (hU.2.1 k).1
  have heps : epStar M (fdeg D.host.E) (s + t + 1) Xx.k0 = epsLev D.host.E D.host.d l.M (s + t + 1) := by
    unfold epsLev epStar
    congr 2
    rw [← hMk]
    ring
  have hLa : frameBasisRadius D.R.r Xx.p0 (fdeg D.host.E) (dE D.host.E) (Real.sqrt (epStar M (fdeg D.host.E) (s + t + 1) Xx.k0))
      (3 * frameRadius (s + t + 1) D.R.r / 5) = cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    unfold cmLen
    rw [hp0, heps]
  rw [hLa] at hLB
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * Xx.k0)| + 3 + Real.log (dE D.host.E) := by
    have := Real.log_nonneg hd1
    have := le_abs_self (Real.log (M * Xx.k0))
    have := abs_nonneg (Real.log (M * Xx.k0))
    linarith
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.T.exists_constant_cmEvaluation_fits_room
  have hLa1 : 1 ≤ cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    rw [← hLa]
    exact (hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) |Real.log (M * Xx.k0)| 0 M Xx.k0 (s + t + 1) hf1 hr
      Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos hw1 hlog).1
  have hSpos : ∀ σ, 0 < supC Xo c U (xiR D) (goodOf c σ) a n F := fun σ => by
    unfold supC
    refine mul_pos (lieFac_pos _ _ _) (lt_of_le_of_ne (supN_nonneg _ _ _) fun h0 => hF0 ?_)
    exact hSD a n ha _ (Formalism.L2.Pj.goodEmb_goodOf (c := c) σ) F hF h0.symm
  have h5 := GlobalTheory.T.meanLogSupNorm_lowerBound_cmFrame_nonvanishing D.host.E H Dw l Xo c D.R.r U (xiR D) h.unf h.xiAbs (by omega) χ hχ a n ha F hF hval hSpos
    k ⟨x, hx⟩ Xx hX D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  refine le_trans ?_ h5
  have et : ((Module.finrank ℚ D.host.E / 2 * D.R.r : ℕ) : ℝ) * n = t := by
    rw [ht]
    simp only [fdeg, Nat.cast_mul]
  rw [et]
  unfold lamSup
  apply le_of_eq
  simp only [absA] at hs
  rw [← hs]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLowerBoundPrincipalLevelStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogSupNorm_lowerBound_principalLevel : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → F ≠ 0 → -lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U (xiR D) (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.lamSup_of_laws | exact GlobalTheory.lamSup_of_laws | (intros; apply GlobalTheory.lamSup_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirst
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamPet

open scoped ENNReal

theorem log_le_of_sq_le {A B : ℝ≥0∞} {K L : ℝ} (hL : 0 < L) (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hA0 : A ≠ 0)
    (h : A ^ 2 ≤ ENNReal.ofReal K * B ^ 2) :
    0 < L * B.toReal ∧ Real.log (L * A.toReal) ≤ 1 / 2 * Real.log K + Real.log (L * B.toReal) := by
  have hApos : 0 < A.toReal := ENNReal.toReal_pos hA0 hA
  have hK0 : 0 ≤ K := by
    by_contra hK
    rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hK)), zero_mul] at h
    exact hA0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h zero_le))
  have h2 : A.toReal ^ 2 ≤ K * B.toReal ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB)) h
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_pow] at this
  have hB0 : 0 < B.toReal := by
    rcases (ENNReal.toReal_nonneg (a := B)).lt_or_eq with hb | hb
    · exact hb
    · rw [← hb] at h2; nlinarith
  have hKpos : 0 < K := by
    by_contra hK
    have : K * B.toReal ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hK) (sq_nonneg _)
    nlinarith
  refine ⟨mul_pos hL hB0, ?_⟩
  rw [Real.log_mul hL.ne' hApos.ne', Real.log_mul hL.ne' hB0.ne']
  have h3 : Real.log (A.toReal ^ 2) ≤ Real.log (K * B.toReal ^ 2) := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul hKpos.ne' (by positivity), Real.log_pow] at h3
  push_cast at h3
  linarith

theorem mean_log_petersson_ge : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 → (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧ -lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) / (Module.finrank ℚ c.F : ℝ) := by
  intro hM hT D j H Dw l Xo c U dict hL _ χ hχ a n hD F hF hF0
  have hFc : (F : Rul Xo c) ∈ cusp Xo c U a n := cuspW_wtZ (Xo := Xo) (c := c) (U := U) a n ▸ F.2
  have hF0' : (F : Rul Xo c) ≠ 0 := fun h => hF0 (Subtype.ext h)
  have hsup := GlobalTheory.T.meanLogSupNorm_lowerBound_principalLevel D j H Dw l Xo c U dict hL χ hχ a n hD _ hFc hF hF0'
  have hsl := GlobalTheory.T.weighted_frame_sum_positive hM hT D j H Dw l Xo c U dict hL
  have hsp := GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict hL
  have hdef : Formalism.L2.Pj.SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp _ H Dw l Xo c _ _ hL.unf)
  set x := xiR D
  set K := supConst D.host.E D.R.r D.host.d l.M
    (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) with hK
  have hper : ∀ σ : c.F →+* ℂ, 0 < normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F ∧
      Real.log (supC Xo c U x (goodOf c σ) a n F) ≤
        1 / 2 * Real.log K + Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    intro σ
    have hσ : GoodEmb c (goodOf c σ) := Formalism.L2.PjFree.goodEmb_goodOf c σ
    have hhol := ((mem_cusp Xo c U a n _).1 hFc).2 _ hσ
    have hw : (0 : ℝ) < ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 := by positivity
    have hb := hsl _ hσ (laU (U (goodOf c σ)) a n) _ hw
      (fun k => (hsp _ hσ a n k).trans (by linarith)) (hL.chiTriv _ hσ a n hD) _ hhol
    have hne0 : supE (U (goodOf c σ)).X (laU (U (goodOf c σ)) a n) (rdU (U (goodOf c σ)) F) ≠ 0 := by
      intro h0
      refine hF0' (hdef a n hD _ hσ _ hFc ?_)
      unfold supN; rw [h0, ENNReal.toReal_zero]
    have hfin := supE_cusp_ne_top hσ hFc
    obtain ⟨_, _, _, _, _, hdu, _⟩ := hL.dictU _ hσ
    have hpfin : petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
        (rdU (U (goodOf c σ)) F) ≠ ⊤ :=
      petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hhol
    have key := log_le_of_sq_le (lieFac_pos Dw x a) hfin hpfin hne0 hb
    have e : normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F = lieFac Dw x a *
        (petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
          (rdU (U (goodOf c σ)) F)).toReal := by
      show lieFacZ Dw x (wtZ a n) * _ = _
      rw [lieFacZ_wtZ, modelWt_wtZ]
    rw [e]
    exact key
  refine ⟨fun σ => (hper σ).1, ?_⟩
  have hN : (0 : ℝ) < (Module.finrank ℚ c.F : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (Finset.univ : Finset (c.F →+* ℂ)).card = Module.finrank ℚ c.F := by
    rw [Finset.card_univ]; exact NumberField.Embeddings.card c.F ℂ
  have hsum : (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U x (goodOf c σ) a n F)) -
      (Module.finrank ℚ c.F : ℝ) * (1 / 2 * Real.log K) ≤
      ∑ σ : c.F →+* ℂ, Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun σ _ => (hper σ).2
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at this
    linarith
  have e : lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ)
      ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) = lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re
      ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 / 2 * Real.log K := rfl
  rw [e, le_div_iff₀ hN]
  rw [le_div_iff₀ hN] at hsup
  nlinarith

end GlobalTheory.LamPet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirstStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_first : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 → (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧ -lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.LamPet.mean_log_petersson_ge | exact GlobalTheory.LamPet.mean_log_petersson_ge | (intros; apply GlobalTheory.LamPet.mean_log_petersson_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCoordsMovedStaySupportedAndRecovered
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCoordsMovedStaySupportedAndRecovered
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem at_mul_of_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n d : ℕ} (G : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (H : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (L : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hL : At (evI F) L) : At (evI F) (G * L * Hᵀ) := by
  intro u hu
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hL u hu, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_infAd_of_evI {F : Type} [Field F] [NumberField F] (u : AF F) (hu : evI F u = 0)
    (α : mixedEmbedding.mixedSpace F) : u * infAd F α = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
  refine Prod.ext ?_ ?_
  · show u.1 * _ = 0
    rw [h1, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem eq_infAd_of_ann {F : Type} [Field F] [NumberField F] (z : AF F)
    (hz : ∀ a : AF F, evI F a = 0 → a * z = 0) : z = infAd F (evI F z) := by
  obtain ⟨a, ha1, ha2⟩ : ∃ a : AF F, a.1 = 0 ∧ a.2 = 1 := ⟨(0, 1), rfl, rfl⟩
  have h0 : evI F a = 0 := by
    have e : evI F a = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 := rfl
    rw [e, ha1, map_zero]
  have h2 : z.2 = 0 := by
    have h3 := congrArg Prod.snd (hz a h0)
    have h4 : (a * z).2 = a.2 * z.2 := rfl
    rw [h4, ha2, one_mul] at h3
    exact h3
  refine Prod.ext ?_ ?_
  · show z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F z.1)
    rw [RingEquiv.symm_apply_apply]
  · show z.2 = 0
    exact h2

theorem liftI_at_movI : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), At (evI F) (liftI M ζ) ∧ liftI M (movI M p ζ) = actAB (cA σ) p⁻¹ (liftI M ζ) := by
  intro F E _ _ _ _ _ σ n d X W M p ζ
  have hL : At (evI F) (liftI M ζ) := by
    intro u hu
    unfold liftI
    rw [← LinearEquiv.map_smul]
    convert (M.co.e.symm).map_zero using 2
    refine Prod.ext ?_ ?_
    · funext i
      exact mul_infAd_of_evI u hu _
    · funext i
      exact mul_infAd_of_evI u hu _
  refine ⟨hL, ?_⟩
  have hw : At (evI F) (actAB (cA σ) p⁻¹ (liftI M ζ)) := at_mul_of_at _ _ _ hL
  set w := actAB (cA σ) p⁻¹ (liftI M ζ) with hwdef
  have hc : ∀ u : AF F, evI F u = 0 → u • M.co.e w = 0 := by
    intro u hu
    rw [← LinearEquiv.map_smul, hw u hu, LinearEquiv.map_zero]
  unfold liftI movI arch
  conv_rhs => rw [← M.co.e.symm_apply_apply w]
  congr 1
  refine Prod.ext ?_ ?_
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.fst (hc a ha)) i).symm
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.snd (hc a ha)) i).symm

end GlobalTheory.ArchDecay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCoordsMovedStaySupportedAndRecoveredStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanCoords_moved_stay_supported_and_recovered : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), At (evI F) (liftI M ζ) ∧ liftI M (movI M p ζ) = actAB (cA σ) p⁻¹ (liftI M ζ) := by
  first | exact @GlobalTheory.ArchDecay.liftI_at_movI | exact GlobalTheory.ArchDecay.liftI_at_movI | (intros; apply GlobalTheory.ArchDecay.liftI_at_movI <;> assumption)
end
end

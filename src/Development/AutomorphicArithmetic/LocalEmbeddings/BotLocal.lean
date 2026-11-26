module

public import Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdUnitInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.LocalCharConductorLeOfHeckeExponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.localChar_conductor_le_of_heckeExponent :
    ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH →
        ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : ℕ), GlobalTheory.CMVal.ExpAt νH (splitPrime τ) c →
        GlobalTheory.SplitFlip.CondLE (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) c (chrW ν τ) ∧ (¬ GlobalTheory.LFun.UnrAt ν (splitPrime τ) → 1 ≤ c) := by
  intro D ν νH h v τ c hc
  refine ⟨fun x hx => ?_, fun hn => ?_⟩
  · have h1 : Valued.v (x : Fv D.host.F v) = 1 := (GlobalTheory.FlipMatch.isEquiv_Fv v).eq_one_iff_eq_one.1 hx.1
    have h2 : Valued.v ((x : Fv D.host.F v) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      refine ((GlobalTheory.FlipMatch.isEquiv_Fv v _ _).1 hx.2).trans_eq ?_
      rw [Units.val_pow_eq_pow_val, map_pow, GlobalTheory.ChrWUnif.valued_unifAt, ← WithZero.exp_nsmul]
      simp
    have h3 := (hc c).2 le_rfl (Units.map (complMap (splitPrime_under τ)).toMonoidHom x)
      ((SplitTie.valued_complMap τ (splitPrime_under τ) _).trans h1) (by
        refine le_of_eq_of_le ?_ h2
        rw [← SplitTie.valued_complMap τ (splitPrime_under τ), RingHom.map_sub, RingHom.map_one]
        rfl)
    rw [← locChar_eq_of_chrEq h] at h3
    exact h3
  · by_contra h0
    apply hn
    rw [unrAt_iff_of_chrEq h]
    intro x hx
    refine (hc 0).2 (by omega) x hx ?_
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valuation.map_sub_le _ (le_of_eq hx) (le_of_eq (map_one _))
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsScaledStandardPairSectionsOfMaxCompactTran
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_iff_isGLO {n : ℕ} (g : GL (Fin n) k) : g ∈ KO k (Fin n) ↔ IsGLO g.val := by
  constructor
  · intro hg
    exact ⟨((mem_KO_iff g).1 hg).1, valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    have hu : IsUnit A.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
    refine ⟨u, Units.ext ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
    rw [hu', e]

theorem mul_mem_cball {m p r : Type} [Fintype p] {s : kˣ} {A : Matrix m p k} {B : Matrix p r k}
    (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ cball s) (i : m) (j : r) : (A * B) i j ∈ cball s := by
  rw [Matrix.mul_apply]
  refine Finset.sum_induction _ (· ∈ cball s) (fun x y hx hy => add_mem_cball hx hy) ?_ fun l _ => ?_
  · simp only [cball, Set.mem_setOf_eq]
    simp
  · simp only [cball, Set.mem_setOf_eq]
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hA i l)).trans (hB l j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem blk₁_mul {m m' a a' : ℕ} (M : Matrix (Fin m') (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem blk₂_mul {m m' a a' : ℕ} (M : Matrix (Fin m') (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
theorem stdA_mul {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k} {g₀ : GL (Fin a) k}
    (hg₀ : g₀.val = blk₁ X) (g : GL (Fin a) k) :
    stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
      ((fun g : GL (Fin a) k => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k))).indicator
        (fun _ => (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) then 1 else 0)) g := by
  have hb1 : blk₁ (g.val * X) = (g * g₀).val := by rw [blk₁_mul, Units.val_mul, hg₀]
  have hb2 : blk₂ (g.val * X) = (g * g₀).val * ((g₀⁻¹).val * blk₂ X) := by
    rw [blk₂_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  by_cases hS : g * g₀ ∈ KO k (Fin a)
  · rw [Set.indicator_of_mem (by simpa using hS)]
    have hG : IsGLO (blk₁ (g.val * X)) := hb1 ▸ (mem_KO_iff_isGLO _).1 hS
    have hdet : (blk₁ (g.val * X)).det ≠ 0 := hb1 ▸ (g * g₀).det_ne_zero
    have hcond : (∀ i j, blk₂ (g.val * X) i j ∈ cball (ϖ ^ c)) ↔
        ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) := by
      constructor
      · intro H
        have e : (g₀⁻¹).val * blk₂ X = ((g * g₀)⁻¹).val * blk₂ (g.val * X) := by
          rw [hb2, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).2 H
      · intro H
        rw [hb2]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).1 H
    have hu : Units.mk0 _ hdet = gdet g * gdet g₀ := by
      ext; simp [hb1, Matrix.GeneralLinearGroup.val_det_apply]
    have hv : valuation k ((gdet (g * g₀) : kˣ) : k) = 1 := valuation_gdet_of_mem_KO hS
    have hap : apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
        apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
      have : gdet g = gdet (g * g₀) * (gdet g₀)⁻¹ := by rw [gdet_mul]; group
      rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv, neg_div]
    by_cases hc : ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c)
    · rw [if_pos hc, stdA, dite_eq_left ⟨hdet, hG, hcond.2 hc⟩, hu, hap, map_mul]
      simp only [_root_.mul_inv_rev, Units.val_mul, mul_one]
      have h1 : ((ν (gdet g) : ℂˣ) : ℂ) * (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      linear_combination ((((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2)) * h1
    · rw [if_neg hc, stdA, dite_eq_right (fun H => hc (hcond.1 H.2.2))]
      simp
  · rw [Set.indicator_of_notMem (by simpa using hS), stdA, dite_eq_right (fun H => hS ((mem_KO_iff_isGLO _).2 (hb1 ▸ H.2.1)))]
    simp

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
theorem stdB_mul {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c a a' : ℕ} {Y : Matrix (Fin a') (Fin (a + a')) k} {g₀ : GL (Fin a') k}
    (hg₀ : g₀.val = blk₂ Y) (g : GL (Fin a') k) :
    stdB ν ϖ c a a' (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
      ((fun g : GL (Fin a') k => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k))).indicator
        (fun _ => (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) then 1 else 0)) g := by
  have hb1 : blk₂ (g.val * Y) = (g * g₀).val := by rw [blk₂_mul, Units.val_mul, hg₀]
  have hb2 : blk₁ (g.val * Y) = (g * g₀).val * ((g₀⁻¹).val * blk₁ Y) := by
    rw [blk₁_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  by_cases hS : g * g₀ ∈ KO k (Fin a')
  · rw [Set.indicator_of_mem (by simpa using hS)]
    have hG : IsGLO (blk₂ (g.val * Y)) := hb1 ▸ (mem_KO_iff_isGLO _).1 hS
    have hdet : (blk₂ (g.val * Y)).det ≠ 0 := hb1 ▸ (g * g₀).det_ne_zero
    have hcond : (∀ i j, blk₁ (g.val * Y) i j ∈ cball (ϖ ^ c)) ↔
        ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) := by
      constructor
      · intro H
        have e : (g₀⁻¹).val * blk₁ Y = ((g * g₀)⁻¹).val * blk₁ (g.val * Y) := by
          rw [hb2, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).2 H
      · intro H
        rw [hb2]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).1 H
    have hu : Units.mk0 _ hdet = gdet g * gdet g₀ := by
      ext; simp [hb1, Matrix.GeneralLinearGroup.val_det_apply]
    have hv : valuation k ((gdet (g * g₀) : kˣ) : k) = 1 := valuation_gdet_of_mem_KO hS
    have hap : apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
        apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
      have : gdet g = gdet (g * g₀) * (gdet g₀)⁻¹ := by rw [gdet_mul]; group
      rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv, neg_div]
    by_cases hc : ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)
    · rw [if_pos hc, stdB, dite_eq_left ⟨hdet, hG, hcond.2 hc⟩, hu, hap, map_mul]
      simp only [_root_.mul_inv_rev, Units.val_mul, mul_one]
      have h1 : ((ν (gdet g) : ℂˣ) : ℂ) * (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      linear_combination ((((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2)) * h1
    · rw [if_neg hc, stdB, dite_eq_right (fun H => hc (hcond.1 H.2.2))]
      simp
  · rw [Set.indicator_of_notMem (by simpa using hS), stdB, dite_eq_right (fun H => hS ((mem_KO_iff_isGLO _).2 (hb1 ▸ H.2.1)))]
    simp

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]


open Classical in
theorem bigF_stdA {ν : kˣ →* ℂˣ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) {a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k}
    {g₀ : GL (Fin a) k} (hg₀ : g₀.val = blk₁ X) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
      (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) then 1 else 0) := by
  set V : ℂ := (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) then 1 else 0) with hV
  set S : Set (GL (Fin a) k) := (fun g => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := GlobalTheory.OneSquareZeta.exists_unique_shell hϖ g₀⁻¹
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) = S.indicator (fun _ => V) g := stdA_mul hg₀
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν
      ((Fintype.card (Fin (a + a')) : ℂ) / 2) (fun M => stdA ν ϖ c a a' (M * X)) m.1 =
      (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • V := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => V) hSm
    rw [e1, setIntegral_const]
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₀⁻¹⁻¹ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₀⁻¹⁻¹ * g₀⁻¹ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₀⁻¹⁻¹)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₀⁻¹ = (g * g₀⁻¹⁻¹)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

theorem bigF_stdA_of_det_eq_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k}
    (hX : (blk₁ X).det = 0) : bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0 := by
  have h0 : ∀ g : Matrix (Fin a) (Fin a) k, stdA ν ϖ c a a' (g * X) = 0 := fun g => by
    rw [stdA, dite_eq_right]
    rintro ⟨hd, -⟩
    exact hd (by rw [blk₁_mul, det_mul, hX, mul_zero])
  simp [bigF, shellSum, shell, h0]


open Classical in
theorem smallF_stdB {ν : kˣ →* ℂˣ} {ϖ : kˣ} (c : ℕ) {a a' : ℕ} {Y : Matrix (Fin a') (Fin (a + a')) k}
    {g₀ : GL (Fin a') k} (hg₀ : g₀.val = blk₂ Y) :
    smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y =
      (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) then 1 else 0) := by
  set S : Set (GL (Fin a') k) := (fun g => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a') k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a') k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a') k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a'))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  unfold smallF
  simp_rw [stdB_mul hg₀]
  rw [← hSdef]
  refine (integral_indicator hSm).trans ((setIntegral_const _).trans ?_)
  erw [hS1, one_smul]

theorem smallF_stdB_of_det_eq_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {a a' : ℕ} {Y : Matrix (Fin a') (Fin (a + a')) k}
    (hY : (blk₂ Y).det = 0) : smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y = 0 := by
  have h0 : ∀ g : Matrix (Fin a') (Fin a') k, stdB ν ϖ c a a' (g * Y) = 0 := fun g => by
    rw [stdB, dite_eq_right]
    rintro ⟨hd, -⟩
    exact hd (by rw [blk₂_mul, det_mul, hY, mul_zero])
  simp [smallF, h0]

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

variable {k : Type} [Field k]

theorem det_mul_det_blk {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    (gdet h : k) * (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val)).det =
      (blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val)).det := by
  set e : Fin a ⊕ Fin a' ≃ Fin (a + a') := finSumFinEquiv with he
  set H := h.val.submatrix e e with hH
  set Hi := (h⁻¹).val.submatrix e e with hHi
  have hHH : H * Hi = 1 := by
    rw [hH, hHi, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hb : fromBlocks (H.toBlocks₁₁ * Hi.toBlocks₁₁ + H.toBlocks₁₂ * Hi.toBlocks₂₁)
      (H.toBlocks₁₁ * Hi.toBlocks₁₂ + H.toBlocks₁₂ * Hi.toBlocks₂₂)
      (H.toBlocks₂₁ * Hi.toBlocks₁₁ + H.toBlocks₂₂ * Hi.toBlocks₂₁)
      (H.toBlocks₂₁ * Hi.toBlocks₁₂ + H.toBlocks₂₂ * Hi.toBlocks₂₂) = fromBlocks 1 0 0 1 := by
    rw [← fromBlocks_multiply, fromBlocks_toBlocks, fromBlocks_toBlocks, hHH, fromBlocks_one]
  obtain ⟨h11, -, h21, -⟩ := fromBlocks_inj.1 hb
  have key : H * fromBlocks Hi.toBlocks₁₁ 0 Hi.toBlocks₂₁ 1 = fromBlocks 1 H.toBlocks₁₂ 0 H.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks H]
    rw [fromBlocks_multiply, h11, h21]
    simp
  have hd := congrArg Matrix.det key
  rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, det_one, mul_one, one_mul] at hd
  have e1 : (gdet h : k) = H.det := by
    rw [hH, det_submatrix_equiv_self]; rfl
  have e2 : blk₁ (X0 k e * (invT h).val) = (Hi.toBlocks₁₁)ᵀ := by
    ext i j; simp [blk₁, frameMatrixFirstColumnBlock_mul_apply, invT_val, hHi, toBlocks₁₁, he]
  have e3 : blk₂ (Y0 k e * h.val) = H.toBlocks₂₂ := by
    ext i j; simp [blk₂, frameMatrixSecondColumnBlock_mul_apply, hH, toBlocks₂₂, he]
  rw [e1, e2, e3, det_transpose, hd]

theorem blk_orth {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    blk₁ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val) *
        (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val))ᵀ +
      blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val) *
        (blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val))ᵀ = 0 := by
  have h0 := frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero (k := k) (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) h
  ext i j
  have h1 := congrFun (congrFun h0 i) j
  rw [Matrix.mul_apply, Fin.sum_univ_add] at h1
  simpa [Matrix.mul_apply, blk₁, blk₂] using h1

theorem inv_mul_blk {a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k} {Y : Matrix (Fin a') (Fin (a + a')) k}
    (hXY : blk₁ Y * (blk₁ X)ᵀ + blk₂ Y * (blk₂ X)ᵀ = 0) {g₀ : GL (Fin a) k} {g₁ : GL (Fin a') k}
    (hg₀ : g₀.val = blk₁ X) (hg₁ : g₁.val = blk₂ Y) :
    (g₁⁻¹).val * blk₁ Y = -((g₀⁻¹).val * blk₂ X)ᵀ := by
  have hC : blk₁ Y * (blk₁ X)ᵀ = -(blk₂ Y * (blk₂ X)ᵀ) := eq_neg_of_add_eq_zero_left hXY
  calc (g₁⁻¹).val * blk₁ Y = (g₁⁻¹).val * blk₁ Y * ((blk₁ X)ᵀ * ((g₀⁻¹).val)ᵀ) := by
        rw [← transpose_mul, ← hg₀, Units.inv_mul, transpose_one, Matrix.mul_one]
    _ = (g₁⁻¹).val * (blk₁ Y * (blk₁ X)ᵀ) * ((g₀⁻¹).val)ᵀ := by simp only [Matrix.mul_assoc]
    _ = -(((g₁⁻¹).val * blk₂ Y) * (blk₂ X)ᵀ * ((g₀⁻¹).val)ᵀ) := by
        rw [hC]; simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    _ = -((g₀⁻¹).val * blk₂ X)ᵀ := by
        rw [← hg₁, Units.inv_mul, Matrix.one_mul, transpose_mul]

theorem matrixFirstColumnBlock_standardFrame_eq_one {a a' : ℕ} : blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _)) = 1 := by
  ext i j; simp [blk₁, X0, Matrix.one_apply, eq_comm]

theorem matrixLastColumnBlock_standardFrame_eq_zero {a a' : ℕ} : blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _)) = 0 := by
  ext i j
  simp only [blk₂, X0, Matrix.of_apply, Matrix.zero_apply]
  split_ifs with h
  · exfalso
    simp [Fin.ext_iff] at h
    omega
  · rfl

end GlobalTheory.StdPairMatch


open Classical in
theorem GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
    GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') =
        GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') ∧
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') ≠ 0 := by
  open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix GlobalTheory.StdPairMatch in
    intro k _ _ _ _ _ _ α β ν ϖ c m a a' hϖ hν _ _ _ _ _ _
    have key : ∀ h : GL (Fin (a + a')) k,
        bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') h =
          smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') h := by
      intro h
      rw [bigZetaIntegral_eq, smallP]
      have hJ := det_mul_det_blk (k := k) (a := a) (a' := a') h
      have hO := blk_orth (k := k) (a := a) (a' := a') h
      set X := X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val with hX
      set Y := Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val with hY
      by_cases hD : (blk₂ Y).det = 0
      · have hP : (blk₁ X).det = 0 := by
          rw [hD] at hJ; exact (mul_eq_zero.1 hJ).resolve_left (Units.ne_zero _)
        rw [bigF_stdA_of_det_eq_zero _ _ _ hP, smallF_stdB_of_det_eq_zero _ _ _ hD]
        simp
      · have hP : (blk₁ X).det ≠ 0 := fun h0 => hD (by rw [← hJ, h0, mul_zero])
        set g₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero (blk₁ X) hP with hg₀
        set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero (blk₂ Y) hD with hg₁
        rw [bigF_stdA hϖ c (g₀ := g₀) rfl, smallF_stdB c (g₀ := g₁) rfl]
        have hrel := inv_mul_blk hO (g₀ := g₀) (g₁ := g₁) rfl rfl
        have hcond : (∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c)) ↔
            (∀ i j, ((g₁⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)) := by
          rw [hrel]
          constructor
          · intro H i j
            rw [Matrix.neg_apply, Matrix.transpose_apply]
            exact neg_mem_cball (H j i)
          · intro H i j
            have := neg_mem_cball (H j i)
            rwa [Matrix.neg_apply, Matrix.transpose_apply, neg_neg] at this
        rw [if_congr hcond rfl rfl]
        have hdet : gdet g₁ = gdet h * gdet g₀ := Units.ext (by
          simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, hg₀, hg₁,
            Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
          exact hJ.symm)
        rw [hdet, map_mul, apow_mul]
        set I : ℂ := if ∀ (i : Fin a') (j : Fin a), ((g₁⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) then 1 else 0 with hI
        have eA : apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) *
            apow (gdet h) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) = apow (gdet h) (-(a : ℂ) / 2) := by
          rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
        have eN : (α (gdet h) : ℂ) = (ν (gdet h) : ℂ) * (β (gdet h) : ℂ) := by
          rw [hν, ← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
        have hx : (ν (gdet h) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [eN]
        simp only [_root_.mul_inv_rev, Units.val_mul]
        linear_combination (-(β (gdet h) : ℂ) * (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) *
            apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) * I * (ν (gdet h) : ℂ) *
            (((ν (gdet h))⁻¹ : ℂˣ) : ℂ)) * eA +
          (-(β (gdet h) : ℂ) * (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) *
            apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) * I * apow (gdet h) (-(a : ℂ) / 2)) * hx
    refine ⟨funext key, fun H => ?_⟩
    have h1 := congrFun H 1
    rw [bigZetaIntegral_eq, map_one, Units.val_one, Matrix.mul_one,
      bigF_stdA hϖ c (g₀ := 1) (by rw [Units.val_one, matrixFirstColumnBlock_standardFrame_eq_one]), matrixLastColumnBlock_standardFrame_eq_zero] at h1
    have h0 : (0 : k) ∈ cball (ϖ ^ c) := by simp [cball]
    simp [h0] at h1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZeroStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPair_localZetaMatch_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
    GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') =
        GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') ∧
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') ≠ 0 := by
  first | exact @GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | exact GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | (intros; apply GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private noncomputable def subst {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) :
    Matrix (Fin m) (Fin n) k ≃ₜ Matrix (Fin m) (Fin n) k where
  toFun X := g.val * X * h.val
  invFun X := (g⁻¹).val * X * (h⁻¹).val
  left_inv X := by
    show (g⁻¹).val * (g.val * X * h.val) * (h⁻¹).val = X
    rw [Matrix.mul_assoc g.val, ← Matrix.mul_assoc (g⁻¹).val, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    show g.val * ((g⁻¹).val * X * (h⁻¹).val) * h.val = X
    rw [Matrix.mul_assoc (g⁻¹).val, ← Matrix.mul_assoc g.val, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem subst_SB {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k)) :
    (fun X => f (g.val * X * h.val)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k) :=
  ⟨hf.1.comp_continuous (subst g h).continuous, hf.2.comp_homeomorph (subst g h)⟩

private theorem subst_ne {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    {Y : Matrix (Fin m) (Fin n) k} (hf : f Y ≠ 0) : ∃ X : Matrix (Fin m) (Fin n) k, f (g.val * X * h.val) ≠ 0 := by
  obtain ⟨X, rfl⟩ := (subst g h).surjective Y
  exact ⟨X, hf⟩

open GlobalTheory.StdPairCone in
private theorem stdA_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ X, stdA ν ϖ c a a' X ≠ 0 := by
  let X : Matrix (Fin a) (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append ((1 : Matrix (Fin a) (Fin a) k) i) (fun _ => 0)
  have h1 : blk₁ X = 1 := by ext i j; simp [blk₁, X]
  have h2 : blk₂ X = 0 := by ext i j; simp [blk₂, X]
  refine ⟨X, ?_⟩
  have h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdA, dite_eq_left h]
  exact Units.ne_zero _

open GlobalTheory.StdPairCone in
private theorem stdB_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ Y, stdB ν ϖ c a a' Y ≠ 0 := by
  let X : Matrix (Fin a') (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append (fun _ => 0) ((1 : Matrix (Fin a') (Fin a') k) i)
  have h1 : blk₂ X = 1 := by ext i j; simp [blk₂, X]
  have h2 : blk₁ X = 0 := by ext i j; simp [blk₁, X]
  refine ⟨X, ?_⟩
  have h : (blk₂ X).det ≠ 0 ∧ IsGLO (blk₂ X) ∧ ∀ i j, blk₁ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdB, dite_eq_left h]
  exact Units.ne_zero _

end SlopeTestRemainingChoices

theorem UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
        (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
        GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
        ∀ (gA : GL (Fin a) k) (gB : GL (Fin a') k) (cc : GL (Fin (a + a')) k), gA ∈ GlobalTheory.SplitWeil.KO k (Fin a) →
        ∃ (lam : ℂ) (Ξ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ), lam ≠ 0 ∧
          (∀ X, Ξ X = GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (cc⁻¹).valᵀ)) ∧
          (∀ Y, Ψ Y = lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val)) ∧
          Ξ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) ∧ Ξ ≠ 0 ∧ Ψ ≠ 0 ∧
          GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β Ξ =
            GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α Ψ := by
  intro k _ _ _ _ _ _ α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ gA gB cc hgA
  obtain ⟨hz, -⟩ := GlobalTheory.T.standardPair_localZetaMatch_ne_zero α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ
  obtain ⟨hA, hB⟩ := GlobalTheory.T.standardPair_members_mem_schwartzBruhat ν ϖ c a a' hϖ hcν
  have hab : ν * β = α := by
    rw [hν]
    ext x
    simp
  have : @Measure.IsHaarMeasure (GL (Fin a') k) _ _
      (@Units.instMeasurableSpace (Matrix (Fin a') (Fin a') k) _
        GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix)
      (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) :=
    GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO
  obtain ⟨lam, hl, H⟩ := GlobalTheory.T.zetaIdentity_persists_row_column_changes k a a rfl (Fin a') (Fin a') (Fin (a + a')) (Fin (a + a')) (Equiv.refl _)
    (Equiv.refl _) finSumFinEquiv finSumFinEquiv (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a')))
    (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) ϖ ν β gA gB cc hgA
  rw [hab] at H
  have H' := H _ _ hz
  refine ⟨lam, fun X => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (GlobalTheory.SplitFlip.invT cc).val),
    fun Y => lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val), hl, fun _ => rfl, fun _ => rfl,
    subst_SB gA _ hA, (GlobalTheory.WeilM.SB _).smul_mem lam (subst_SB gB cc hB), ?_, ?_, H'⟩
  · obtain ⟨Y, hY⟩ := stdA_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gA (GlobalTheory.SplitFlip.invT cc) hY
    exact fun h => hX (congrFun h X)
  · obtain ⟨Y, hY⟩ := stdB_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gB cc hY
    exact fun h => mul_ne_zero hl hX (congrFun h X)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StdPairConeChars

theorem condLE_mono {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {e m : ℕ} (hem : e ≤ m)
    {χ : (Fv F v)ˣ →* ℂˣ} (h : GlobalTheory.SplitFlip.CondLE (unifAt v) e χ) : GlobalTheory.SplitFlip.CondLE (unifAt v) m χ := by
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have h1 : ValuativeRel.valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) ≤ 1 := hϖ.mem
  intro x hx
  refine h x ⟨hx.1, hx.2.trans ?_⟩
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' h1 hem

theorem nu_cond_at_ram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : B.P, v.1 ∈ X.T →
      GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) ∧ 1 ≤ (condExp (chrW X.ν (B.τ v))) ∧
      chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) ∧
      (∃ m, GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.α (B.τ v)) ∧ GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.β (B.τ v))) ∧
      (∀ x, ‖(chrW X.α (B.τ v) x : ℂ)‖ = 1) ∧ ∀ x, ‖(chrW X.β (B.τ v) x : ℂ)‖ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hvT
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v.1)).choose_spec
  have hα := hT.chars.heckeα.1
  have hβ := hT.chars.heckeβ.1
  have hν : Continuous X.ν := (show Continuous fun x => X.α x / X.β x from hα.div' hβ)
  have hne : {c | GlobalTheory.SplitFlip.CondLE (unifAt v.1) c (chrW X.ν (B.τ v))}.Nonempty :=
    GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.ν hν (B.τ v))
  have hmem : GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) := Nat.sInf_mem hne
  obtain ⟨eα, heα⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.α hα (B.τ v))
  obtain ⟨eβ, heβ⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.β hβ (B.τ v))
  have hram : ¬ UnrAt X.ν (splitPrime (B.τ v)) :=
    hT.chars.ram _ (by rw [splitPrime_under]; exact hvT)
  obtain ⟨x₀, hx₀, hx₀', hνx₀⟩ := GlobalTheory.StepFacNe.chrW_ram X.ν (B.τ v) hram
  have hx₀v : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) = 1 := by
    have h1 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀
    have h2 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀'
    have h3 : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) *
        ValuativeRel.valuation (Fv F v.1) ((x₀⁻¹ : (Fv F v.1)ˣ) : Fv F v.1) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValuativeRel.ValueGroupWithZero (Fv F v.1)) = _ := h3.symm
      _ ≤ _ := mul_le_of_le_one_right' h2
  have hc1 : 1 ≤ condExp (chrW X.ν (B.τ v)) := by
    by_contra h
    have h0 : condExp (chrW X.ν (B.τ v)) = 0 := by omega
    have hm := hmem
    rw [h0] at hm
    refine hνx₀ (hm x₀ ⟨hx₀v, ?_⟩)
    rw [pow_zero, Units.val_one, map_one]
    exact ((ValuativeRel.valuation (Fv F v.1)).map_sub _ _).trans (by simp [hx₀v])
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, locChar, Chars.ν]
  refine ⟨hmem, hc1, hdiv, ⟨max eα eβ, condLE_mono (le_max_left _ _) heα, condLE_mono (le_max_right _ _) heβ⟩,
    fun x => ?_, fun x => ?_⟩
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.α (B.τ v) x
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.β (B.τ v) x

end GlobalTheory.StdPairConeChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawCharacter_conductor_at_ramified_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : B.P, v.1 ∈ X.T →
      GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) ∧ 1 ≤ (condExp (chrW X.ν (B.τ v))) ∧
      chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) ∧
      (∃ m, GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.α (B.τ v)) ∧ GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.β (B.τ v))) ∧
      (∀ x, ‖(chrW X.α (B.τ v) x : ℂ)‖ = 1) ∧ ∀ x, ‖(chrW X.β (B.τ v) x : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.StdPairConeChars.nu_cond_at_ram | exact GlobalTheory.StdPairConeChars.nu_cond_at_ram | (intros; apply GlobalTheory.StdPairConeChars.nu_cond_at_ram <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.BotCoord
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

section Mat

variable {K : Type} [CommRing K] {a d k : Type} [Fintype a] [Fintype d] [Fintype k] [DecidableEq a] [DecidableEq d]
  [DecidableEq k]

theorem coord_fst (e : k ≃ d) (x : Matrix d a K) {G G' : Matrix a a K} (hG : G' * G = 1) (β : Matrix a a K) {b b' : Matrix a a K}
    (hb : b * b' = 1) {c c' : Matrix k k K} (hc : c * c' = 1) (γ : Matrix d d K) :
    (βᵀ * Gᵀ * b) * (b' * ((x * G')ᵀ.submatrix id e) * c'ᵀ) * (γ.submatrix e e * c)ᵀ = (γ * x * β)ᵀ.submatrix id e := by
  have h1 : c'ᵀ * cᵀ = 1 := by rw [← transpose_mul, hc, transpose_one]
  have h2 : Gᵀ * G'ᵀ = 1 := by rw [← transpose_mul, hG, transpose_one]
  have h3 : (x * G')ᵀ.submatrix id e = G'ᵀ * xᵀ.submatrix id e := by
    rw [transpose_mul]; ext i j; simp [Matrix.mul_apply]
  have h4 : (γ * x * β)ᵀ.submatrix id e = βᵀ * (xᵀ.submatrix id e * (γ.submatrix e e)ᵀ) := by
    rw [transpose_submatrix, Matrix.submatrix_mul_equiv, transpose_mul, transpose_mul]
    ext i j; simp [Matrix.mul_apply]
  rw [h3, h4, transpose_mul]
  calc _ = βᵀ * (Gᵀ * (b * b') * G'ᵀ) * xᵀ.submatrix id e * (c'ᵀ * cᵀ) * (γ.submatrix e e)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb, Matrix.mul_one, h2, h1]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]

theorem coord_snd (e : k ≃ d) (y : Matrix a d K) {G G' : Matrix a a K} (hG : G * G' = 1) (β : Matrix a a K) {b b' : Matrix a a K}
    (hb : b * b' = 1) {c c' : Matrix k k K} (hc : c * c' = 1) (H γ : Matrix d d K) (ξ : K) :
    (β * G' * b'ᵀ) * (-(bᵀ * (-G) * ((G' * y).submatrix id e) * (ξ • Hᵀ.submatrix e e)ᵀ * c)) * (c' * γ.submatrix e e) =
      (ξ • (β * (G' * y * H) * γ)).submatrix id e := by
  have h1 : b'ᵀ * bᵀ = 1 := by rw [← transpose_mul, hb, transpose_one]
  have h3 : (G' * y).submatrix id e = G' * y.submatrix id e := by ext i j; simp [Matrix.mul_apply]
  have h4 : (ξ • (β * (G' * y * H) * γ)).submatrix id e = ξ • (β * G' * (y.submatrix id e * H.submatrix e e * γ.submatrix e e)) := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp only [Matrix.mul_assoc]
    ext i j; simp [Matrix.mul_apply]
  have h5 : (ξ • Hᵀ.submatrix e e)ᵀ = ξ • H.submatrix e e := rfl
  rw [h3, h4, h5]
  calc _ = ξ • (β * G' * ((b'ᵀ * bᵀ) * (G * G') * y.submatrix id e * H.submatrix e e * (c * c') * γ.submatrix e e)) := by
        simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by rw [h1, hG, hc]; simp only [Matrix.mul_one, Matrix.one_mul]

end Mat

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_atPl (y : Fv D.host.F v) : piW τ (atPl (splitPrime τ) (complEquiv τ (splitPrime_under τ) y)) = y := by
  classical
  exact (complEquiv τ (splitPrime_under τ)).injective
    (by rw [GlobalTheory.FlipMatch.isPlaceIso_complEquiv τ, (atPl_spec _ _).2, Pi.single_eq_same])

theorem piW_atPl_one : piW τ (atPl (D := D) (splitPrime τ) 1) = 1 := by
  have := piW_atPl τ 1
  rwa [map_one] at this

theorem piW_conj_atPl_one : piW (τ.comp D.sp.cm.sig) (atPl (D := D) (splitPrime τ) 1) = 0 := by
  classical
  exact (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
    rw [GlobalTheory.FlipMatch.isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec _ _).2,
      Pi.single_eq_of_ne (splitPrime_comp_ne (isCMExt_host D) τ), map_zero])

theorem atPl_mul_eq_zero {z : AE D} (h : piW τ z = 0) : atPl (splitPrime τ) 1 * z = 0 := by
  classical
  refine ae_ext (by rw [RingHom.map_mul, (atPl_spec _ _).1, zero_mul, map_zero]) fun Q => ?_
  rw [RingHom.map_mul, RingHom.map_mul, (atPl_spec _ _).2, map_zero, map_zero]
  by_cases hQ : Q = splitPrime τ
  · subst hQ
    rw [← GlobalTheory.FlipMatch.isPlaceIso_complEquiv τ z, h, map_zero, mul_zero]
  · rw [Pi.single_eq_of_ne hQ, zero_mul]

theorem exists_map_piW {m n : Type} (U : Matrix m n (Fv D.host.F v)) : ∃ u : Matrix m n (AE D), u.map (piW τ) = U :=
  ⟨U.map fun y => atPl (splitPrime τ) (complEquiv τ (splitPrime_under τ) y), Matrix.ext fun _ _ => piW_atPl τ _⟩

theorem piW_incA (x : D.host.E) : piW τ (incA D x) = τ x :=
  (GlobalTheory.FlipMatch.piW_tmul τ 1 x).trans (by rw [map_one, one_mul])

theorem evW_eToEAf (x : D.host.E) : evW τ (eToEAf D x) = τ x := (evW_toEAf τ (incA D x)).trans (piW_incA τ x)

theorem half_iff {m n : ℕ} (hsum : atPl (D := D) (splitPrime τ) 1 + cA D (atPl (splitPrime τ) 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) (u : Matrix (Fin m) (Fin n) (AE D)) :
    ((At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ↔ IsHalf (atPl (splitPrime τ) 1) u) ∧
    ((At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) ↔ IsHalf (cA D (atPl (splitPrime τ) 1)) u) := by
  have hat := GlobalTheory.FlipMatch.at_atPl τ 1
  have hat' := GlobalTheory.FlipMatch.RowChart.at_cA hat
  have hone : At (evFin D.host.F v) u → ∀ p q, atPl (splitPrime τ) 1 * u p q + cA D (atPl (splitPrime τ) 1) * u p q = u p q :=
    fun h p q => by
      have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
      rw [sub_smul, one_smul, sub_eq_zero] at h1
      rw [← add_mul, hsum, ← Algebra.smul_def]
      exact (congrFun (congrFun h1 p) q).symm
  have hAt : ∀ b : AE D, At (evFin D.host.F v) b → IsHalf b u → At (evFin D.host.F v) u := fun b hb h c hc => by
    ext p q
    rw [Matrix.smul_apply, ← h p q, ← smul_mul_assoc, hb c hc, zero_mul, Matrix.zero_apply]
  refine ⟨⟨fun h p q => ?_, fun h => ⟨hAt _ hat h, Matrix.ext fun p q => ?_⟩⟩,
    ⟨fun h p q => ?_, fun h => ⟨hAt _ hat' h, Matrix.ext fun p q => ?_⟩⟩⟩
  · have h1 := congrArg (cA D) (atPl_mul_eq_zero τ (z := cA D (u p q))
      ((GlobalTheory.FlipMatch.RowChart.piW_cA_eq τ _).trans (congrFun (congrFun h.2 p) q)))
    rw [RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA, map_zero] at h1
    have h2 := hone h.1 p q
    rwa [h1, add_zero] at h2
  · rw [Matrix.map_apply, ← h p q, RingHom.map_mul, piW_conj_atPl_one, zero_mul, Matrix.zero_apply]
  · have h2 := hone h.1 p q
    rwa [atPl_mul_eq_zero τ (congrFun (congrFun h.2 p) q), zero_add] at h2
  · rw [Matrix.map_apply, ← h p q, RingHom.map_mul, GlobalTheory.FlipMatch.RowChart.piW_cA_eq, piW_conj_atPl_one, zero_mul,
      Matrix.zero_apply]

theorem gram_inv_map (S : HSp D) : (S.gram⁻¹).map τ * S.gram.map τ = 1 := by
  have := Matrix.map_mul (L := S.gram⁻¹) (M := S.gram) (f := (τ : D.host.E →+* Fv D.host.F v))
  rw [Matrix.nonsing_inv_mul _ (Formalism.L2.Theta.gram_det_ne S).isUnit, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this.symm

theorem frMapO_coX (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βX : GL (Fin X.rank) (Lev.EAf D)) (b : GL (Fin S.rank) (Fv D.host.F v)) (c : GL (Fin k) (Fv D.host.F v)) (x : WO S X) :
    ((βS.val.map (evW τ))ᵀ * (S.gram.map τ)ᵀ * b.val) * ((b⁻¹).val * (GlobalTheory.TripleRead.ptO S.gram e x).map (piW τ) * (c⁻¹).valᵀ) *
      ((((βX⁻¹).val.map (evW τ)).submatrix e e) * c.val)ᵀ = (((frMapO S X βS βX x).map (evW τ))ᵀ).submatrix id e := by
  have h1 : (GlobalTheory.TripleRead.ptO S.gram e x).map (piW τ) = (x.map (piW τ) * (S.gram⁻¹).map τ)ᵀ.submatrix id e := by
    have : (S.gram⁻¹).map τ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹).map (piW τ) := Matrix.ext fun _ _ => (piW_incA τ _).symm
    rw [this, ← Matrix.map_mul]
    rfl
  have h2 : (frMapO S X βS βX x).map (evW τ) = (βX⁻¹).val.map (evW τ) * x.map (piW τ) * βS.val.map (evW τ) := by
    have : x.map (piW τ) = (x.map (toEAf D)).map (evW τ) := Matrix.ext fun _ _ => (evW_toEAf τ _).symm
    rw [this, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  rw [h1, h2]
  exact coord_fst e _ (gram_inv_map τ S) _ b.mul_inv c.mul_inv _

theorem dualCoord_coY (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βX : GL (Fin X.rank) (Lev.EAf D)) (b : GL (Fin S.rank) (Fv D.host.F v)) (c : GL (Fin k) (Fv D.host.F v)) (y : WO S X) :
    ((βS⁻¹).val.map (evW τ) * (S.gram⁻¹).map τ * (b⁻¹).valᵀ) *
      (-(b.valᵀ * ((-1 : D.host.E) • S.gram).map τ * (GlobalTheory.TripleRead.ptO S.gram e y).map (piW (τ.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (X.gramᵀ).submatrix e e).map τ)ᵀ * c.val)) * ((c⁻¹).val * (βX.val.map (evW τ)).submatrix e e) =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S X βS βX y).map (evW τ)).submatrix id e := by
  have hs : (S.gram⁻¹).map star = (S.gram⁻¹)ᵀ := by
    have h0 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
    have := Matrix.conjTranspose_nonsing_inv S.gram
    rw [h0] at this
    ext a b
    exact congrFun (congrFun this b) a
  have h1 : (GlobalTheory.TripleRead.ptO S.gram e y).map (piW (τ.comp D.sp.cm.sig)) =
      ((S.gram⁻¹).map τ * ((y.map (cA D)).map (piW τ))ᵀ).submatrix id e := by
    have e1 : (S.gram⁻¹).map τ = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹).map (piW (τ.comp D.sp.cm.sig)))ᵀ :=
      Matrix.ext fun a b => ((piW_incA (τ.comp D.sp.cm.sig) _).trans (congrArg τ (congrFun (congrFun hs b) a))).symm
    have e2 : (y.map (cA D)).map (piW τ) = y.map (piW (τ.comp D.sp.cm.sig)) :=
      Matrix.ext fun _ _ => GlobalTheory.FlipMatch.RowChart.piW_cA_eq τ _
    rw [e1, e2, ← transpose_mul, ← Matrix.map_mul]
    rfl
  have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S X βS βX y).map (evW τ) = τ D.host.xi0 • ((βS⁻¹).val.map (evW τ) *
      ((S.gram⁻¹).map τ * ((y.map (cA D)).map (piW τ))ᵀ * X.gram.map τ) * βX.val.map (evW τ)) := by
    have e1 : ∀ {p : ℕ} (M : Matrix (Fin p) (Fin p) D.host.E), M.map τ = (M.map (incA D)).map (piW τ) := fun M =>
      Matrix.ext fun _ _ => (piW_incA τ _).symm
    have e2 : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) (AE D)), M.map (piW τ) = (M.map (toEAf D)).map (evW τ) := fun M =>
      Matrix.ext fun _ _ => (evW_toEAf τ _).symm
    rw [e1, e1 X.gram, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, e2, ← Matrix.map_mul, ← Matrix.map_mul,
      ← evW_eToEAf]
    exact Matrix.ext fun _ _ => map_mul (evW τ) _ _
  have h3 : ((-1 : D.host.E) • S.gram).map τ = -S.gram.map τ := Matrix.ext fun _ _ => by simp
  have h4 : (D.host.xi0 • (X.gramᵀ).submatrix e e).map τ = τ D.host.xi0 • (X.gram.map τ)ᵀ.submatrix e e :=
    Matrix.ext fun _ _ => map_mul τ _ _
  rw [h1, h2, h3, h4]
  exact coord_snd e _ (mul_eq_one_comm.1 (gram_inv_map τ S)) _ b.mul_inv c.mul_inv _ _ _

end GlobalTheory.BotMatch

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

namespace GlobalTheory.BotMatch

variable {D : D7}

set_option maxHeartbeats 1600000 in
theorem local_pair {ψ : AddChar (AF D.host.F) ℂ} {W W₁ X : HSp D} {A : GlobalTheory.ChainFr.Fr W} {A₁ : GlobalTheory.ChainFr.Fr W₁}
    {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs : Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank} {Xc : Chars D.host.F D.host.E} {om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
    {om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W} (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc) {R Rf}
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf) {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (sW : IsSelfDualC (GlobalTheory.Grid.sgn true W) ΛW) {βW : GL (Fin W.rank) (Lev.EAf D)} (fW : Formalism.L2.DIV.IsFrame βW ΛW)
    (hL : Γ.V.L = GlobalTheory.TripleSpaceW.conjSub ΛW) (βW₁ : GL (Fin W₁.rank) (Lev.EAf D)) (βX : GL (Fin X.rank) (Lev.EAf D))
    {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq (α / β) νH) (i : Bs.P) (hi : i.1 ∈ Xc.T) {c : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt νH (splitPrime (Bs.τ i)) c) :
    ∃ (I : ((Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (I' : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (φ : (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ)
      (φ' : (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) (lam : ℂ),
      Γ.M.IsLinW Bs.ψ (Bs.τ i) (Γ.V.bas i) (Γ.W.bas i) I ∧ Γ.M'.IsLinBar Bs.ψ (Bs.τ i) (Γ.V'.bas i) (Γ.W.bas i) I' ∧
      φ ∈ GlobalTheory.WeilM.SB _ ∧ φ' ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ lam ≠ 0 ∧ Rf.p i φ = Rf.p' i φ' ∧
      (∀ x : WO W X, I φ (((Γ.V.bas i)⁻¹).1 * (GlobalTheory.TripleRead.ptO (GlobalTheory.Grid.sgn true W).gram e x).map (piW (Bs.τ i)) *
          ((Γ.W.bas i)⁻¹).1ᵀ) =
        GlobalTheory.StdPairCone.stdA (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          ((((frMapO W X βW βX x).map (evW (Bs.τ i)))ᵀ).submatrix id e)) ∧
      ∀ y : WO W₁ X, I' φ' (-((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i) *
          (GlobalTheory.TripleRead.ptO W₁.gram e y).map (piW ((Bs.τ i).comp D.sp.cm.sig)) * (Γ.W.J.map (Bs.τ i))ᵀ * (Γ.W.bas i).1)) =
        lam * GlobalTheory.StdPairCone.stdB (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord W₁ X βW₁ βX y).map (evW (Bs.τ i))).submatrix id e) := by
  have hXν : Xc.ν = α / β := by
    show Xc.α / Xc.β = _
    rw [h.α, h.β]
  obtain ⟨I, I', hI, hI', -, -, hiff⟩ := hM.fin.zeta i hi
  obtain ⟨-, -, hquot, ⟨m, hmα, hmβ⟩, hua, hub⟩ := GlobalTheory.T.seesawCharacter_conductor_at_ramified_place _ _ _ Bs _ _ Γ Xc om om' hM.triple i hi
  obtain ⟨hcond, hc1⟩ := UpperTheory.localChar_conductor_le_of_heckeExponent D (α / β) νH hν i.1 (Bs.τ i) c hc
  have hram := hM.triple.chars.ram (splitPrime (Bs.τ i)) ((splitPrime_under (Bs.τ i)).symm ▸ hi)
  rw [hXν] at hram
  obtain ⟨gA, hgA, egA⟩ := UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis D (GlobalTheory.Grid.sgn true W) ΛW βW sW fW i.1 (Bs.τ i) (Γ.V.bas i)
    (hL ▸ hM.triple.geo.hV.bas i)
  have hx1 : (βX.val.map (evW (Bs.τ i))).submatrix e e * ((βX⁻¹).val.map (evW (Bs.τ i))).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.submatrix_one_equiv]
  let bX : GL (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) := ⟨_, _, hx1, mul_eq_one_comm.1 hx1⟩
  have hy1 : (βW₁⁻¹).val.map (evW (Bs.τ i)) * βW₁.val.map (evW (Bs.τ i)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hy2 := gram_inv_map (Bs.τ i) W₁
  have hy3 : ((Γ.V'.bas i)⁻¹).valᵀ * (Γ.V'.bas i).valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  let gB : GL (Fin W₁.rank) (Fv D.host.F i.1) :=
    ⟨_, _, hy1, mul_eq_one_comm.1 hy1⟩ * ⟨_, _, hy2, mul_eq_one_comm.1 hy2⟩ * ⟨_, _, hy3, mul_eq_one_comm.1 hy3⟩
  rw [← hXν] at hcond ⊢
  obtain ⟨lam, Ξ, Ψ, hlam, eΞ, eΨ, sΞ, sΨ, nΞ, nΨ, hz⟩ := UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate (Fv D.host.F i.1) _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c m
    W.rank W₁.rank (GlobalTheory.SplitFlip.exists_isUnif).choose_spec hquot (hc1 hram) hcond hmα hmβ hua hub gA gB
    ((Γ.W.bas i)⁻¹ * bX) hgA
  obtain ⟨φ, sφ, rfl⟩ := hI.bij.surjOn sΞ
  obtain ⟨φ', sφ', rfl⟩ := hI'.bij.surjOn sΨ
  refine ⟨I, I', φ, φ', lam, hI, hI', sφ, sφ', fun h0 => nΞ (by rw [h0, map_zero]), fun h0 => nΨ (by rw [h0, map_zero]), hlam,
    (hiff φ sφ φ' sφ').2 hz, fun x => ?_, fun y => ?_⟩
  · rw [eΞ, egA]
    exact congrArg _ (frMapO_coX (Bs.τ i) (GlobalTheory.Grid.sgn true W) X e βW βX (Γ.V.bas i) (Γ.W.bas i) x)
  · rw [eΨ, h.JW₁, h.JX]
    exact congrArg (fun z => lam * GlobalTheory.StdPairCone.stdB _ _ c _ _ z)
      (dualCoord_coY (Bs.τ i) W₁ X e βW₁ βX (Γ.V'.bas i) (Γ.W.bas i) y)

end GlobalTheory.BotMatch

end

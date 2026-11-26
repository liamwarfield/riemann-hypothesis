module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockAlg.MinFirst

noncomputable section
namespace GlobalTheory.RealLift.GenLift

section Objects

variable {P Q R S : ℕ}

theorem trace_Eab {p q : ℕ} (a b : Ix p q) : (Eab a b).trace = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h; simp [Eab, Matrix.trace_single_eq_same]
  · simp [Eab, Matrix.trace_single_eq_of_ne _ _ _ h]

def chAct (p q : ℕ) (x : ℚ) : Mat p q →ₗ[ℂ] Module.End ℂ ℂ :=
  ((x : ℂ) • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight LinearMap.id

theorem chAct_apply (p q : ℕ) (x : ℚ) (X : Mat p q) (z : ℂ) :
    chAct p q x X z = ((x : ℂ) * X.trace) • z := by
  simp [chAct]

abbrev chMod (p q : ℕ) (x : ℚ) : GKMod p q where
  V := ℂ
  act := chAct p q x
  lie := by
    intro X Y
    ext
    simp [chAct_apply, Matrix.trace_sub, Matrix.trace_mul_comm X Y]
    ring
  kfin := fun _ => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  wts := fun v => by
    refine Submodule.mem_iSup_of_mem (fun _ => x) ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [chAct_apply, trace_Eab, if_pos rfl, mul_one, sub_self]

abbrev shiftMod {r s : ℕ} (M : GKMod r s) (t : ℚ) : GKMod r s where
  V := M.V
  act := M.act - ((t : ℂ) • Matrix.traceLinearMap (Ix r s) ℂ ℂ).smulRight LinearMap.id
  lie := by
    intro X Y
    ext v
    have h := LinearMap.congr_fun (M.lie X Y) v
    simp only [LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      Matrix.traceLinearMap_apply, Module.End.mul_apply, LinearMap.id_apply, map_sub, map_smul,
      Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, smul_zero, zero_smul, sub_zero] at h ⊢
    linear_combination (norm := module) h
  kfin := fun v => by
    obtain ⟨W, fW, hv, sW⟩ := M.kfin v
    refine ⟨W, fW, hv, fun X hX w hw => ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      Matrix.traceLinearMap_apply, LinearMap.id_apply]
    exact W.sub_mem (sW X hX w hw) (W.smul_mem _ hw)
  wts := fun v => by
    refine (iSup_le fun μ => le_iSup_of_le (fun c => μ c - t) ?_ : (⨆ μ, wtSub M.act μ) ≤ _) (M.wts v)
    intro w hw
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply] at hw ⊢
    intro a
    have := hw a
    rw [trace_Eab, if_pos rfl]
    linear_combination (norm := module) this

theorem shiftMod_act {r s : ℕ} (M : GKMod r s) (t : ℚ) (Y : Mat r s) (v : M.V) :
    (shiftMod M t).act Y v = M.act Y v - ((t : ℂ) * Y.trace) • v := by
  show ((M.act - ((t : ℂ) • Matrix.traceLinearMap (Ix r s) ℂ ℂ).smulRight LinearMap.id :
    Mat r s →ₗ[ℂ] Module.End ℂ M.V) Y) v = _
  rw [LinearMap.sub_apply, LinearMap.sub_apply]
  simp [mul_smul]

end Objects

section Main

variable {P Q R S : ℕ}

theorem tmul_one_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] {v : V}
    (h : (1 : ℂ) ⊗ₜ[ℂ] v = 0) : v = 0 := by
  have := congrArg (TensorProduct.lid ℂ V) h
  simpa using this

def fMap (x t : ℚ) {M : GKMod R S} (pr : Pol P Q R S →ₗ[ℂ] M.V) :
    Pol P Q R S →ₗ[ℂ] TensorProduct ℂ (chMod P Q x).V (shiftMod M t).V :=
  TensorProduct.mk ℂ ℂ M.V 1 ∘ₗ pr

theorem fMap_apply (x t : ℚ) {M : GKMod R S} (pr : Pol P Q R S →ₗ[ℂ] M.V) (f : Pol P Q R S) :
    fMap x t pr f = (1 : ℂ) ⊗ₜ[ℂ] pr f := rfl

theorem fMap_eq_zero {x t : ℚ} {M : GKMod R S} {pr : Pol P Q R S →ₗ[ℂ] M.V} {f : Pol P Q R S}
    (h : fMap x t pr f = 0) : pr f = 0 := tmul_one_eq_zero h

theorem intw_fMap {x t : ℚ} {M : GKMod R S} {pr : Pol P Q R S →ₗ[ℂ] M.V} (hL : IsLift x t M pr) :
    Intw (chMod P Q x) (shiftMod M t) (fMap x t pr) := by
  refine ⟨fun X => LinearMap.ext fun f => ?_, fun Y => LinearMap.ext fun f => ?_⟩
  · change (1 : ℂ) ⊗ₜ[ℂ] pr (fockAct1 P Q R S X f) =
      TensorProduct.map (chAct P Q x X) LinearMap.id ((1 : ℂ) ⊗ₜ[ℂ] pr f)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hL.2.1 X f, chAct_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · change (1 : ℂ) ⊗ₜ[ℂ] pr (fockAct2 P Q R S Y f) =
      TensorProduct.map LinearMap.id ((shiftMod M t).act Y) ((1 : ℂ) ⊗ₜ[ℂ] pr f)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, shiftMod_act, hL.2.2 Y f, add_sub_cancel_right]

theorem hw_chMod (p q : ℕ) (x : ℚ) : IsHW (chMod p q x).act (fun _ => x) (1 : ℂ) := by
  refine ⟨one_ne_zero, (mem_hwSub _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩⟩
  · change chAct p q x _ 1 - _ = 0
    rw [chAct_apply, trace_Eab, if_pos rfl]; simp [smul_eq_mul]
  · change chAct p q x _ 1 = 0
    have : a ≠ b := by
      rintro rfl
      cases a <;> simp [posC] at hab
    rw [chAct_apply, trace_Eab, if_neg this]; simp

theorem hw_chMod_eq {p q : ℕ} {x : ℚ} {ν : Ix p q → ℚ} {w : (chMod p q x).V}
    (h : IsHW (chMod p q x).act ν w) : ν = fun _ => x := by
  funext a
  have h1 := ((mem_hwSub _ _ _).1 h.2).1 a
  change chAct p q x _ w - _ = 0 at h1
  rw [chAct_apply, trace_Eab, if_pos rfl, mul_one, ← sub_smul, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact_mod_cast (sub_eq_zero.1 h1).symm
  · exact absurd h1 h.1

theorem irr_chMod (p q : ℕ) (x : ℚ) : IrrGK (chMod p q x) :=
  ⟨inferInstanceAs (Nontrivial ℂ), fun N _ => Ideal.eq_bot_or_top N⟩

theorem admissible_traceCharacterGKModule (p q : ℕ) (x : ℚ) : AdmGK (chMod p q x) := fun _ =>
  inferInstanceAs (FiniteDimensional ℂ ↥(hwSub (chAct p q x) _))

end Main

theorem genBy_of_isLift : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S)
    (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V →
    ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧
      GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := by
  intro P Q R S x t M pr hL hM
  have hI := intw_fMap (P := P) (Q := Q) hL
  have hf : fMap x t pr ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
    obtain ⟨f, rfl⟩ := hL.1 v
    intro h
    exact hv (fMap_eq_zero (LinearMap.congr_fun h f))
  have hmin : ∀ ν w, IsHW (chMod P Q x).act ν w →
      degW (cPair R S) (fun _ : Ix P Q => x) ≤ degW (cPair R S) ν := by
    intro ν w h
    rw [hw_chMod_eq h]
  obtain ⟨⟨μ', P0, hJ0, h10, h20, hf0⟩, -⟩ := GlobalTheory.FockAlg.min_first P Q R S (chMod P Q x)
    (shiftMod M t) (fMap x t pr) (irr_chMod P Q x) (admissible_traceCharacterGKModule P Q x) hI hf (fun _ => x)
    ⟨1, hw_chMod P Q x⟩ hmin
  have hpr0 : pr P0 ≠ 0 := fun h => hf0 (by rw [fMap_apply, h, TensorProduct.tmul_zero])
  have hP0mem : P0 ∈ hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
      Submodule.span ℂ (jointHarm P Q R S) := ⟨⟨h10.2, h20.2⟩, Submodule.subset_span hJ0⟩
  have hshape : JointShape P Q R S (fun _ => x) μ' := by
    by_contra h
    have := hP0mem
    rw [GlobalTheory.FockAlg.jointHarm_hw_eq_bot P Q R S _ _ h, Submodule.mem_bot] at this
    exact h10.1 this

  have hw0 : IsHW M.act (fun c => μ' c + t) (pr P0) := by
    refine ⟨hpr0, (mem_hwSub _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩⟩
    · have e := ((mem_hwSub _ _ _).1 h20.2).1 a
      rw [hL.2.2, trace_Eab, if_pos rfl, sub_eq_zero.1 e, map_smul]
      push_cast
      module
    · have e := ((mem_hwSub _ _ _).1 h20.2).2 a b hab
      have : a ≠ b := by
        rintro rfl
        cases a <;> simp [posC] at hab
      rw [hL.2.2, trace_Eab, if_neg this, e, map_zero]
      simp
  refine ⟨μ', hshape, pr P0, hw0, ?_⟩

  set G := genSub M.act {pr P0} with hG
  set T : Submodule ℂ (Pol P Q R S) := G.comap pr with hT
  have hT1 : ∀ X, ∀ y ∈ T, fockAct1 P Q R S X y ∈ T := by
    intro X y hy
    rw [Submodule.mem_comap, hL.2.1]
    exact G.smul_mem _ hy
  have hT2 : ∀ Z, ∀ y ∈ T, fockAct2 P Q R S Z y ∈ T := by
    intro Z y hy
    have e := hL.2.2 Z y
    rw [Submodule.mem_comap, eq_sub_of_add_eq e.symm]
    exact G.sub_mem (genSub_stable _ _ Z hy) (G.smul_mem _ hy)
  have hker : LinearMap.ker (fMap x t pr) ≤ T := by
    intro y hy
    rw [Submodule.mem_comap, fMap_eq_zero (LinearMap.mem_ker.1 hy)]
    exact G.zero_mem
  have hP0T : P0 ∈ T := subset_genSub M.act {pr P0} rfl
  have hJ : ∀ P' ∈ jointHarm P Q R S, P' ∈ hwSub (fockAct1 P Q R S) (fun _ => x) → P' ∈ T := by
    intro P' hJ' hh
    obtain ⟨U, fU, hU, sU⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 P').1
    obtain ⟨-, -, s2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inr rfl))
    have sH : KStable (fockAct2 P Q R S) (hwSub (fockAct1 P Q R S) (fun _ => x)) :=
      fun Z _ w hw => hw_map (fockAct2 P Q R S Z) (fun Y _ v => fockAct1_fockAct2_commute Y Z v) hw
    by_contra hPT
    obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie2 wts2
      (W := U ⊓ (Submodule.span ℂ (jointHarm P Q R S) ⊓ hwSub (fockAct1 P Q R S) (fun _ => x)))
      (N := T) inferInstance (kStable_inf sU (kStable_inf s2 sH)) (fun Z _ y hy => hT2 Z y hy)
      (fun h => hPT (h ⟨hU, Submodule.subset_span hJ', hh⟩))
    have hmem : u ∈ hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) ν ⊓
        Submodule.span ℂ (jointHarm P Q R S) := ⟨⟨hu.2.2, hhw.2⟩, hu.2.1⟩
    have hsh : JointShape P Q R S (fun _ => x) ν := by
      by_contra h
      rw [GlobalTheory.FockAlg.jointHarm_hw_eq_bot P Q R S _ _ h, Submodule.mem_bot] at hmem
      exact hhw.1 hmem
    obtain rfl : ν = μ' :=
      (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hsh hshape).1.1 rfl
    have hline := GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hshape
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨P0, hP0mem⟩ : ↥(hwSub (fockAct1 P Q R S)
      (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) ν ⊓ Submodule.span ℂ (jointHarm P Q R S)))
      (fun h => h10.1 (congrArg Subtype.val h))).1 hline ⟨u, hmem⟩
    have hu' : u = c • P0 := (congrArg Subtype.val hc).symm
    exact hN (hu' ▸ T.smul_mem c hP0T)
  have hall : ∀ P', P' ∈ T := by
    intro P'
    obtain ⟨W, fW, hW, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 P').1
    by_contra hPT
    obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie1 wts1 fW sW (fun X _ y hy => hT1 X y hy)
      (fun h => hPT (h hW))
    have hpru : pr u ≠ 0 := fun h => hN (by rw [Submodule.mem_comap, h]; exact G.zero_mem)
    obtain rfl : ν = fun _ => x := by
      funext a
      have e := ((mem_hwSub _ _ _).1 hhw.2).1 a
      have e2 := congrArg pr e
      rw [map_sub, map_smul, hL.2.1, trace_Eab, if_pos rfl, mul_one, map_zero, ← sub_smul,
        smul_eq_zero] at e2
      rcases e2 with e2 | e2
      · exact_mod_cast (sub_eq_zero.1 e2).symm
      · exact absurd e2 hpru
    exact hN (hw_mem hI hmin T hker hT2 hJ hhw.2)
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, rfl⟩ := hL.1 v
  exact hall f

end GlobalTheory.RealLift.GenLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellUAbsorbUnip
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.WeylUnipotentShell

section BlockKeep

variable {R : Type} [CommRing R] {n : ℕ}

def blockKeep (a b : Fin n) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (a ≤ i ∧ i ≤ b) ∧ (a ≤ j ∧ j ≤ b) then A i j else (1 : Matrix (Fin n) (Fin n) R) i j

theorem blockKeep_one (a b : Fin n) : blockKeep a b (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j; unfold blockKeep; split_ifs <;> rfl

theorem blockKeep_mul (a b : Fin n) (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : blockKeep a b (A * B) = blockKeep a b A * blockKeep a b B := by
  ext i j
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hj : a ≤ j ∧ j ≤ b
    · simp only [blockKeep, Matrix.mul_apply, if_pos (And.intro hi hj)]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : a ≤ k ∧ k ≤ b
      · rw [if_pos ⟨hi, hk⟩, if_pos ⟨hk, hj⟩]
      · rw [if_neg (fun h => hk h.2), Matrix.one_apply_ne (by rintro rfl; exact hk hi), zero_mul]
        rcases not_and_or.1 hk with h | h
        · rw [hA i k (lt_of_lt_of_le (not_le.1 h) hi.1), zero_mul]
        · rw [hB k j (lt_of_le_of_lt hj.2 (not_le.1 h)), mul_zero]
    · have hcol : ∀ k, blockKeep a b B k j = (1 : Matrix (Fin n) (Fin n) R) k j := fun k => if_neg (fun h => hj h.2)
      rw [Matrix.mul_apply]
      simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [blockKeep, hi, hj, and_false, if_false, true_and, Matrix.one_apply]
  · have hrow : ∀ k, blockKeep a b A i k = (1 : Matrix (Fin n) (Fin n) R) i k := fun k => if_neg (fun h => hi h.1)
    rw [Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [blockKeep, hi, false_and, if_false, Matrix.one_apply]

end BlockKeep

section Keep

variable {L : Type} [Field L] {n : ℕ}

def blockKeepGL (a b : Fin n) (g : GL (Fin n) L) (hg : g ∈ unipB L (Fin n)) : GL (Fin n) L where
  val := blockKeep a b (g : Matrix (Fin n) (Fin n) L)
  inv := blockKeep a b ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  val_inv := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 hg).1 ((mem_unipB L).1 (inv_mem hg)).1, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, blockKeep_one]
  inv_val := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 (inv_mem hg)).1 ((mem_unipB L).1 hg).1, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, blockKeep_one]

theorem blockKeepGL_mem_GU [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} (a : Fin n) (g : GL (Fin n) L)
    (hg : g ∈ unipB L (Fin n)) (hG : g ∈ GU σ n) : blockKeepGL a a.rev g hg ∈ GU σ n := by
  rw [LGrp.mem_GU_iff] at hG ⊢
  intro i j
  show blockKeep a a.rev ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
    σ (blockKeep a a.rev (g : Matrix (Fin n) (Fin n) L) j.rev i.rev)
  have key : ∀ i : Fin n, (a ≤ i.rev ∧ i.rev ≤ a.rev) ↔ (a ≤ i ∧ i ≤ a.rev) := by
    intro i
    have := i.isLt
    have := a.isLt
    simp only [Fin.le_iff_val_le_val, Fin.val_rev]
    omega
  unfold blockKeep
  simp only [key]
  by_cases h : (a ≤ i ∧ i ≤ a.rev) ∧ (a ≤ j ∧ j ≤ a.rev)
  · rw [if_pos h, if_pos h.symm, hG]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), Matrix.one_apply, Matrix.one_apply, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, eq_comm (a := j)]

theorem blockKeep_eq_self (a b : Fin n) (A : Matrix (Fin n) (Fin n) L) (h1 : ∀ i j, j < i → A i j = 0)
    (h2 : ∀ i, A i i = 1) (h3 : ∀ i j, i < j → (i < a ∨ b < j) → A i j = 0) : blockKeep a b A = A := by
  ext i j
  unfold blockKeep
  split_ifs with h
  · rfl
  · rcases lt_trichotomy i j with hij | rfl | hij
    · rw [Matrix.one_apply_ne hij.ne, h3 i j hij]
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      exact h ⟨⟨hc.1, hij.le.trans hc.2⟩, hc.1.trans hij.le, hc.2⟩
    · rw [Matrix.one_apply_eq, h2]
    · rw [Matrix.one_apply_ne hij.ne', h1 i j hij]

end Keep

end GlobalTheory.WeylCell.WeylUnipotentShell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOne
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Classical

section SignAdele

variable {F : Type} [Field F] [NumberField F]

def sgnAd (w : InfinitePlace F) : AF F :=
  (((fun v : InfinitePlace F => (if v = w then -1 else 1 : v.Completion)) : Ainf F), (1 : Af F))

theorem sgnAd_mul_self (w : InfinitePlace F) : sgnAd w * sgnAd w = 1 := by
  refine Prod.ext (funext fun v => ?_) (mul_one _)
  show (if v = w then -1 else 1 : v.Completion) * (if v = w then -1 else 1) = 1
  split_ifs <;> simp

theorem evInf_sgnAd (w v : InfinitePlace F) : evInf F v (sgnAd w) = if v = w then -1 else 1 := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem piInf_algebraMap {v : InfinitePlace F} (τ : EmbOver E v) (y : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) y) = InfinitePlace.Completion.extensionEmbedding v (evInf F v y) := by
  unfold piInf
  rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]
  simp [compInf]

theorem at_algebraMap_sgnAd_sub_one (w : InfinitePlace F) :
    At (evI F) (algebraMap (AF F) (AE F E) (sgnAd w) - 1) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have h2 : u * (sgnAd w - 1) = 0 := by
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [h1, zero_mul]
    · show u.2 * ((1 : Af F) - 1) = 0
      rw [sub_self, mul_zero]
  rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul, h2, map_zero]

end SignAdele

theorem even_im_hermitian_sub : Parity := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT w
  let u : (AF F)ˣ := ⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩
  let z : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u
  have hz : At (evI F) ((z : AE F E) - 1) := at_algebraMap_sgnAd_sub_one w
  have hpi : ∀ v, piInf (B.emb v) (z : AE F E) = if v = w then -1 else 1 := by
    intro v
    show piInf (B.emb v) (algebraMap (AF F) (AE F E) (sgnAd w)) = _
    rw [piInf_algebraMap, evInf_sgnAd]
    split_ifs <;> simp
  have hexp : ∀ m : InfinitePlace F → ℤ,
      ∏ v, (piInf (B.emb v) (z : AE F E) / ‖piInf (B.emb v) (z : AE F E)‖) ^ m v = (-1 : ℂ) ^ m w := by
    intro m
    rw [Finset.prod_eq_single w (fun v _ hv => by rw [hpi, if_neg hv]; simp) (fun h => absurd (Finset.mem_univ w) h),
      hpi, if_pos rfl]
    simp
  have eα := hT.chars.expα z hz
  have eβ := hT.chars.expβ z hz
  rw [hexp] at eα eβ
  have rα : (X.α z : ℂ) = _ := hT.chars.resα u
  have rβ : (X.β z : ℂ) = _ := hT.chars.resβ u
  have hpar : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    have he := hT.geo.even
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, ((Nat.even_add.1 he).1 ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.1 fun h => Nat.not_even_iff_odd.2 ha ((Nat.even_add.1 he).2 h)
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hab : (-1 : ℂ) ^ B.mα w = (-1) ^ B.mβ w := by
    rw [← eα, ← eβ, rα, rβ, hpar]
  rcases Int.even_or_odd (B.mα w - B.mβ w) with h | h
  · exact h
  · exfalso
    have h1 := h.neg_one_zpow (α := ℂ)
    rw [zpow_sub₀ (by norm_num), hab, div_self (zpow_ne_zero _ (by norm_num))] at h1
    norm_num at h1
end GlobalTheory.RealLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOneStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLift_parity : GlobalTheory.RealLift.Parity := by
  first | exact @GlobalTheory.RealLift.even_im_hermitian_sub | exact GlobalTheory.RealLift.even_im_hermitian_sub | (intros; apply GlobalTheory.RealLift.even_im_hermitian_sub <;> assumption)
end
end

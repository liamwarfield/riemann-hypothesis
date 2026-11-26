module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.LeviInt

open ValuativeRel Matrix in
theorem _root_.GlobalTheory.SmGL.LeviInt.nabs_det_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 := by
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hdet : ∀ M : Matrix n n k, (∀ i j, M i j ∈ (valuation k).integer) →
      M.det ∈ (valuation k).integer := by
    intro M hM
    rw [Matrix.det_apply]
    refine sum_mem fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (prod_mem fun i _ => hM _ _) _
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have hd1 : valuation k ((GeneralLinearGroup.det g : kˣ) : k) ≤ 1 := by
    rw [← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h1
  have hd2 : valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [← map_inv, ← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h2
  have hprod : valuation k ((GeneralLinearGroup.det g : kˣ) : k) *
      valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact le_antisymm hd1 (hprod ▸ mul_le_of_le_one_right' hd2)

theorem _root_.GlobalTheory.SmGL.LeviInt.levi_integral_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n), (∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e → (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔ (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ u ∈ _root_.GlobalTheory.SplitWeil.KO k n)) ∧ (∀ p : _root_.GlobalTheory.SmGL.parab k e, (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n → ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ (∀ g : _root_.GlobalTheory.SmGL.Levi k m, (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1) ∧ (∀ g h : _root_.GlobalTheory.SmGL.Levi k m, _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h) ∧ Continuous (_root_.GlobalTheory.SmGL.modulus k m) ∧ Continuous (_root_.GlobalTheory.SmGL.leviProj k e) ∧ IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∧ IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) ∧ ∀ g : GL n k, ∃ p ∈ _root_.GlobalTheory.SmGL.parab k e, ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, g = p * x := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e
  have hT2 : T2Space k := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have hlevi : ∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e →
      (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔
        (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧
          u ∈ _root_.GlobalTheory.SplitWeil.KO k n) := by
    intro g u hu
    rw [← Subgroup.inv_mem_iff, mul_inv_rev, ← map_inv]
    refine (_root_.GlobalTheory.SmGL.UnitInd.unip_mul_levi_mem_KO e ⟨u⁻¹, inv_mem hu⟩ g⁻¹).trans ?_
    have hinv : ∀ a, (g⁻¹) a = (g a)⁻¹ := fun a => rfl
    simp only [hinv, Subgroup.inv_mem_iff]
    exact and_comm
  have hemb : ∀ g : _root_.GlobalTheory.SmGL.Levi k m,
      _root_.GlobalTheory.SmGL.leviEmb k e g ∈ _root_.GlobalTheory.SmGL.parab k e := by
    intro g
    apply _root_.GlobalTheory.SmGL.mem_parab_iff.2
    intro a b i j hab
    classical
    simp [_root_.GlobalTheory.SmGL.leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
  have hdec : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
      ∃ u ∈ _root_.GlobalTheory.SmGL.unipRad k e,
        (p : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e (_root_.GlobalTheory.SmGL.leviProj k e p) * u := by
    intro p
    let L : _root_.GlobalTheory.SmGL.parab k e :=
      ⟨_root_.GlobalTheory.SmGL.leviEmb k e (_root_.GlobalTheory.SmGL.leviProj k e p), hemb _⟩
    have hL : _root_.GlobalTheory.SmGL.leviProj k e L = _root_.GlobalTheory.SmGL.leviProj k e p := by
      funext a
      ext i j
      simp [_root_.GlobalTheory.SmGL.leviProj_apply, L, _root_.GlobalTheory.SmGL.leviEmb, Matrix.blockDiagonal'_apply_eq]
    refine ⟨((L⁻¹ * p : _root_.GlobalTheory.SmGL.parab k e) : GL n k), ?_, ?_⟩
    · unfold _root_.GlobalTheory.SmGL.unipRad
      refine Subgroup.mem_map.mpr ⟨L⁻¹ * p, ?_, rfl⟩
      change _root_.GlobalTheory.SmGL.leviProj k e (L⁻¹ * p) = 1
      rw [map_mul, map_inv, hL, inv_mul_cancel]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mul_inv_cancel_left _ _).symm
  have hproj : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
      (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n →
        ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a) := by
    intro p hp a
    obtain ⟨u, hu, hpu⟩ := hdec p
    rw [hpu] at hp
    exact ((hlevi _ u hu).1 hp).1 a
  have hmod : ∀ g : _root_.GlobalTheory.SmGL.Levi k m,
      (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1 := by
    intro g hg
    unfold _root_.GlobalTheory.SmGL.modulus
    exact Finset.prod_eq_one fun a _ => by
      rw [_root_.GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (hg a), one_zpow]
  have hmul : ∀ g h : _root_.GlobalTheory.SmGL.Levi k m,
      _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h := by
    intro g h
    unfold _root_.GlobalTheory.SmGL.modulus
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← mul_zpow, ← _root_.GlobalTheory.SmGL.nabs_mul', ← map_mul]
    rfl
  have hcont : Continuous (_root_.GlobalTheory.SmGL.leviProj k e) := by
    refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Function.comp_apply, _root_.GlobalTheory.SmGL.leviProj_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · have hinv : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
          (_root_.GlobalTheory.SmGL.leviProj k e p a)⁻¹ = _root_.GlobalTheory.SmGL.leviProj k e p⁻¹ a := by
        intro p
        rw [map_inv]
        rfl
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [hinv, _root_.GlobalTheory.SmGL.leviProj_apply, Subgroup.coe_inv]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _
  have hP : IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) =
        ⋂ (a) (b) (i : m a) (j : m b) (_ : b < a),
          {g : GL n k | (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_parab_iff]
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const
  have hN : IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) =
        (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∩
          ⋂ (a) (i : m a) (j : m a), {g : GL n k |
            (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_unipRad]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    rw [hset]
    exact hP.inter (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const)
  refine ⟨hlevi, hproj, hmod, hmul, _root_.GlobalTheory.SmGL.UnitInd.isLocallyConstant_modulus.continuous, hcont,
    hP, hN, fun g => ?_⟩
  obtain ⟨u, h, w, hw, rfl⟩ := _root_.GlobalTheory.SmGL.UnitInd.exists_iwasawa e g
  exact ⟨_, mul_mem (_root_.GlobalTheory.SmGL.unipRad_le_parab k e u.2)
    (hemb h), w, hw, rfl⟩

end GlobalTheory.SmGL.LeviInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling

namespace GlobalTheory.ZonalCellDecomposition

def blkEquiv (l t : ℕ) : Fin (l * t) ≃ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t :=
  finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin l) (Fin t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mtor {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GL (A ⊕ D) k :=
  torusElt k (A ⊕ D) ϖ (Sum.elim 0 e)

def dcell {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    Set (GL (A ⊕ D) k) :=
  DoubleCoset.doubleCoset (mtor ϖ e) (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D : Set (GL (A ⊕ D) k))
    (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D)

def IsBiType {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ)
    (φ : GL (A ⊕ D) k → ℂ) : Prop :=
  ∀ j ∈ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    ∀ g, φ (j * g) = (ξ d : ℂ) * φ g ∧ φ (g * j) = (ξ d : ℂ) * φ g

def sumAbs {D : Type} [Fintype D] (e : D → ℤ) : ℤ := ∑ i, |e i|

def zonalInt {N : ℕ} [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) : ℂ :=
  ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * g) ∂μK

def borelParam {N : ℕ} (q : ℕ) (α : Fin N → ℂˣ) (x : Fin N) : ℂ :=
  (α x : ℂ) * (q : ℂ) ^ (((x : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)

end GlobalTheory.ZonalCellDecomposition
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFiltrationExists
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] [DecidableEq b] in
theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ

end

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
open Formalism.REAL Finset

namespace GlobalTheory

theorem affine_mul_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (d : ℕ) (p q : A) (c : ℕ → A) :
    ∃ c' : ℕ → A, c' (d + 1) = p * c d ∧ ∀ u : ℂ, (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • c' i := by
  refine ⟨fun i => (Nat.casesOn i 0 (fun j => p * c j) : A)
    + (if i < d + 1 then q * c i else 0), by simp, fun u => ?_⟩
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (t : ℕ) (p q : Fin t → A) :
    ∃ c : ℕ → A, c t = (List.ofFn p).prod ∧ ∀ u : ℂ, (List.ofFn fun k => u • p k + q k).prod
      = ∑ i ∈ range (t + 1), u ^ i • c i := by
  induction t with
  | zero => exact ⟨fun _ => 1, by simp, fun u => by simp⟩
  | succ t ih =>
    obtain ⟨c, hct, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    obtain ⟨c', hct', hc'⟩ := affine_mul_polyMap_top t (p 0) (q 0) c
    refine ⟨c', ?_, fun u => ?_⟩
    · rw [hct', hct, List.ofFn_succ, List.prod_cons]
    · rw [List.ofFn_succ, List.prod_cons, hc u, hc' u]

theorem qdet_polyMap_monic (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  have h : ∀ σ : Equiv.Perm (Fin n), ∃ c : ℕ → A,
      c n = (List.ofFn fun k : Fin n => if σ k = k then (1 : A) else 0).prod ∧ ∀ u : ℂ,
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (n + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hct, hc⟩ := prod_affine_polyMap_top n
      (fun k => if σ k = k then (1 : A) else 0)
      (fun k => Tm E (-(k : ℂ)) (σ k) k)
    refine ⟨c, hct, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Tm
    simp only [id]
    split_ifs
    · rw [← add_assoc, ← Algebra.algebraMap_eq_smul_one, ← map_add (f := _)]
      congr 2
      all_goals ring
    · simp
  choose c hct hc using h
  have htop : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 → c σ n = 0 := by
    intro σ hσ
    rw [hct σ]
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra hne
      push_neg at hne
      exact hσ (Equiv.ext hne)
    apply List.prod_eq_zero
    rw [List.mem_ofFn]
    exact ⟨k, if_neg hk⟩
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [hct 1]
      simp
    · intro σ _ hσ
      rw [htop σ hσ, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  · unfold qdet qminor
    simp only [hc, mul_sum, smul_sum, mul_smul_comm]
    exact sum_comm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_poly_eq_qdet : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  first | exact @GlobalTheory.qdet_polyMap_monic | exact GlobalTheory.qdet_polyMap_monic | (intros; apply GlobalTheory.qdet_polyMap_monic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverse
open Formalism.REAL Finset

namespace GlobalTheory.TracedComatrix

theorem epow_succ_left {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) :
    ∀ (k : ℕ) (a b : Fin n), epow E (k + 1) a b = ∑ c, E a c * epow E k c b := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp [epow]
  | succ k ih =>
    intro a b
    calc epow E (k + 1 + 1) a b = ∑ c, epow E (k + 1) a c * E c b := rfl
      _ = ∑ c, (∑ d, E a d * epow E k d c) * E c b :=
          Finset.sum_congr rfl fun c _ => by rw [ih a c]
      _ = ∑ d, E a d * ∑ c, epow E k d c * E c b := by
          simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ d, E a d * epow E (k + 1) d b := rfl

theorem key {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) (N : ℕ)
    (j i : Fin n) :
    ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i =
      algebraMap ℂ A (x ^ (N + 1)) * (if j = i then 1 else 0) +
        algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i := by
  have h1 : ∀ k, ∑ l, Tm E x j l * epow E k l i = algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i := by
    intro k
    rw [epow_succ_left]
    simp [Tm, add_mul, Finset.sum_add_distrib, ite_mul]
  have h2 : ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i
      = ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * ∑ l, Tm E x j l * epow E k l i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
  rw [h2]
  simp_rw [h1]
  set a : ℕ → A := fun k => algebraMap ℂ A ((-1) ^ k * x ^ (N + 1 - k)) * epow E k j i with ha
  have h3 : ∀ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) *
      (algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i) = a k - a (k + 1) := by
    intro k hk
    have hk' : N + 1 - k = (N - k) + 1 := by
      have := Finset.mem_range.mp hk; omega
    simp only [ha, hk', Nat.add_sub_add_right, mul_add, ← mul_assoc, ← map_mul, sub_eq_add_neg,
      ← neg_mul, ← map_neg]
    congr 3 <;> ring
  rw [Finset.sum_congr rfl h3, Finset.sum_range_sub']
  simp only [ha, Nat.sub_self, pow_zero, mul_one, one_mul, Nat.sub_zero, sub_eq_add_neg, ← neg_mul, ← map_neg]
  congr 2
  congr 1
  ring

theorem traced_comatrix : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
  intro A _ _ m E hE u N
  set C : Fin (m + 1) → Fin (m + 1) → A := fun i j =>
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u with hC
  set P : Fin (m + 1) → Fin (m + 1) → A := fun l i =>
    ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * epow E k l i with hP
  have hQ := qComatrix A m E hE u
  have S1 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
    simp only [hC, hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    congr 1
    simp only [hP, etr, Finset.mul_sum]
    exact Finset.sum_comm
  have S2 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i := by
    have h : ∀ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
        ∑ j, C i j * (algebraMap ℂ A ((u - m) ^ (N + 1)) * (if j = i then 1 else 0) +
          algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i) := by
      intro i
      calc ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i
          = ∑ j, C i j * ∑ l, Tm E (u - (m : ℂ)) j l * P l i := by
            simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
            exact Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun j _ => congrArg (C i j * ·) (key E (u - (m : ℂ)) N j i)
    simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.commutes]
      simp [hC, ← two_mul, pow_mul]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← mul_assoc, ← Algebra.commutes, hC]
  exact S2.symm.trans S1

end GlobalTheory.TracedComatrix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traced_qminor_comatrix_truncated_inverse : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
  first | exact @GlobalTheory.TracedComatrix.traced_comatrix | exact GlobalTheory.TracedComatrix.traced_comatrix | (intros; apply GlobalTheory.TracedComatrix.traced_comatrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminor
open Formalism.REAL Finset

namespace GlobalTheory.CapelliDiff

theorem prod_ofFn_sub {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (n : ℕ) (x y : Fin (n + 1) → A) (d : Fin (n + 1) → ℂ),
      (∀ k, y k = x k + algebraMap ℂ A (d k)) →
      (List.ofFn y).prod - (List.ofFn x).prod =
        ∑ k : Fin (n + 1), algebraMap ℂ A (d k) *
          (List.ofFn fun j : Fin n => if Fin.castSucc j < k then x (Fin.castSucc j) else y j.succ).prod := by
  intro n
  induction n with
  | zero =>
    intro x y d h
    simp [h 0]
  | succ n ih =>
    intro x y d h
    rw [List.ofFn_succ (f := y), List.ofFn_succ (f := x), List.prod_cons, List.prod_cons, Fin.sum_univ_succ]
    have key := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => d i.succ) (fun i => h i.succ)
    have e1 : y 0 * (List.ofFn fun i : Fin (n+1) => y i.succ).prod - x 0 * (List.ofFn fun i : Fin (n+1) => x i.succ).prod
        = algebraMap ℂ A (d 0) * (List.ofFn fun i : Fin (n+1) => y i.succ).prod + x 0 * ((List.ofFn fun i : Fin (n+1) => y i.succ).prod - (List.ofFn fun i : Fin (n+1) => x i.succ).prod) := by
      rw [h 0]; noncomm_ring
    rw [e1, key, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · congr 2
    · apply Finset.sum_congr rfl
      intro k _
      rw [List.ofFn_succ, List.prod_cons]
      have h0 : (Fin.castSucc (0 : Fin (n+1)) : Fin (n+2)) < k.succ := by simp [Fin.succ_pos]
      rw [if_pos h0, Fin.castSucc_zero, ← mul_assoc (x 0), ← Algebra.commutes, mul_assoc]
      have hl : (List.ofFn fun j : Fin n => if j.castSucc < k then x j.castSucc.succ else y j.succ.succ) =
          (List.ofFn fun i : Fin n => if i.succ.castSucc < k.succ then x i.succ.castSucc else y i.succ.succ) := by
        congr 1; funext j; simp only [← Fin.succ_castSucc, Fin.succ_lt_succ_iff]
      rw [hl]

theorem Tm_add_one {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) :
    Tm E (v + 1) a b = Tm E v a b + algebraMap ℂ A (if a = b then 1 else 0) := by
  unfold Tm
  split_ifs <;> simp [map_add (f := _)]; abel

def extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.ofSubtype ((finSuccAboveEquiv k).permCongr τ)

theorem extAt_succAbove {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    extAt k τ (k.succAbove j) = k.succAbove (τ j) := by
  have hj : k.succAbove j = ((finSuccAboveEquiv k j : {x // x ≠ k}) : Fin (m + 1)) := by
    rw [finSuccAboveEquiv_apply]
  unfold extAt
  rw [hj, Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSuccAboveEquiv_apply]

theorem sign_extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extAt k τ) = Equiv.Perm.sign τ := by
  unfold extAt
  rw [Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]

theorem sum_fix_eq {A : Type*} [AddCommMonoid A] {m : ℕ} (k : Fin (m + 1))
    (g : Equiv.Perm (Fin (m + 1)) → A) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ k = k then g σ else 0) =
      ∑ τ : Equiv.Perm (Fin m), g (extAt k τ) := by
  let e : Equiv.Perm (Fin m) ≃ {f : Equiv.Perm (Fin (m + 1)) // ∀ a, ¬ (a ≠ k) → f a = a} :=
    ((finSuccAboveEquiv k).permCongr).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ≠ k))
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun f : Equiv.Perm (Fin (m + 1)) => ∀ a, ¬ (a ≠ k) → f a = a)]
  · rw [← Equiv.sum_comp e]
    rfl
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor
    · intro h a ha; rw [ha]; exact h
    · intro h; exact h k rfl

theorem qdet_add_one_sub (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ) :
    qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u := by
  unfold qdet qminor
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have step : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn fun k : Fin (m + 1) => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)).prod -
        (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ k : Fin (m + 1), algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod := by
    intro σ
    rw [prod_ofFn_sub m (fun k => Tm E (u - (k : ℂ)) (id (σ k)) (id k))
      (fun k => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)) (fun k => if σ k = k then 1 else 0)]
    · apply Finset.sum_congr rfl
      intro k _
      congr 2
      congr 1
      funext j
      by_cases hj : Fin.castSucc j < k
      · rw [if_pos hj, Fin.succAbove_of_castSucc_lt k j hj]
        simp [Fin.coe_castSucc]
      · rw [if_neg hj, Fin.succAbove_of_le_castSucc k j (not_lt.mp hj)]
        simp only [id, Fin.val_succ]
        congr 1
        push_cast; ring
    · intro k
      have : u + 1 - (k : ℂ) = (u - (k : ℂ)) + 1 := by ring
      simp only [this, Tm_add_one, id]
  simp_rw [step, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤ) : A) * (algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod) =
      if σ k = k then ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod else 0 := by
    intro σ
    split_ifs <;> simp
  simp_rw [h2]
  rw [sum_fix_eq k (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod)]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [sign_extAt, extAt_succAbove]

end GlobalTheory.CapelliDiff

theorem GlobalTheory.qdet_add_one_sub_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u :=
  GlobalTheory.CapelliDiff.qdet_add_one_sub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}

theorem _root_.GlobalTheory.LevelUnfold.mul_inv_q (q : _root_.GlobalTheory.LatPair.Unif k) :
    (q.1 : k) * q.inv = 1 :=
  mul_inv_cancel₀ q.ne_zero

theorem _root_.GlobalTheory.LevelUnfold.mem_gluedS {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {y : n ⊕ Fin c → k} :
    y ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔ ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
      (i.val = 0 → y (Sum.inr i) = q.inv * s) ∧
        (0 < i.val → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k]) := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, _root_.GlobalTheory.LatPair.mem_gluedLat]
  refine exists_congr fun s => and_congr_right fun _ => forall_congr' fun i => ?_
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨fun h => h2 (by omega), fun h => h3 (by omega)⟩
  · rintro ⟨h2, h3⟩
    exact ⟨fun h => absurd h (by omega), fun h => h2 (by omega), fun h => h3 (by omega)⟩

theorem _root_.GlobalTheory.LevelUnfold.gluedS_le_iff {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {M : Submodule 𝒪[k] (n ⊕ Fin c → k)} :
    _root_.GlobalTheory.LatPair.gluedS q c L f ≤ M ↔ (∀ y ∈ L, _root_.GlobalTheory.LatPair.inX k n c y ∈ M) ∧
      q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
          _root_.GlobalTheory.LatPair.inX k n c f ∈ M ∧
      ∀ i : Fin c, 0 < i.val →
        q.inv • _root_.GlobalTheory.LatPair.avec k n c (i.val + 1) ∈ M := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  rw [sup_le_iff, sup_le_iff, Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem,
    Submodule.span_le, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h i hi
    exact h ⟨i.val + 1, by omega, by omega, rfl⟩
  · rintro h y ⟨j, hj2, hjc, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact h ⟨m, by omega⟩ (by simp only; omega)

theorem _root_.GlobalTheory.LevelUnfold.interX_gluedS (hc : 1 ≤ c) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration.interX (_root_.GlobalTheory.LatPair.gluedS q c L f) = L := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration.interX
  ext x
  rw [Submodule.mem_comap, ← _root_.GlobalTheory.LatPair.gluedLat_one]
  exact _root_.GlobalTheory.LatPair.inX_mem_gluedLat le_rfl hc

theorem _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
      _root_.GlobalTheory.LatPair.inX k n c f ∈ _root_.GlobalTheory.LatPair.gluedS q c L f := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

theorem _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (hc : 1 ≤ c) {L : Submodule 𝒪[k] (n → k)}
    {f x : n → k} :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c x ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔
      x - f ∈ L := by
  have hg := _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := c) L f
  have hsplit : q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c x =
      (q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c f) + _root_.GlobalTheory.LatPair.inX k n c (x - f) := by
    rw [map_sub]
    abel
  rw [hsplit, Submodule.add_mem_iff_right _ hg, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.inX_mem_gluedLat le_rfl hc]

theorem _root_.GlobalTheory.LevelUnfold.gluedS_congr {L : Submodule 𝒪[k] (n → k)} {f f' : n → k}
    (h : f - f' ∈ L) : _root_.GlobalTheory.LatPair.gluedS q c L f = _root_.GlobalTheory.LatPair.gluedS q c L f' := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.gluedLat_congr q c 1 h]

variable [Fintype n] [DecidableEq n]

theorem _root_.GlobalTheory.LevelUnfold.embX_smul_gluedS (g : GL n k) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) :
    _root_.GlobalTheory.RootEx.embX c g • _root_.GlobalTheory.LatPair.gluedS q c L f =
      _root_.GlobalTheory.LatPair.gluedS q c (g • L) (g • f) := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.embX_smul_gluedLat]

end GlobalTheory.LevelUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology

namespace GlobalTheory.SBUniform

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_deep (a : ℤ) : IsOpen {x : k | Deep a x} := by
  have hγ : (uniformizer k ^ a : ValueGroupWithZero k) ≠ 0 := zpow_ne_zero _ uniformizer_ne_zero
  unfold Deep
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 _ hγ, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hx ⊢

  have h := (valuation k).map_add (z - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hz.le hx)

theorem eventually_deep_subset {s : Set k} (hs : s ∈ 𝓝 (0 : k)) :
    ∀ᶠ M : ℕ in atTop, ∀ x : k, Deep (M : ℤ) x → x ∈ s := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs

  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) γ
  filter_upwards [eventually_ge_atTop M₀] with M hM x hx
  apply hγ
  unfold Deep at hx
  show valuation k x < γ
  have hle : uniformizer k ^ (M : ℤ) ≤ uniformizer k ^ (M₀ : ℤ) :=
    zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le (by exact_mod_cast hM)
  have hM₀' : uniformizer k ^ (M₀ : ℤ) < γ := by rwa [zpow_natCast]
  exact hx.trans_lt (hle.trans_lt hM₀')

theorem exists_deep_subset {n : Type} [Fintype n] {s : Set (Matrix n n k)} (hs : s ∈ 𝓝 (0 : Matrix n n k)) :
    ∃ M : ℕ, ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → y ∈ s := by
  have hs' : s ∈ 𝓝 (0 : n → n → k) := hs
  rw [nhds_pi] at hs'
  obtain ⟨I, -, t, ht, hts⟩ := Filter.mem_pi.1 hs'

  have ht' : ∀ i, ∃ J : Set n, J.Finite ∧ ∃ u : n → Set k, (∀ j, u j ∈ 𝓝 (0 : k)) ∧ J.pi u ⊆ t i := by
    intro i
    have hi : t i ∈ 𝓝 (0 : n → k) := ht i
    rw [nhds_pi] at hi
    exact Filter.mem_pi.1 hi
  choose J _ u hu hJu using ht'
  have hev : ∀ᶠ M : ℕ in atTop, ∀ i j, ∀ x : k, Deep (M : ℤ) x → x ∈ u i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_deep_subset (hu i j)
  obtain ⟨M, hM⟩ := hev.exists
  exact ⟨M, fun y hy => hts (Set.mem_pi.2 fun i _ => hJu i (Set.mem_pi.2 fun j _ => hM i j _ (hy i j)))⟩

private theorem deep_neg {a : ℤ} {x : k} (h : Deep a x) : Deep a (-x) := by
  unfold Deep at h ⊢
  rwa [Valuation.map_neg]

private theorem deep_add {a : ℤ} {x y : k} (hx : Deep a x) (hy : Deep a y) : Deep a (x + y) := by
  unfold Deep at hx hy ⊢
  exact ((valuation k).map_add x y).trans (max_le hx hy)

private theorem deep_zero' (a : ℤ) : Deep a (0 : k) := by
  unfold Deep
  simp

private theorem deep_of_le' {a b : ℤ} (hab : a ≤ b) {x : k} (h : Deep b x) : Deep a x := by
  unfold Deep at h ⊢
  exact h.trans (zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab)

private theorem exists_deep_neg_natCast (x : k) : ∃ N : ℕ, Deep (-(N : ℤ)) x := by
  unfold Deep
  by_cases hx : valuation k x = 0
  · exact ⟨0, by simp [hx]⟩

  obtain ⟨N, hN⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨N, ?_⟩
  rw [Units.val_mk0] at hN
  have hpos : (0 : ValueGroupWithZero k) < uniformizer k ^ N := pow_pos uniformizer_pos N
  have hx0 : (0 : ValueGroupWithZero k) < valuation k x := zero_lt_iff.2 hx
  rw [_root_.zpow_neg, zpow_natCast]
  exact ((lt_inv_comm₀ hpos hx0).1 hN).le

private theorem isOpen_setOf_forall_deep {n : Type} [Fintype n] (a : ℤ) :
    IsOpen {y : Matrix n n k | ∀ i j, Deep a (y i j)} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_deep (k := k) a).preimage (continuous_id.matrix_elem i j)

theorem exists_bound_period : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n], ∀ Φ ∈ SB (Matrix n n k),
    ∃ N M : ℕ, (∀ x, Φ x ≠ 0 → ∀ i j, Deep (-(N : ℤ)) (x i j)) ∧
      ∀ x y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x := by
  intro k _ _ _ _ n _ _ Φ hΦ
  have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨hlc, hcs⟩ := hΦ'
  have hC : IsCompact (tsupport Φ) := hcs
  have hzero : ∀ z, z ∉ tsupport Φ → Φ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport Φ h)

  let U : ℕ → Set (Matrix n n k) := fun N => {x | ∀ i j, Deep (-(N : ℤ)) (x i j)}
  have hUm : Monotone U := fun N N' h x hx i j =>
    deep_of_le' (neg_le_neg (by exact_mod_cast h)) (hx i j)
  have hUcov : tsupport Φ ⊆ ⋃ N, U N := by
    intro x _
    have hev : ∀ᶠ N : ℕ in atTop, ∀ i j, Deep (-(N : ℤ)) (x i j) := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      obtain ⟨N₀, hN₀⟩ := exists_deep_neg_natCast (x i j)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact deep_of_le' (neg_le_neg (by exact_mod_cast hN)) hN₀
    obtain ⟨N, hN⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  obtain ⟨N, hN⟩ := hC.elim_directed_cover U (fun N => isOpen_setOf_forall_deep _) hUcov hUm.directed_le

  let W : ℕ → Set (Matrix n n k) :=
    fun M => {x | ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x}
  have hWm : Monotone W := fun M M' h x hx y hy =>
    hx y fun i j => deep_of_le' (by exact_mod_cast h) (hy i j)
  have hWo : ∀ M, IsOpen (W M) := by
    intro M
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hD : {y : Matrix n n k | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 (0 : Matrix n n k) :=
      (isOpen_setOf_forall_deep _).mem_nhds fun i j => deep_zero' _
    have hD' : (fun z : Matrix n n k => z - x) ⁻¹' {y | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 x := by
      apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      simpa using hD
    refine Filter.mem_of_superset hD' fun z hz y hy => ?_
    have hz' : ∀ i j, Deep (M : ℤ) ((z - x) i j) := hz
    have h1 : Φ (x + ((z - x) + y)) = Φ x :=
      hx _ fun i j => by simpa using deep_add (hz' i j) (hy i j)
    have h2 : Φ (x + (z - x)) = Φ x := hx _ hz'
    rw [add_sub_cancel] at h2
    have he : x + ((z - x) + y) = z + y := by abel
    rw [he] at h1
    rw [h1, h2]
  have hWcov : tsupport Φ ⊆ ⋃ M, W M := by
    intro x _
    have hs : {y : Matrix n n k | Φ (x + y) = Φ x} ∈ 𝓝 (0 : Matrix n n k) := by
      apply IsOpen.mem_nhds
      · exact (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
      · simp
    obtain ⟨M, hM⟩ := exists_deep_subset hs
    exact Set.mem_iUnion.2 ⟨M, fun y hy => hM y hy⟩
  obtain ⟨M, hM⟩ := hC.elim_directed_cover W hWo hWcov hWm.directed_le
  refine ⟨N, M, fun x hx i j => hN (subset_tsupport Φ hx) i j, fun x y hy => ?_⟩
  by_cases hx : x ∈ tsupport Φ
  · exact hM hx y hy
  by_cases hxy : x + y ∈ tsupport Φ
  · have h := hM hxy (-y) fun i j => by simpa using deep_neg (hy i j)
    rw [add_neg_cancel_right] at h
    exact h.symm
  · rw [hzero _ hx, hzero _ hxy]

end GlobalTheory.SBUniform
end

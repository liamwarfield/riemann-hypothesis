module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtension

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShift
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.ConjEv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_box_iff_forall_valuation_le {m : ℕ} {s : kˣ} {x : Fin m → k} :
    x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s ↔ ∀ j, valuation k (x j) ≤ valuation k (s : k) :=
  Iff.rfl

theorem exists_mulVec_box (m : ℕ) (g : Matrix (Fin m) (Fin m) k) (t : kˣ) :
    ∃ t' : kˣ, ∀ x ∈ box m t, g *ᵥ x ∈ box m t' := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exact ⟨t, fun x _ => mem_box_iff_forall_valuation_le.2 fun j => isEmptyElim j⟩
  obtain ⟨ij, hij⟩ := Finite.exists_max (fun ij : Fin m × Fin m => valuation k (g ij.1 ij.2))
  by_cases h0 : g ij.1 ij.2 = 0
  · refine ⟨t, fun x _ => ?_⟩
    have hg : g = 0 := by
      ext i j
      simpa [h0] using hij (i, j)
    rw [hg, Matrix.zero_mulVec]
    exact zero_mem _
  · refine ⟨Units.mk0 _ h0 * t, fun x hx => ?_⟩
    rw [mem_box_iff_forall_valuation_le] at hx ⊢
    intro i
    show valuation k (∑ j, g i j * x j) ≤ _
    refine Finset.sum_induction _ (fun y => valuation k y ≤ valuation k ((Units.mk0 _ h0 * t : kˣ) : k))
      (fun a b ha hb => (valuation k).map_add_le ha hb) (by simp) (fun j _ => ?_)
    rw [map_mul, Units.val_mul, map_mul, Units.val_mk0]
    exact mul_le_mul' (hij (i, j)) (hx j)

theorem box_mono {m : ℕ} {t t' : kˣ} (h : valuation k (t : k) ≤ valuation k (t' : k)) :
    ∀ x ∈ box m t, x ∈ box m t' := by
  intro x hx
  rw [mem_box_iff_forall_valuation_le] at hx ⊢
  exact fun j => le_trans (hx j) h


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem val_mul_inv_le {c r t : kˣ} (h : valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t : k)) :
    valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  have e1 : c * t⁻¹ = (c * r⁻¹) * (r * t⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left]
  have e2 : t * (r * t⁻¹) = r := by
    rw [mul_comm r, ← mul_assoc, mul_inv_cancel, one_mul]
  calc valuation k ((c * t⁻¹ : kˣ) : k)
      = valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((r * t⁻¹ : kˣ) : k) := by
        rw [e1, Units.val_mul, map_mul]
    _ ≤ valuation k (t : k) * valuation k ((r * t⁻¹ : kˣ) : k) := mul_le_mul' h le_rfl
    _ = valuation k (r : k) := by
        rw [← map_mul, ← Units.val_mul, e2]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem wt_mir (ψ : AddChar k Circle) {n : ℕ} (p : Mir k n) (y : Fin (n + 1) → k) :
    wt ψ n (((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) = wt ψ n y := by
  unfold GlobalTheory.CompanionTheory.MirPair.wt
  rw [GlobalTheory.BZMir.mulVec_last_of_mem k _ p.2]

theorem absPow_succ_val (s : ℕ) (u : kˣ) :
    ((absPow k ((s + 1 : ℕ) : ℂ) u : ℂˣ) : ℂ) = ((absPow k (s : ℂ) u : ℂˣ) : ℂ) * ((nabs k u : ℝ) : ℂ) := by
  rw [show ((s + 1 : ℕ) : ℂ) = (s : ℂ) + 1 by push_cast; ring, GlobalTheory.SmGL.absPow_add,
    MonoidHom.mul_apply, Units.val_mul, GlobalTheory.SmGL.val_absPow k 1, Complex.cpow_one]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
  (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ)

theorem JJ_conj (hB : TwInv T T' B s) (p : Mir k n) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') :
    JJ ν ψ T B M (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
        (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') =
      ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
        JJ ν ψ T B {y | ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} v v' := by
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hw : ∀ x : Fin (n + 1) → k, GlobalTheory.CompanionTheory.MirPair.wt ψ n x =
      GlobalTheory.CompanionTheory.MirPair.wt ψ n
        ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := GlobalTheory.CompanionTheory.MirPair.ConjEv.wt_mir ψ p⁻¹ x
    rw [Subgroup.coe_inv] at h
    exact h.symm
  have hF := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (p : GL (Fin (n + 1)) k) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n y * GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  have key : ∀ x : Fin (n + 1) → k,
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x *
                   GlobalTheory.CompanionTheory.MirPair.coef T B (T (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
                     (T' (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') x =
        ((GlobalTheory.SmGL.detChar (Fin (n + 1)) (GlobalTheory.SmGL.absPow k (s : ℂ))
            (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
          (GlobalTheory.CompanionTheory.MirPair.wt ψ n
                       ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) *
            GlobalTheory.CompanionTheory.MirPair.coef T B v v'
              ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
    intro x
    rw [hlevi, ← hw]
    ring
  unfold GlobalTheory.CompanionTheory.MirPair.JJ
  simp only [key]
  rw [integral_const_mul, hF, ← mul_assoc]
  congr 1
  rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.ConjEv.absPow_succ_val]

end GlobalTheory.CompanionTheory.MirPair.ConjEv

namespace GlobalTheory.CompanionTheory.MirPair

theorem evVal_conj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB p v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB
    (p : GL (Fin (n + 1)) k) v v'
  obtain ⟨t₁, ht₁₀, ht₁r⟩ : ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t₁ : k) := by
    rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
    · exact ⟨c * r⁻¹, h, le_rfl⟩
    · exact ⟨t₀, le_rfl, h⟩
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.CompanionTheory.MirPair.ConjEv.exists_mulVec_box (n + 1)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) t₁
  refine ⟨t₂, fun t ht => ?_⟩
  rw [GlobalTheory.CompanionTheory.MirPair.ConjEv.JJ_conj ν ψ T T' B s hB p]
  congr 1
  rw [← ht₀ t₁ ht₁₀]
  exact hr t₁ (GlobalTheory.CompanionTheory.MirPair.ConjEv.val_mul_inv_le ht₁r) t
    (fun x hx => GlobalTheory.CompanionTheory.MirPair.ConjEv.box_mono ht _ (ht₂ x hx))

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShiftStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_shift : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.evVal_conj | exact GlobalTheory.CompanionTheory.MirPair.evVal_conj | (intros; apply GlobalTheory.CompanionTheory.MirPair.evVal_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInduction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInduction
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_threshold_mem_box {m : ℕ} (y : Fin m → k) (t₀ : kˣ) :
    ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ t : kˣ, valuation k (t₁ : k) ≤ valuation k (t : k) → y ∈ box m t := by
  classical
  have hstep : ∀ (S : Finset (Fin m)), ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ j ∈ S, valuation k (y j) ≤ valuation k (t₁ : k) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨t₀, le_rfl, by simp⟩
    | insert a S _ ih =>
      obtain ⟨t₁, h0, h1⟩ := ih
      by_cases hle : valuation k (y a) ≤ valuation k (t₁ : k)
      · refine ⟨t₁, h0, fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hle
        · exact h1 j hj
      · have hlt := lt_of_not_ge hle
        have hya : y a ≠ 0 := by
          intro h0'
          rw [h0', map_zero] at hlt
          exact not_lt_zero' hlt
        refine ⟨Units.mk0 (y a) hya, ?_, fun j hj => ?_⟩
        · simpa using h0.trans hlt.le
        · rcases Finset.mem_insert.1 hj with rfl | hj
          · simp
          · simpa using (h1 j hj).trans hlt.le
  obtain ⟨t₁, h0, h1⟩ := hstep Finset.univ
  exact ⟨t₁, h0, fun t ht j => (h1 j (Finset.mem_univ j)).trans ht⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem setIntegral_box_add (ν : Measure k) [ν.IsAddHaarMeasure] {m : ℕ} (t : kˣ) {y : Fin m → k}
    (hy : y ∈ box m t) (f : (Fin m → k) → ℂ) :
    ∫ x in (box m t : Set (Fin m → k)), f (x + y) ∂(piHaar ν m) =
      ∫ x in (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) := by
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : (piHaar ν m).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hpre : (fun x => x + y) ⁻¹' (box m t : Set (Fin m → k)) = box m t := by
    ext x
    exact (box m t).add_mem_cancel_right hy
  have := (measurePreserving_add_right (piHaar ν m) y).setIntegral_preimage_emb
    (measurableEmbedding_addRight y) f (box m t : Set (Fin m → k))
  rwa [hpre] at this

theorem wt_sub (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x - y) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x - y) (Fin.last n) = y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.sub_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem wt_add (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x + y) = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x + y) (Fin.last n) = -y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.add_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem EvVal_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB y v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨t₁, h01, h1⟩ := exists_threshold_mem_box y t₀
  obtain ⟨hc1, hc2, -⟩ := GlobalTheory.T.mirabolic_coefficient_translation T T' B s hB
  refine ⟨⟨t₁, fun t ht => ?_⟩, ⟨t₁, fun t ht => ?_⟩⟩
  · have hy := h1 t ht
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy (fun x => wt ψ n (x - y) * coef T B v v' x)
    simp only [add_sub_cancel_right] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) (T (uM (n + 1) y) v) v' =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x + y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc1]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_sub, mul_assoc]
  · have hy := h1 t ht
    have hy' : -y ∈ box (n + 1) t := neg_mem hy
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy' (fun x => wt ψ n (x + y) * coef T B v v' x)
    simp only [← sub_eq_add_neg, sub_add_cancel] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v (T' (uM (n + 1) y) v') =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x - y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc2]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_add, mul_assoc]

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInductionStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_depth_induction : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.EvVal_translate | exact GlobalTheory.CompanionTheory.MirPair.EvVal_translate | (intros; apply GlobalTheory.CompanionTheory.MirPair.EvVal_translate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacter
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Descend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_uM (ψ : AddChar k Circle) (n : ℕ) (u : MirUin k (n + 1)) :
    ∃ y : Fin (n + 1) → k, (u : Mir k (n + 1)) = uM (n + 1) y ∧
      ((mirChar k ψ n u : ℂˣ) : ℂ) = ((ψ (y (Fin.last n)) : Circle) : ℂ) := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp u.2)
  refine ⟨Multiplicative.toAdd w, Subtype.ext hw.symm, ?_⟩
  rw [GlobalTheory.BZMir.mirChar_eq k ψ n u w hw.symm, Circle.toUnits_apply, Units.val_mk0]

theorem left_kill (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (f : V →ₗ[ℂ] ℂ)
    (h : ∀ (y : Fin (n + 1) → k) v, f (T (uM (n + 1) y) v) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * f v) :
    twKer T (MirUin k (n + 1)) (mirChar k ψ n) ≤ LinearMap.ker f := by
  rw [GlobalTheory.PRep.twKer, Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  obtain ⟨y, hu, hχ⟩ := GlobalTheory.CompanionTheory.MirPair.Descend.exists_uM ψ n u
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu, h, hχ, sub_self]

theorem phiMinus_mk (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (p : Mir k n) (v : V) :
    phiMinus k ψ T p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) := rfl

theorem descend : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ n s V V' _ _ _ _ T T' B₀ hT hT' hL hnd
  have hleft : ∀ v' : V', GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker (B₀.flip v') := fun v' =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ T (B₀.flip v') fun y v => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply]
      exact hT y v v'
  have hright : ∀ v : V, GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker (B₀ v) := fun v =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ⁻¹ T' (B₀ v) fun y v' => by
      rw [AddChar.inv_apply]
      exact hT' y v v'
  have h₁ : GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker B₀ := by
    intro v hv
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun v' => ?_
    have h := LinearMap.mem_ker.mp (hleft v' hv)
    rw [LinearMap.flip_apply] at h
    rw [h, LinearMap.zero_apply]
  let B₁ : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] V' →ₗ[ℂ] ℂ :=
    Submodule.liftQ _ B₀ h₁
  have h₂ : GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker B₁.flip := by
    intro v' hv'
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.mem_ker.mp (hright v hv')
  let B' : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] GlobalTheory.PRep.TwJacquet T'
      (GlobalTheory.BZMir.MirUin k (n + 1)) (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ :=
    (Submodule.liftQ _ B₁.flip h₂).flip
  have hB' : ∀ (v : V) (v' : V'), B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B₀ v v' :=
    fun _ _ => rfl
  refine ⟨B', ?_, ?_⟩
  · intro p w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    rw [GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, hB', hB', hL]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ∉ GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
        (GlobalTheory.BZMir.mirChar k ψ n) := fun h =>
      hw ((Submodule.Quotient.mk_eq_zero _).mpr h)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPair.Descend

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacterStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_invariant_pairing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.Descend.descend | exact GlobalTheory.CompanionTheory.MirPair.Descend.descend | (intros; apply GlobalTheory.CompanionTheory.MirPair.Descend.descend <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicEvaluationLinear
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicEvaluationLinear
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair.EvLin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM (k := k) n 0 = 1 := by
  simp only [uM, ofAdd_zero, map_one]

theorem continuous_coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T)
    (v : V) (v' : V') : Continuous (coef T B v v') := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => uM n (y - x)) ⁻¹' {g | T g v = v}, (hT v).preimage
    ((continuous_uM n).comp (continuous_id.sub continuous_const)), ?_, fun y hy => ?_⟩
  · simp [uM_zero]
  · have hy' : T (uM n (y - x)) v = v := hy
    have h : uM n y = uM n x * uM n (y - x) := by
      rw [← uM_add, add_sub_cancel]
    simp only [coef, h, map_mul, Module.End.mul_apply, hy']

theorem continuous_wt (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) : Continuous (wt ψ n) :=
  continuous_subtype_val.comp (hψ.comp (continuous_apply _).neg)

variable [MeasurableSpace k] [BorelSpace k]

theorem integrableOn_box (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) (v : V) (v' : V') (t : kˣ) :
    IntegrableOn (fun x => wt ψ n x * coef T B v v' x) (box (n + 1) t : Set (Fin (n + 1) → k))
      (piHaar ν (n + 1)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : IsFiniteMeasureOnCompacts (piHaar ν (n + 1)) := by
    unfold piHaar
    infer_instance
  exact ((continuous_wt ψ hψ n).mul (continuous_coef T B hT v v')).continuousOn.integrableOn_compact
    (isCompact_box _ t)

theorem coef_add_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v₁ v₂ : V) (v' : V')
    (x : Fin n → k) : coef T B (v₁ + v₂) v' x = coef T B v₁ v' x + coef T B v₂ v' x := by
  simp [coef]

theorem coef_smul_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B (z • v) v' x = z * coef T B v v' x := by
  simp [coef]

theorem coef_add_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v₁ v₂ : V')
    (x : Fin n → k) : coef T B v (v₁ + v₂) x = coef T B v v₁ x + coef T B v v₂ x := by
  simp [coef]

theorem coef_smul_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B v (z • v') x = z * coef T B v v' x := by
  simp [coef]

theorem exists_common_threshold {P Q : kˣ → Prop}
    (hP : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t)
    (hQ : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → Q t) :
    ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t ∧ Q t := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
  · exact ⟨b, fun t ht => ⟨ha t (h.trans ht), hb t ht⟩⟩
  · exact ⟨a, fun t ht => ⟨ha t ht, hb t (h.trans ht)⟩⟩

theorem evVal_bilinear (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) :
    (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ →
      EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧
    (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ →
      EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  refine ⟨fun v₁ v₂ v' A₁ A₂ h₁ h₂ => ?_, fun z v v' A h => ?_, fun v v₁ v₂ A₁ A₂ h₁ h₂ => ?_,
    fun z v v' A h => ?_⟩
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_left, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v₁ v' t) (integrableOn_box ν ψ T B hψ hT v₂ v' t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_left, mul_left_comm _ z]
    exact integral_const_mul z _
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_right, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v v₁ t) (integrableOn_box ν ψ T B hψ hT v v₂ t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_right, mul_left_comm _ z]
    exact integral_const_mul z _

theorem evVal_additive_homogeneous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ → EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧ (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ → EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT
  exact evVal_bilinear ν ψ T B hψ hT

end GlobalTheory.CompanionTheory.MirPair.EvLin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicEvaluationLinearStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_evaluation_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ → EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧ (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ → EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.EvLin.evVal_additive_homogeneous | exact GlobalTheory.CompanionTheory.MirPair.EvLin.evVal_additive_homogeneous | (intros; apply GlobalTheory.CompanionTheory.MirPair.EvLin.evVal_additive_homogeneous <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmooth
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem pairing_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT hT' B hB hnd
  borelize k
  let ν : Measure k := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hinv : TwInv T T' B s := hB
  have hlin := GlobalTheory.T.mirabolic_evaluation_linear ν ψ T B hψ hT
  have hex := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv
  have huniq : ∀ {v v' A A'}, EvVal ν ψ T B v v' A → EvVal ν ψ T B v v' A' → A = A' := by
    rintro v v' A A' ⟨t₀, h₀⟩ ⟨t₁, h₁⟩
    rcases le_total (valuation k (t₀ : k)) (valuation k (t₁ : k)) with h | h
    · rw [← h₀ t₁ h, h₁ t₁ le_rfl]
    · rw [← h₀ t₀ le_rfl, h₁ t₀ h]
  choose f hf using hex
  let B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ f
    (fun v₁ v₂ v' => huniq (hf _ _) (hlin.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.1 _ _ _ _ (hf _ _)))
    (fun v v₁ v₂ => huniq (hf _ _) (hlin.2.2.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.2.2 _ _ _ _ (hf _ _)))
  have hB₀ : ∀ v v', B₀ v v' = f v v' := fun _ _ => rfl
  refine GlobalTheory.T.twisted_invariant_pairing_character ψ n s V V' T T' B₀ ?_ ?_ ?_ ?_
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).1
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).2
  · intro p v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_conductor_shift ν ψ c T T' B s hψ hc hT hT' hinv p v v' _ (hf _ _))
  · intro v hv
    obtain ⟨v', A, hA, hA0⟩ := GlobalTheory.T.mirabolic_pairing_conductor_extension ν ψ c T T' B s hψ hc hT hT' hinv hnd v hv
    exact ⟨v', by rw [hB₀, huniq (hf _ _) hA]; exact hA0⟩

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmoothStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_mirabolic_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.pairing_phi | exact GlobalTheory.CompanionTheory.MirPair.pairing_phi | (intros; apply GlobalTheory.CompanionTheory.MirPair.pairing_phi <;> assumption)
end

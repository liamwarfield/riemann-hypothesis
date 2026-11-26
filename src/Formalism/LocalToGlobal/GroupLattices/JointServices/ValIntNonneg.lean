module

public import Formalism.LocalToGlobal.GroupLattices.JointServices
public import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.JointServices.ValIntNonneg
section -- merged from Formalism.LocalToGlobal.GroupLattices.JointServices.VAddEqVw
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)

noncomputable section

namespace Formalism.L2.G.ServJoint

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private theorem vAdd_mul_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold Formalism.BasicNotions.vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring

private theorem vw_mul_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    Formalism.DivisionValues.vw w (x * y) = Formalism.DivisionValues.vw w x + Formalism.DivisionValues.vw w y := by
  have hx' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hx
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hy
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w hx' hy']

private theorem vAdd_algebraMap_eq_vw_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    vAdd w (algebraMap (𝓞 K) K a) = Formalism.DivisionValues.vw w (algebraMap (𝓞 K) K a) := by
  have hI : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  unfold Formalism.BasicNotions.vAdd Formalism.DivisionValues.vw
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha, WithZero.log_exp,
    neg_neg, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hI]

theorem vAdd_eq_vw (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) : vAdd w x = vw w x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hx; rw [h, zero_div]
  have ha0 : a ≠ 0 := by
    rintro rfl; exact haK (map_zero _)
  have hq : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a :=
    div_mul_cancel₀ _ hbK
  have h1 := vAdd_mul_of_ne_zero w hx hbK
  have h2 := vw_mul_of_ne_zero w hx hbK
  rw [hq] at h1 h2
  have e1 := vAdd_algebraMap_eq_vw_of_ne_zero w a ha0
  have e2 := vAdd_algebraMap_eq_vw_of_ne_zero w b hb0
  linarith

def VGeq (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) (z : K) : Prop := z = 0 ∨ s ≤ (vAdd w z : ℝ)

theorem VGeq.zero (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : VGeq w s (0 : K) := Or.inl rfl

private theorem vAdd_le_of_valuation_le {w : HeightOneSpectrum (𝓞 K)} {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : w.valuation K y ≤ w.valuation K x) : vAdd w x ≤ vAdd w y := by
  have hx' : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hy' : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have h' : WithZero.exp (WithZero.log (w.valuation K y)) ≤ WithZero.exp (WithZero.log (w.valuation K x)) := by
    rwa [WithZero.exp_log hx', WithZero.exp_log hy']
  have h'' := WithZero.exp_le_exp.mp h'
  unfold Formalism.BasicNotions.vAdd
  linarith

theorem VGeq.add {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {a b : K} (ha : VGeq w s a) (hb : VGeq w s b) :
    VGeq w s (a + b) := by
  by_cases ha0 : a = 0
  · simpa [ha0] using hb
  by_cases hb0 : b = 0
  · simpa [hb0] using ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  rcases ha with h | ha
  · exact absurd h ha0
  rcases hb with h | hb
  · exact absurd h hb0
  right
  rcases le_max_iff.mp ((w.valuation K).map_add a b) with h | h
  · exact ha.trans (by exact_mod_cast vAdd_le_of_valuation_le ha0 hab h)
  · exact hb.trans (by exact_mod_cast vAdd_le_of_valuation_le hb0 hab h)

theorem VGeq.int_mul {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {a : K} (c : 𝓞 K) (ha : VGeq w s a) :
    VGeq w s ((c : K) * a) := by
  by_cases ha0 : a = 0
  · left; simp [ha0]
  by_cases hc : (c : K) = 0
  · left; simp [hc]
  rcases ha with h | ha
  · exact absurd h ha0
  right
  have hca : (c : K) * a ≠ 0 := mul_ne_zero hc ha0
  have hv : w.valuation K ((c : K) * a) ≤ w.valuation K a := by
    rw [map_mul]
    exact mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one w c)
  exact ha.trans (by exact_mod_cast vAdd_le_of_valuation_le ha0 hca hv)

theorem VGeq.sum {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {ι : Type*} (S : Finset ι) (f : ι → K)
    (h : ∀ i ∈ S, VGeq w s (f i)) : VGeq w s (∑ i ∈ S, f i) := by
  exact Finset.sum_induction f (VGeq w s) (fun a b ha hb => ha.add hb) (VGeq.zero w s) h

theorem VGeq.vw {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {z : K} (h : VGeq w s z) : z = 0 ∨ s ≤ (Formalism.DivisionValues.vw w z : ℝ) := by
  by_cases hz : z = 0
  · exact Or.inl hz
  rcases h with h | h
  · exact Or.inl h
  right
  rw [← vAdd_eq_vw w z hz]
  exact h

end Formalism.L2.G.ServJoint

end
end

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem perCol_lin (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (φ : D.what₂.Mu u) :
    ∃ f : D.what₂.Amb μ →ₗ[ℂ] ℂ, ∀ F, D.what₂.perCol u μ φ F = f F := by
  by_cases h : μ = D.what₂.mu0
  · subst h
    refine ⟨((D.mem u).P.period ((D.mem u).P.lowerMap ((D.mem u).P.evz ((D.mem u).C.col ↑(D.eMu u φ))))).comp
      (D.eMt u).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_base_eq_PtilCol]
    rfl
  · refine ⟨((D.PTw u μ).period ((D.PTw u μ).lowerMap ((D.PTw u μ).evz
      ((D.chTw u μ).col (D.e0Tw u μ ↑(D.eMu u φ)))))).comp (D.eMtTw u μ).symm.toLinearMap, fun F => ?_⟩
    rw [D.perCol_tie u μ h]
    rfl

theorem perToVal2 : PerToVal2 := by
  intro D B hB u t hcut z s N h φ hφ F hF
  obtain ⟨s0, hOk⟩ := hB.ok
  have hV0 : B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F) ∈ D.what₂.V0 (B.I.tup t) := by
    refine ⟨B.I.jA t ((rV0 D B.A B.Ps B.ψs t).mulVec F), ?_⟩
    have h1 := (hB.sharp.forms t).op_eq ((rV0 D B.A B.Ps B.ψs t).mulVec F)
    rw [level_operator_fixes_image hOk B.Ps B.ψs B.Zs t F] at h1
    exact h1
  have hgen := ((hB.sharp.Mtilde t).2 _).1 ((image_mem_nabla_iff hOk B.Ps B.ψs B.Zs t F).2 hF)
  obtain ⟨S, c, hS, hx0⟩ := hcut _ hgen hV0
  have key : ∀ φ ∈ Submodule.span (𝓞 D.what₂.LL) N, VGeq z s (B.Dc.Pt (B.I.wU u) t φ F) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      have hex : ∀ y : D.what₂.Amb (B.I.tup t), ∃ a : D.what₂.LL, y ∈ S →
          (D.what₂.embLL a = D.what₂.perCol u (B.I.tup t) (D.jN u (B.I.eNu u x)) y ∧ (a = 0 ∨ s ≤ (vAdd z a : ℝ))) := by
        intro y
        by_cases hy : y ∈ S
        · obtain ⟨a, ha⟩ := h x hx y (hS hy).1 (hS hy).2
          exact ⟨a, fun _ => ha⟩
        · exact ⟨0, fun h' => absurd h' hy⟩
      choose a ha using hex
      obtain ⟨f, hf⟩ := perCol_lin D u (B.I.tup t) (D.jN u (B.I.eNu u x))
      have heq : B.Dc.Pt (B.I.wU u) t x F = ∑ y ∈ S, ((c y : 𝓞 D.what₂.LL) : D.what₂.LL) * a y := by
        apply D.what₂.embLL.injective
        rw [hB.dcPt u t x F, hf]
        refine (congrArg f hx0).trans ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [map_smul, smul_eq_mul, map_mul, (ha y hy).1, hf]
      rw [heq]
      exact VGeq.sum S _ fun y hy => VGeq.int_mul (c y) (ha y hy).2
    | zero =>
      rw [map_zero, LinearMap.zero_apply]
      exact VGeq.zero z s
    | add x y _ _ hx hy =>
      rw [map_add (f := _), LinearMap.add_apply]
      exact hx.add hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact VGeq.int_mul a hx
  exact (key φ hφ).vw

theorem val2AllAtR : SecondLevelValuationAtRestricted := by
  intro D L B hB hcut h u Nu hNu z
  have hμ := hB.mu (D.plEq.symm z)
  rw [Equiv.apply_symm_apply] at hμ
  have h2 : ∀ μ, D.what₂.muAt (D.plEq.symm z) = μ → ∀ φ ∈ L.NuLat u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
        (y = 0 ∨ ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) ≤ (vAdd (D.plEq (D.plEq.symm z)) y : ℝ)) := by
    rintro μ rfl
    exact h u (D.plEq.symm z)
  have h3 := perToVal2 D B hB u (B.S1.μ z) (hcut _ (hμ ▸ used_muAt D (D.plEq.symm z))) z ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ) (Nu : Set _)
    (fun x hx F hF1 hF0 => by
      have h4 := h2 _ hμ _ (hNu x hx) F hF1 hF0
      rw [Equiv.apply_symm_apply] at h4
      exact h4)
  rw [Submodule.span_eq] at h3
  exact h3

end Formalism.L2.G.ServJoint

end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.JointServices.Cut
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem carrier_sum {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {ι : Type} (S : Finset ι) (f : ι → V) (h : ∀ i ∈ S, f i ∈ M.carrier) : ∑ i ∈ S, f i ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq] at h ⊢
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨c1, hc1⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨c2, hc2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨c1 + c2, ?_⟩
    rw [hc1, hc2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [add_smul]

theorem gen_mem_carrier {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {v : V} (hv : v ∈ M.gen) : v ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq]
  refine ⟨fun w => if w = v then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => absurd hv h)]
  simp

theorem cutUp_of_stable (D : D7) (μ : D.what₂.Tup)
    (h : ∀ (a : 𝓞 D.what₂.LL), ∀ x ∈ (D.what₂.Mtilde μ).carrier, D.what₂.embLL (a : D.what₂.LL) • x ∈ (D.what₂.Mtilde μ).carrier) :
    CutUp D μ := by
  classical
  unfold CutUp
  rintro x ⟨c, hc⟩ hx0
  have hxM : x ∈ (D.what₂.Mtilde μ).carrier := by
    rw [hc]
    exact carrier_sum _ _ _ (fun w hw => h (c w) w (gen_mem_carrier _ hw))
  refine ⟨{x}, fun _ => 1, ?_, ?_⟩
  · rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact Set.mem_inter hxM hx0
  · simp

end Formalism.L2.G.ServJoint

end
end

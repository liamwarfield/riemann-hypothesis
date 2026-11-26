module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_l (a b y : Fin n → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub_l (a b y : Fin n → E) : hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul_l (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_r (a b y : Fin n → E) : hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_sub_r (a b y : Fin n → E) : hf L Hm y (a - b) = hf L Hm y a - hf L Hm y b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem hf_neg_r (a y : Fin n → E) : hf L Hm y (-a) = - hf L Hm y a := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_neg_l (a y : Fin n → E) : hf L Hm (-a) y = - hf L Hm a y := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_smul_r (c : E) (a y : Fin n → E) : hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_cj {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x y : Fin n → E) :
    L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def eichL (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun := eich L Hm x u s
  map_add' a b := by
    simp only [eich, hf_add_l]; module
  map_smul' c a := by
    simp only [eich, hf_smul_l, RingHom.id_apply]; module

theorem eich_inv {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v : Fin n → E) :
    eich L Hm x (-u) (L.cj s) (eich L Hm x u s v) = v := by
  have hu' : hf L Hm x u = 0 := by rw [← hf_cj L h, hu, map_zero]
  simp only [eich, hf_add_l, hf_sub_l, hf_smul_l, hf_neg_r, hx, hu, hu', ← hs]
  module

theorem eich_isom {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v w : Fin n → E) :
    hf L Hm (eich L Hm x u s v) (eich L Hm x u s w) = hf L Hm v w := by
  have hu' : hf L Hm x u = 0 := by rw [← hf_cj L h, hu, map_zero]
  simp only [eich, hf_add_l, hf_sub_l, hf_smul_l, hf_add_r, hf_sub_r, hf_smul_r, hx, hu, hu', ← hs,
    hf_cj L h]
  ring

end

theorem eichler_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (x u : Fin n → E) (s : E), hf L Hm x x = 0 → hf L Hm u x = 0 → s + L.cj s = hf L Hm u u → ∃ g ∈ isomG L Hm, (∀ v, g v = eich L Hm x u s v) ∧ ∀ v, g⁻¹ v = eich L Hm x (-u) (L.cj s) v := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH x u s hx hu hs
  have h1 := eich_inv L hH.1 x u s hx hu hs
  have h2 := eich_inv L hH.1 x (-u) (L.cj s) hx (by rw [hf_neg_l, hu, neg_zero])
    (by rw [L.cj_cj, hf_neg_l, hf_neg_r, neg_neg, add_comm, hs])
  simp only [neg_neg, L.cj_cj] at h2
  refine ⟨{ eichL L Hm x u s with
      invFun := eich L Hm x (-u) (L.cj s)
      left_inv := h1
      right_inv := h2 }, ?_, fun _ => rfl, fun _ => rfl⟩
  exact fun v w => eich_isom L hH.1 x u s hx hu hs v w

end GlobalTheory.HL.Eichler
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem _root_.GlobalTheory.HL.invVol_eq_div_of_le {G : Type*} [Group G] {D A B : Subgroup G}
    (hA : D ≤ A) (hB : D ≤ B) (h : D.relIndex A ≠ 0) :
    _root_.GlobalTheory.HL.invVol A B = (D.relIndex A : ℝ) / (D.relIndex B : ℝ) := by
  unfold _root_.GlobalTheory.HL.invVol
  have hDC : D ≤ A ⊓ B := le_inf hA hB
  have eA := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hDC inf_le_left
  have eB := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hDC inf_le_right
  rw [Subgroup.inf_relIndex_left] at eA
  rw [Subgroup.inf_relIndex_right] at eB
  have ha : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply h
    rw [← eA, h0, zero_mul]
  rw [← eA, ← eB, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr ha)]

theorem _root_.GlobalTheory.HL.invVol_mul_pos_le_conj : ∀ {G : Type} [Group G] (K0 K1 K : Subgroup G),
    K0.relIndex K1 ≠ 0 → K1.relIndex K0 ≠ 0 → K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
    _root_.GlobalTheory.HL.invVol K0 K = _root_.GlobalTheory.HL.invVol K0 K1 * _root_.GlobalTheory.HL.invVol K1 K ∧
    0 < _root_.GlobalTheory.HL.invVol K0 K ∧
    (K ≤ K1 → _root_.GlobalTheory.HL.invVol K0 K =
      _root_.GlobalTheory.HL.invVol K0 K1 * (K.relIndex K1 : ℝ)) ∧
    ∀ g : G, _root_.GlobalTheory.HL.invVol (MulAut.conj g • K0) (MulAut.conj g • K) =
      _root_.GlobalTheory.HL.invVol K0 K := by
  intro G _ K0 K1 K h01 h10 h0K hK0
  have hd0 : (K0 ⊓ K1 ⊓ K).relIndex K0 ≠ 0 :=
    Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero (by simp) h10) hK0
  have hd1 : (K0 ⊓ K1 ⊓ K).relIndex K1 ≠ 0 := Subgroup.relIndex_ne_zero_trans hd0 h01
  have hdK : (K0 ⊓ K1 ⊓ K).relIndex K ≠ 0 := Subgroup.relIndex_ne_zero_trans hd0 h0K
  have l0 : K0 ⊓ K1 ⊓ K ≤ K0 := inf_le_left.trans inf_le_left
  have l1 : K0 ⊓ K1 ⊓ K ≤ K1 := inf_le_left.trans inf_le_right
  have lK : K0 ⊓ K1 ⊓ K ≤ K := inf_le_right
  have e0K := _root_.GlobalTheory.HL.invVol_eq_div_of_le l0 lK hd0
  have e01 := _root_.GlobalTheory.HL.invVol_eq_div_of_le l0 l1 hd0
  have e1K := _root_.GlobalTheory.HL.invVol_eq_div_of_le l1 lK hd1
  have hmul : _root_.GlobalTheory.HL.invVol K0 K =
      _root_.GlobalTheory.HL.invVol K0 K1 * _root_.GlobalTheory.HL.invVol K1 K := by
    rw [e0K, e01, e1K, div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hd1)]
  refine ⟨hmul, ?_, ?_, ?_⟩
  · rw [e0K]
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdK))
  · intro hle
    have h1 : K1.relIndex K = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hmul]
    congr 1
    unfold _root_.GlobalTheory.HL.invVol
    rw [h1, Nat.cast_one, div_one]
  · intro g
    have hc : ∀ L : Subgroup G, MulAut.conj g • L = ConjAct.toConjAct g • L := fun L => rfl
    unfold _root_.GlobalTheory.HL.invVol
    rw [hc, hc, Subgroup.relIndex_pointwise_smul, Subgroup.relIndex_pointwise_smul]

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBound
open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Lin

variable {W : Type} [AddCommGroup W]

open Function in
private lemma quotientEquivProdOfLE_mk_fst {W : Type} [AddCommGroup W] {C B : AddSubgroup W}
    (h : C ≤ B) (w : W) : ((AddSubgroup.quotientEquivProdOfLE h) (w : W ⧸ C)).1 = (w : W ⧸ B) :=
  rfl

open Function in
private lemma Fine_of_le_of_relIndex_ne_zero {W : Type} [AddCommGroup W] {A B C : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex A ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ C := by
  obtain ⟨hBA, -, hinv, hsupp⟩ := hB
  have hidx : C.relIndex B ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA] at hC
    exact left_ne_zero_of_mul hC
  have hfin : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hidx
  refine ⟨hCB.trans hBA, hC, fun w b hb => hinv w b (hCB hb), ?_⟩
  let e := AddSubgroup.quotientEquivProdOfLE hCB
  refine ((hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
    e.injective.injOn).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [quotientEquivProdOfLE_mk_fst]
  exact ⟨w, hw, rfl⟩

private lemma exists_fine_fine_of_nice_nice {W : Type} [AddCommGroup W] {A : AddSubgroup W} {φ ψ : W → ℂ}
    (hφ : _root_.GlobalTheory.IdxInt.Nice A φ) (hψ : _root_.GlobalTheory.IdxInt.Nice A ψ) :
    ∃ C, _root_.GlobalTheory.IdxInt.Fine A φ C ∧ _root_.GlobalTheory.IdxInt.Fine A ψ C := by
  obtain ⟨B, hB⟩ := hφ
  obtain ⟨B', hB'⟩ := hψ
  have hidx : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB'.2.1
  exact ⟨B ⊓ B', Fine_of_le_of_relIndex_ne_zero hB inf_le_left hidx, Fine_of_le_of_relIndex_ne_zero hB' inf_le_right hidx⟩

private lemma Fine_add {W : Type} [AddCommGroup W] {A C : AddSubgroup W} {φ ψ : W → ℂ}
    (hφ : _root_.GlobalTheory.IdxInt.Fine A φ C) (hψ : _root_.GlobalTheory.IdxInt.Fine A ψ C) :
    _root_.GlobalTheory.IdxInt.Fine A (φ + ψ) C := by
  refine ⟨hφ.1, hφ.2.1, fun w b hb => by simp only [Pi.add_apply, hφ.2.2.1 w b hb, hψ.2.2.1 w b hb], ?_⟩
  refine (hφ.2.2.2.union hψ.2.2.2).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  rcases Function.support_add φ ψ hw with h | h
  · exact Or.inl ⟨w, h, rfl⟩
  · exact Or.inr ⟨w, h, rfl⟩

open Function in
private lemma finite_support_quotient_out_of_finite_image {W : Type} [AddCommGroup W] {B : AddSubgroup W} (φ : W → ℂ)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    (support fun c : W ⧸ B => φ (Quotient.out c)).Finite := by
  refine hφ.subset fun c hc => ⟨Quotient.out c, hc, QuotientAddGroup.out_eq' c⟩

theorem _root_.GlobalTheory.IdxInt.Lin.main : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A ψ → _root_.GlobalTheory.IdxInt.Nice A (φ + ψ) ∧ _root_.GlobalTheory.IdxInt.cint A (φ + ψ) = _root_.GlobalTheory.IdxInt.cint A φ + _root_.GlobalTheory.IdxInt.cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖_root_.GlobalTheory.IdxInt.cint A φ‖ ≤ (_root_.GlobalTheory.IdxInt.cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A (fun w => c * φ w) ∧ _root_.GlobalTheory.IdxInt.cint A (fun w => c * φ w) = c * _root_.GlobalTheory.IdxInt.cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (_root_.GlobalTheory.IdxInt.cint A (_root_.GlobalTheory.IdxInt.ind P)).re ∧ (_root_.GlobalTheory.IdxInt.cint A (_root_.GlobalTheory.IdxInt.ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, _root_.GlobalTheory.IdxInt.Nice A (φ i)) → _root_.GlobalTheory.IdxInt.Nice A (fun w => ∑ i ∈ s, φ i w) ∧ _root_.GlobalTheory.IdxInt.cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, _root_.GlobalTheory.IdxInt.cint A (φ i) := by
  intro W _ A
  have hadd : ∀ φ ψ : W → ℂ, _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A ψ → _root_.GlobalTheory.IdxInt.Nice A (φ + ψ) ∧ _root_.GlobalTheory.IdxInt.cint A (φ + ψ) = _root_.GlobalTheory.IdxInt.cint A φ + _root_.GlobalTheory.IdxInt.cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖_root_.GlobalTheory.IdxInt.cint A φ‖ ≤ (_root_.GlobalTheory.IdxInt.cint A ψ).re) := by
    intro φ ψ hφ hψ
    obtain ⟨C, hφC, hψC⟩ := exists_fine_fine_of_nice_nice hφ hψ
    have hsum := Fine_add hφC hψC
    have hfφ := finite_support_quotient_out_of_finite_image φ hφC.2.2.2
    have hfψ := finite_support_quotient_out_of_finite_image ψ hψC.2.2.2
    refine ⟨⟨C, hsum⟩, ?_, fun hle => ?_⟩
    · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hsum, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hφC,
        _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hψC, ← add_div]
      simp only [Pi.add_apply]
      rw [finsum_add_distrib hfφ hfψ]
    · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hφC, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hψC,
        finsum_eq_sum_of_support_subset (s := (hfφ.union hfψ).toFinset) _ (by simp),
        finsum_eq_sum_of_support_subset (s := (hfφ.union hfψ).toFinset) _ (by simp),
        norm_div, Complex.norm_natCast, Complex.div_natCast_re, Complex.re_sum]
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hle _)
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c φ hφ
    obtain ⟨B, hB⟩ := hφ
    have hc : _root_.GlobalTheory.IdxInt.Fine A (fun w => c * φ w) B :=
      ⟨hB.1, hB.2.1, fun w b hb => by simp only [hB.2.2.1 w b hb],
        hB.2.2.2.subset (Set.image_mono (Function.support_mul_subset_right _ _))⟩
    refine ⟨⟨B, hc⟩, ?_⟩
    rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hc, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hB,
      ← mul_finsum, mul_div_assoc]
  · intro P
    by_cases h : _root_.GlobalTheory.IdxInt.Nice A (_root_.GlobalTheory.IdxInt.ind P)
    · obtain ⟨B, hB⟩ := h
      rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hB,
        finsum_eq_sum _ (finite_support_quotient_out_of_finite_image _ hB.2.2.2), Complex.div_natCast_re, Complex.div_natCast_im,
        Complex.re_sum, Complex.im_sum]
      refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => ?_) (Nat.cast_nonneg _), ?_⟩
      · unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
      · rw [Finset.sum_eq_zero fun i _ => ?_, zero_div]
        unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dite_eq_right h]
      simp
  · intro ι s φ hs
    induction s using Finset.induction_on with
    | empty =>
      have h0 : _root_.GlobalTheory.IdxInt.Fine A (fun _ : W => (0 : ℂ)) A :=
        ⟨le_rfl, by simp [AddSubgroup.relIndex_self], fun _ _ _ => rfl, by simp⟩
      simp only [Finset.sum_empty]
      refine ⟨⟨A, h0⟩, ?_⟩
      rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A A _ h0]
      simp
    | insert i s hi ih =>
      have hi' := hs i (Finset.mem_insert_self i s)
      have ih' := ih fun j hj => hs j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      obtain ⟨hn, he, -⟩ := hadd (φ i) (fun w => ∑ j ∈ s, φ j w) hi' ih'.1
      exact ⟨hn, he.trans (by rw [ih'.2])⟩

end GlobalTheory.IdxInt.Lin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBoundStatement
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, Nice A φ → Nice A ψ → Nice A (φ + ψ) ∧ cint A (φ + ψ) = cint A φ + cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖cint A φ‖ ≤ (cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), Nice A φ → Nice A (fun w => c * φ w) ∧ cint A (fun w => c * φ w) = c * cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (cint A (ind P)).re ∧ (cint A (ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, Nice A (φ i)) → Nice A (fun w => ∑ i ∈ s, φ i w) ∧ cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, cint A (φ i) := by
  first | exact @GlobalTheory.IdxInt.Lin.main | exact GlobalTheory.IdxInt.Lin.main | (intros; apply GlobalTheory.IdxInt.Lin.main <;> assumption)
end
end

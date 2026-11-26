module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameUnipotentExchangingDualIsotropic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameUnipotentExchangingDualIsotropic
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameDual

open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

end

theorem exists_unip_change_dual : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (t : E) (gs gs2 : Fin r → S.V), (∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0) → (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → (∀ a j, hf L S.Hm (g a) (gs2 j) = if a = j.castSucc then 1 else 0) → (∀ i j, hf L S.Hm (gs i) (gs j) = 0) → (∀ i j, hf L S.Hm (gs2 i) (gs2 j) = 0) → ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧ (∀ j, m (gs j) = gs2 j) ∧ ∀ A : Submodule L.O S.V, (∀ x ∈ S.spanTo g r, x ∈ A) → (∀ x ∈ A, x ∈ perp L S.Hm (S.spanTo g r)) → m • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) = A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs2))).restrictScalars L.O := by
  intro F _ _ _ _ _ E _ _ _ L r k S g t gs gs2 hg hd hd2 hi hi2
  have hcj := hf_cj L S.herm.1
  obtain ⟨G, hG⟩ : ∃ G : Fin r → S.V, ∀ j, G j = g j.castSucc := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin r → S.V, ∀ j, w j = gs2 j - gs j := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin r → S.V, ∀ j, u j = w j + ∑ i, hf L S.Hm (gs j) (w i) • G i :=
    ⟨_, fun _ => rfl⟩
  have hGa : ∀ i a, hf L S.Hm (G i) (g a) = 0 := fun i a => by
    rw [hG, hg, if_neg]; rintro ⟨h, -⟩; exact Fin.castSucc_ne_last i h
  have haG : ∀ a i, hf L S.Hm (g a) (G i) = 0 := fun a i => by
    rw [hG, hg, if_neg]; rintro ⟨-, h⟩; exact Fin.castSucc_ne_last i h
  have hGG : ∀ i j, hf L S.Hm (G i) (G j) = 0 := fun i j => by rw [hG j]; exact hGa i _
  have hgw : ∀ a i, hf L S.Hm (g a) (w i) = 0 := fun a i => by rw [hw, hf_sub_r, hd, hd2, sub_self]
  have hwg : ∀ i a, hf L S.Hm (w i) (g a) = 0 := fun i a => by rw [← hcj, hgw, map_zero]
  have hGw : ∀ i j, hf L S.Hm (G i) (w j) = 0 := fun i j => by rw [hG i]; exact hgw _ _
  have hwG : ∀ i j, hf L S.Hm (w i) (G j) = 0 := fun i j => by rw [hG j]; exact hwg _ _
  have hGu : ∀ i j, hf L S.Hm (G i) (u j) = 0 := fun i j => by
    simp only [hu, hf_add_r, hf_sum_r, hf_smul_r, hGw, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huG : ∀ j i, hf L S.Hm (u j) (G i) = 0 := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hwG, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huw : ∀ j i, hf L S.Hm (u j) (w i) = hf L S.Hm (w j) (w i) := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hGw, mul_zero, Finset.sum_const_zero, add_zero]
  have huu : ∀ j l, hf L S.Hm (u j) (u l) = hf L S.Hm (w j) (w l) := fun j l => by
    conv_lhs => rw [hu l]
    simp only [hf_add_r, hf_sum_r, hf_smul_r, huG, huw, mul_zero, Finset.sum_const_zero, add_zero]
  have hgsG : ∀ j l, hf L S.Hm (gs j) (G l) = if l = j then 1 else 0 := fun j l => by
    rw [← hcj, hG, hd]
    by_cases h : l = j
    · subst h; simp
    · rw [if_neg (fun e => h (Fin.castSucc_injective _ e)), if_neg h, map_zero]
  have K : ∀ j i, hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (gs i) + hf L S.Hm (w j) (w i) = 0 := by
    intro j i
    have e : ∀ j, gs2 j = gs j + w j := fun j => by rw [hw]; abel
    have h2 := hi2 j i
    rw [e, e, hf_add_l, hf_add_r, hf_add_r, hi] at h2
    linear_combination h2

  obtain ⟨ff, hff⟩ : ∃ ff : S.V → S.V, ∀ v, ff v = v + ∑ j, hf L S.Hm v (G j) • u j -
      ∑ i, hf L S.Hm v (w i) • G i := ⟨_, fun _ => rfl⟩
  obtain ⟨fi, hfi⟩ : ∃ fi : S.V → S.V, ∀ v, fi v = v - ∑ j, hf L S.Hm v (G j) • u j +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) • G i :=
    ⟨_, fun _ => rfl⟩
  have hff_l : ∀ v y, hf L S.Hm (ff v) y = hf L S.Hm v y + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y -
      ∑ i, hf L S.Hm v (w i) * hf L S.Hm (G i) y := fun v y => by
    rw [hff]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have hff_r : ∀ y v, hf L S.Hm y (ff v) = hf L S.Hm y v + ∑ j, hf L S.Hm (G j) v * hf L S.Hm y (u j) -
      ∑ i, hf L S.Hm (w i) v * hf L S.Hm y (G i) := fun y v => by
    rw [hff]; simp only [hf_add_r, hf_sub_r, hf_sum_r, hf_smul_r, hcj]
  have hfi_l : ∀ v y, hf L S.Hm (fi v) y = hf L S.Hm v y - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) * hf L S.Hm (G i) y :=
    fun v y => by
    rw [hfi]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have h1 : ∀ v, ff (fi v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (fi v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hfi_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (fi v) (w l) =
        hf L S.Hm v (w l) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hfi_l, huw, hGw, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hff]; simp only [eG, ew]; rw [hfi]; abel
  have h2 : ∀ v, fi (ff v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (ff v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hff_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (ff v) (w l) =
        hf L S.Hm v (w l) + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hff_l, huw, hGw, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hfi]; simp only [eG, ew, add_sub_cancel_right]; rw [hff]; abel
  obtain ⟨m, hm⟩ : ∃ m : S.GLV, ∀ v, m v = ff v := by
    refine ⟨{ toFun := ff, invFun := fi, left_inv := h2, right_inv := h1, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro x y; simp only [hff, hf_add_l, add_smul, Finset.sum_add_distrib]; abel
    · intro c x; simp only [hff, hf_smul_l, smul_add, smul_sub, Finset.smul_sum, mul_smul, RingHom.id_apply]
  have iso : ∀ v v', hf L S.Hm (ff v) (ff v') = hf L S.Hm v v' := by
    intro v v'
    rw [hff_l]
    simp only [hff_r, huu, huG, hGu, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

    have hvu : ∀ j, hf L S.Hm v (u j) = hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i) := by
      intro j; rw [hu, hf_add_r, hf_sum_r]; simp only [hf_smul_r, hcj]
    have huv : ∀ j, hf L S.Hm (u j) v' = hf L S.Hm (w j) v' + ∑ i, hf L S.Hm (gs j) (w i) * hf L S.Hm (G i) v' := by
      intro j; rw [hu, hf_add_l, hf_sum_l]; simp only [hf_smul_l]
    simp only [hvu, huv]
    have e1 : ∑ j, hf L S.Hm (G j) v' * (hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i)) =
        ∑ j, hf L S.Hm v (w j) * hf L S.Hm (G j) v' +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ x, hf L S.Hm v (G x) * (hf L S.Hm (w x) v' + ∑ i, hf L S.Hm (gs x) (w i) * hf L S.Hm (G i) v' +
          ∑ l, hf L S.Hm (G l) v' * hf L S.Hm (w x) (w l)) =
        ∑ x, hf L S.Hm (w x) v' * hf L S.Hm v (G x) +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_add, mul_add, mul_comm (hf L S.Hm v (G x)), add_assoc]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have key : (∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i)) +
        ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      linear_combination hf L S.Hm v (G j) * hf L S.Hm (G i) v' * K j i
    rw [e1, e2]
    linear_combination key

  have hiso : ∀ x y, hf L S.Hm (m x) (m y) = hf L S.Hm x y := by simp only [hm]; exact iso
  have hmg : ∀ a, m (g a) = g a := fun a => by
    rw [hm, hff]; simp only [haG, hgw, zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
  have hmgs : ∀ j, m (gs j) = gs2 j := fun j => by
    rw [hm, hff]
    simp only [hgsG, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hu, hw]; abel
  have hX : ∀ i, G i ∈ S.spanTo g r := fun i => by
    rw [hG]; exact Submodule.subset_span ⟨i.castSucc, by simp, rfl⟩
  have hfix : ∀ J, ∀ v ∈ S.spanTo g J, m v = v := by
    intro J v hv
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨a, -, rfl⟩ := hy; exact hmg a
    | zero => exact map_zero m
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have hspan : ∀ J v, m v ∈ S.spanTo g J ↔ v ∈ S.spanTo g J := fun J v =>
    ⟨fun h => by
      have e : m (m v) = m v := hfix J _ h
      rw [m.injective e] at h; exact h,
     fun h => by rw [hfix J v h]; exact h⟩
  have hmperp : ∀ v ∈ perp L S.Hm (S.spanTo g r), m v = v - ∑ i, hf L S.Hm v (w i) • G i := by
    intro v hv
    rw [hm, hff]
    simp only [hv _ (hX _), zero_smul, Finset.sum_const_zero, add_zero]
  have hperp : ∀ v, m v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := fun v =>
    ⟨fun h y hy => by
      have := h y hy
      rwa [← hfix r y hy, hiso] at this,
     fun h y hy => by
      rw [← hfix r y hy, hiso]; exact h y hy⟩
  have hpspan : ∀ (f : Fin r → S.V) x,
      x ∈ perp L S.Hm (Submodule.span E (Set.range f)) ↔ ∀ l, hf L S.Hm x (f l) = 0 := fun f x =>
    ⟨fun h l => h _ (Submodule.subset_span ⟨l, rfl⟩),
     fun h => GlobalTheory.FramePsi.hf_span_right L S.Hm x _ (by rintro _ ⟨l, rfl⟩; exact h l)⟩
  refine ⟨m, ?_, hmg, hmgs, ?_⟩
  · simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf]
    refine ⟨⟨hiso, fun j => ⟨fun v => hspan _ v, fun v hv => ?_⟩⟩, hperp, fun v hv => ?_⟩
    · rw [hfix _ v hv, sub_self]; exact Submodule.zero_mem _
    · rw [hmperp v hv, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
  · intro A hXA hAp
    have hsum : ∀ x, ∑ i, hf L S.Hm x (w i) • G i ∈ A := fun x =>
      hXA _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
    have hAm : ∀ x, m x ∈ A ↔ x ∈ A := fun x =>
      ⟨fun h => by
        have hp : x ∈ perp L S.Hm (S.spanTo g r) := (hperp x).1 (hAp _ h)
        have e : x = m x + ∑ i, hf L S.Hm x (w i) • G i := by rw [hmperp x hp]; abel
        rw [e]; exact A.add_mem h (hsum x),
       fun h => by rw [hmperp x (hAp x h)]; exact A.sub_mem h (hsum x)⟩
    have hPm : ∀ x, m x ∈ perp L S.Hm (Submodule.span E (Set.range gs2)) ↔
        x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) := fun x => by
      rw [hpspan, hpspan]
      simp only [← hmgs, hiso]
    have hsm : ∀ (Λ : Submodule L.O S.V) x, m x ∈ m • Λ ↔ x ∈ Λ := fun Λ x => by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨fun ⟨y, hy, e⟩ => (m.injective e) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    ext y
    obtain ⟨x, rfl⟩ := m.surjective y
    rw [hsm]
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, hAm, hPm]

end GlobalTheory.FrameDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameUnipotentExchangingDualIsotropicStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameUnipotent_exchanging_dual_isotropic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (t : E) (gs gs2 : Fin r → S.V), (∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0) → (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → (∀ a j, hf L S.Hm (g a) (gs2 j) = if a = j.castSucc then 1 else 0) → (∀ i j, hf L S.Hm (gs i) (gs j) = 0) → (∀ i j, hf L S.Hm (gs2 i) (gs2 j) = 0) → ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧ (∀ j, m (gs j) = gs2 j) ∧ ∀ A : Submodule L.O S.V, (∀ x ∈ S.spanTo g r, x ∈ A) → (∀ x ∈ A, x ∈ perp L S.Hm (S.spanTo g r)) → m • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) = A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs2))).restrictScalars L.O := by
  first | exact @GlobalTheory.FrameDual.exists_unip_change_dual | exact GlobalTheory.FrameDual.exists_unip_change_dual | (intros; apply GlobalTheory.FrameDual.exists_unip_change_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabil
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem inv_apply (h : S.GLV) (v : S.V) : h⁻¹ v = h.symm v := rfl

theorem fix {h : S.GLV} (hh : h ∈ S.H0) {v : S.V} (hv : v ∈ S.ME) : h v = v := by
  have := hh.2.2 v hv
  rw [Submodule.mem_bot, sub_eq_zero] at this
  exact this

theorem spanTo_le (g : Fin (r + 1) → S.V) (j : ℕ) : S.spanTo g j ≤ S.spanTo g (r + 1) :=
  Submodule.span_mono (Set.image_mono fun i _ => i.2)

theorem spanTo_le_ME (j : ℕ) : S.spanTo S.f j ≤ S.ME := (spanTo_le S S.f j).trans le_sup_left

theorem spanTo_le_ME' (j : ℕ) : S.spanTo S.f' j ≤ S.ME := (spanTo_le S S.f' j).trans le_sup_right

theorem f_mem (a : Fin (r + 1)) : S.f a ∈ S.ME :=
  spanTo_le_ME S (r + 1) (Submodule.subset_span ⟨a, a.2, rfl⟩)

theorem f'_mem (a : Fin (r + 1)) : S.f' a ∈ S.ME :=
  spanTo_le_ME' S (r + 1) (Submodule.subset_span ⟨a, a.2, rfl⟩)

theorem mem_iff {h : S.GLV} (hh : h ∈ S.H0) (A : Submodule E S.V) (hA : A ≤ S.ME) (v : S.V) :
    h v ∈ A ↔ v ∈ A := by
  constructor
  · intro H
    have : v ∈ S.ME := (hh.2.1 v).1 (hA H)
    rwa [fix S hh this] at H
  · intro H
    rwa [fix S hh (hA H)]

theorem perp_mem_iff {h : S.GLV} (hh : h ∈ S.H0) (A : Submodule E S.V) (hA : A ≤ S.ME) (v : S.V) :
    h v ∈ perp L S.Hm A ↔ v ∈ perp L S.Hm A := by
  constructor
  · intro H y hy
    rw [← hh.1 v y, fix S hh (hA hy)]
    exact H y hy
  · intro H y hy
    rw [← fix S hh (hA hy), hh.1 v y]
    exact H y hy

theorem conj_unipOn (h : S.GLV) (A B : Submodule E S.V) (hA : ∀ v, h v ∈ A ↔ v ∈ A)
    (hB : ∀ v, h v ∈ B ↔ v ∈ B) (s : S.GLV) (hs : s ∈ unipOn A B) : h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h⁻¹ v ∈ A ↔ v ∈ A := fun v => by
    rw [← hA (h⁻¹ v), inv_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h⁻¹ v)) ∈ A ↔ v ∈ A
    rw [hA, hs.1, hA']
  · change h (s (h⁻¹ v)) - v ∈ B
    have e : h (s (h⁻¹ v)) - v = h (s (h⁻¹ v) - h⁻¹ v) := by
      rw [map_sub, inv_apply, LinearEquiv.apply_symm_apply]
    rw [e, hB]
    exact hs.2 _ ((hA' v).2 hv)

theorem nof_conj (g : Fin (r + 1) → S.V) (hg : ∀ j, S.spanTo g j ≤ S.ME) {h : S.GLV} (hh : h ∈ S.H0)
    (s : S.GLV) (hs : s ∈ S.Nof g) : h * s * h⁻¹ ∈ S.Nof g := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hs ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  have hI : h ∈ isomG L S.Hm := hh.1
  refine ⟨⟨(isomG L S.Hm).mul_mem ((isomG L S.Hm).mul_mem hI h1) ((isomG L S.Hm).inv_mem hI),
    fun j => ?_⟩, ?_⟩
  · exact conj_unipOn S h _ _ (mem_iff S hh _ (hg _)) (mem_iff S hh _ (hg _)) s (h2 j)
  · exact conj_unipOn S h _ _ (perp_mem_iff S hh _ (hg _)) (mem_iff S hh _ (hg _)) s h3

theorem normalises {h : S.GLV} (hh : h ∈ S.H0) :
    (∀ s ∈ S.N, h * s * h⁻¹ ∈ S.N) ∧ (∀ s ∈ S.N', h * s * h⁻¹ ∈ S.N') ∧
      ∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St :=
  ⟨fun s hs => nof_conj S S.f (spanTo_le_ME S) hh s hs,
    fun s hs => nof_conj S S.f' (spanTo_le_ME' S) hh s hs,
    fun s hs => ⟨nof_conj S S.f (spanTo_le_ME S) hh s hs.1, nof_conj S S.f' (spanTo_le_ME' S) hh s hs.2⟩⟩

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

open GlobalTheory.FrameAct in
theorem graph_sub {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) (p : S.V × S.V)
    (hp : p ∈ S.graphOf Λ) : (h p.1, h p.2) ∈ S.graphOf (h • Λ) := by
  obtain ⟨y', hy', y, hy, a', a, b', b, c⟩ := hp
  refine ⟨h y', (mem_smul_iff S h Λ _).2 hy', h y, (mem_smul_iff S h Λ _).2 hy,
    (perp_mem_iff S hh S.X' (spanTo_le_ME' S r) _).2 a', (perp_mem_iff S hh S.X (spanTo_le_ME S r) _).2 a,
    ?_, ?_, ?_⟩
  · rw [← map_sub]; exact (mem_iff S hh S.X' (spanTo_le_ME' S r) _).2 b'
  · rw [← map_sub]; exact (mem_iff S hh S.X (spanTo_le_ME S r) _).2 b
  · rw [← map_sub, inTh_iff]; exact c

theorem graph_move {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.graphOf (h • Λ) = h • S.graphOf Λ := by
  have hh' : h⁻¹ ∈ S.H0 := S.H0.inv_mem hh
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro H
    have := graph_sub S hh' (h • Λ) p H
    rwa [inv_smul_smul] at this
  · intro H
    have := graph_sub S hh Λ _ H
    simpa [LinearEquiv.smul_def] using this

theorem conj_stab (h x : S.GLV) (P : Submodule L.O S.V) :
    h⁻¹ * x * h ∈ MulAction.stabilizer S.GLV P ↔ x ∈ MulAction.stabilizer S.GLV (h • P) := by
  simp only [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]

theorem conj_St {h : S.GLV} (hh : h ∈ S.H0) (x : S.GLV) : h⁻¹ * x * h ∈ S.St ↔ x ∈ S.St := by
  constructor
  · intro H
    have := (normalises S hh).2.2 _ H
    simpa [mul_assoc] using this
  · intro H
    have := (normalises S (S.H0.inv_mem hh)).2.2 _ H
    simpa using this

theorem mu_move {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) : S.mu (h • Λ) = S.mu Λ := by
  have hfixf : ∀ a, h (S.f a) = S.f a := fun a => fix S hh (f_mem S a)
  have hfixf' : ∀ a, h (S.f' a) = S.f' a := fun a => fix S hh (f'_mem S a)
  have sf : h • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := by
    rw [GlobalTheory.FrameAct.smul_span, ← Set.range_comp]
    congr 2
    funext a
    exact hfixf a
  have sf' : h • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') := by
    rw [GlobalTheory.FrameAct.smul_span, ← Set.range_comp]
    congr 2
    funext a
    exact hfixf' a
  have e1 : (S.St ⊓ MulAction.stabilizer S.GLV Λ).map (MulAut.conj h).toMonoidHom =
      S.St ⊓ MulAction.stabilizer S.GLV (h • Λ) := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_inf, Subgroup.mem_inf, conj_St S hh,
      conj_stab]
  have e0 : S.K0.map (MulAut.conj h).toMonoidHom = S.K0 := by
    ext x
    unfold Frames.K0
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp only [Subgroup.mem_inf, conj_St S hh, conj_stab, sf, sf']
  have inj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  unfold Frames.mu invVol
  rw [← e1, ← e0, Subgroup.relIndex_map_map_of_injective _ _ inj,
    Subgroup.relIndex_map_map_of_injective _ _ inj, e0]

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

open GlobalTheory.FrameAct in
theorem mem_perp_span (s : Set S.V) (x : S.V) :
    x ∈ perp L S.Hm (Submodule.span E s) ↔ ∀ y ∈ s, hf L S.Hm x y = 0 :=
  ⟨fun H y hy => H y (Submodule.subset_span hy), fun H => GlobalTheory.FramePsi.hf_span_right L S.Hm x s H⟩

theorem fix_span (g : Fin (r + 1) → S.V) (h : S.GLV) (hfix : ∀ a, h (g a) = g a) (j : ℕ) (v : S.V)
    (hv : v ∈ S.spanTo g j) : h v = v := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, -, rfl⟩ := hx; exact hfix a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem perp_spanTo_iff (g : Fin (r + 1) → S.V) (h : S.GLV) (hI : h ∈ isomG L S.Hm)
    (hfix : ∀ a, h (g a) = g a) (j : ℕ) (v : S.V) :
    h v ∈ perp L S.Hm (S.spanTo g j) ↔ v ∈ perp L S.Hm (S.spanTo g j) := by
  constructor
  · intro H y hy
    rw [← hI v y, fix_span S g h hfix j y hy]
    exact H y hy
  · intro H y hy
    rw [← fix_span S g h hfix j y hy, hI v y]
    exact H y hy

theorem perp_range_iff (gs : Fin r → S.V) (h : S.GLV) (hI : h ∈ isomG L S.Hm) (x : S.V) :
    h x ∈ perp L S.Hm (Submodule.span E (Set.range fun j => h (gs j))) ↔
      x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) := by
  have hI' : ∀ a b, hf L S.Hm (h a) (h b) = hf L S.Hm a b := hI
  rw [mem_perp_span, mem_perp_span, Set.forall_mem_range, Set.forall_mem_range]
  simp only [hI']

theorem fg_smul (a : S.GLV) (N : Submodule L.O S.V) (hN : N.FG) : (a • N).FG := by
  rw [Submodule.pointwise_smul_def]
  exact hN.map _

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)


open GlobalTheory.FrameAct in
theorem inner_transport (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (h : S.GLV) (hI : h ∈ isomG L S.Hm) (hfix : ∀ a, h (g a) = g a)
    (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    S.IsInner g gs (h • A) ∧ ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧
      m • S.stdLat g gs (h • A) = h • S.stdLat g gs A := by
  have hI' : ∀ a b, hf L S.Hm (h a) (h b) = hf L S.Hm a b := hI
  obtain ⟨a1, a2, a3, a4, a5, y, hy, a6⟩ := hA
  have hd2 : ∀ a j, hf L S.Hm (g a) (h (gs j)) = if a = j.castSucc then 1 else 0 := fun a j => by
    rw [← hfix a, hI', hd]
  have hi2 : ∀ i j, hf L S.Hm (h (gs i)) (h (gs j)) = 0 := fun i j => by rw [hI']; exact hi i j
  obtain ⟨m, hm, mfix, mgs, mA⟩ := GlobalTheory.T.exists_frameUnipotent_exchanging_dual_isotropic L r k S g t gs (fun j => h (gs j)) hg hd hd2 hi hi2
  have b1 : ∀ x ∈ S.spanTo g r, x ∈ h • A := fun x hx => by
    rw [← fix_span S g h hfix r x hx]
    exact (mem_smul_iff S h A x).2 (a1 x hx)
  have b2 : ∀ x ∈ h • A, x ∈ perp L S.Hm (S.spanTo g r) := fun x hx => by
    obtain ⟨x0, rfl⟩ := h.surjective x
    exact (perp_spanTo_iff S g h hI hfix r x0).2 (a2 x0 ((mem_smul_iff S h A x0).1 hx))
  have key := mA (h • A) b1 b2
  have eA : (h • A) ⊓ (perp L S.Hm (Submodule.span E (Set.range fun j => h (gs j)))).restrictScalars L.O =
      h • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) := by
    refine eq_smul_of S h _ _ fun x => ?_
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff, perp_range_iff S gs h hI]
  have hfg : (h • A) ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O =
      m⁻¹ • (h • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O)) := by
    rw [← eA, ← key, inv_smul_smul]
  refine ⟨⟨b1, b2, ?_, fun z hz => ?_, ?_, h y, (mem_smul_iff S h A y).2 hy, ?_⟩, m, hm, mfix, ?_⟩
  · rw [hfg]
    exact fg_smul S _ _ (fg_smul S _ _ a3)
  · obtain ⟨z0, rfl⟩ := h.surjective z
    have hz0 := (perp_spanTo_iff S g h hI hfix r z0).1 hz
    rw [mem_smul_iff, ← a4 z0 hz0]
    constructor
    · intro H x hx
      have := H (h x) ((mem_smul_iff S h A x).2 hx)
      simpa only [Frames.h, hI'] using this
    · intro H x hx
      obtain ⟨x0, rfl⟩ := h.surjective x
      have := H x0 ((mem_smul_iff S h A x0).1 hx)
      simpa only [Frames.h, hI'] using this
  · rw [← hfix (Fin.last r)]
    exact (mem_smul_iff S h A _).2 a5
  · show hf L S.Hm (g (Fin.last r)) (h y) = 1
    rw [← hfix (Fin.last r), hI']
    exact a6
  · have s1 : h • Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) =
        Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact hfix _
    have s2 : m • Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) =
        Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact mfix _
    have s3 : h • Submodule.span L.O (Set.range gs) =
        Submodule.span L.O (Set.range fun j => h (gs j)) := by
      rw [smul_span, ← Set.range_comp]
      rfl
    have s4 : m • Submodule.span L.O (Set.range gs) =
        Submodule.span L.O (Set.range fun j => h (gs j)) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact mgs _
    unfold Frames.stdLat
    rw [Submodule.smul_sup', Submodule.smul_sup', Submodule.smul_sup', Submodule.smul_sup', s1, s2, s3, s4,
      key, eA]

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem psiOf_conj (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (h n : S.GLV)
    (H : ∀ b, (h * n * h⁻¹) (g b) = n (g b)) : S.psiOf g gs (h * n * h⁻¹) = S.psiOf g gs n := by
  unfold Frames.psiOf Frames.coef
  simp only [H]

theorem psiOf_fix (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (m : S.GLV) (mfix : ∀ a, m (g a) = g a) : S.psiOf g gs m = 1 := by
  have ne : ∀ j : Fin r, j.succ ≠ j.castSucc := fun j e => by
    have := congrArg Fin.val e
    simp at this
  unfold Frames.psiOf Frames.coef
  simp only [mfix, Frames.h, hd, ne, if_false, Finset.sum_const_zero, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.HL.FixFrames


open GlobalTheory.HL.FixFrames GlobalTheory.FrameAct in
theorem GlobalTheory.HL.FixFrames.unitary_complement_acts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, (∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St) ∧ ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh
  obtain ⟨nN, nN', nSt⟩ := normalises S hh
  refine ⟨nSt, fun d Λ H => ?_⟩
  have hh' : h⁻¹ ∈ S.H0 := S.H0.inv_mem hh
  have hfixf : ∀ a, h (S.f a) = S.f a := fun a => fix S hh (f_mem S a)
  have hfixf' : ∀ a, h (S.f' a) = S.f' a := fun a => fix S hh (f'_mem S a)
  have ifixf : ∀ a, h⁻¹ (S.f a) = S.f a := fun a => fix S hh' (f_mem S a)
  have ifixf' : ∀ a, h⁻¹ (S.f' a) = S.f' a := fun a => fix S hh' (f'_mem S a)
  have W0 := wit_spec S d Λ H
  obtain ⟨iA, iA', hn, hn', e1, e2, cg, gr⟩ := W0
  obtain ⟨jA, m, hm, mfix, em⟩ :=
    inner_transport S S.f S.es _ S.gram S.dual S.iso h hh.1 hfixf d.1 iA
  obtain ⟨jA', m', hm', mfix', em'⟩ :=
    inner_transport S S.f' S.es' _ S.gram' S.dual' S.iso' h hh.1 hfixf' d.2.1 iA'
  have W1 : S.IsTermW (h • d) (h • Λ) (h * (S.wit d Λ).1 * h⁻¹ * m) (h * (S.wit d Λ).2 * h⁻¹ * m') := by
    refine ⟨jA, jA', S.N.mul_mem (nN _ hn) hm, S.N'.mul_mem (nN' _ hn') hm', ?_, ?_, fun b => ?_, ?_⟩
    · show h • Λ = (h * (S.wit d Λ).1 * h⁻¹ * m) • S.stdLat S.f S.es (h • d.1)
      rw [mul_smul, em, mul_smul, inv_smul_smul, mul_smul, ← e1]
    · show h • Λ = (h * (S.wit d Λ).2 * h⁻¹ * m') • S.stdLat S.f' S.es' (h • d.2.1)
      rw [mul_smul, em', mul_smul, inv_smul_smul, mul_smul, ← e2]
    · have e : (h * (S.wit d Λ).2 * h⁻¹ * m') (S.f' b) - (h * (S.wit d Λ).1 * h⁻¹ * m) (S.f b) =
          h ((S.wit d Λ).2 (S.f' b) - (S.wit d Λ).1 (S.f b)) := by
        change h ((S.wit d Λ).2 (h⁻¹ (m' (S.f' b)))) - h ((S.wit d Λ).1 (h⁻¹ (m (S.f b)))) = _
        rw [mfix', mfix, ifixf', ifixf, map_sub]
      rw [e, inTh_iff]
      exact cg b
    · show h • d.2.2 = S.graphOf (h • Λ)
      rw [gr, graph_move S hh Λ]
  have hmemN : ∀ b, (h * (S.wit d Λ).1 * h⁻¹) (S.f b) = (S.wit d Λ).1 (S.f b) := fun b => by
    change h ((S.wit d Λ).1 (h⁻¹ (S.f b))) = _
    rw [ifixf]
    exact fix S hh (spanTo_le_ME S (r + 1)
      (spanTo_map S S.f _ S.gram _ hn (r + 1) _ (Submodule.subset_span ⟨b, b.2, rfl⟩)))
  have hmemN' : ∀ b, (h * (S.wit d Λ).2 * h⁻¹) (S.f' b) = (S.wit d Λ).2 (S.f' b) := fun b => by
    change h ((S.wit d Λ).2 (h⁻¹ (S.f' b))) = _
    rw [ifixf']
    exact fix S hh (spanTo_le_ME' S (r + 1)
      (spanTo_map S S.f' _ S.gram' _ hn' (r + 1) _ (Submodule.subset_span ⟨b, b.2, rfl⟩)))
  obtain ⟨o1, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S _ _ _ _ W1
  obtain ⟨o0, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S _ _ _ _ (wit_spec S d Λ H)
  obtain ⟨p1, p2, -⟩ := GlobalTheory.FramePsi.psi_unitary_character L r k S
  have q1 : S.psi (h * (S.wit d Λ).1 * h⁻¹ * m) = S.psi (S.wit d Λ).1 := by
    rw [p1 _ (nN _ hn) _ hm]
    unfold Frames.psi
    rw [psiOf_conj S _ _ _ _ hmemN, psiOf_fix S _ _ S.dual m mfix, mul_one]
  have q2 : S.psi' (h * (S.wit d Λ).2 * h⁻¹ * m') = S.psi' (S.wit d Λ).2 := by
    rw [p2 _ (nN' _ hn') _ hm']
    unfold Frames.psi'
    rw [psiOf_conj S _ _ _ _ hmemN', psiOf_fix S _ _ S.dual' m' mfix', mul_one]
  refine ⟨⟨(_, _), W1⟩, ?_, mu_move S hh Λ⟩
  rw [o1, o0, q1, q2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabilStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, (∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St) ∧ ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ := by
  first | exact @GlobalTheory.HL.FixFrames.unitary_complement_acts | exact GlobalTheory.HL.FixFrames.unitary_complement_acts | (intros; apply GlobalTheory.HL.FixFrames.unitary_complement_acts <;> assumption)
end

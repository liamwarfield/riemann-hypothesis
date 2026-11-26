module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAInj

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATop
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MkWEqOfSubMem
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACorr
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrLemmas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

private theorem h_finset_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simpa using H.h_smul_left 0 0 y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

private theorem h_add_right_rank_point_counts (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

private theorem h_smul_right_eq_cj_mul (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

private theorem h_zero_right_rank_point_counts (x : V) : H.h x 0 = 0 := by
  simpa using h_add_right_rank_point_counts H x 0 0

theorem mem_perpX_of {f : Fin (r + 1) → V} {v : V} (h : ∀ j : Fin r, H.h v (f j.castSucc) = 0) :
    v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h v x = 0
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact h j
  | zero => exact h_zero_right_rank_point_counts H v
  | add y z _ _ hy hz => rw [h_add_right_rank_point_counts, hy, hz, add_zero]
  | smul a y _ hy => rw [h_smul_right_eq_cj_mul, hy, mul_zero]

theorem z_mem_perpX {f : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) :
    f (Fin.last r) ∈ H.perp (H.X f) :=
  mem_perpX_of H fun j => hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne)

theorem om'_mem_perpX (f f' : Fin (r + 1) → V) : H.om' f f' ∈ H.perp (H.X f) := by
  refine mem_perpX_of H fun j => ?_
  unfold HermSp.om'
  rw [h_sum_smul_left]
  have e := congrFun (congrFun (mul_adjugate (H.Zhat f f')) j.castSucc) (Fin.last r)
  rw [Matrix.smul_apply, one_apply_ne (Fin.castSucc_lt_last j).ne, smul_zero, Matrix.mul_apply] at e
  rw [← e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [HermSp.Zhat, Matrix.of_apply]
  ring

theorem om'_mem_U (f f' : Fin (r + 1) → V) :
    H.om' f f' ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
  unfold HermSp.om'
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

theorem decomp_U_perpX {f f' : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hZ : IsUnit (H.Zhat f f').det) {u : V} (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (hp : u ∈ H.perp (H.X f)) :
    ∃ x ∈ H.X f, ∃ β γ : E, u = x + β • f (Fin.last r) + γ • H.om' f f' := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hu
  obtain ⟨a, p, rfl⟩ : ∃ a p, c = Sum.elim a p := ⟨c ∘ Sum.inl, c ∘ Sum.inr, by ext (i | i) <;> rfl⟩
  have hp' : ∀ x ∈ H.X f, H.h (∑ i, Sum.elim a p i • Sum.elim f f' i) x = 0 := hp
  rw [Fintype.sum_sum_type] at hp' ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at hp' ⊢
  obtain ⟨d, hd⟩ := hZ
  have hperp : ∀ j : Fin r, (H.Zhat f f' *ᵥ p) j.castSucc = 0 := by
    intro j
    have h0 := hp' (f j.castSucc) (Submodule.subset_span ⟨j, rfl⟩)
    rw [H.h_add_left, h_finset_sum_smul_left, h_finset_sum_smul_left,
      Finset.sum_eq_zero (fun i _ => by rw [hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne), mul_zero]),
      zero_add] at h0
    refine Eq.trans ?_ h0
    simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZp : H.Zhat f f' *ᵥ p = Pi.single (Fin.last r) ((H.Zhat f f' *ᵥ p) (Fin.last r)) := by
    funext k
    by_cases hk : k = Fin.last r
    · subst hk
      simp
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      rw [hperp j, Pi.single_eq_of_ne hk]
  have hp2 : ∀ b, p b = (↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r)) * (H.Zhat f f').adjugate b (Fin.last r) := by
    intro b
    have h1 : (H.Zhat f f').adjugate *ᵥ (H.Zhat f f' *ᵥ p) = (H.Zhat f f').det • p := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 b
    rw [hZp] at h2
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul] at h2
    rw [← hd] at h2
    calc p b = ↑d⁻¹ * (↑d * p b) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by
        rw [← h2]
        simp only [Matrix.mulVec, dotProduct]
        ring
  refine ⟨∑ j : Fin r, a j.castSucc • f j.castSucc, ?_, a (Fin.last r),
    ↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r), ?_⟩
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Fin.sum_univ_castSucc (fun i => a i • f i)]
    congr 1
    unfold HermSp.om'
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, ← hp2 b]

theorem Gdet_rel (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (h : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Gdet f₂ f₂' T T' * H.normE (H.Dl f₁ f₁' (r + 1)) =
      H.normE (H.Dl f₂ f₂' (r + 1)) * H.Gdet f₁ f₁' T T' := by
  unfold HermSp.Gdet HermSp.normE
  have h' : M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1)) =
      M.L.cj (H.Dl f₂ f₂' r) * M.L.cj (H.Dl f₁ f₁' (r + 1)) := by
    rw [← map_mul, ← map_mul, h]
  linear_combination (algebraMap F E (T * T')) * (M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * h +
    (algebraMap F E (T * T')) * (H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) * h'

end CorrLemmas

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrProof

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem Dl_succ {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dite_eq_left le_rfl]
  congr 1

theorem mkW_eq_of_sub_mem {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) - y ∈ H.X f) : H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

theorem corrIso_holds (M : Model F E) (r n : ℕ) : CorrIso M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, hz, hz'⟩ := hyp
  have hT1 := hg₁.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT1.2.1.2.1, hT1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT1.2.2.1.2.1, hT1.2.2.1.2.2.1⟩
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  obtain ⟨hIs, -, hW0c, hom', -, hκ⟩ := hI
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hκ
    have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hU₁ := isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ hG₁
  have hU₂ := isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂ hG₂
  have hXU : ∀ g g' : Fin (r + 1) → V, H.X g ≤ Submodule.span E (Set.range (Sum.elim g g')) :=
    fun g g' => Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inl j.castSucc, rfl⟩)
  have huniq : ∀ (a b : V) (ha : a ∈ H.W0 f₂ f₂') (hb : b ∈ H.W0 f₂ f₂'),
      H.mkW f₂ ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H ha⟩ = H.mkW f₂ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩ → a = b := by
    intro a b ha hb hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₂.disjoint) _ (hXU f₂ f₂' h1) (Submodule.sub_mem _ ha hb))
  have hex : ∀ w : ↥(H.W0 t₁.f t₁.f'), ∃ w₂ : ↥(H.W0 f₂ f₂'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ ∧
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H w₂.2⟩ := by
    intro w
    obtain ⟨w₂, hw₂, s1, s2⟩ := hW0c w w.2
    refine ⟨⟨w₂, hw₂⟩, ?_, ?_⟩
    · have := s1 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ rfl rfl
      simpa using this
    · have := s2 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ rfl rfl
      simpa using this
  choose ψf hψf using hex
  have hψadd : ∀ a b, ψf (a + b) = ψf a + ψf b := by
    intro a b
    apply Subtype.ext
    apply huniq _ _ (ψf (a + b)).2 (ψf a + ψf b).2
    rw [← (hψf (a + b)).1]
    have e : (⟨((a + b : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (a + b).2⟩ : ↥(H.perp (H.X t₁.f))) =
        ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ + ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ := Subtype.ext rfl
    have e2 : (⟨((ψf a + ψf b : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (ψf a + ψf b).2⟩ : ↥(H.perp (H.X f₂))) =
        ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ + ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ := Subtype.ext rfl
    rw [e, e2, map_add (f := _), map_add (f := _), map_add (f := _), (hψf a).1, (hψf b).1]
  have hψsmul : ∀ (c : E) a, ψf (c • a) = c • ψf a := by
    intro c a
    apply Subtype.ext
    apply huniq _ _ (ψf (c • a)).2 (c • ψf a).2
    rw [← (hψf (c • a)).1]
    have e : (⟨((c • a : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • a).2⟩ : ↥(H.perp (H.X t₁.f))) =
        c • ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ := Subtype.ext rfl
    have e2 : (⟨((c • ψf a : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • ψf a).2⟩ : ↥(H.perp (H.X f₂))) =
        c • ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ := Subtype.ext rfl
    rw [e, e2, map_smul, map_smul, map_smul, (hψf a).1]
  let ψL : ↥(H.W0 t₁.f t₁.f') →ₗ[E] ↥(H.W0 f₂ f₂') :=
    { toFun := ψf, map_add' := hψadd, map_smul' := hψsmul }
  have hinj : Function.Injective ψL := by
    intro a b hab
    have hab' : ψf a = ψf b := hab
    have e : H.mkW t₁.f ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ = H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ :=
      φ.injective (by rw [(hψf a).1, (hψf b).1, hab'])
    have h1 := sub_mem_X_of_mkW_eq H e
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₁.disjoint) _ (hXU t₁.f t₁.f' h1)
      (Submodule.sub_mem _ a.2 b.2)))
  have hsurj : Function.Surjective ψL := by
    intro w₂
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩))
    have hy' : φ (H.mkW t₁.f y) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ := by
      have : H.mkW t₁.f y = φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩) := hy
      rw [this, LinearEquiv.apply_symm_apply]
    have hyU : (y : V) ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')) ⊔ H.W0 t₁.f t₁.f' := by
      rw [hU₁.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hyU
    have hup : u ∈ H.perp (H.X t₁.f) := by
      have : u = (y : V) - w := by rw [← huw]; abel
      rw [this]
      exact Submodule.sub_mem _ y.2 (mem_perp_isotropicSpan_of_mem_framePerp H hw)
    have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
    obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
    refine ⟨⟨w, hw⟩, ?_⟩
    set D₂ := H.Dl f₂ f₂' (r + 1)
    set D₁ := H.Dl t₁.f t₁.f' (r + 1)
    let zP₁ : ↥(H.perp (H.X t₁.f)) := ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩
    let oP₁ : ↥(H.perp (H.X t₁.f)) := ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩
    let zP₂ : ↥(H.perp (H.X f₂)) := ⟨f₂ (Fin.last r), z_mem_perpX H hF₂⟩
    let oP₂ : ↥(H.perp (H.X f₂)) := ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩
    let wP : ↥(H.perp (H.X t₁.f)) := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩
    let vP : ↥(H.perp (H.X f₂)) := ⟨ψf ⟨w, hw⟩, mem_perp_isotropicSpan_of_mem_framePerp H (ψf ⟨w, hw⟩).2⟩
    have hq₁ : H.mkW t₁.f y = H.mkW t₁.f (β • zP₁ + γ • oP₁ + wP) := by
      apply mkW_eq_of_sub_mem
      show (y : V) - (β • t₁.f (Fin.last r) + γ • H.om' t₁.f t₁.f' + w) ∈ H.X t₁.f
      rw [← huw, hxe]
      convert hx using 1
      abel
    have hz1 : φ (H.mkW t₁.f zP₁) = H.mkW f₂ zP₂ := by
      have := hz zP₁ zP₂ rfl rfl
      simpa using this
    have ho0 : D₂ • φ (H.mkW t₁.f oP₁) = D₁ • H.mkW f₂ oP₂ := by
      have := hom' oP₁ oP₂ rfl rfl
      simpa using this
    have ho1 : φ (H.mkW t₁.f oP₁) = (Ring.inverse D₂ * D₁) • H.mkW f₂ oP₂ := by
      rw [mul_smul, ← ho0, smul_smul, Ring.inverse_mul_cancel _ hD₂, one_smul]
    have hw1 : φ (H.mkW t₁.f wP) = H.mkW f₂ vP := (hψf ⟨w, hw⟩).1
    have hq₂ : H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ =
        H.mkW f₂ (β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP) := by
      rw [← hy', hq₁]
      simp only [map_add (f := _), map_smul, hz1, ho1, hw1, smul_smul]
    have hd := sub_mem_X_of_mkW_eq H hq₂
    have hU2mem : (w₂ : V) - (ψf ⟨w, hw⟩ : V) ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')) := by
      have e : (w₂ : V) - (ψf ⟨w, hw⟩ : V) =
          ((w₂ : V) - ((β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP : ↥(H.perp (H.X f₂))) : V)) +
            (β • f₂ (Fin.last r) + (γ * (Ring.inverse D₂ * D₁)) • H.om' f₂ f₂') := by
        simp only [Submodule.coe_add, Submodule.coe_smul, zP₂, oP₂, vP]
        abel
      rw [e]
      exact Submodule.add_mem _ (hXU f₂ f₂' hd) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
        (Submodule.smul_mem _ _ (om'_mem_U H f₂ f₂')))
    have h0 := (Submodule.disjoint_def.1 hU₂.disjoint) _ hU2mem (Submodule.sub_mem _ w₂.2 (ψf ⟨w, hw⟩).2)
    exact Subtype.ext (sub_eq_zero.1 h0).symm
  refine ⟨LinearEquiv.ofBijective ψL ⟨hinj, hsurj⟩, fun a b => ?_, fun n₁ n₂ => ?_⟩
  · show H.h ((ψf a : ↥(H.W0 f₂ f₂')) : V) ((ψf b : ↥(H.W0 f₂ f₂')) : V) = H.h a b
    exact hIs ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩
      ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ (hψf a).1 (hψf b).1
  · constructor
    · rintro ⟨h₁, h₂, c1, -⟩
      refine ⟨h₁, ?_⟩
      show ((ψf ⟨n₁, h₁⟩ : ↥(H.W0 f₂ f₂')) : V) = n₂
      exact huniq _ _ (ψf ⟨n₁, h₁⟩).2 h₂ ((hψf ⟨n₁, h₁⟩).1.symm.trans c1)
    · rintro ⟨h₁, rfl⟩
      exact ⟨h₁, (ψf ⟨n₁, h₁⟩).2, (hψf ⟨n₁, h₁⟩).1, (hψf ⟨n₁, h₁⟩).2⟩

end CorrProof

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem glue_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : Glue M r n :=
  glue_of M r n (glueFwd_of M r n hM (corrIso_holds M r n) hE)
    (glueBack_of M r n hM (corrIso_holds M r n) hE hV hP hG hFG hS) (glueInj_of M r n hM (corrIso_holds M r n))

theorem latSide_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) (hR : ClaimR M r n) :
    LatSide M r n :=
  latSide_of M r n (glue_at M r n hM hE hV hP hG hFG hS) hR

end Top

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Tools

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem hermSp_h_sum_smul_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (c : ι → E) (x : ι → V) (y : V) : H.h (∑ i, c i • x i) y = ∑ i, c i * H.h (x i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  have h1 := map_sum φ (fun i => c i • x i) Finset.univ
  simp only [φ, AddMonoidHom.mk'_apply, H.h_smul_left] at h1
  exact h1

private theorem hermSp_h_sum_smul_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (y : V) (c : ι → E) (x : ι → V) :
    H.h y (∑ i, c i • x i) = ∑ i, M.L.cj (c i) * H.h y (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm (∑ i, c i • x i) y, hermSp_h_sum_smul_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

theorem gram_recomb {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type}
    [Fintype ι] (v : ι → V) (A : Matrix ι ι E) :
    H.gram (fun j => ∑ i, A i j • v i) = (A.map M.L.cj)ᵀ * H.gram v * A := by
  ext a b
  simp only [HermSp.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hermSp_h_sum_smul_left]
  simp only [hermSp_h_sum_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem thSpan_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThSpan M r := by
  intro V _ _ H t hg
  apply le_antisymm
  · exact (Submodule.span_le (R := E)).2 fun v hv => hv.2
  · intro w hw
    have hwΛ : w ∈ Submodule.span E (t.abelian₂ : Set V) := by
      rw [hg.1.1.2.1]
      exact Submodule.mem_top
    obtain ⟨c, hc0, hc⟩ := PI.LocHerm.Glue.existsIntegralMultiple M hM V t.abelian₂ w hwΛ
    have hcW : algebraMap F E (c : F) • w ∈ ThL H t := ⟨hc, Submodule.smul_mem _ _ hw⟩
    have hunit : IsUnit (algebraMap F E (c : F)) := (Units.mk0 (c : F) hc0).isUnit.map _
    have e : w = (hunit.unit⁻¹ : Eˣ) • (algebraMap F E (c : F) • w) := by
      rw [Units.smul_def, smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [e, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcW)

theorem gramMM_holds (M : Model F E) (r n : ℕ) : GramMM M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  obtain ⟨s, hs, hdet⟩ := gram_det H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂
  have hgu : IsUnit (H.gram (Sum.elim f₂ f₂')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim f₂ f₂')).det = H.Gdet f₂ f₂' t₁.T t₁.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG₂.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ f₂' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) hq0)⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
        Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) = fun j => ∑ i, A i j • Sum.elim f₂ f₂' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, smul_sub, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁, det_smul]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

end Tools

end Formalism.L2.SG.LsDatumA

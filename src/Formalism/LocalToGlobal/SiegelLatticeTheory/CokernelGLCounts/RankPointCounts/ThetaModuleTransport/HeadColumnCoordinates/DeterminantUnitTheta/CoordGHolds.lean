module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GraphTransport4
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Transport

theorem graph_transport4 {D₁ D₂ Dc₁ Dc₂ W₁ W₂ W₁' W₂' P P' : Type} (Ψ₁ : D₁ ≃ Dc₁) (Ψ₂ : D₂ ≃ Dc₂)
    (θ : D₁ ≃ D₂) (φ : W₁ → W₂) (φ' : W₁' → W₂') (Pc₁ : W₁ → P) (Pc₂ : W₂ → P) (Pc₁' : W₁' → P')
    (Pc₂' : W₂' → P') (Γ₁ : Set (D₁ × D₁ × W₁ × W₁')) (Γ₂ : Set (D₂ × D₂ × W₂ × W₂'))
    (Γc₁ : Set (Dc₁ × Dc₁ × P × P')) (Γc₂ : Set (Dc₂ × Dc₂ × P × P'))
    (h1 : (fun p => (Ψ₁ p.1, Ψ₁ p.2.1, Pc₁ p.2.2.1, Pc₁' p.2.2.2)) '' Γ₁ = Γc₁)
    (h2 : (fun p => (Ψ₂ p.1, Ψ₂ p.2.1, Pc₂ p.2.2.1, Pc₂' p.2.2.2)) '' Γ₂ = Γc₂)
    (hP : ∀ w, Pc₂ (φ w) = Pc₁ w) (hP' : ∀ w, Pc₂' (φ' w) = Pc₁' w)
    (hinj : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, Pc₂ q.2.2.1 = Pc₁ p.2.2.1 → Pc₂' q.2.2.2 = Pc₁' p.2.2.2 →
      q.2.2.1 = φ p.2.2.1 ∧ q.2.2.2 = φ' p.2.2.2) :
    ((fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' Γ₁ = Γ₂) ↔
      ((fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), Ψ₂ (θ (Ψ₁.symm p.2.1)), p.2.2.1, p.2.2.2)) '' Γc₁ = Γc₂) := by
  subst h1 h2
  constructor
  · intro h
    rw [← h, Set.image_image, Set.image_image]
    congr 1
    funext p
    simp [hP, hP']
  · intro h
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hc : (Ψ₂ (θ p.1), Ψ₂ (θ p.2.1), Pc₁ p.2.2.1, Pc₁' p.2.2.2) ∈
          (fun p => (Ψ₂ p.1, Ψ₂ p.2.1, Pc₂ p.2.2.1, Pc₂' p.2.2.2)) '' Γ₂ := by
        rw [← h]
        exact ⟨_, ⟨p, hp, rfl⟩, by simp⟩
      obtain ⟨q, hq, hqe⟩ := hc
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨e1, e2, e3, e4⟩ := hqe
      obtain ⟨f1, f2⟩ := hinj p hp q hq e3 e4
      have hpq : ((θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2) : D₂ × D₂ × W₂ × W₂') = q :=
        Prod.ext (Ψ₂.injective e1).symm (Prod.ext (Ψ₂.injective e2).symm (Prod.ext f1.symm f2.symm))
      show ((θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2) : D₂ × D₂ × W₂ × W₂') ∈ Γ₂
      rw [hpq]
      exact hq
    · intro hq
      have hc : (Ψ₂ q.1, Ψ₂ q.2.1, Pc₂ q.2.2.1, Pc₂' q.2.2.2) ∈
          (fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), Ψ₂ (θ (Ψ₁.symm p.2.1)), p.2.2.1, p.2.2.2)) ''
            ((fun p => (Ψ₁ p.1, Ψ₁ p.2.1, Pc₁ p.2.2.1, Pc₁' p.2.2.2)) '' Γ₁) := by
        rw [h]
        exact ⟨q, hq, rfl⟩
      obtain ⟨_, ⟨p, hp, rfl⟩, hpe⟩ := hc
      simp only [Equiv.symm_apply_apply, Prod.mk.injEq] at hpe
      obtain ⟨e1, e2, e3, e4⟩ := hpe
      obtain ⟨f1, f2⟩ := hinj p hp q hq e3.symm e4.symm
      exact ⟨p, hp, Prod.ext (Ψ₂.injective e1) (Prod.ext (Ψ₂.injective e2) (Prod.ext f1.symm f2.symm))⟩

end Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def PcG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) : H.Wb t.f →ₗ[E] E × E :=
  coordW H t.f (t.f (Fin.last r)) (omP H t.f t.f') (z_mem H t.f t.T hg.2.1)
    (omP_mem H t.f t.f' hg.2.2.2.1)

def PcG' {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) : H.Wb t.f' →ₗ[E] E × E :=
  coordW H t.f' (omP H t.f' t.f) (t.f' (Fin.last r))
    (omP_mem H t.f' t.f (unit_swap H t.f t.f' hg.2.2.2.1)) (z_mem H t.f' t.T' hg.2.2.1)

theorem pcG_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (hu : (u : V) ∈ H.perp (H.X t.f)) :
    PcG H hg (H.mkW t.f ⟨u, hu⟩) = ((sharpEquiv H t (unit_gramHG H hg) u (Sum.inl (Fin.last r)) : E),
      lamStarC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (fun b =>
        (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl b) : E) +
          algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr b) : E))) := by
  simp only [PcG, coordW_mk]
  refine Prod.ext ?_ ?_
  · show H.h u (t.f (Fin.last r)) = _
    rw [sharpG_inl H hg]
  · show H.h u (omP H t.f t.f') = _
    rw [h_omP, lamStarC]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sharpG_f' H hg]
    rfl

theorem pcG'_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (hu : (u : V) ∈ H.perp (H.X t.f')) :
    PcG' H hg (H.mkW t.f' ⟨u, hu⟩) = (lamC (H.Zhat t.f t.f') (fun a =>
        (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl a) : E)),
      (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl (Fin.last r)) : E) +
        algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr (Fin.last r)) : E)) := by
  simp only [PcG', coordW_mk]
  refine Prod.ext ?_ ?_
  · show H.h u (omP H t.f' t.f) = _
    rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sharpG_inl H hg]
  · show H.h u (t.f' (Fin.last r)) = _
    rw [sharpG_f' H hg]

theorem gamR_image {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    (fun p => (PsiG H hg p.1, PsiG H hg p.2.1, PcG H hg p.2.2.1, PcG' H hg p.2.2.2)) ''
        GamR H t (algebraMap F E (g.q : F)) =
      GamRC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹))
        (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  set s := sharpEquiv H t (unit_gramHG H hg) with hsdef
  ext ⟨d, e, c, c'⟩
  constructor
  · rintro ⟨_, ⟨u, u', u'', hu, hu', huu, rfl⟩, he⟩
    refine ⟨s u, s u', s u'', fun a => ?_, fun a => ?_, fun i => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharpG_inl H hg]
      exact (mem_perpX_iff H t.f u).1 hu a
    · rw [← sharpG_f' H hg]
      exact (mem_perpX_iff H t.f' u').1 hu' a
    · rw [sharpEquiv_apply, sharpEquiv_apply, sharpEquiv_apply, ← h_sub_left, huu, H.h_smul_left]
    · rw [← he]
      simp only [PsiG_mk, pcG_mk, pcG'_mk, ← hsdef]
  · rintro ⟨Y, Y', Y'', hY, hY', hYY, he⟩
    set u := s.symm Y with hu
    set u' := s.symm Y' with hu'
    set u'' := s.symm Y'' with hu''
    have sY : s u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have sY' : s u' = Y' := by rw [hu', LinearEquiv.apply_symm_apply]
    have sY'' : s u'' = Y'' := by rw [hu'', LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f) := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharpG_inl H hg, ← hsdef, sY, hY a]
      rfl
    have hX' : (u' : V) ∈ H.perp (H.X t.f') := by
      rw [mem_perpX_iff]
      intro a
      rw [sharpG_f' H hg, ← hsdef, sY']
      exact hY' a
    have hqO : algebraMap F E (g.q : F) ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L g.q
    have huu : (u : V) - u' = algebraMap F E (g.q : F) • (u'' : V) := by
      have h0 : u - u' - (⟨_, hqO⟩ : M.L.O) • u'' = 0 := by
        apply s.injective
        rw [map_zero, map_sub, map_sub, map_smul, sY, sY', sY'']
        funext i
        apply Subtype.ext
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        push_cast
        rw [hYY i]
        ring
      have h1 := congrArg Subtype.val h0
      simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_zero, Subring.smul_def] at h1
      exact sub_eq_zero.1 h1
    refine ⟨(ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hX⟩, H.mkW t.f' ⟨u', hX'⟩),
      ⟨u, u', u'', hX, hX', huu, rfl⟩, ?_⟩
    rw [he]
    simp only [PsiG_mk, pcG_mk, pcG'_mk, ← hsdef, sY, sY', sY'']

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

private theorem mem_span_sum_elim_swap (f f' : Fin (r + 1) → V) (u : V)
    (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    u ∈ Submodule.span E (Set.range (Sum.elim f' f)) := by
  rwa [Set.Sum.elim_range, Set.union_comm, ← Set.Sum.elim_range]

theorem gamR_sep {g : SplitG M.L} {t₁ t₂ : Term V M r} (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g t₂)
    (hD0₁ : H.Dl t₁.f t₁.f' r = 0) (hD0₂ : H.Dl t₂.f t₂.f' r = 0) (hT : t₂.T = t₁.T) (hT' : t₂.T' = t₁.T') (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW t₂.f ⟨_, omP_mem H t₂.f t₂.f' hg₂.2.2.2.1⟩)
    (hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩)
    (ho' : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW t₂.f' ⟨_, omP_mem H t₂.f' t₂.f (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ GamR H t₁ (algebraMap F E (g.q : F)), ∀ p₂ ∈ GamR H t₂ (algebraMap F E (g.q : F)),
      PcG H hg₂ p₂.2.2.1 = PcG H hg₁ p.2.2.1 → PcG' H hg₂ p₂.2.2.2 = PcG' H hg₁ p.2.2.2 →
      p₂.2.2.1 = φ p.2.2.1 ∧ p₂.2.2.2 = φ' p.2.2.2 := by
  intro p hp p₂ hp₂ e1 e2
  obtain ⟨u, u', u'', hu, hu', -, rfl⟩ := hp
  obtain ⟨v, v', v'', hv, hv', -, rfl⟩ := hp₂
  simp only [PcG, PcG', coordW_mk, Prod.mk.injEq] at e1 e2
  obtain ⟨a1, a2⟩ := e1
  obtain ⟨b1, b2⟩ := e2
  have D1 := mkW_decomp H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hD0₁ ⟨u, hu⟩
    (mem_span_of_sharpG H hg₁ u)
  have D2 := mkW_decomp H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hD0₂ ⟨v, hv⟩
    (mem_span_of_sharpG H hg₂ v)
  have D1' := mkW_decomp H t₁.f' t₁.f t₁.T' t₁.T hg₁.2.2.1 hg₁.2.1
    (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1) (by rw [dl_swap_r, hD0₁, map_zero]) ⟨u', hu'⟩
    (mem_span_sum_elim_swap t₁.f t₁.f' _ (mem_span_of_sharpG H hg₁ u'))
  have D2' := mkW_decomp H t₂.f' t₂.f t₂.T' t₂.T hg₂.2.2.1 hg₂.2.1
    (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1) (by rw [dl_swap_r, hD0₂, map_zero]) ⟨v', hv'⟩
    (mem_span_sum_elim_swap t₂.f t₂.f' _ (mem_span_of_sharpG H hg₂ v'))
  dsimp only at D1 D2 D1' D2'
  have eT : algebraMap F E t₂.T = algebraMap F E t₁.T := by rw [hT]
  have eT' : algebraMap F E t₂.T' = algebraMap F E t₁.T' := by rw [hT']
  constructor
  · show H.mkW t₂.f ⟨v, hv⟩ = φ (H.mkW t₁.f ⟨u, hu⟩)
    rw [D1, D2, map_add (f := _), map_smul, map_smul, hz, ho, a1, a2, eT]
  · show H.mkW t₂.f' ⟨v', hv'⟩ = φ' (H.mkW t₁.f' ⟨u', hu'⟩)
    rw [D1', D2', map_add (f := _), map_smul, map_smul, hz', ho', b1, b2, eT']

theorem isomD_iffG {g : SplitG M.L} {t₁ t₂ : Term V M r} (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g t₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :
    IsomD H t₁ t₂ θ ↔ ∀ Y W Y₂ W₂ : Ix r → M.L.O,
      PsiG H hg₂ (θ ((PsiG H hg₁).symm (Submodule.Quotient.mk Y))) = Submodule.Quotient.mk Y₂ →
      PsiG H hg₂ (θ ((PsiG H hg₁).symm (Submodule.Quotient.mk W))) = Submodule.Quotient.mk W₂ →
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₂.f t₂.f')
          (algebraMap F E t₂.T) (algebraMap F E t₂.T') Y₂ W₂ -
        formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₁.f t₁.f')
          (algebraMap F E t₁.T) (algebraMap F E t₁.T') Y W ∈ M.L.O := by
  constructor
  · intro hI Y W Y₂ W₂ h1 h2
    rw [PsiG_symm_mk] at h1 h2
    have e1 : θ (ddMk H t₁ ((sharpEquiv H t₁ (unit_gramHG H hg₁)).symm Y)) =
        ddMk H t₂ ((sharpEquiv H t₂ (unit_gramHG H hg₂)).symm Y₂) := by
      rw [← PsiG_symm_mk H hg₂, ← h1, LinearEquiv.symm_apply_apply]
    have e2 : θ (ddMk H t₁ ((sharpEquiv H t₁ (unit_gramHG H hg₁)).symm W)) =
        ddMk H t₂ ((sharpEquiv H t₂ (unit_gramHG H hg₂)).symm W₂) := by
      rw [← PsiG_symm_mk H hg₂, ← h2, LinearEquiv.symm_apply_apply]
    have k := hI _ _ _ _ e1 e2
    rw [h_eq_formG H hg₂, h_eq_formG H hg₁] at k
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at k
    exact k
  · intro hI x y x₂ y₂ h1 h2
    have k1 : PsiG H hg₂ (θ ((PsiG H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHG H hg₁) x)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHG H hg₂) x₂) := by
      rw [PsiG_symm_mk, LinearEquiv.symm_apply_apply, h1, PsiG_mk]
    have k2 : PsiG H hg₂ (θ ((PsiG H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHG H hg₁) y)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHG H hg₂) y₂) := by
      rw [PsiG_symm_mk, LinearEquiv.symm_apply_apply, h2, PsiG_mk]
    have k := hI _ _ _ _ k1 k2
    rw [h_eq_formG H hg₂ x₂ y₂, h_eq_formG H hg₁ x y]
    exact k

end Parts

theorem coordG_holds : CoordG := by
  unfold CoordG
  intro F _ _ _ E _ _ _ _ M g hsplit r n V _ _ H _ t₁ f₂ f₂' φ φ' hyp hD0 hDu hZZ
  obtain ⟨hGen, hF₂, hF₂', hId, hS, hS'⟩ := hyp
  have hTerm := hGen.1
  have hFr := hTerm.2.1
  have hFr' := hTerm.2.2.1
  have hF₁ : MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hFr.2.1, hFr.2.2.1⟩
  have hF₁' : MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hFr'.2.1, hFr'.2.2.1⟩
  have hDu₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hTerm.2.2.2.1
  have hg₁ : GoodG H g t₁ := ⟨hsplit, hF₁, hF₁', hDu₁, unit_gramH_of H hsplit hF₁ hF₁' hDu₁ hD0⟩
  have hD0₂ : H.Dl f₂ f₂' r = 0 := by
    have e := hId.2.2.2.2.2
    rw [hD0, zero_mul] at e
    exact (hDu₁.mul_left_eq_zero).mp e.symm
  set t₂ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have hg₂ : GoodG H g t₂ :=
    ⟨hsplit, hF₂, hF₂', hDu, unit_gramH_of H hsplit (t := t₂) hF₂ hF₂' hDu hD0₂⟩
  have hMM : MMInt H t₂ := mmInt_G H hg₂ hFr.2.2.2.1 (hTerm.2.2.2.2.2 g hsplit).2.1 hZZ
  have hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) =
      H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩ := by
    have e := hS ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩ ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩ rfl rfl
    rwa [one_smul, one_smul] at e
  have hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩ := by
    have e := hS' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩ ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩ rfl rfl
    rwa [one_smul, one_smul] at e
  have ho := sends_omP H φ hDu₁ hDu hId.2.2.2.1
  have ho' := sends_omP' H φ' hDu₁ hDu hId.2.2.2.2.1
  have hP : ∀ w, PcG H hg₂ (φ w) = PcG H hg₁ w :=
    fun w => coordW_comp H φ hId.1 _ _ _ _ _ _ _ _ hz ho w
  have hP' : ∀ w, PcG' H hg₂ (φ' w) = PcG' H hg₁ w :=
    fun w => coordW_comp H φ' hId.2.1 _ _ _ _ _ _ _ _ ho' hz' w
  have hinj := gamR_sep H hg₁ hg₂ hD0 hD0₂ rfl rfl φ φ' hz ho hz' ho'
  apply Nat.card_congr
  refine Equiv.subtypeEquiv
    ⟨fun θ => (PsiG H hg₁).symm.trans (θ.trans (PsiG H hg₂)),
      fun ψ => (PsiG H hg₁).trans (ψ.trans (PsiG H hg₂).symm),
      fun θ => by ext x; simp, fun ψ => by ext x; simp⟩ ?_
  intro θ
  have hGR := graph_transport4 (PsiG H hg₁).toEquiv (PsiG H hg₂).toEquiv θ.toEquiv φ φ'
    (PcG H hg₁) (PcG H hg₂) (PcG' H hg₁) (PcG' H hg₂) _ _ _ _ (gamR_image H hg₁) (gamR_image H hg₂)
    hP hP' hinj
  constructor
  · rintro ⟨-, -, hI, -, hG⟩
    exact ⟨(isomD_iffG H hg₁ hg₂ θ).1 hI, hGR.1 (hG g hsplit)⟩
  · rintro ⟨hI, hG⟩
    refine ⟨hDu, hMM, (isomD_iffG H hg₁ hg₂ θ).2 hI,
      fun h => (Option.some_ne_none g (hsplit.symm.trans h)).elim, ?_⟩
    intro g' hg'
    rw [hsplit] at hg'
    obtain rfl := Option.some.inj hg'
    exact hGR.2 hG

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

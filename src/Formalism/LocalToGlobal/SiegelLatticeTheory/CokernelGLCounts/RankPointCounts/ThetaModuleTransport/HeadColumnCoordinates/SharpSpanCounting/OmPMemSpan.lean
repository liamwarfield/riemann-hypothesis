module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.AdjLast
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.GraphTransport
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.MemPerpSpanIff
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.HSumRight
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section General

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_right {ι : Type} (s : Finset ι) (c : ι → E) (g : ι → V) (u : V) :
    H.h u (∑ i ∈ s, c i • g i) = ∑ i ∈ s, M.L.cj (c i) * H.h u (g i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem span_eq_sum (g : ι → V) (hG : IsUnit (gramH H g).det) (u : V)
    (hu : u ∈ Submodule.span E (Set.range g)) :
    u = ∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i := by
  have hs : (∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i) ∈
      Submodule.span E (Set.range g) :=
    (Submodule.mem_span_range_iff_exists_fun E).2 ⟨_, rfl⟩
  have h' : pairSpan H g ⟨u, hu⟩ = pairSpan H g ⟨_, hs⟩ := by
    show pairing H g u = pairing H g (∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i)
    rw [pairing_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
    rfl
  exact congrArg Subtype.val ((pairSpan_bij H g hG).1 h')

theorem h_eq_form (g : ι → V) (hG : IsUnit (gramH H g).det) (u w : V)
    (hu : u ∈ Submodule.span E (Set.range g)) :
    H.h u w = ∑ i, ∑ j, H.h u (g i) * (gramH H g)⁻¹ i j * M.L.cj (H.h w (g j)) := by
  refine (congrArg (fun x => H.h x w) (span_eq_sum H g hG u hu)).trans ?_
  rw [h_sum_left]
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [H.h_herm w (g j)]

end General

section Term

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def GoodL {r : ℕ} (t : Term V M r) : Prop :=
  M.split = none ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ H.Dl t.f t.f' r = 0

theorem mmfam_none (hs : M.split = none) {r : ℕ} (t : Term V M r) :
    H.MMfam t = Sum.elim t.f t.f' := by
  unfold HermSp.MMfam; rw [hs]

theorem gramH_eq {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    gramH H (H.MMfam t) = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  rw [gramC_eq H _ _ _ _ hg.2.1 hg.2.2.1, mmfam_none H hg.1]
  ext i j
  rfl

theorem unit_gramH {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    IsUnit (gramH H (H.MMfam t)).det := by
  rw [gramH_eq H hg]
  exact unit_gramC H _ _ _ _ hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2

theorem relSub_eq {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    relSub H t = relC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  ext y
  show (∃ c : Ix r → M.L.O, ∀ j, (y j : E) = ∑ i, (c i : E) * gramH H (H.MMfam t) i j) ↔ _
  rw [gramH_eq H hg]
  rfl

def Psi {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    DDt H t ≃ₗ[M.L.O] DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') :=
  (ddEquiv H t (unit_gramH H hg)).trans (Submodule.quotEquivOfEq _ _ (relSub_eq H hg))

theorem Psi_mk {r : ℕ} {t : Term V M r} (hg : GoodL H t) (u : ↥(MMsharp H t)) :
    Psi H hg (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t (unit_gramH H hg) u) := rfl

theorem h_eq_formC {r : ℕ} {t : Term V M r} (hg : GoodL H t) (u w : ↥(MMsharp H t)) :
    H.h u w = formC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') (sharpEquiv H t (unit_gramH H hg) u)
      (sharpEquiv H t (unit_gramH H hg) w) := by
  rw [h_eq_form H (H.MMfam t) (unit_gramH H hg) u w ((mem_MMsharp_iff H t u).1 u.2).1, formC,
    ← gramH_eq H hg]
  rfl

end Term

end Formalism.L2.SG.LocalCountModules.LocCntCommon
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem mem_perp_span_iff {ι : Type} (s : ι → V) (v : V) :
    v ∈ H.perp (Submodule.span E (Set.range s)) ↔ ∀ i, H.h v (s i) = 0 := by
  constructor
  · intro hv i
    exact hv _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hv x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hv i
    | zero => exact h_zero_right H v
    | add x y _ _ hx hy => rw [h_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [h_smul_right, hx, mul_zero]

theorem mem_perpX_iff {r : ℕ} (f : Fin (r + 1) → V) (v : V) :
    v ∈ H.perp (H.X f) ↔ ∀ a : Fin r, H.h v (f a.castSucc) = 0 :=
  mem_perp_span_iff H _ v

variable {r : ℕ}

theorem h_om'_f (f f' : Fin (r + 1) → V) (a : Fin (r + 1)) :
    H.h (H.om' f f') (f a) = if a = Fin.last r then (H.Zhat f f').det else 0 := by
  have : H.h (H.om' f f') (f a) = ((H.Zhat f f') * (H.Zhat f f').adjugate) a (Fin.last r) := by
    unfold HermSp.om'
    rw [h_sum_left, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]; rfl
  rw [this, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

def omP (f f' : Fin (r + 1) → V) : V := Ring.inverse (H.Dl f f' (r + 1)) • H.om' f f'

theorem h_omP_f (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) (a : Fin (r + 1)) :
    H.h (omP H f f') (f a) = if a = Fin.last r then 1 else 0 := by
  rw [omP, H.h_smul_left, h_om'_f, ← dl_full]
  split_ifs
  · exact Ring.inverse_mul_cancel _ hD
  · exact mul_zero _

theorem omP_mem (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) :
    omP H f f' ∈ H.perp (H.X f) := by
  rw [mem_perpX_iff]
  intro a
  rw [h_omP_f H f f' hD, if_neg (Fin.castSucc_lt_last a).ne]

theorem z_mem (f : Fin (r + 1) → V) (T : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) :
    f (Fin.last r) ∈ H.perp (H.X f) := by
  rw [mem_perpX_iff]
  intro a
  exact hF.1 _ _ (Or.inr (Fin.castSucc_lt_last a).ne)

theorem h_X_perp (f : Fin (r + 1) → V) (v : V) (hv : v ∈ H.perp (H.X f)) (x : V) (hx : x ∈ H.X f) :
    H.h x v = 0 := by
  rw [H.h_herm v x, hv x hx, map_zero]

def coordW (f : Fin (r + 1) → V) (v v' : V) (hv : v ∈ H.perp (H.X f)) (hv' : v' ∈ H.perp (H.X f)) :
    H.Wb f →ₗ[E] E × E :=
  Submodule.liftQ _ (((hLm H v).prod (hLm H v')).comp (H.perp (H.X f)).subtype) (by
    intro x hx
    rw [Submodule.mem_comap] at hx
    rw [LinearMap.mem_ker]
    exact Prod.ext (h_X_perp H f v hv _ hx) (h_X_perp H f v' hv' _ hx))

theorem coordW_mk (f : Fin (r + 1) → V) (v v' : V) (hv : v ∈ H.perp (H.X f))
    (hv' : v' ∈ H.perp (H.X f)) (x : ↥(H.perp (H.X f))) :
    coordW H f v v' hv hv' (H.mkW f x) = (H.h x v, H.h x v') := rfl

theorem coordW_comp {f₁ f₂ : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂) (hφ : H.IsIsomW φ)
    (v₁ v₁' v₂ v₂' : V) (h₁ : v₁ ∈ H.perp (H.X f₁)) (h₁' : v₁' ∈ H.perp (H.X f₁))
    (h₂ : v₂ ∈ H.perp (H.X f₂)) (h₂' : v₂' ∈ H.perp (H.X f₂))
    (e : φ (H.mkW f₁ ⟨v₁, h₁⟩) = H.mkW f₂ ⟨v₂, h₂⟩) (e' : φ (H.mkW f₁ ⟨v₁', h₁'⟩) = H.mkW f₂ ⟨v₂', h₂'⟩)
    (w : H.Wb f₁) : coordW H f₂ v₂ v₂' h₂ h₂' (φ w) = coordW H f₁ v₁ v₁' h₁ h₁' w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  obtain ⟨x₂, hx₂⟩ := Submodule.mkQ_surjective _ (φ (H.mkW f₁ x))
  have hx₂' : φ (H.mkW f₁ x) = H.mkW f₂ x₂ := hx₂.symm
  change coordW H f₂ v₂ v₂' h₂ h₂' (φ (H.mkW f₁ x)) = coordW H f₁ v₁ v₁' h₁ h₁' (H.mkW f₁ x)
  rw [hx₂', coordW_mk, coordW_mk]
  exact Prod.ext (hφ x ⟨v₁, h₁⟩ x₂ ⟨v₂, h₂⟩ hx₂' e) (hφ x ⟨v₁', h₁'⟩ x₂ ⟨v₂', h₂'⟩ hx₂' e')

end Formalism.L2.SG.LocalCountModules.LocCntCommon
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Transport

theorem graph_transport {D₁ D₂ Dc₁ Dc₂ W₁ W₂ P : Type} (Ψ₁ : D₁ ≃ Dc₁) (Ψ₂ : D₂ ≃ Dc₂)
    (θ : D₁ ≃ D₂) (φ : W₁ → W₂) (Pc₁ : W₁ → P) (Pc₂ : W₂ → P) (Γ₁ : Set (D₁ × W₁))
    (Γ₂ : Set (D₂ × W₂)) (Γc₁ : Set (Dc₁ × P)) (Γc₂ : Set (Dc₂ × P))
    (h1 : (fun p => (Ψ₁ p.1, Pc₁ p.2)) '' Γ₁ = Γc₁) (h2 : (fun p => (Ψ₂ p.1, Pc₂ p.2)) '' Γ₂ = Γc₂)
    (hP : ∀ w, Pc₂ (φ w) = Pc₁ w)
    (hinj : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, Pc₂ q.2 = Pc₁ p.2 → q.2 = φ p.2) :
    ((fun p => (θ p.1, φ p.2)) '' Γ₁ = Γ₂) ↔
      ((fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), p.2)) '' Γc₁ = Γc₂) := by
  constructor
  · intro h
    rw [← h1, ← h2, ← h, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro p _
    simp [hP]
  · intro h
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hc : (Ψ₂ (θ p.1), Pc₁ p.2) ∈ Γc₂ := by
        rw [← h]
        refine ⟨(Ψ₁ p.1, Pc₁ p.2), ?_, by simp⟩
        rw [← h1]
        exact ⟨p, hp, rfl⟩
      rw [← h2] at hc
      obtain ⟨q', hq', hqe⟩ := hc
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hqe
      have e2 : q'.2 = φ p.2 := hinj p hp q' hq' hqe.2
      have : q' = (θ p.1, φ p.2) := Prod.ext hqe.1 e2
      show (θ p.1, φ p.2) ∈ Γ₂
      rw [← this]
      exact hq'
    · intro hq
      have hc : (Ψ₂ q.1, Pc₂ q.2) ∈ Γc₂ := by
        rw [← h2]
        exact ⟨q, hq, rfl⟩
      rw [← h] at hc
      obtain ⟨c, hc1, hce⟩ := hc
      rw [← h1] at hc1
      obtain ⟨p, hp, rfl⟩ := hc1
      simp only [Prod.mk.injEq, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq] at hce
      refine ⟨p, hp, ?_⟩
      have e2 : q.2 = φ p.2 := hinj p hp q hq hce.2.symm
      exact Prod.ext hce.1 e2.symm

end Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem smul_transport {A B : Type} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]
    (φ : A ≃ₗ[E] B) (c₁ c₂ k₁ k₂ : E) (hk₁ : k₁ * c₁ = 1) (hk₂ : k₂ * c₂ = 1) (a : A) (b : B)
    (e : c₂ • φ a = c₁ • b) : φ (k₁ • a) = k₂ • b := by
  rw [map_smul]
  have h1 : φ a = k₂ • (c₂ • φ a) := by rw [smul_smul, hk₂, one_smul]
  rw [h1, e, smul_smul, smul_smul]
  congr 1
  calc k₁ * k₂ * c₁ = k₂ * (k₁ * c₁) := by ring
    _ = k₂ := by rw [hk₁, mul_one]

variable {r : ℕ}

theorem om'_mem (f f' : Fin (r + 1) → V) : H.om' f f' ∈ H.perp (H.X f) := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => H.h (H.om' f f') x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    unfold HermSp.om'
    rw [h_sum_left]
    have hm := congrFun (congrFun (Matrix.mul_adjugate (H.Zhat f f')) a.castSucc) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne, smul_zero] at hm
    rw [← hm]
    apply Finset.sum_congr rfl
    intro b _
    simp [HermSp.Zhat, mul_comm]
  · exact h_zero_right H _
  · intro x y _ _ hx hy
    rw [h_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [h_smul_right, hx, mul_zero]

theorem sends_one {f₁ f₂ : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂) (v₁ v₂ : V)
    (h₁ : v₁ ∈ H.perp (H.X f₁)) (h₂ : v₂ ∈ H.perp (H.X f₂))
    (hs : H.SendsTo φ.toLinearMap 1 1 v₁ v₂) : φ (H.mkW f₁ ⟨v₁, h₁⟩) = H.mkW f₂ ⟨v₂, h₂⟩ := by
  have := hs ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ rfl rfl
  simpa using this

theorem sends_omP {f₁ f₁' f₂ f₂' : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂)
    (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1))) (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hs : H.SendsTo φ.toLinearMap (H.Dl f₂ f₂' (r + 1)) (H.Dl f₁ f₁' (r + 1)) (H.om' f₁ f₁')
      (H.om' f₂ f₂')) :
    φ (H.mkW f₁ ⟨omP H f₁ f₁', omP_mem H f₁ f₁' hD₁⟩) = H.mkW f₂ ⟨omP H f₂ f₂', omP_mem H f₂ f₂' hD₂⟩ := by
  have e := hs ⟨_, om'_mem H f₁ f₁'⟩ ⟨_, om'_mem H f₂ f₂'⟩ rfl rfl
  have e1 : H.mkW f₁ ⟨omP H f₁ f₁', omP_mem H f₁ f₁' hD₁⟩ =
      Ring.inverse (H.Dl f₁ f₁' (r + 1)) • H.mkW f₁ ⟨_, om'_mem H f₁ f₁'⟩ := by
    rw [← LinearMap.map_smul]
    rfl
  have e2 : H.mkW f₂ ⟨omP H f₂ f₂', omP_mem H f₂ f₂' hD₂⟩ =
      Ring.inverse (H.Dl f₂ f₂' (r + 1)) • H.mkW f₂ ⟨_, om'_mem H f₂ f₂'⟩ := by
    rw [← LinearMap.map_smul]
    rfl
  rw [e1, e2]
  exact smul_transport φ _ _ _ _ (Ring.inverse_mul_cancel _ hD₁) (Ring.inverse_mul_cancel _ hD₂) _ _ e

theorem h_omP (f f' : Fin (r + 1) → V) (u : V) :
    H.h u (omP H f f') = ∑ b, M.L.cj ((H.Zhat f f')⁻¹ b (Fin.last r)) * H.h u (f' b) := by
  have hD : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    unfold HermSp.Dl
    rw [dite_eq_left le_rfl]
    simp [Fin.castLE_refl]
  unfold omP HermSp.om'
  rw [h_smul_right, h_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, ← map_mul, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, hD]

end Formalism.L2.SG.LocalCountModules.LocCntCommon
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem h_frame (f : Fin (r + 1) → V) (T : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (a b : Fin (r + 1)) :
    H.h (f b) (f a) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0 := by
  split_ifs with hab
  · obtain ⟨rfl, rfl⟩ := hab
    exact hF.2
  · apply hF.1 b a
    by_contra hc
    push_neg at hc
    exact hab ⟨hc.2, hc.1⟩

theorem adj_last (f f' : Fin (r + 1) → V) :
    (H.Zhat f f').adjugate (Fin.last r) (Fin.last r) = H.Dl f f' r := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  unfold HermSp.Dl
  rw [dite_eq_left (Nat.le_succ r)]
  have hpow : ((-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hpow, one_mul]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, Fin.succAbove_last]
  rfl

theorem h_om'_f' (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD0 : H.Dl f f' r = 0) (b : Fin (r + 1)) : H.h (H.om' f f') (f' b) = 0 := by
  unfold HermSp.om'
  rw [h_sum_left]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c = Fin.last r ∧ b = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hc
    rw [adj_last, hD0, zero_mul]
  · rw [hF'.1 c b (not_and_or.mp hc), mul_zero]

theorem mem_X_of (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0)
    (v : V) (hv : v ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (h1 : ∀ a, H.h v (f a) = 0) (h2 : H.h (H.om' f f') v = 0) : v ∈ H.X f := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  rw [Fintype.sum_sum_type] at h1 h2 ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢

  have hl : c (Sum.inl (Fin.last r)) = 0 := by
    rw [h_add_right, h_sum_right, h_sum_right] at h2
    simp only [h_om'_f' H f f' T' hF' hD0, mul_zero, Finset.sum_const_zero, add_zero, h_om'_f] at h2
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by rw [if_neg hb, mul_zero])
      (by simp), if_pos rfl, ← dl_full] at h2
    have h3 : M.L.cj (c (Sum.inl (Fin.last r))) = 0 := (hD.mul_left_eq_zero).1 h2
    have := congrArg M.L.cj h3
    rwa [M.L.cj_cj, map_zero] at this

  have hZ : (H.Zhat f f').mulVec (fun b => c (Sum.inr b)) = 0 := by
    funext a
    have := h1 a
    rw [H.h_add_left, h_sum_left, h_sum_left] at this
    simp only [h_frame H f T hF] at this
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [hb]) (by simp)] at this
    simp only [hl, zero_mul, zero_add] at this
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct, ← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]; rfl
  have hp' : (fun b => c (Sum.inr b)) = 0 := by
    have hu : IsUnit (H.Zhat f f').det := by rw [← dl_full]; exact hD
    have := congrArg (fun w => (H.Zhat f f')⁻¹.mulVec w) hZ
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
  have hp'' : ∀ b, c (Sum.inr b) = 0 := fun b => congrFun hp' b
  simp only [hp'', zero_smul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_castSucc, hl, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Formalism.L2.SG.LocalCountModules.LocCntCommon
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem h_omP_omP (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD0 : H.Dl f f' r = 0) : H.h (omP H f f') (omP H f f') = 0 := by
  have hadj : (H.Zhat f f').adjugate (Fin.last r) (Fin.last r) = 0 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    have hcast : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc := by
      funext a
      rfl
    have h2 : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
      rw [Formalism.MainNotions.S.Loc.HermSp.Dl, dite_eq_left (Nat.le_succ r), hcast]
    rw [← h2, hD0, mul_zero]
  have hterm : ∀ b b', (H.Zhat f f').adjugate b (Fin.last r) *
      (M.L.cj ((H.Zhat f f').adjugate b' (Fin.last r)) * H.h (f' b) (f' b')) = 0 := by
    intro b b'
    by_cases hb : b = Fin.last r
    · subst hb
      rw [hadj, zero_mul]
    · rw [hF'.1 b b' (Or.inl hb), mul_zero, mul_zero]
  unfold omP
  rw [H.h_smul_left, h_smul_right, Formalism.MainNotions.S.Loc.HermSp.om', h_sum_left]
  simp only [h_sum_right, Finset.mul_sum, hterm, Finset.sum_const_zero, mul_zero]

theorem h_z_omP (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) :
    H.h (f (Fin.last r)) (omP H f f') = 1 := by
  have hDl : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    simp [Formalism.MainNotions.S.Loc.HermSp.Dl, Fin.castLE_rfl, Matrix.submatrix_id_id]
  have hz : ∀ b, H.h (f (Fin.last r)) (f' b) = M.L.cj (H.Zhat f f' (Fin.last r) b) := fun b => H.h_herm _ _
  have hsum : ∑ b, M.L.cj ((H.Zhat f f').adjugate b (Fin.last r)) * M.L.cj (H.Zhat f f' (Fin.last r) b) =
      M.L.cj (H.Zhat f f').det := by
    have h1 := congrFun (congrFun (Matrix.mul_adjugate (H.Zhat f f')) (Fin.last r)) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [map_mul, mul_comm]
  unfold omP
  rw [h_smul_right, Formalism.MainNotions.S.Loc.HermSp.om', h_sum_right]
  simp only [hz]
  rw [hsum, ← map_mul, ← hDl, Ring.inverse_mul_cancel _ hD, map_one]

theorem omP_mem_span (f f' : Fin (r + 1) → V) :
    omP H f f' ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
  unfold omP
  apply Submodule.smul_mem
  unfold Formalism.MainNotions.S.Loc.HermSp.om'
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

theorem decomp (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0)
    (u : V) (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) (hX : u ∈ H.perp (H.X f))
    (α β : E) (hα : α = H.h u (omP H f f'))
    (hβ : β = H.h u (f (Fin.last r)) + algebraMap F E T * α) :
    u - (α • f (Fin.last r) + β • omP H f f') ∈ H.X f := by
  have hsubL : ∀ x x' y, H.h (x - x') y = H.h x y - H.h x' y := by
    intro x x' y
    rw [sub_eq_add_neg, H.h_add_left, ← neg_one_smul E x', H.h_smul_left]
    ring
  have hzo : H.h (f (Fin.last r)) (omP H f f') = 1 := h_z_omP H f f' hD
  have hoz : H.h (omP H f f') (f (Fin.last r)) = 1 := by
    rw [H.h_herm, hzo, map_one]
  have hoo : H.h (omP H f f') (omP H f f') = 0 := h_omP_omP H f f' T' hF' hD0
  have hwz : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (f (Fin.last r)) = 0 := by
    rw [hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, hF.2, hoz, hβ]
    ring
  have hwo : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f') = 0 := by
    rw [hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, hzo, hoo, ← hα]
    ring
  have hom : H.om' f f' = H.Dl f f' (r + 1) • omP H f f' := by
    unfold omP
    rw [smul_smul, Ring.mul_inverse_cancel _ hD, one_smul]
  apply mem_X_of H f f' T T' hF hF' hD hD0
  · exact Submodule.sub_mem _ hu (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
      (Submodule.smul_mem _ _ (omP_mem_span H f f')))
  · intro a
    by_cases ha : a = Fin.last r
    · subst ha
      exact hwz
    · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
      have hxa : f a'.castSucc ∈ H.X f := Submodule.subset_span ⟨a', rfl⟩
      have e1 : H.h u (f a'.castSucc) = 0 := hX _ hxa
      have e2 : H.h (f (Fin.last r)) (f a'.castSucc) = 0 := hF.1 _ _ (Or.inr (Fin.castSucc_ne_last a'))
      have e3 : H.h (omP H f f') (f a'.castSucc) = 0 := (omP_mem H f f' hD) _ hxa
      rw [hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, e1, e2, e3]
      ring
  · rw [hom, H.h_smul_left, H.h_herm (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f'), hwo, map_zero,
      mul_zero]

theorem mkW_decomp (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0)
    (u : ↥(H.perp (H.X f))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f u = H.h u (omP H f f') • H.mkW f ⟨f (Fin.last r), z_mem H f T hF⟩ +
      (H.h u (f (Fin.last r)) + algebraMap F E T * H.h u (omP H f f')) •
        H.mkW f ⟨omP H f f', omP_mem H f f' hD⟩ := by
  have hmem := decomp H f f' T T' hF hF' hD hD0 u hu u.2 _ _ rfl rfl
  rw [← sub_eq_zero, ← map_smul, ← map_smul, ← map_add (f := _), ← map_sub, Formalism.MainNotions.S.Loc.HermSp.mkW,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact hmem

end Formalism.L2.SG.LocalCountModules.LocCntCommon

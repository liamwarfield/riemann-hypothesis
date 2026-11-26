module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjSub
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueEtaPf
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace PI.LocCntLat.GE

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_add_right' (H : HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem h_expand (H : HermSp M V) (x a y b : V) :
    H.h (x + a) (y + b) = H.h x y + H.h x b + H.h a y + H.h a b := by
  rw [H.h_add_left, h_add_right', h_add_right']
  abel

theorem span_MMfam (H : HermSp M V) {r : ℕ} (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) = Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  unfold HermSp.MMfam
  rcases hs : M.split with _ | g
  · rfl
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
          (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
        have e : t.f' i = algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (t.f' i - t.f i)) + t.f i := by
          rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul, sub_add_cancel]
        show t.f' i ∈ _
        rw [e]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
          (Submodule.subset_span ⟨Sum.inl i, rfl⟩)

theorem hermSp_W0_eq_perp_span_range_MMfam (H : HermSp M V) {r : ℕ} (t : Term V M r) :
    H.W0 t.f t.f' = H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
  unfold HermSp.W0
  congr 1
  rw [span_MMfam H t, Set.Sum.elim_range, Submodule.span_union]
  rfl

theorem isCompl_MM (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t) :
    IsCompl (Submodule.span E (Set.range (H.MMfam t))) (H.perp (Submodule.span E (Set.range (H.MMfam t)))) := by
  have hT := hg.1
  have hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T := ⟨hT.2.1.2.1, hT.2.1.2.2.1⟩
  have hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' := ⟨hT.2.2.1.2.1, hT.2.2.1.2.2.1⟩
  have h := isCompl_span_frames_W0 (H := H) t.f t.f' t.T t.T' hF hF' hT.2.2.2.1
    (isUnit_Gdet (H := H) t.f t.f' t.T t.T' hT.2.2.2.2.1)
  rw [← hermSp_W0_eq_perp_span_range_MMfam H t, span_MMfam H t]
  exact h

theorem MMo_le (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t) : MMo H t ≤ t.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hg.2.1 a)

theorem mem_spanE_of_mem_MMo (H : HermSp M V) {r : ℕ} (t : Term V M r) {m : V} (hm : m ∈ MMo H t) :
    m ∈ Submodule.span E (Set.range (H.MMfam t)) := by
  exact (Submodule.span_le (p := (Submodule.span E (Set.range (H.MMfam t))).restrictScalars M.L.O)).2
    Submodule.subset_span hm

theorem hermitian_span_orthogonal_W0 (H : HermSp M V) {r : ℕ} (t : Term V M r) {m n : V}
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) (hn : n ∈ H.W0 t.f t.f') : H.h m n = 0 := by
  have hn' : n ∈ H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hn
  rw [H.h_herm n m, hn' m hm, map_zero]

theorem hermitian_W0_orthogonal_span (H : HermSp M V) {r : ℕ} (t : Term V M r) {m n : V}
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) (hn : n ∈ H.W0 t.f t.f') : H.h n m = 0 := by
  have hn' : n ∈ H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hn
  exact hn' m hm

theorem dwMk_eq_iff (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V)
    (a b : ↥(ThSharp H t N)) : dwMk H t N a = dwMk H t N b ↔ (a : V) - b ∈ N := by
  unfold dwMk
  rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub]
  rfl

end Basic

section Halves

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem prM (hOK : M.OK) (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t)
    (u : V) (hu : u ∈ MMsharp H t) : ∃ n ∈ H.W0 t.f t.f', u + n ∈ t.abelian₂ := by
  have hU := isCompl_MM H t hg
  obtain ⟨h1, -⟩ := local_hermitian_glue F E M hOK V H t.abelian₂ hg.1.1 _ hU
  obtain ⟨x, hx, hxu⟩ := (h1 u hu.1).2 (fun y hy hyU => hu.2 y (hg.2.2.2 y hy hyU))
  refine ⟨x - u, ?_, by convert hx using 1; abel⟩
  rw [hermSp_W0_eq_perp_span_range_MMfam H t, ← hxu]
  exact PI.LocHerm.Glue.sub_proj_mem hU x

theorem prN (hOK : M.OK) (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t)
    (w : V) (hw : w ∈ ThSharp H t (ThL H t)) :
    ∃ m ∈ MMsharp H t, m + w ∈ t.abelian₂ := by
  have hU := isCompl_MM H t hg
  obtain ⟨-, h2⟩ := local_hermitian_glue F E M hOK V H t.abelian₂ hg.1.1 _ hU
  have hwp : w ∈ H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hw.1
  obtain ⟨x, hx, hxw⟩ := (h2 w hwp).2 (fun y hy hyp => hw.2 y ⟨hy, by
    show y ∈ H.W0 t.f t.f'
    rw [hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hyp⟩)
  have hmU : x - w ∈ Submodule.span E (Set.range (H.MMfam t)) := by
    rw [← hxw]
    exact PI.LocHerm.Glue.sub_proj_mem hU.symm x
  refine ⟨x - w, ⟨hmU, fun m' hm' => ?_⟩, by convert hx using 1; abel⟩
  have e := H.h_add_left (x - w) w m'
  rw [sub_add_cancel, hermitian_W0_orthogonal_span H t (mem_spanE_of_mem_MMo H t hm') hw.1, add_zero] at e
  rw [← e]
  exact (hg.1.1.2.2 x).1 hx m' (MMo_le H t hg hm')

end Halves

section Eta

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem glueEta_holds (M : Model F E) (r : ℕ) : GlueEta M r := by
  intro hOK V _ _ H t hg
  have hSD := hg.1.1
  have hLam : ∀ x y : V, x ∈ t.abelian₂ → y ∈ t.abelian₂ → H.h x y ∈ M.L.O := fun x y hx hy => (hSD.2.2 x).1 hx y hy
  have liftM : ∀ m : ↥(MMsharp H t), ∃ w : ↥(ThSharp H t (ThL H t)), (m : V) + w ∈ t.abelian₂ := by
    intro m
    obtain ⟨n, hn, hmn⟩ := prM hOK H t hg m m.2
    refine ⟨⟨n, hn, fun n' hn' => ?_⟩, hmn⟩
    have e := H.h_add_left (m : V) n n'
    rw [hermitian_span_orthogonal_W0 H t m.2.1 hn'.2, zero_add] at e
    rw [← e]
    exact hLam _ _ hmn hn'.1
  have liftW : ∀ w : ↥(ThSharp H t (ThL H t)), ∃ m : ↥(MMsharp H t), (m : V) + w ∈ t.abelian₂ := by
    intro w
    obtain ⟨m, hm, hmw⟩ := prN hOK H t hg w w.2
    exact ⟨⟨m, hm⟩, hmw⟩
  let G : Submodule M.L.O (↥(MMsharp H t) × ↥(ThSharp H t (ThL H t))) :=
    { carrier := {p | (p.1 : V) + (p.2 : V) ∈ t.abelian₂}
      add_mem' := fun {a b} ha hb => by
        show ((a.1 + b.1 : ↥(MMsharp H t)) : V) + ((a.2 + b.2 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂
        rw [Submodule.coe_add, Submodule.coe_add, add_add_add_comm]
        exact t.abelian₂.add_mem ha hb
      zero_mem' := by
        show ((0 : ↥(MMsharp H t)) : V) + ((0 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂
        rw [Submodule.coe_zero, Submodule.coe_zero, add_zero]
        exact t.abelian₂.zero_mem
      smul_mem' := fun c p hp => by
        show ((c • p.1 : ↥(MMsharp H t)) : V) + ((c • p.2 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂
        rw [Submodule.coe_smul, Submodule.coe_smul, ← smul_add]
        exact t.abelian₂.smul_mem c hp }
  let α : G →ₗ[M.L.O] DDt H t :=
    (Submodule.mkQ _).comp ((LinearMap.fst M.L.O _ _).comp G.subtype)
  let β : G →ₗ[M.L.O] DDW H t (ThL H t) :=
    (Submodule.mkQ _).comp ((LinearMap.snd M.L.O _ _).comp G.subtype)
  have hα : Function.Surjective α := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨w, hw⟩ := liftM m
    exact ⟨⟨(m, w), hw⟩, rfl⟩
  have hβ : Function.Surjective β := by
    intro q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨m, hm⟩ := liftW w
    exact ⟨⟨(m, w), hm⟩, rfl⟩
  have hker : LinearMap.ker α = LinearMap.ker β := by
    ext p
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    change (Submodule.Quotient.mk p.val.1 : DDt H t) = 0 ↔
      (Submodule.Quotient.mk p.val.2 : DDW H t (ThL H t)) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.subtype_apply]
    have hp : (p.val.1 : V) + (p.val.2 : V) ∈ t.abelian₂ := p.2
    constructor
    · intro hm
      refine ⟨?_, p.val.2.2.1⟩
      have := t.abelian₂.sub_mem hp (MMo_le H t hg hm)
      rwa [add_sub_cancel_left] at this
    · intro hw
      have h1 : (p.val.1 : V) ∈ t.abelian₂ := by
        have := t.abelian₂.sub_mem hp hw.1
        rwa [add_sub_cancel_right] at this
      exact hg.2.2.2 _ h1 p.val.1.2.1
  let η : DDt H t ≃ₗ[M.L.O] DDW H t (ThL H t) :=
    (α.quotKerEquivOfSurjective hα).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (β.quotKerEquivOfSurjective hβ))
  have hη : ∀ g : G, η (α g) = β g := by
    intro g
    show (β.quotKerEquivOfSurjective hβ) (Submodule.quotEquivOfEq _ _ hker
      ((α.quotKerEquivOfSurjective hα).symm (α g))) = β g
    have e1 : (α.quotKerEquivOfSurjective hα).symm (α g) = Submodule.Quotient.mk g := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [e1, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have key : ∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t (ThL H t))),
      η (ddMk H t m) = dwMk H t _ w ↔ (m : V) + w ∈ t.abelian₂ := by
    intro m w
    obtain ⟨w0, hw0⟩ := liftM m
    have e : η (ddMk H t m) = dwMk H t _ w0 := hη ⟨(m, w0), hw0⟩
    rw [e, dwMk_eq_iff]
    constructor
    · rintro ⟨hl, -⟩
      have e2 : (m : V) + w = ((m : V) + w0) - ((w0 : V) - w) := by abel
      rw [e2]
      exact t.abelian₂.sub_mem hw0 hl
    · intro hmw
      refine ⟨?_, ?_⟩
      · have e2 : (w0 : V) - w = ((m : V) + w0) - ((m : V) + w) := by abel
        rw [e2]
        exact t.abelian₂.sub_mem hw0 hmw
      · exact (H.W0 t.f t.f').sub_mem w0.2.1 w.2.1
  refine ⟨η, key, fun m m' w w' h1 h2 => ?_⟩
  have := hLam _ _ ((key m w).1 h1) ((key m' w').1 h2)
  rw [h_expand, hermitian_span_orthogonal_W0 H t m.2.1 w'.2.1, hermitian_W0_orthogonal_span H t m'.2.1 w.2.1, add_zero, add_zero] at this
  exact this

end Eta

end PI.LocCntLat.GE
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Matrix

namespace PI.LocCntLat.GC

open PI.LocCntLat.GE

section Lin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_zero_right' (H : HermSp M V) (x : V) : H.h x 0 = 0 := by
  rw [H.h_herm, H.h_zero_left, map_zero]

theorem h_smul_right' (H : HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem cj_mem_O (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem hermSp_h_finset_sum_smul_left (H : HermSp M V) {κ : Type} (s : Finset κ) (d : κ → E) (g : κ → V) (y : V) :
    H.h (∑ k ∈ s, d k • g k) y = ∑ k ∈ s, d k * H.h (g k) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [H.h_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem gram_mulVec (H : HermSp M V) (g : ι → V) (d : ι → E) (i : ι) :
    H.h (∑ k, d k • g k) (g i) = ((H.gram g) *ᵥ d) i := by
  rw [hermSp_h_finset_sum_smul_left]
  simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem exists_dual (H : HermSp M V) (g : ι → V) (hG : IsUnit (H.gram g).det) (j : ι) :
    ∃ u ∈ Submodule.span E (Set.range g), ∀ i, H.h u (g i) = if i = j then 1 else 0 := by
  refine ⟨∑ k, ((H.gram g)⁻¹ *ᵥ Pi.single j 1) k • g k, ?_, fun i => ?_⟩
  · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [gram_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec, Pi.single_apply]

theorem linIndep_of_gram (H : HermSp M V) (g : ι → V) (hG : IsUnit (H.gram g).det) :
    LinearIndependent E g := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : H.gram g *ᵥ c = 0 := by
    funext i
    have := gram_mulVec H g c i
    rw [hc, H.h_zero_left] at this
    simpa using this.symm
  have hc0 : c = 0 := by
    rw [← Matrix.one_mulVec c, ← Matrix.nonsing_inv_mul _ hG, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  intro i
  rw [hc0]
  rfl

private theorem hermSp_h_add_right (H : HermSp M V) (w x y : V) : H.h w (x + y) = H.h w x + H.h w y := by
  rw [H.h_herm, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

end Lin

section Dual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem dual_mem_sharp (H : HermSp M V) {r : ℕ} (t : Term V M r) {u : V}
    (hu : u ∈ Submodule.span E (Set.range (H.MMfam t))) (j : Fin (r + 1) ⊕ Fin (r + 1))
    (hu' : ∀ i, H.h u (H.MMfam t i) = if i = j then 1 else 0) : u ∈ MMsharp H t := by
  show u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O
  refine ⟨hu, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hu' i]
    split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  | zero => rw [h_zero_right']; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [hermSp_h_add_right]; exact M.L.O.add_mem hx hy
  | smul c x _ hx => rw [Subring.smul_def, h_smul_right']; exact M.L.O.mul_mem (cj_mem_O _ c.2) hx

theorem mem_MMo_of_dual (H : HermSp M V) {r : ℕ} (t : Term V M r) (hG : IsUnit (H.gram (H.MMfam t)).det)
    {m : V} (hm : m ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hd : ∀ u ∈ MMsharp H t, H.h m u ∈ M.L.O) : m ∈ MMo H t := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hm
  have hc : ∀ j, c j ∈ M.L.O := by
    intro j
    obtain ⟨u, hu, hu'⟩ := exists_dual H (H.MMfam t) hG j
    have h1 := hd u (dual_mem_sharp H t hu j hu')
    have h2 : H.h (∑ i, c i • H.MMfam t i) u = c j := by
      rw [hermSp_h_finset_sum_smul_left, Finset.sum_eq_single j]
      · rw [H.h_herm u, hu' j, if_pos rfl, map_one, mul_one]
      · intro i _ hij
        rw [H.h_herm u, hu' i, if_neg hij, map_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rwa [h2] at h1
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem (MMo H t) (⟨c i, hc i⟩ : M.L.O) (Submodule.subset_span ⟨i, rfl⟩)

theorem sharp_le_span_dual (H : HermSp M V) {r : ℕ} (t : Term V M r) (hG : IsUnit (H.gram (H.MMfam t)).det)
    (u : Fin (r + 1) ⊕ Fin (r + 1) → V) (hu : ∀ j, u j ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hu' : ∀ j i, H.h (u j) (H.MMfam t i) = if i = j then 1 else 0) :
    (MMsharp H t : Set V) ⊆ Submodule.span M.L.O (Set.range u) := by
  intro x hx
  have hx' : x ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h x m ∈ M.L.O := hx
  have hy : ∀ i, H.h (∑ j, H.h x (H.MMfam t j) • u j) (H.MMfam t i) = H.h x (H.MMfam t i) := by
    intro i
    rw [hermSp_h_finset_sum_smul_left, Finset.sum_eq_single i]
    · rw [hu' i i, if_pos rfl, mul_one]
    · intro j _ hji
      rw [hu' j i, if_neg (Ne.symm hji), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hmem : x - ∑ j, H.h x (H.MMfam t j) • u j ∈ Submodule.span E (Set.range (H.MMfam t)) :=
    Submodule.sub_mem _ hx'.1 (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have h0 : H.gram (H.MMfam t) *ᵥ c = 0 := by
    funext i
    have := gram_mulVec H (H.MMfam t) c i
    rw [hc, sub_eq_add_neg, ← neg_one_smul E, H.h_add_left, H.h_smul_left, hy i] at this
    simpa using this.symm
  have hc0 : c = 0 := by
    rw [← Matrix.one_mulVec c, ← Matrix.nonsing_inv_mul _ hG, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hxy : x = ∑ j, H.h x (H.MMfam t j) • u j := by
    rw [← sub_eq_zero, ← hc, hc0]
    simp
  show x ∈ Submodule.span M.L.O (Set.range u)
  rw [hxy]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem _ (⟨_, hx'.2 _ (Submodule.subset_span ⟨j, rfl⟩)⟩ : M.L.O)
    (Submodule.subset_span ⟨j, rfl⟩)

end Dual

end PI.LocCntLat.GC

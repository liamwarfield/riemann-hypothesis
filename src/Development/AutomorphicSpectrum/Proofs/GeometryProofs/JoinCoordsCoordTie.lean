module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTie
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTie
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.Retie

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Transport

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {y : Y}
    (h : genPt (η ≫ f) ⤳ f y) : genPt η ⤳ y := by
  have h1 := h.map (inv f).continuous
  have e : ∀ z : Y, (inv f) (f z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have e2 : genPt (η ≫ f) = f (genPt η) := Scheme.Hom.comp_apply _ _ _
  rw [e2, e, e] at h1
  exact h1

theorem exists_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (q : Cpt (η ≫ f)) :
    ∃ p : Cpt η, push η f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  exact ⟨⟨y, specializes_of_iso η f hq⟩, rfl⟩

theorem inChart_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {κ : Type} (x : κ → Ω) (c : κ)
    (p : Cpt η) : InChart (η ≫ f) x c (push η f p) ↔ InChart η x c p := by
  unfold InChart
  rw [regAt_push]

theorem coordTie_comp_iso {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (h : CoordTie o η x) :
    CoordTie o (η ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp η f]
    have hb : Function.Bijective (f.stalkMap (η (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push η f q
    exact genMap_push_injective η f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push η f q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push η f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨(inv f) ⁻¹ᵁ U, hU.preimage (inv f), fun q => ?_⟩
    obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have e : (inv f) (f y) = y := by
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
    have e1 : f y ∈ (inv f) ⁻¹ᵁ U ↔ y ∈ U := by
      change (inv f) (f y) ∈ U ↔ _
      rw [e]
    rw [e1, hq y]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(push η f ⟨y, h1⟩).2, (inChart_push η f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨specializes_of_iso η f h1, (inChart_push η f x c ⟨y, specializes_of_iso η f h1⟩).1 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push η f q
      rw [regAt_push]
      exact H p ((inChart_push η f x c p).1 hq)
    · intro H p hp
      have := H (push η f p) ((inChart_push η f x c p).2 hp)
      rwa [regAt_push] at this

end Transport

theorem dominates_id_iff {X Y : Scheme.{0}} {Ω : Type} [Field Ω] {ξ' : Spec (CommRingCat.of Ω) ⟶ Y}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : Y ⟶ X} : Dominates ξ' ξ f (RingHom.id Ω) ↔ ξ' ≫ f = ξ := by
  unfold Dominates
  rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id, Category.id_comp]

theorem mem_ctrSet_self {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (p : Cpt M.ξ) : p ∈ ctrSet o x (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  exact ⟨c, hc.1, fun a ha => (GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).1 a ha⟩

theorem mem_ctrSet_join {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {κ' : Type} {w : κ' → Ω} (p : Cpt M.ξ) (hw : ∃ l, InChart M.ξ w l p) :
    p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨l, hl⟩ := hw
  refine ⟨(c, l), mul_ne_zero hc.1 hl.1, fun a ha => ?_⟩
  change a ∈ regAt M.ξ p
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨j, m⟩, rfl⟩ := hy
    have e : joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
        (x j / x c) * (w m / w l) := by
      simp only [joinCo, RingHom.id_apply]
      rw [mul_div_mul_comm]
    beta_reduce
    rw [e]
    exact mul_mem (hc.2 j) (hl.2 m)
  | algebraMap r =>
    exact (GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).1 _ (Subalgebra.algebraMap_mem _ r)
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem coordTie_join_of_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω),
    (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  intro o _ Ω _ _ κ _ x M κ' _ w hw
  have hl : ∃ l, w l ≠ 0 := by
    obtain ⟨l, h⟩ := hw ⟨genPt M.ξ, specializes_rfl⟩
    exact ⟨l, h.1⟩
  obtain ⟨M', f, hf⟩ := GlobalTheory.T.exists_join_model_dominates o Ω κ x M Ω (RingHom.id Ω) κ' w (fun _ => rfl) hl
    (eq_top_iff.2 fun a _ => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_dominating_map o Ω (κ × κ') _ M' o Ω κ x M (RingHom.id Ω)
    (fun p => mem_ctrSet_join M p (hw p))
  rw [dominates_id_iff] at hf hg
  have u1 := GlobalTheory.T.existsUnique_dominating_map o Ω κ x M o Ω κ x M (RingHom.id Ω) (mem_ctrSet_self M)
  have u2 := GlobalTheory.T.existsUnique_dominating_map o Ω (κ × κ') _ M' o Ω (κ × κ') _ M' (RingHom.id Ω) (mem_ctrSet_self M')
  have e1 : g ≫ f = 𝟙 _ := u1.unique (dominates_id_iff.2 (by rw [← Category.assoc, hg, hf]))
    (dominates_id_iff.2 (Category.comp_id _))
  have e2 : f ≫ g = 𝟙 _ := u2.unique (dominates_id_iff.2 (by rw [← Category.assoc, hf, hg]))
    (dominates_id_iff.2 (Category.comp_id _))
  haveI : IsIso f := ⟨g, e2, e1⟩
  have := coordTie_comp_iso M'.ξ f M'.tie
  rwa [hf] at this

end GlobalTheory.CompanionTheory.Ar.Retie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTieStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_coords_coordTie : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω), (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | exact GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBasisExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBasisExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem dual_pull : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (r : ℕ) (b : Fin r → Module.Dual Ω W), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (0 < r → ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V)))) → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = ⊤ → ω.map (W.dualRestrict.restrictScalars R) = Submodule.span R (Set.range b) → Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j jd W W' ω ω' r b hj hR hjd hW' hω' hli hsp hmap
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hD : ∀ f : Module.Dual Ω W, f = 0 := by
      intro f
      have hf : f ∈ Submodule.span Ω (Set.range b) := hsp ▸ Submodule.mem_top
      rw [Set.range_eq_empty, Submodule.span_empty] at hf
      exact (Submodule.mem_bot Ω).1 hf
    have hW0 : ∀ e ∈ W, e = 0 := by
      intro e he
      have : (⟨e, he⟩ : W) = 0 :=
        (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => by rw [hD f]; rfl
      exact congrArg Subtype.val this
    have hW'0 : W' = ⊥ := by
      rw [hW', Submodule.span_eq_bot]
      rintro _ ⟨e, he, rfl⟩
      rw [hW0 e he, map_zero]
    have hS0 : Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} = ⊥ :=
      Submodule.span_eq_bot.2 fun e he => hW0 e he.1
    rw [hS0, Submodule.span_eq_bot.2, Submodule.span_eq_bot.2]
    · rintro _ ⟨e, he, rfl⟩
      have : e = 0 := by simpa using he
      rw [this, map_zero]
    · rintro e ⟨he, -⟩
      rw [hW'0] at he
      exact (Submodule.mem_bot Ω').1 he
  have hω'' := hω' hr
  let hb : Module.Basis (Fin r) Ω (Module.Dual Ω W) := Module.Basis.mk hli hsp.ge
  have hbb : ∀ k, hb k = b k := fun k => Module.Basis.mk_apply hli hsp.ge k
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis hb
  haveI : Module.Finite Ω W := Module.finite_dual_iff Ω |>.1 inferInstance
  let c : Module.Basis (Fin r) Ω W := hb.dualBasis.map (Module.evalEquiv Ω W).symm
  have hbc : ∀ l k, b l (c k) = if l = k then 1 else 0 := by
    intro l k
    have h1 : c k = (Module.evalEquiv Ω W).symm (hb.dualBasis k) := by
      simp [c]
    rw [h1, Module.apply_evalEquiv_symm_apply, ← hbb, Module.Basis.dualBasis_apply_self]

  have hexp : ∀ e : W, e = ∑ k, b k e • c k := by
    intro e
    conv_lhs => rw [← c.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : b k e = ∑ m, c.repr e m * b k (c m) := by
      calc b k e = b k (∑ m, c.repr e m • c m) := by rw [c.sum_repr]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    simp [hbc]

  have hcS : ∀ k, (c k : V) ∈ {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} := by
    intro k
    refine ⟨(c k).2, fun w hw => ?_⟩
    have hwr : W.dualRestrict w ∈ Submodule.span R (Set.range b) := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    have key : ∀ f ∈ Submodule.span R (Set.range b), f (c k) ∈ R := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        rw [hbc]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      | zero => simpa using R.zero_mem
      | add x y _ _ hx hy => simpa using R.add_mem hx hy
      | smul a x _ hx =>
        have : (a • x) (c k) = (a : Ω) * x (c k) := rfl
        rw [this]
        exact R.mul_mem a.2 hx
    exact key _ hwr

  have hpick : ∀ l, ∃ w ∈ ω, W.dualRestrict w = b l := by
    intro l
    have : b l ∈ ω.map (W.dualRestrict.restrictScalars R) := by
      rw [hmap]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨w, hw, hwb⟩ := this
    exact ⟨w, hw, hwb⟩
  choose wl hwl hwb using hpick
  have hspan : ∀ e' ∈ W', ∃ a : Fin r → Ω', e' = ∑ k, a k • j (c k : V) := by
    intro e' he'
    have hle : W' ≤ Submodule.span Ω' (Set.range fun k => j (c k : V)) := by
      rw [hW', Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      have h1 : e = ∑ k, b k ⟨e, he⟩ • (c k : V) := by
        have := congrArg (Subtype.val) (hexp ⟨e, he⟩)
        simpa using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [SetLike.mem_coe, h1, map_sum]
      refine sum_mem fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω').1 (hle he')
    exact ⟨a, ha.symm⟩
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨he', hint⟩
    obtain ⟨a, rfl⟩ := hspan e' he'
    have hal : ∀ l, a l ∈ R' := by
      intro l
      have h1 := hint (jd (wl l)) (by
        rw [hω'']
        exact Submodule.subset_span ⟨wl l, hwl l, rfl⟩)
      have h2 : jd (wl l) (∑ k, a k • j (c k : V)) = a l := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        have : ∀ k, jd (wl l) (a k • j (c k : V)) = a k * (if l = k then 1 else 0) := by
          intro k
          have h3 : wl l (c k : V) = if l = k then 1 else 0 := by
            rw [← hbc, ← hwb]
            simp [Submodule.dualRestrict_apply]
          rw [map_smul, hjd, smul_eq_mul, h3, apply_ite i, map_one, map_zero]
        simp [this]
      rwa [h2] at h1
    rw [SetLike.mem_coe]
    refine sum_mem fun k _ => ?_
    have : a k • j (c k : V) = (⟨a k, hal k⟩ : R') • j (c k : V) := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨(c k : V), Submodule.subset_span (hcS k), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun w hw => ?_⟩
      · rw [hW']
        exact Submodule.subset_span ⟨x, hx.1, rfl⟩
      · rw [hω''] at hw
        induction hw using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨u, hu, rfl⟩ := hf
          rw [hjd]
          exact hR _ (hx.2 u hu)
        | zero => simpa using R'.zero_mem
        | add f g _ _ hf hg => simpa using R'.add_mem hf hg
        | smul a f _ hf =>
          have : (a • f) (j x) = (a : Ω') * f (j x) := rfl
          rw [this]
          exact R'.mul_mem a.2 hf
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : j (a • x) = (⟨i a, hR a a.2⟩ : R') • j x := hj.1 (a : Ω) x
      rw [this]
      exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.Ar.HcptPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBasisExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_basis_extension : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (r : ℕ) (b : Fin r → Module.Dual Ω W), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (0 < r → ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V)))) → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = ⊤ → ω.map (W.dualRestrict.restrictScalars R) = Submodule.span R (Set.range b) → Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptPull.dual_pull | exact GlobalTheory.CompanionTheory.Ar.HcptPull.dual_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptPull.dual_pull <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnQuotientOfDifferentiableOnSlice
open Filter Metric Set
open scoped Topology

namespace GlobalTheory

theorem exists_circle_ne_zero_of_frequently_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {g : E → ℂ} {z₀ : E} (hS : S ∈ 𝓝 z₀)
    (hg : DifferentiableOn ℂ g S) (hfr : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ (v : E) (r : ℝ), 0 < r ∧ (∀ t ∈ closedBall (0 : ℂ) r, z₀ + t • v ∈ S) ∧
      ∀ t ∈ sphere (0 : ℂ) r, g (z₀ + t • v) ≠ 0 := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.1 hS
  obtain ⟨z₁, hz₁, hz₁b⟩ := (hfr.and_eventually (ball_mem_nhds z₀ (half_pos hε))).exists
  have hv : ‖z₁ - z₀‖ < ε / 2 := by simpa [dist_eq_norm] using hz₁b
  have hmem : ∀ t ∈ ball (0 : ℂ) 2, z₀ + t • (z₁ - z₀) ∈ S := by
    intro t ht
    apply hεS
    rw [mem_ball_zero_iff] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg (z₁ - z₀)]
  have hd : DifferentiableOn ℂ (fun t : ℂ => g (z₀ + t • (z₁ - z₀))) (ball 0 2) :=
    hg.comp (f := fun t : ℂ => z₀ + t • (z₁ - z₀)) (by fun_prop) hmem
  have han := hd.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
  rcases (han 0 h0).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 2).isPreconnected
      h0 h (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by simp)
    exact absurd (by simpa using this) hz₁
  · rw [eventually_nhdsWithin_iff] at h
    obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1
      (h.and (ball_mem_nhds (0 : ℂ) two_pos))
    refine ⟨z₁ - z₀, r, hr, fun t ht => hmem t (hrs ht).2, fun t ht => ?_⟩
    refine (hrs (sphere_subset_closedBall ht)).1 ?_
    rintro rfl
    simp at ht
    exact hr.ne ht

theorem differentiableOn_quotient_of_differentiableOn_slice :
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V'))
      (f θ F : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W →
      (∀ w ∈ W, F w * θ w = f w) →
      (∀ b, DifferentiableOn ℂ (fun z => F (b, z)) {z | (b, z) ∈ W}) →
      (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1, z) ≠ 0) → DifferentiableOn ℂ F W := by
  intro V V' _ _ _ _ _ _ W f θ F hW hf hθ hF hsl hfr w hw
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) (hfr w hw)
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · have hEq : ∀ y ∈ U, F y = (2 * Real.pi)⁻¹ • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)) := by
      intro y hy
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (p y t)) (closedBall 0 r) :=
        (hsl y.1).comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (p y t)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def] at hav
      have : F y = F (p y 0) := by simp [p]
      rw [this, ← hav]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      rw [eq_div_iff ((hU y hy).2 _ hs), hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))]
    have hFU : DifferentiableOn ℂ F U := (hG.const_smul ((2 * Real.pi)⁻¹ : ℝ)).congr hEq
    exact (hFU.differentiableAt (hUo.mem_nhds hwU)).differentiableWithinAt
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupOfFinite
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.LevQuot

variable {X Y : Scheme.{0}}

theorem isOpenImmersion_graph (r : X ⟶ Y) [Etale r] (f : X ⟶ X) (h : 𝟙 X ≫ r = f ≫ r) :
    IsOpenImmersion (pullback.lift (𝟙 X) f h) := by
  have hpost : (@IsOpenImmersion : MorphismProperty Scheme.{0}).HasOfPostcompProperty
      (@Etale : MorphismProperty Scheme.{0}) := by
    refine MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr ?_
    intro A B u hu
    have : Etale u := hu
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal u))
  have hsec : IsOpenImmersion (pullback.lift (𝟙 X) f h ≫ pullback.fst r r) := by
    rw [pullback.lift_fst]
    infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) _ (pullback.fst r r)
    (inferInstance : Etale (pullback.fst r r)) hsec

theorem appLE_congr_hom {Z : Scheme.{0}} {f g : Z ⟶ X} (e : f = g) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  simp only [e]

theorem exists_geomPoint (Z : Scheme.{0}) (z : Z) : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k)
    (w : Spec (CommRingCat.of k) ⟶ Z) (p : Spec (CommRingCat.of k)), w p = z := by
  let K := AlgebraicClosure (Z.residueField z)
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z, p, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem invariant_descends (r : X ⟶ Y) [Etale r] [QuasiCompact r] [Surjective r] {Γ : Type} (ρ : Γ → (X ⟶ X))
    (hρ : ∀ g, ρ g ≫ r = r)
    (htr : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Spec (CommRingCat.of k) ⟶ X), y ≫ r = y' ≫ r →
      ∃ g, y' = y ≫ ρ g) (V : Y.Opens) :
    Function.Injective (r.app V).hom ∧ ∀ f : Γ(X, r ⁻¹ᵁ V),
      (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom := by
  have hcond : ∀ g, 𝟙 X ≫ r = ρ g ≫ r := fun g => by rw [Category.id_comp, hρ g]
  have hpb := IsPullback.of_hasPullback r r
  have hsame : ∀ x : ↥(pullback r r), r (pullback.snd r r x) = r (pullback.fst r r x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hgW : pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V ≤ pullback.snd r r ⁻¹ᵁ r ⁻¹ᵁ V := fun x hx => by
    change r (pullback.snd r r x) ∈ V
    rw [hsame]
    exact hx
  have hinvle : ∀ g, r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V) := fun g y hy => by
    change r (ρ g y) ∈ V
    rw [← Scheme.Hom.comp_apply, hρ g]
    exact hy
  have key := fun s => GlobalTheory.FlatDescent.existsUnique_app_eq_iff r hpb V
    (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) rfl le_rfl hgW s
  have hcompat : r.app V ≫ (pullback.fst r r).appLE _ _ le_rfl =
      r.app V ≫ (pullback.snd r r).appLE _ _ hgW :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans
      ((appLE_congr_hom pullback.condition _ _ _ _).trans (Scheme.Hom.comp_appLE _ _ _ _ _))
  constructor
  · intro a b hab
    obtain ⟨c, -, huniq⟩ := (key ((r.app V).hom a)).mpr (congrArg (fun φ => φ.hom a) hcompat)
    exact (huniq a rfl).trans (huniq b hab.symm).symm
  · intro f hinv
    refine ExistsUnique.exists ((key f).mpr ?_)
    apply TopCat.Presheaf.section_ext (pullback r r).sheaf
    intro x hx
    obtain ⟨k, _, _, w, pt, hw⟩ := exists_geomPoint (pullback r r) x
    obtain ⟨g, hg⟩ := htr k (w ≫ pullback.fst r r) (w ≫ pullback.snd r r)
      (by simp only [Category.assoc, pullback.condition])
    obtain ⟨ι, hιfst, hιsnd, hιop⟩ : ∃ ι : X ⟶ pullback r r,
        ι ≫ pullback.fst r r = 𝟙 X ∧ ι ≫ pullback.snd r r = ρ g ∧ IsOpenImmersion ι :=
      ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, isOpenImmersion_graph r (ρ g) (hcond g)⟩
    have hwι : w = (w ≫ pullback.fst r r) ≫ ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hιfst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, hιsnd, hg, Category.assoc]
    have hxι : x = ι ((w ≫ pullback.fst r r) pt) := by
      rw [← Scheme.Hom.comp_apply, ← hwι, hw]
    subst hxι
    have hfi : ∀ y, pullback.fst r r (ι y) = y := fun y => by
      rw [← Scheme.Hom.comp_apply, hιfst]
      rfl
    have hle : ι ⁻¹ᵁ (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) ≤ r ⁻¹ᵁ V := fun y hy => by
      change r (pullback.fst r r (ι y)) ∈ V at hy
      rw [hfi] at hy
      exact hy
    have e1 : (pullback.fst r r).appLE (r ⁻¹ᵁ V) _ le_rfl ≫ ι.app _ =
        X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hιfst _ _ _ hle]
      dsimp only [Scheme.Hom.appLE]
      rw [Scheme.Hom.id_app]
      exact Category.id_comp _
    have e2 : (pullback.snd r r).appLE (r ⁻¹ᵁ V) _ hgW ≫ ι.app _ =
        (ρ g).appLE (r ⁻¹ᵁ V) (r ⁻¹ᵁ V) (hinvle g) ≫ X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        appLE_congr_hom hιsnd _ _ _ (hle.trans (hinvle g)), Scheme.Hom.appLE_map]
    apply (ConcreteCategory.bijective_of_isIso (ι.stalkMap _)).1
    erw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    have h1 := congrArg (fun φ => φ.hom f) e1
    have h2 := congrArg (fun φ => φ.hom f) e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
    rw [hinv g (hinvle g)] at h2
    exact h1.trans h2.symm

def autOver (r : X ⟶ Y) : Subgroup (Aut X) where
  carrier := {ρ | ρ.asIso.hom ≫ r = r}
  mul_mem' := fun {a b} ha hb => by
    show (b.asIso.hom ≫ a.asIso.hom) ≫ r = r
    rw [Category.assoc, ha, hb]
  one_mem' := Category.id_comp _
  inv_mem' := fun {a} ha => by
    show a.asIso.inv ≫ r = r
    exact (Iso.inv_comp_eq a.asIso).2 (Eq.symm ha)

theorem exists_liftAut {P Q : Scheme.{0}} {φ : P ⟶ Q} {p : P ⟶ X} {q : Q ⟶ Y} {r : X ⟶ Y} (h : IsPullback φ p q r) :
    ∃ τ : autOver r →* Aut P, ∀ ω, (τ ω).asIso.hom ≫ φ = φ ∧ (τ ω).asIso.hom ≫ p = p ≫ ω.1.asIso.hom := by
  have hom_r : ∀ ω : autOver r, ω.1.asIso.hom ≫ r = r := fun ω => ω.2
  have inv_r : ∀ ω : autOver r, ω.1.asIso.inv ≫ r = r := fun ω => (Iso.inv_comp_eq ω.1.asIso).2 (hom_r ω).symm
  have sq : ∀ u : X ⟶ X, u ≫ r = r → φ ≫ q = (p ≫ u) ≫ r := fun u hu => by
    rw [Category.assoc, hu, h.w]
  have back : ∀ (u v : X ⟶ X) (hu : u ≫ r = r) (hv : v ≫ r = r), u ≫ v = 𝟙 X →
      h.lift φ (p ≫ u) (sq u hu) ≫ h.lift φ (p ≫ v) (sq v hv) = 𝟙 P := fun u v hu hv huv => by
    apply h.hom_ext
    · simp
    · simp only [Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc, huv, Category.comp_id,
        Category.id_comp]
  let lift1 : autOver r → Aut P := fun ω =>
    Aut.of ⟨h.lift φ (p ≫ ω.1.asIso.hom) (sq _ (hom_r ω)),
      h.lift φ (p ≫ ω.1.asIso.inv) (sq _ (inv_r ω)),
      back _ _ (hom_r ω) (inv_r ω) ω.1.asIso.hom_inv_id,
      back _ _ (inv_r ω) (hom_r ω) ω.1.asIso.inv_hom_id⟩
  refine ⟨{ toFun := lift1, map_one' := ?_, map_mul' := ?_ }, fun ω => ⟨h.lift_fst _ _ _, h.lift_snd _ _ _⟩⟩
  · ext1
    ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = 𝟙 P ≫ φ
      rw [IsPullback.lift_fst, Category.id_comp]
    · change h.lift _ _ _ ≫ p = 𝟙 P ≫ p
      rw [IsPullback.lift_snd, Category.id_comp]
      exact Category.comp_id p
  · intro a b
    ext1
    ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = (h.lift φ (p ≫ b.1.asIso.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.asIso.hom) (sq _ (hom_r a))) ≫ φ
      simp only [IsPullback.lift_fst, Category.assoc]
    · change h.lift _ _ _ ≫ p = (h.lift φ (p ≫ b.1.asIso.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.asIso.hom) (sq _ (hom_r a))) ≫ p
      simp only [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd_assoc]
      rfl

theorem exists_subgroup_of_finite {G : Type} [Group G] (S : Submonoid G) [Finite S] :
    ∃ T : Subgroup G, ∀ g, g ∈ T ↔ g ∈ S := by
  refine ⟨{ S with inv_mem' := fun {x} hx => ?_ }, fun _ => Iff.rfl⟩
  have hx' : IsOfFinOrder x := by
    by_contra hne
    have hinj := injective_pow_iff_not_isOfFinOrder.mpr hne
    exact not_injective_infinite_finite (fun n : ℕ => (⟨x ^ n, S.pow_mem hx n⟩ : S))
      (fun a b hab => hinj (congrArg Subtype.val hab))
  obtain ⟨n, hn⟩ := hx'.mem_powers_iff_mem_zpowers.mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  rw [← hn]
  exact S.pow_mem hx n

end GlobalTheory.LevQuot
end

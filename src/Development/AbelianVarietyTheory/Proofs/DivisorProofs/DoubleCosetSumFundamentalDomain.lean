module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
open MeasureTheory

namespace GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)


omit [μ.IsMulLeftInvariant] [Countable Γ] in
theorem isFundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) ⁻¹' 𝓕) μ :=
  h𝓕.preimage_of_equiv (measurePreserving_mul_right μ y).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g h => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])

omit [μ.IsMulLeftInvariant] [Countable Γ] [μ.IsMulRightInvariant] [TopologicalSpace H]
  [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] in
theorem preimage_preimage_mul (y : H) :
    (fun h => h * y) ⁻¹' ((fun h => h * y⁻¹) ⁻¹' 𝓕) = 𝓕 := by
  ext h; simp

theorem setIntegral_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  have h1 := (measurePreserving_mul_right μ y).setIntegral_preimage_emb
    (measurableEmbedding_mulRight y) u ((fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  rw [h1]
  exact (isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).setIntegral_eq h𝓕
    (fun g h => hu g g.2 h)

theorem integrableOn_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  have h1 := (measurePreserving_mul_right μ y).integrableOn_comp_preimage
    (measurableEmbedding_mulRight y) (f := u) (s := (fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  refine h1.2 ?_
  exact ((isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).integrableOn_iff h𝓕
    (fun g h => hu g g.2 h)).2 hi


omit [Group H] [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
theorem integrableOn_star_mul (F F' : H → ℂ) (hF : Continuous F) (hF' : Continuous F')
    (h1 : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ)
    (h2 : IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ) :
    IntegrableOn (fun h => star (F h) * F' h) 𝓕 μ := by
  refine Integrable.mono' (h1.norm.add h2.norm)
    (hF.star.mul hF').aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  simp only [Pi.add_apply, norm_mul, norm_star]
  nlinarith [sq_nonneg (‖F h‖ - ‖F' h‖), mul_nonneg (norm_nonneg (F h)) (norm_nonneg (F' h))]

end GlobalTheory.DoubleCosetAdjoint


open GlobalTheory.DoubleCosetAdjoint in
theorem GlobalTheory.doubleCosetSum_adjoint : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  intro H _ _ _ _ _ μ _ _ Γ K _ 𝓕 x A A' F F' h𝓕 hA hA' hc cF cF' lF lF' rF rF' iF iF'
  set u : H → ℂ := fun h => star (F (h * x)) * F' h with hu
  have lu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h := by
    intro γ hγ h
    simp only [hu, mul_assoc, lF γ hγ, lF' γ hγ]
  have iu : IntegrableOn u 𝓕 μ := by
    refine integrableOn_star_mul μ 𝓕 (fun h => F (h * x)) F'
      (cF.comp (continuous_mul_const x)) cF' ?_ iF'
    exact integrableOn_mul_right μ Γ 𝓕 h𝓕 (fun h => star (F h) * F h)
      (fun γ hγ h => by simp only [lF γ hγ]) x iF
  have eA : ∀ a ∈ A, ∃ y, ∀ h, star (F (h * a)) * F' h = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF k₂ hk₂, rF' k₁ hk₁]
  have eA' : ∀ a ∈ A', ∃ y, ∀ h, star (F h) * F' (h * a) = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF' k₂ hk₂, inv_mul_cancel_right, rF k₁ hk₁]
  have key : ∀ (B : Finset H) (t : H → H → ℂ), (∀ a ∈ B, ∃ y, ∀ h, t a h = u (h * y)) →
      ∫ h in 𝓕, ∑ a ∈ B, t a h ∂μ = B.card • ∫ h in 𝓕, u h ∂μ := by
    intro B t ht
    rw [MeasureTheory.integral_finsetSum, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨y, hy⟩ := ht a ha
      simp only [hy]
      exact setIntegral_mul_right μ Γ 𝓕 h𝓕 u lu y
    · intro a ha
      obtain ⟨y, hy⟩ := ht a ha
      have : t a = fun h => u (h * y) := funext hy
      rw [this]
      exact integrableOn_mul_right μ Γ 𝓕 h𝓕 u lu y iu
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [key A (fun a h => star (F (h * a)) * F' h) eA,
    key A' (fun a h => star (F h) * F' (h * a)) eA', hc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYoneda
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYoneda
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SpecWidePullback

noncomputable def specHomEquiv (X : Scheme.{0}) (R : CommRingCat.{0}) :
    (R ⟶ Γ(X, ⊤)) ≃ (X ⟶ Spec R) where
  toFun φ := ΓSpec.adjunction.homEquiv X (op R) (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op)
  invFun y := ((ΓSpec.adjunction.homEquiv X (op R)).symm y).unop
  left_inv φ := congrArg Quiver.Hom.unop (Equiv.symm_apply_apply (ΓSpec.adjunction.homEquiv X (op R))
    (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op))
  right_inv y := Equiv.apply_symm_apply (ΓSpec.adjunction.homEquiv X (op R)) y

theorem specHomEquiv_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (ψ : R' ⟶ R) (φ : R ⟶ Γ(X, ⊤)) :
    specHomEquiv X R' (ψ ≫ φ) = specHomEquiv X R φ ≫ Spec.map ψ := by
  exact ΓSpec.adjunction.homEquiv_naturality_right (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op) ψ.op

theorem specHomEquiv_symm_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (y : X ⟶ Spec R) (ψ : R' ⟶ R) :
    (specHomEquiv X R').symm (y ≫ Spec.map ψ) = ψ ≫ (specHomEquiv X R).symm y := by
  rw [Equiv.symm_apply_eq, specHomEquiv_comp, Equiv.apply_symm_apply]

theorem existsUnique_lift {A B T : Type} [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) {k : ℕ}
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (X : Scheme.{0}) (y : Fin (k + 1) → (X ⟶ Spec (CommRingCat.of B)))
    (hy : ∀ j, y j ≫ Spec.map (CommRingCat.ofHom a) = y 0 ≫ Spec.map (CommRingCat.ofHom a)) :
    ∃! m : X ⟶ Spec (CommRingCat.of T), ∀ j, m ≫ Spec.map (CommRingCat.ofHom (ι j)) = y j := by
  let g : Fin (k + 1) → (B →+* Γ(X, ⊤)) := fun j => ((specHomEquiv X _).symm (y j)).hom
  have hg : ∀ j, (g j).comp a = (g 0).comp a := fun j => by
    have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of A)).symm z).hom) (hy j)
    simpa [g, specHomEquiv_symm_comp] using this
  obtain ⟨φ, hφ, huniq⟩ := hu Γ(X, ⊤) g hg
  refine ⟨specHomEquiv X _ (CommRingCat.ofHom φ), fun j => ?_, fun m hm => ?_⟩
  · rw [← specHomEquiv_comp, Equiv.apply_eq_iff_eq_symm_apply]
    exact CommRingCat.hom_ext (hφ j)
  · have h1 : ((specHomEquiv X _).symm m).hom = φ := huniq _ fun j => by
      have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of B)).symm z).hom) (hm j)
      simpa [g, specHomEquiv_symm_comp] using this
    rw [← h1]
    simp

end GlobalTheory.SpecWidePullback

namespace GlobalTheory.SpecWidePullback

theorem yoneda_spec_isoWidePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B)
    (k : ℕ) (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  have hleg : ∀ j, Spec.map (CommRingCat.ofHom (ι j)) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom ((ι 0).comp a)) := fun j => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hι j]
  let c : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
      (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a)))) :=
    WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom ((ι 0).comp a))))
      (fun j => yoneda.map (Spec.map (CommRingCat.ofHom (ι j))))
      (fun j => by
        change yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) ≫ yoneda.map (Spec.map (CommRingCat.ofHom a)) = _
        rw [← yoneda.map_comp, hleg j])
  have hc : IsLimit c := by
    apply evaluationJointlyReflectsLimits
    intro U
    have hw : ∀ (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) j,
        s.π.app (some j) x ≫ Spec.map (CommRingCat.ofHom a) = s.π.app none x := fun s x j =>
      ConcreteCategory.congr_hom (s.w (WidePullbackShape.Hom.term j)) x
    have H := fun (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) =>
      existsUnique_lift a ι hu (unop U) (fun j => s.π.app (some j) x)
        (fun j => (hw s x j).trans (hw s x 0).symm)
    refine IsLimit.mk (fun s => TypeCat.ofHom (fun x => (H s x).exists.choose)) (fun s j => ?_) (fun s m hm => ?_)
    · ext x
      rcases j with _ | j
      · change (H s x).exists.choose ≫ Spec.map (CommRingCat.ofHom ((ι 0).comp a)) = s.π.app none x
        rw [← hleg 0, ← Category.assoc, (H s x).exists.choose_spec 0, hw]
      · exact (H s x).exists.choose_spec j
    · ext x
      refine (H s x).unique (fun j => ?_) (H s x).exists.choose_spec
      have h := ConcreteCategory.congr_hom (hm (some j)) x
      rw [ConcreteCategory.comp_apply] at h
      exact h
  exact ⟨hc.conePointUniqueUpToIso (limit.isLimit _), fun j =>
    hc.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)⟩

end GlobalTheory.SpecWidePullback
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYonedaStatement
open CategoryTheory Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda : ∀ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ) (ι : Fin (k + 1) → (B →+* T)), (∀ j, (ι j).comp a = (ι 0).comp a) → (∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) → ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A))) (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))), ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  first | (exact @GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (exact GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (intros; apply GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallEqOfIntegralDvr
namespace GlobalTheory

theorem unitBall_eq_of_integral_dvr (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [IsLocalHom (algebraMap V W)]
    (hinj : Function.Injective (algebraMap V W))
    (κ : FractionRing V →+* PadicAlgCl p) (κ' : FractionRing W →+* PadicAlgCl p)
    (hc : ∀ v : V, κ' (algebraMap W (FractionRing W) (algebraMap V W v)) =
      κ (algebraMap V (FractionRing V) v))
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  classical
  have hW1 : ∀ w : W, ‖κ' (algebraMap W (FractionRing W) w)‖ ≤ 1 := by
    intro w
    let vP : Valuation (PadicAlgCl p) NNReal := Valued.v
    have hmem : ∀ a : V, κ (algebraMap V (FractionRing V) a) ∈ vP.integer := by
      intro a
      rw [Valuation.mem_integer_iff]
      show ‖κ (algebraMap V (FractionRing V) a)‖₊ ≤ 1
      exact NNReal.coe_le_coe.1 (by simpa using (hV _).2 ⟨a, rfl⟩)
    let ψ : V →+* vP.integer :=
      (κ.comp (algebraMap V (FractionRing V))).codRestrict vP.integer hmem
    obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := V) w
    have hint : IsIntegral vP.integer (κ' (algebraMap W (FractionRing W) w)) := by
      refine ⟨q.map ψ, hqm.map ψ, ?_⟩
      have hcomp : (algebraMap vP.integer (PadicAlgCl p)).comp ψ =
          (κ'.comp (algebraMap W (FractionRing W))).comp (algebraMap V W) :=
        RingHom.ext fun a => (hc a).symm
      rw [Polynomial.eval₂_map, hcomp]
      have h0 : (κ'.comp (algebraMap W (FractionRing W))) (q.eval₂ (algebraMap V W) w) = 0 := by
        rw [hq, map_zero]
      exact (Polynomial.hom_eval₂ q (algebraMap V W) _ w).symm.trans h0
    have h1 := (Valuation.integer.integers vP).mem_of_integral hint
    rw [Valuation.mem_integer_iff] at h1
    have h2 : ‖κ' (algebraMap W (FractionRing W) w)‖₊ ≤ 1 := h1
    have h3 : ((‖κ' (algebraMap W (FractionRing W) w)‖₊ : NNReal) : ℝ) ≤ 1 := by exact_mod_cast h2
    simpa using h3
  have hunit : ∀ u : Wˣ, ‖κ' (algebraMap W (FractionRing W) u)‖ = 1 := by
    intro u
    have hm : ‖κ' (algebraMap W (FractionRing W) u)‖ *
        ‖κ' (algebraMap W (FractionRing W) ↑u⁻¹)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have ha := hW1 u
    have hb := hW1 ↑u⁻¹
    refine le_antisymm ha ?_
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (κ' (algebraMap W (FractionRing W) u)))]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπK0 : algebraMap V (FractionRing V) π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm)
  have hπ1 : ‖κ (algebraMap V (FractionRing V) π)‖ < 1 := by
    refine lt_of_le_of_ne ((hV _).2 ⟨π, rfl⟩) fun h => hπ.not_isUnit ?_
    have hinv : ‖κ (algebraMap V (FractionRing V) π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hinv
    refine isUnit_iff_exists_inv.2 ⟨a, IsFractionRing.injective V (FractionRing V) ?_⟩
    rw [map_mul, ha, mul_inv_cancel₀ hπK0, map_one]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hϖ1 : ‖κ' (algebraMap W (FractionRing W) ϖ)‖ < 1 := by
    have hπW0 : algebraMap V W π ≠ 0 := fun h =>
      hπ.ne_zero (hinj (h.trans (map_zero _).symm))
    obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπW0 hϖ
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at he
      exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap V W) π (he ▸ u.isUnit))
    have hnorm : ‖κ' (algebraMap W (FractionRing W) ϖ)‖ ^ e < 1 := by
      have h := congrArg norm (hc π)
      rw [he, map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow, hunit, one_mul] at h
      rw [← h] at hπ1
      exact hπ1
    by_contra hge
    exact absurd hnorm (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))
  intro x
  constructor
  · intro hx
    by_contra hxW
    rcases ValuationRing.isInteger_or_isInteger W x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact hxW ⟨a, ha⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxW ⟨0, map_zero _⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact hx0 (inv_eq_zero.1 ha.symm)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hn
      apply hxW
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap W (FractionRing W) ↑u * algebraMap W (FractionRing W) ↑u⁻¹ = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [eq_inv_of_mul_eq_one_right h1, ← hn, ha, inv_inv]
    have hsmall : ‖κ' x⁻¹‖ < 1 := by
      rw [← ha, hn, map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow, hunit, one_mul]
      exact pow_lt_one₀ (norm_nonneg _) hϖ1 hn0
    have hprod : ‖κ' x‖ * ‖κ' x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h0 := norm_nonneg (κ' x⁻¹)
    nlinarith
  · rintro ⟨w, rfl⟩
    exact hW1 w

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpoly
open Matrix Polynomial

namespace GlobalTheory

open Matrix Polynomial in
private theorem exists_eigenvector_of_isRoot_charpoly {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (r : L) (h : y.charpoly.IsRoot r) :
    ∃ v : Fin n → L, v ≠ 0 ∧ y *ᵥ v = r • v := by
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff] at h
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at hv
  exact hv.symm

open Matrix Polynomial in
private theorem isUnit_of_eigenvector_columns_of_injective {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (μ : Fin n → L) (hμ : Function.Injective μ)
    (v : Fin n → Fin n → L) (hv0 : ∀ j, v j ≠ 0) (hv : ∀ j, y *ᵥ v j = μ j • v j) :
    IsUnit (Matrix.of fun i j => v j i) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact Module.End.eigenvectors_linearIndependent' (Matrix.toLin' y) μ hμ v
    (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hv j), hv0 j⟩)

open Matrix Polynomial in
private theorem eq_diagonal_of_commute_diagonal_injective {L : Type} [Field L] {n : ℕ}
    (μ : Fin n → L) (hμ : Function.Injective μ) (m : Matrix (Fin n) (Fin n) L)
    (hm : m * diagonal μ = diagonal μ * m) : m = diagonal fun i => m i i := by
  ext i j
  have hij := congrFun (congrFun hm i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    have hne : μ j - μ i ≠ 0 := sub_ne_zero.mpr fun e => h (hμ e).symm
    have : m i j * (μ j - μ i) = 0 := by rw [mul_sub, hij, mul_comm]; ring
    exact (mul_eq_zero.mp this).resolve_right hne

open Matrix Polynomial in
private theorem commute_of_commute_of_charpoly_separable_of_isAlgClosed {L : Type} [Field L]
    [IsAlgClosed L] {n : ℕ} (y a b : Matrix (Fin n) (Fin n) L) (hy : y.charpoly.Separable)
    (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  classical
  set s := y.charpoly.roots.toFinset with hs_def
  have hs : s.card = n := by
    rw [hs_def, Multiset.toFinset_card_of_nodup (nodup_roots hy),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let μ : Fin n → L := fun i => (e i : L)
  have hμ : Function.Injective μ := fun i j hij => e.injective (Subtype.ext hij)
  have hroot : ∀ i, y.charpoly.IsRoot (μ i) := fun i => by
    have hmem : (μ i) ∈ s := (e i).2
    rw [hs_def, Multiset.mem_toFinset] at hmem
    exact (mem_roots hy.ne_zero).mp hmem
  choose v hv0 hv using fun i => exists_eigenvector_of_isRoot_charpoly y (μ i) (hroot i)
  set P : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => v j i with hP
  have hPu : IsUnit P := isUnit_of_eigenvector_columns_of_injective y μ hμ v hv0 hv
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  set Q := P⁻¹ with hQ
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPQ' : ∀ X : Matrix (Fin n) (Fin n) L, P * (Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hQP' : ∀ X : Matrix (Fin n) (Fin n) L, Q * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hyP : y * P = P * diagonal μ := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (hv j) i
    simpa [hP, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  have hD : Q * y * P = diagonal μ := by
    rw [Matrix.mul_assoc, hyP, hQP']
  have hcomm : ∀ m : Matrix (Fin n) (Fin n) L, m * y = y * m →
      (Q * m * P) * diagonal μ = diagonal μ * (Q * m * P) := fun m hm => by
    rw [← hD]
    simp only [Matrix.mul_assoc, hPQ']
    rw [← Matrix.mul_assoc m y P, hm, Matrix.mul_assoc]
  have hA := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm a ha)
  have hB := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm b hb)
  have hAB : (Q * a * P) * (Q * b * P) = (Q * b * P) * (Q * a * P) := by
    rw [hA, hB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have key : ∀ c d : Matrix (Fin n) (Fin n) L, c * d = P * ((Q * c * P) * (Q * d * P)) * Q :=
    fun c d => by
      simp only [Matrix.mul_assoc, hPQ', hPQ, Matrix.mul_one]
  rw [key a b, key b a, hAB]


open Matrix Polynomial in
theorem _root_.GlobalTheory.commute_of_commute_separable_charpoly :
    ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable →
      a * y = y * a → b * y = y * b → a * b = b * a := by
  intro K _ n y a b hy ha hb
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hyL : (y.map f).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hy.map
  have haL : a.map f * y.map f = y.map f * a.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ha]
  have hbL : b.map f * y.map f = y.map f * b.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hb]
  have h := commute_of_commute_of_charpoly_separable_of_isAlgClosed _ _ _ hyL haL hbL
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h
  exact Matrix.map_injective f.injective h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleModelOfIsColimit
open IsLocalRing CategoryTheory Limits

namespace GlobalTheory.EtaleDescent

open TensorProduct

theorem exists_etale_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (A : Type) [CommRing A] [Algebra c.pt A] [Algebra.Etale c.pt A], ∃ (j : J), (letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra; ∃ (Aj : Type) (_ : CommRing Aj) (_ : Algebra (D.obj j) Aj), Algebra.Etale (D.obj j) Aj ∧ Nonempty (TensorProduct (D.obj j) c.pt Aj ≃ₐ[c.pt] A)) := by
  intro J _ _ D c hc A _ _ _
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := c.pt) (S := A)).mp
      inferInstance |>.out

  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨D.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (D.obj j) A := ((algebraMap c.pt A).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (D.obj j) c.pt A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (D.obj j) := ⟨by rw [RingHom.coe_range]; exact hj⟩
  letI : Fintype σ := Fintype.ofFinite σ
  let P₀ := P.toPreSubmersivePresentation.ofHasCoeffs (D.obj j)
  have hP₀ : P₀.jacobian = Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs (D.obj j)) := by
    simp only [P₀]
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Algebra.SubmersivePresentation.jacobianOfHasCoeffs]
    rw [← Algebra.Generators.algebraMap_apply]
    rfl

  set E : MvPolynomial ι (D.obj j) :=
    ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i -
      (P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) - 1) with hEdef
  have hE : E.map (algebraMap (D.obj j) c.pt) = 0 := by
    simp [E, P.map_relationOfHasCoeffs, P.jacobianRelations_spec]

  have hdie : ∀ m : E.support, ∃ (k : J) (f : j ⟶ k), D.map f (E.coeff m) = 0 := by
    intro m
    have h0 : (c.ι.app j).hom (E.coeff m) = (c.ι.app j).hom 0 := by
      rw [map_zero]
      have := congr(($hE).coeff (m : ι →₀ ℕ))
      simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
      exact this
    obtain ⟨k, f, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' (E.coeff m) 0).1 (by exact h0)
    exact ⟨k, f, by simpa using e⟩
  choose k f hf using hdie
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j k f)
  set K := c'.pt
  set g : j ⟶ K := c'.ι.app none
  have hEK : E.map (D.map g).hom = 0 := by
    ext m
    rw [MvPolynomial.coeff_map]
    change (D.map g).hom (E.coeff m) = 0
    by_cases hm : m ∈ E.support
    · have hw := c'.w (WidePushoutShape.Hom.init ⟨m, hm⟩)
      have h3 : (D.map g).hom (E.coeff m) = (D.map ((WidePushoutShape.wideSpan j k f).map
          (WidePushoutShape.Hom.init ⟨m, hm⟩) ≫ c'.ι.app (some ⟨m, hm⟩))).hom (E.coeff m) := by
        rw [hw]
      rw [h3, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
      erw [hf ⟨m, hm⟩]
      exact map_zero _
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]

  letI : Algebra (D.obj j) (D.obj K) := (D.map g).hom.toAlgebra
  letI : Algebra (D.obj K) c.pt := (c.ι.app K).hom.toAlgebra
  haveI : IsScalarTower (D.obj j) (D.obj K) c.pt := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    change (c.ι.app j).hom x = (c.ι.app K).hom ((D.map g).hom x)
    rw [← c.w g]
    rfl)
  let M := P.ModelOfHasCoeffs (D.obj j)
  let Q := P₀.baseChange (D.obj K)
  let φ : MvPolynomial ι (D.obj j) →ₐ[D.obj j] D.obj K ⊗[D.obj j] M :=
    (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ _ _)
  have hφrel : ∀ i, φ (P.relationOfHasCoeffs (D.obj j) i) = 0 := by
    intro i
    change Algebra.TensorProduct.includeRight (Ideal.Quotient.mk _ (P.relationOfHasCoeffs (D.obj j) i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  have hφE : φ E = 0 := by
    rw [MvPolynomial.aeval_unique φ, MvPolynomial.aeval_def,
      IsScalarTower.algebraMap_eq (D.obj j) (D.obj K) (D.obj K ⊗[D.obj j] M),
      ← MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂ _ _ (E.map (D.map g).hom) = 0
    rw [hEK, MvPolynomial.eval₂_zero]
  have hQ : IsUnit Q.jacobian := by
    rw [Algebra.PreSubmersivePresentation.baseChange_jacobian, hP₀]
    refine IsUnit.of_mul_eq_one (φ (P.invJacobianOfHasCoeffs (D.obj j))) ?_
    have h1 : P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) =
        ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i
          - E + 1 := by
      rw [hEdef]; ring
    have h2 := congr(φ $h1)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_add (f := _), map_sub, map_sum, map_one, hφrel, mul_zero,
      Finset.sum_const_zero, hφE, sub_zero, zero_add] at h2
    exact h2
  let Q' : Algebra.SubmersivePresentation (D.obj K) (D.obj K ⊗[D.obj j] M) ι σ :=
    { toPreSubmersivePresentation := Q, jacobian_isUnit := hQ }
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (D.obj K) (D.obj K ⊗[D.obj j] M) :=
    Q'.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  refine ⟨K, D.obj K ⊗[D.obj j] M, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.cancelBaseChange (D.obj j) (D.obj K) c.pt c.pt M).trans
    (P.tensorModelOfHasCoeffsEquiv (D.obj j))

end GlobalTheory.EtaleDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsGroup
open TensorProduct WithConv

namespace GlobalTheory.HopfShear

variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]


open Algebra.TensorProduct Bialgebra HopfAlgebra in
@[reducible] noncomputable def pointsGroup : Group (WithConv (A →ₐ[R] X)) where
  __ := (inferInstance : Monoid (WithConv (A →ₐ[R] X)))
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)
  inv_mul_cancel f := by
    have H : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
    trans toConv <|
      ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
        (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (Bialgebra.comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp
      (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] X)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

attribute [local instance] pointsGroup

noncomputable def pre (f : B →ₐc[R] A) : WithConv (A →ₐ[R] X) →* WithConv (B →ₐ[R] X) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (x.ofConv.comp (f : B →ₐ[R] A))) fun x y => by
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]

noncomputable def post (h : X →ₐ[R] Y) : WithConv (A →ₐ[R] X) →* WithConv (A →ₐ[R] Y) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (h.comp x.ofConv)) fun x y => by
    rw [AlgHom.comp_convMul_distrib, toConv_ofConv]

theorem pre_apply (f : B →ₐc[R] A) (x : WithConv (A →ₐ[R] X)) (b : B) :
    (pre f x).ofConv b = x.ofConv (f b) := rfl

theorem conv_ext {x y : WithConv (A →ₐ[R] X)} (h : ∀ a, x.ofConv a = y.ofConv a) : x = y :=
  ofConv_injective (AlgHom.ext h)

theorem shear (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
    [HopfAlgebra R B] (f : B →ₐc[R] A) :
    Nonempty ((TensorProduct (AlgHom.range (f : B →ₐ[R] A)) A A) ≃ₗ[A]
      TensorProduct R A (A ⧸ Ideal.map (f : B →ₐ[R] A)
        (RingHom.ker (Bialgebra.counitAlgHom R B)))) := by
  set S := AlgHom.range (f : B →ₐ[R] A) with hS
  set I : Ideal A := Ideal.map (f : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) with hI
  let l : WithConv (A →ₐ[R] A ⊗[S] A) := toConv (IsScalarTower.toAlgHom R A (A ⊗[S] A))
  let r : WithConv (A →ₐ[R] A ⊗[S] A) :=
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).restrictScalars R)
  let l' : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) := toConv (IsScalarTower.toAlgHom R A _)
  let p : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) :=
    toConv ((Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).comp
      (Ideal.Quotient.mkₐ R I))
  have hl : ∀ a, l.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hr : ∀ a, r.ofConv a = 1 ⊗ₜ a := fun a => rfl
  have hl' : ∀ a, l'.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hp : ∀ a, p.ofConv a = 1 ⊗ₜ Ideal.Quotient.mk I a := fun a => rfl
  have hlr : pre f l = pre f r := conv_ext fun b => by
    rw [pre_apply, pre_apply, hl, hr]
    have := TensorProduct.smul_tmul (R := S) (⟨f b, ⟨b, rfl⟩⟩ : S) (1 : A) (1 : A)
    simpa [Subalgebra.smul_def] using this
  have hpf : pre f p = 1 := conv_ext fun b => by
    rw [pre_apply, hp]
    have hb : b - algebraMap R B (Coalgebra.counit b) ∈
        RingHom.ker (Bialgebra.counitAlgHom R B) := by
      simp [RingHom.mem_ker]
    have h1 : Ideal.Quotient.mk I (f b) = algebraMap R _ (Coalgebra.counit b) := by
      have h2 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem (f : B →ₐ[R] A) hb)
      rw [map_sub, map_sub, sub_eq_zero, AlgHom.commutes] at h2
      exact h2
    rw [h1]
    exact (Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).commutes _
  let g : A →ₐ[S] A ⊗[R] (A ⧸ I) :=
    { (l' * p).ofConv.toRingHom with
      commutes' := by
        rintro ⟨_, b, rfl⟩
        have h : pre f (l' * p) = pre f l' := by rw [map_mul, hpf, mul_one]
        have h2 : (l' * p).ofConv (f b) = f b ⊗ₜ 1 := congrArg (fun x => x.ofConv b) h
        exact h2 }
  let Φ : A ⊗[S] A →ₐ[A] A ⊗[R] (A ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) g fun _ _ => Commute.all _ _
  have hk : ∀ a ∈ I, (l⁻¹ * r).ofConv a = 0 := by
    have h : pre f (l⁻¹ * r) = 1 := by rw [map_mul, map_inv, hlr, inv_mul_cancel]
    have : I ≤ RingHom.ker (l⁻¹ * r).ofConv := by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      have h2 : (l⁻¹ * r).ofConv (f b) = algebraMap R _ (Coalgebra.counit b) :=
        congrArg (fun x => x.ofConv b) h
      have h3 : Coalgebra.counit (R := R) b = 0 := hb
      rw [h3, map_zero] at h2
      exact h2
    exact fun a ha => this ha
  let k : (A ⧸ I) →ₐ[R] A ⊗[S] A := Ideal.Quotient.liftₐ I (l⁻¹ * r).ofConv hk
  let Ψ : A ⊗[R] (A ⧸ I) →ₐ[A] A ⊗[S] A :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) k fun _ _ => Commute.all _ _
  have hΦl : post (Φ.restrictScalars R) l = l' := conv_ext fun a => Φ.commutes a
  have hΦr : post (Φ.restrictScalars R) r = l' * p := conv_ext fun a => by
    change Φ (1 ⊗ₜ a) = g a
    simp [Φ, ← Algebra.TensorProduct.one_def]
  have hΨl : post (Ψ.restrictScalars R) l' = l := conv_ext fun a => Ψ.commutes a
  have hΨp : post (Ψ.restrictScalars R) p = l⁻¹ * r := conv_ext fun a => by
    change Ψ (1 ⊗ₜ Ideal.Quotient.mk I a) = k (Ideal.Quotient.mk I a)
    simp [Ψ, ← Algebra.TensorProduct.one_def]
  have h1 : ∀ a, Φ (Ψ (p.ofConv a)) = p.ofConv a := fun a => by
    have h : post (Φ.restrictScalars R) (post (Ψ.restrictScalars R) p) = p := by
      rw [hΨp, map_mul, map_inv, hΦl, hΦr, inv_mul_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  have h2 : ∀ a, Ψ (Φ (r.ofConv a)) = r.ofConv a := fun a => by
    have h : post (Ψ.restrictScalars R) (post (Φ.restrictScalars R) r) = r := by
      rw [hΦr, map_mul, hΨl, hΨp, mul_inv_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  refine ⟨(AlgEquiv.ofAlgHom Φ Ψ ?_ ?_).toLinearEquiv⟩
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun c => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact h1 a
  · exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => h2 a)

end GlobalTheory.HopfShear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem finite_fibre_and_eq_of_specializes_of_isFinite :
    ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y,
      {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  intro Y Y' k hk y
  refine ⟨k.finite_preimage_singleton y, ?_⟩
  intro a b ha hb h
  have hd := (k.isDiscrete_preimage_singleton y).to_subtype
  have h' : (⟨a, ha⟩ : k ⁻¹' {y}) ⤳ ⟨b, hb⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCountLogConcavePrimePowers
open NumberField

namespace GlobalTheory

def killedBy {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) :
    AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha, neg_zero]

theorem card_eq_card_ker_mul_card_range {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverField
namespace GlobalTheory

theorem isReduced_of_smooth_over_field (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] : IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  by_contra h0
  obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal (Ideal.span {a}).annihilator fun h =>
    h0 ((one_smul A a).symm.trans ((Submodule.mem_annihilator_span_singleton a 1).1 (h ▸ Submodule.mem_top)))
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  have : IsReduced (TensorProduct P (FractionRing P) (Localization.Away f)) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing P) _
  have : IsReduced (Localization.Away f) := isReduced_of_injective _
    (Algebra.TensorProduct.includeRight_injective (A := FractionRing P) (IsFractionRing.injective P _))
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) a).1
    (ha.map (algebraMap A (Localization.Away f))).eq_zero
  exact hf (hp.isPrime.mem_of_pow_mem N (hI ((Submodule.mem_annihilator_span_singleton a _).2 hN)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntRingHomExtOfIsHausdorff
open Matrix Polynomial

namespace GlobalTheory

theorem padicInt_ringHom_ext_of_isHausdorff : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  (f g : ℤ_[p] →+* O), f = g := by
  intro p _ O _ hH f g
  ext z
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hH _ fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (p : ℤ_[p]) ^ n * w + (z.appr n : ℕ) := by rw [mul_comm, hw]; ring
  have key : f z - g z = (p : O) ^ n * (f w - g w) := by
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, mul_sub]
    abel
  rw [SModEq.zero, key, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyMulGaussianBounded
namespace GlobalTheory.PolynomialGaussianBounded

theorem poly_mul_gaussian_bounded :
    ∀ (c : ℝ), (0 : ℝ) < c → ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r →
      ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : ((1 : ℝ) + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    calc ((1 : ℝ) + r) ^ N ≤ (Real.exp r) ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp ((N : ℝ) * r) := by rw [← Real.exp_nat_mul]
  calc ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ)))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ (2 : ℕ))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := by
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (2 * c * r - N)]

end GlobalTheory.PolynomialGaussianBounded
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntEqFinrankRingOfIntegersMul
open NumberField

namespace GlobalTheory

open TensorProduct nonZeroDivisors in
theorem finrank_int_eq_finrank_ringOfIntegers_mul : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N], Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E := by
  intro E _ _ N _ _ _ _
  let g : N →ₗ[𝓞 E] E ⊗[𝓞 E] N := TensorProduct.mk (𝓞 E) E N 1
  have hb : IsBaseChange E g := TensorProduct.isBaseChange (𝓞 E) N E
  have h1 : Module.finrank E (E ⊗[𝓞 E] N) = Module.finrank (𝓞 E) N := hb.finrank_eq
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E := inferInstance
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) g :=
    (isLocalizedModule_iff_isBaseChange _ E g).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (g.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars ℤ⁰ g
  have h4 : Module.finrank ℤ (E ⊗[𝓞 E] N) = Module.finrank ℤ N :=
    IsLocalizedModule.finrank_eq ℤ⁰ (g.restrictScalars ℤ) le_rfl
  have h5 : Module.finrank ℚ (E ⊗[𝓞 E] N) = Module.finrank ℤ (E ⊗[𝓞 E] N) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  rw [← h4, ← h5, ← h1, mul_comm, Module.finrank_mul_finrank]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AlgConn

abbrev twoπ (O : Type) [CommRing O] : Spec (.of (O × O)) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))

abbrev fst1 (O : Type) [CommRing O] : Γ(Spec (.of (O × O)), ⊤) :=
  (Scheme.ΓSpecIso (.of (O × O))).inv.hom ((1, 0) : O × O)

theorem isProper_twoπ (O : Type) [CommRing O] : IsProper (twoπ O) := by
  haveI : IsFinite (twoπ O) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  infer_instance

theorem isClopen_basicOpen_specProdSelfFirstIdempotent (O : Type) [CommRing O] :
    IsClopen (((Spec (.of (O × O))).basicOpen (fst1 O) : (Spec (.of (O × O))).Opens) :
      Set (Spec (.of (O × O)))) := by
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.isClopen_iff.2 ⟨((1, 0) : O × O), by ext <;> simp [IsIdempotentElem], rfl⟩

end GlobalTheory.AlgConn
end
end

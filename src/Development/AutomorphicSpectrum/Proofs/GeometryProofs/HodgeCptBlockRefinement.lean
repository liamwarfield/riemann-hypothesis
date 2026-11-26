module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBlockRefinementLines
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinement
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem HodgeCpt.Flag.exists_recoord_rootLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)) (tie' : CoordTie ℤ 𝔐.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ ∀ r, (Fl.rootLat r).IsDegOn Set.univ y' (xdeg r) (e r) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl
  classical
  haveI : Fintype (CMType H) := Fintype.ofFinite _
  have hlin : ∀ s, LinearIndependent Ω (Fl.b s) := by
    intro s
    letI := 𝔐.fn.toAlgebra
    obtain ⟨_, _, _, _, _, h4, _⟩ := Fl.generic
    exact h4 s
  have hgr : ∀ s i, ((𝔐.V s).gr (Fl.b s) i).IsVBOn Set.univ 1 ⊤ := fun s i =>
    (Lat.IsFlagVBOn.isVBOn_gr_inter _ _ _ _ _ _ _ (Fl.b s) (hlin s) (Fl.sub s)).2.1 i
  have hroot : ∀ r, (Fl.rootLat r).IsVB 1 ⊤ := fun r =>
    (GlobalTheory.T.lattice_tensor_power_line_bundle _ _ _ Unit _ Set.univ (fun _ => hgr _ _) _).1
  obtain ⟨K', fK, J', fJ, y', κ, v, hκ, hv, tie', h⟩ :=
    GlobalTheory.T.exists_block_refinement_lines 𝔐.X Ω 𝔐.ξ K J y (CMType H × Fin (D.p + D.q)) Fl.rootLat 𝔐.tie hroot
  choose xdeg e hdeg using h
  exact ⟨K', fK, J', fJ, y', κ, v, tie', xdeg, e, hκ, hv, hdeg⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_block_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)) (tie' : CoordTie ℤ 𝔐.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ ∀ r, (Fl.rootLat r).IsDegOn Set.univ y' (xdeg r) (e r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines | exact GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Reindex

theorem coordTie_one_block (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ)
    (x : Fin (N + 1) → Ω) (h : CoordTie ℤ ξ x) :
    CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  have he : Function.Surjective (fun c' : Unit → Fin (N + 1) => c' ()) :=
    fun j => ⟨fun _ => j, rfl⟩
  have hfun : (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) =
      fun c' : Unit → Fin (N + 1) => x (c' ()) := by
    funext c'
    simp
  rw [hfun]
  have hc : ∀ (c : Unit → Fin (N + 1)) p,
      InChart ξ (fun c' : Unit → Fin (N + 1) => x (c' ())) c p ↔ InChart ξ x (c ()) p :=
    fun c p => and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (c ()) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    exact ⟨fun _ => c, (hc _ p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (c ()) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have hr : (Set.range fun j : Unit → Fin (N + 1) => x (j ()) / x (c ())) =
        Set.range fun j => x j / x (c ()) :=
      he.range_comp fun j => x j / x (c ())
    simpa only [hc, hr] using h.ring (c ()) h0 a

end GlobalTheory.CompanionTheory.Ar.SncBase.Reindex
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_single_block_segre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω), CoordTie ℤ ξ x → CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k => ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | exact GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantWeightGapShift
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantWeightGapShift
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.WtShift

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem ent_sub_smul (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) (i : ℕ) :
    ent (lam - s • nu) τ i = ent lam τ i - s * ent nu τ i := by
  simp only [ent]
  split_ifs <;> simp

theorem abs_ent_le (nu : Wt Ψ N) (τ : Ψ) (i : ℕ) : |ent nu τ i| ≤ ‖nu‖ := by
  simp only [ent]
  split_ifs with h
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (nu τ) _).trans (norm_le_pi_norm nu τ)
  · simp

theorem dominant_of_step (mu : Wt Ψ N)
    (h : ∀ τ (i : ℕ), i + 1 < N → ent mu τ (i + 1) ≤ ent mu τ i) : Dominant mu := by
  intro τ a b hab
  have key : ∀ k i, i + k < N → ent mu τ (i + k) ≤ ent mu τ i := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
      intro i hi
      exact (h τ (i + k) (by omega)).trans (ih i (by omega))
  have hab' : (a : ℕ) ≤ b := hab
  have hk := key ((b : ℕ) - a) a (by omega)
  rw [Nat.add_sub_cancel' hab'] at hk
  simpa [ent, a.2, b.2] using hk

theorem sub_small_dominant : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (nu : Wt Ψ N) (c₀ : ℝ), 1 ≤ j → j < N →
    0 < c₀ → ∃ θ₀ > (0 : ℝ), θ₀ ≤ 1 ∧ ∀ (lam : Wt Ψ N) (θ : ℝ), ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (∀ τ, θ ≤ gap j lam τ) →
      CompactGapsGE j c₀ lam → Dominant (lam - θ ^ 2 • nu) ∧ ‖lam - θ ^ 2 • nu‖ ≤ 2 ∧
        ∀ τ, θ / 2 ≤ gap j (lam - θ ^ 2 • nu) τ := by
  intro Ψ _ _ N j nu c₀ hj hjN hc₀
  have hM0 : 0 ≤ ‖nu‖ := norm_nonneg _
  refine ⟨min 1 (min (1 / (4 * (‖nu‖ + 1))) (c₀ / (2 * (‖nu‖ + 1)))), by positivity, min_le_left _ _, ?_⟩
  intro lam θ hlam hθ hθ₀ hgap hcg
  have hθ1 : θ ≤ 1 := hθ₀.trans (min_le_left _ _)
  have hA' : θ ≤ 1 / (4 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hB' : θ ≤ c₀ / (2 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA := (le_div_iff₀ (by positivity)).1 hA'
  have hB := (le_div_iff₀ (by positivity)).1 hB'
  have hθM : θ * ‖nu‖ ≤ 1 / 4 := by nlinarith
  have hθM' : θ * ‖nu‖ ≤ c₀ / 2 := by nlinarith
  have hdiff : ∀ τ i i', ent nu τ i - ent nu τ i' ≤ 2 * ‖nu‖ := fun τ i i' => by
    have h1 := abs_le.1 (abs_ent_le nu τ i)
    have h2 := abs_le.1 (abs_ent_le nu τ i')
    linarith [h1.2, h2.1]
  have hsq : θ ^ 2 * (2 * ‖nu‖) ≤ θ / 2 := by nlinarith
  have hsq2 : θ ^ 2 * (2 * ‖nu‖) ≤ c₀ := by nlinarith
  refine ⟨dominant_of_step _ fun τ i hi => ?_, ?_, fun τ => ?_⟩
  · rw [ent_sub_smul, ent_sub_smul]
    have hd := mul_le_mul_of_nonneg_left (hdiff τ i (i + 1)) (sq_nonneg θ)
    by_cases hij : i + 1 = j
    · subst hij
      have hg := hgap τ
      simp only [gap, Nat.add_sub_cancel] at hg
      nlinarith
    · have hc := hcg τ i hi hij
      nlinarith
  · calc ‖lam - θ ^ 2 • nu‖ ≤ ‖lam‖ + ‖θ ^ 2 • nu‖ := norm_sub_le _ _
      _ = ‖lam‖ + θ ^ 2 * ‖nu‖ := by rw [norm_smul, Real.norm_of_nonneg (sq_nonneg θ)]
      _ ≤ 2 := by nlinarith
  · have hg := hgap τ
    have hd := mul_le_mul_of_nonneg_left (hdiff τ (j - 1) j) (sq_nonneg θ)
    simp only [gap] at hg ⊢
    rw [ent_sub_smul, ent_sub_smul]
    nlinarith

end GlobalTheory.CompanionTheory.Ar.WtShift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantWeightGapShiftStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_weight_gap_shift : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (nu : Wt Ψ N) (c₀ : ℝ), 1 ≤ j → j < N → 0 < c₀ → ∃ θ₀ > (0 : ℝ), θ₀ ≤ 1 ∧ ∀ (lam : Wt Ψ N) (θ : ℝ), ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (∀ τ, θ ≤ gap j lam τ) → CompactGapsGE j c₀ lam → Dominant (lam - θ ^ 2 • nu) ∧ ‖lam - θ ^ 2 • nu‖ ≤ 2 ∧ ∀ τ, θ / 2 ≤ gap j (lam - θ ^ 2 • nu) τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant | exact GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqual
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_prime_nonunitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hg : IsCptGen ξ) (p : Cpt ξ) {o : Type} [CommRing o] [Algebra o Ω] (A : Subalgebra o Ω)
    (hA : ∀ s ∈ A, s ∈ regAt ξ p) :
    ∃ I : Ideal A, I.IsPrime ∧ ∀ s : A, s ∉ I ↔ unitAt ξ p (s : Ω) := by
  haveI : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).1
  let φ : A →+* regAt ξ p := RingHom.codRestrict A.val.toRingHom (regAt ξ p) (fun s => hA s s.2)
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), inferInstance, fun s => ?_⟩
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h.exists_right_inv
    have e : (s : Ω) * (t : Ω) = 1 := congrArg Subtype.val ht
    refine ⟨left_ne_zero_of_mul_eq_one e, hA s s.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right e]
    exact t.2
  · rintro ⟨h0, -, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : regAt ξ p) (Subtype.ext ?_)
    exact mul_inv_cancel₀ h0

theorem unitAt_of_le {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (p : Cpt ξ) (p' : Cpt ξ') (h : regAt ξ p ≤ regAt ξ' p') {a : Ω}
    (ha : unitAt ξ p a) : unitAt ξ' p' a :=
  ⟨ha.1, h ha.2.1, h ha.2.2⟩

theorem image_eq_of_regAt_eq :
    ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P)
      (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ →
      IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ →
      f₁ p₁.1 = f₂ p₂.1 := by
  intro P X₁ X₂ Ω _ ξ₀ ξ₁ ξ₂ f₁ f₂ o _ _ κ u hu g₁ g₂ e₁ e₂ p₁ p₂ hR
  have dom : ∀ {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ P), ξ ≫ f = ξ₀ →
      Dominates ξ ξ₀ f (RingHom.id Ω) := by
    intro X ξ f e
    have : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
      rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [this, Category.id_comp, e]
  obtain ⟨h₁, r₁, n₁⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₁ Ω ξ₁ f₁ (RingHom.id Ω) (dom ξ₁ f₁ e₁) p₁
  obtain ⟨h₂, r₂, n₂⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₂ Ω ξ₂ f₂ (RingHom.id Ω) (dom ξ₂ f₂ e₂) p₂
  set a₁ : Cpt ξ₀ := ⟨f₁ p₁.1, h₁⟩ with ha₁
  set a₂ : Cpt ξ₀ := ⟨f₂ p₂.1, h₂⟩ with ha₂
  have l₁ : regAt ξ₀ a₁ ≤ regAt ξ₁ p₁ := fun a ha => r₁ a ha
  have l₂ : regAt ξ₀ a₂ ≤ regAt ξ₁ p₁ := fun a ha => hR ▸ r₂ a ha
  have m₁ : ∀ a ∈ regAt ξ₀ a₁, unitAt ξ₁ p₁ a → unitAt ξ₀ a₁ a := n₁ g₁
  have m₂ : ∀ a ∈ regAt ξ₀ a₂, unitAt ξ₁ p₁ a → unitAt ξ₀ a₂ a := fun a ha h =>
    n₂ g₂ a ha ⟨h.1, hR ▸ h.2.1, hR ▸ h.2.2⟩
  obtain ⟨c₁, hc₁⟩ := hu.cover a₁
  obtain ⟨c, hc⟩ := hu.cover a₂

  have hq : unitAt ξ₀ a₁ (u c / u c₁) := by
    refine m₁ _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, l₁ (hc₁.2 c), ?_⟩
    rw [inv_div]
    exact l₂ (hc.2 c₁)
  have hin : InChart ξ₀ u c a₁ := by
    refine ⟨hc.1, fun j => ?_⟩
    have : u j / u c = u j / u c₁ * (u c / u c₁)⁻¹ := by
      have := hc₁.1
      have := hc.1
      field_simp
    rw [this]
    exact mul_mem (hc₁.2 j) hq.2.2
  set A := Algebra.adjoin o (Set.range fun j => u j / u c) with hA
  have A₁ : ∀ s ∈ A, s ∈ regAt ξ₀ a₁ := fun s hs => (hu.ring c hc.1 s).1 hs a₁ hin
  have A₂ : ∀ s ∈ A, s ∈ regAt ξ₀ a₂ := fun s hs => (hu.ring c hc.1 s).1 hs a₂ hc
  obtain ⟨I, hI, hI₁⟩ := exists_prime_nonunitAt ξ₀ hu.gen a₁ A A₁
  have hI₂ : ∀ s : A, s ∉ I ↔ unitAt ξ₀ a₂ (s : Ω) := fun s => by
    rw [hI₁ s]
    exact ⟨fun h => m₂ _ (A₂ s s.2) (unitAt_of_le ξ₀ ξ₁ a₁ p₁ l₁ h),
      fun h => m₁ _ (A₁ s s.2) (unitAt_of_le ξ₀ ξ₁ a₂ p₁ l₂ h)⟩
  have e := (GlobalTheory.T.prime_chart_existsUnique_point P Ω ξ₀ o κ u hu c hc.1 I hI).unique ⟨hin, hI₁⟩ ⟨hc, hI₂⟩
  exact congrArg Subtype.val e

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqualStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_rings_equal_images_equal : ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P) (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ → IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ → f₁ p₁.1 = f₂ p₂.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIso
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIso
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_isIso_restrict {W X' : Scheme.{0}} (f : X' ⟶ W) (U : W.Opens) (hU : IsIso (f ∣_ U)) {y y' : X'}
    (hy : f y ∈ U) (hy' : f y' ∈ U) (e : f y = f y') : y = y' := by
  haveI := IsOpenImmersion.of_isIso (f ∣_ U)
  let a : (f ⁻¹ᵁ U : Scheme) := ⟨y, hy⟩
  let a' : (f ⁻¹ᵁ U : Scheme) := ⟨y', hy'⟩
  have h : (f ∣_ U) a = (f ∣_ U) a' :=
    Subtype.ext (by rw [morphismRestrict_base_coe, morphismRestrict_base_coe]; exact e)
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective h)

private theorem eq_closedPoint_of_isField {R : Type} [CommRing R] [IsLocalRing R] (hR : IsField R)
    (z : PrimeSpectrum R) : z = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  have h := (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).1 hR
  have h1 : z.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal z.isPrime.ne_top
  show z.asIdeal = IsLocalRing.maximalIdeal R
  rw [h] at h1 ⊢
  exact le_bot_iff.1 h1

private theorem eq_genPt_of_specializes_of_bijective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hb).toMulEquiv
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := hy'
  rw [eq_closedPoint_of_isField hF q, Scheme.fromSpecStalk_closedPoint]

private theorem surjective_stalkClosedPointTo_of_comp {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
    (g : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y) (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : g ≫ f = ξ)
    (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    Function.Surjective (Scheme.stalkClosedPointTo g).hom := by
  subst h
  rw [Scheme.stalkClosedPointTo_comp] at hξ
  intro z
  obtain ⟨a, ha⟩ := hξ z
  exact ⟨(Scheme.Hom.stalkMap f _).hom a, ha⟩

theorem exists_lift_isCptGen : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W),
    IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) →
    ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  intro W X' f U Ω _ ξ hiso hU hξ hdom
  obtain ⟨hb, -⟩ := hξ
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [eq_closedPoint_of_isField (Field.toIsField Ω) z]
    exact hU
  let ξ' : Sp Ω ⟶ X' := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hfac : ξ' ≫ f = ξ := by
    simp only [ξ', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hfg : f (genPt ξ') = genPt ξ := by
    have h3 := Scheme.Hom.comp_apply ξ' f (IsLocalRing.closedPoint Ω)
    rw [hfac] at h3
    exact h3.symm
  have hmem : genPt ξ' ∈ f ⁻¹ᵁ U := by
    show f (genPt ξ') ∈ U
    rw [hfg]; exact hU
  refine ⟨ξ', hfac, ?_⟩
  refine isCptGen_of_maximal_of_surjective hdom ξ' ?_ ?_
  · intro y hy
    have hyU : y ∈ f ⁻¹ᵁ U := hy.mem_open (f ⁻¹ᵁ U).isOpen hmem
    have h1 : f y ⤳ genPt ξ := by
      have h2 := hy.map f.continuous
      rwa [hfg] at h2
    exact eq_of_isIso_restrict f U hiso hyU hmem ((eq_genPt_of_specializes_of_bijective ξ hb (f y) h1).trans hfg.symm)
  · exact surjective_stalkClosedPointTo_of_comp ξ' f ξ hfac hb.2

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_lift_along_iso : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W), IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) → ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_lift_isCptGen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsGenerateFunctionField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsGenerateFunctionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac

theorem exists_frac_field {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {W : Scheme.{0}}
    {ξ : Spec (CommRingCat.of Ω) ⟶ W} {κ : Type} {x : κ → Ω} (h : CoordTie F ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ r ∈ Algebra.adjoin F (Set.range fun j => x j / x c),
      ∃ s ∈ Algebra.adjoin F (Set.range fun j => x j / x c), s ≠ 0 ∧ a * s = r := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover p₀
  obtain ⟨U, hU, hq⟩ := h.affine c hc.1
  have h0 : genPt ξ ∈ U := (hq _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(W, U), (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.germ U (genPt ξ) h0 r) ∈
      Algebra.adjoin F (Set.range fun j => x j / x c) := fun r => by
    rw [h.ring c hc.1]
    intro q hqc
    have hqU : q.1 ∈ U := (hq _).2 ⟨q.2, hqc⟩
    refine ⟨W.presheaf.germ U q.1 hqU r, ?_⟩
    show (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.stalkSpecializes q.2 (W.presheaf.germ U q.1 hqU r)) = _
    congr 1
    exact W.presheaf.germ_stalkSpecializes_apply hqU q.2 r
  refine ⟨c, hc.1, fun a => ?_⟩
  obtain ⟨s, rfl⟩ := h.gen.bij.2 a
  letI := W.presheaf.algebra_section_stalk (⟨genPt ξ, h0⟩ : U)
  have hl := hU.isLocalization_stalk ⟨genPt ξ, h0⟩
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, h0⟩).asIdeal.primeCompl
    (S := W.presheaf.stalk (genPt ξ)) s
  refine ⟨_, key r, _, key t, ?_, ?_⟩
  · have := IsLocalization.map_units (W.presheaf.stalk (genPt ξ)) t
    exact (this.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · exact (map_mul (Scheme.stalkClosedPointTo ξ).hom _ _).symm.trans (congrArg _ e)

theorem exists_clear {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {S : Set Ω} {b : Ω}
    (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ ∃ g ∈ Algebra.adjoin o S, algebraMap o Ω d * b = g := by
  induction hb using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_ne_zero, y, Algebra.subset_adjoin hy, by simp⟩
  | algebraMap f =>
    obtain ⟨⟨n, d⟩, e⟩ := IsLocalization.surj (nonZeroDivisors o) f
    refine ⟨d, nonZeroDivisors.ne_zero d.2, algebraMap o Ω n, Subalgebra.algebraMap_mem _ n, ?_⟩
    rw [IsScalarTower.algebraMap_apply o F Ω n, IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, ← e, mul_comm]
  | add u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, algebraMap o Ω d₂ * g₁ + algebraMap o Ω d₁ * g₂,
      add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) m₁) (mul_mem (Subalgebra.algebraMap_mem _ _) m₂), ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, g₁ * g₂, mul_mem m₁ m₂, ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring

theorem algebraMap_ne_zero {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω d]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

theorem chartRing_frac : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type)
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (W : Scheme.{0}) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω),
    CoordTie F ξ' t → ∃ c₀, t c₀ ≠ 0 ∧ ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀),
      ∃ h ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), h ≠ 0 ∧ a = g / h := by
  intro o F _ _ _ _ _ Ω _ _ _ _ W ξ' κ t hT
  obtain ⟨c, hc, hf⟩ := exists_frac_field hT
  refine ⟨c, hc, fun a => ?_⟩
  obtain ⟨r, hr, s, hs, hs0, e⟩ := hf a
  obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := exists_clear (o := o) hr
  obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := exists_clear (o := o) hs
  have n₁ := algebraMap_ne_zero (F := F) (Ω := Ω) h₁
  have n₂ := algebraMap_ne_zero (F := F) (Ω := Ω) h₂
  have hg₂ : g₂ ≠ 0 := e₂ ▸ mul_ne_zero n₂ hs0
  refine ⟨algebraMap o Ω d₂ * g₁, mul_mem (Subalgebra.algebraMap_mem _ _) m₁,
    algebraMap o Ω d₁ * g₂, mul_mem (Subalgebra.algebraMap_mem _ _) m₂, mul_ne_zero n₁ hg₂, ?_⟩
  rw [eq_div_iff (mul_ne_zero n₁ hg₂), ← e₁, ← e₂, ← e]
  ring

end GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsGenerateFunctionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_generate_function_field : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (W : Scheme.{0}) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω), CoordTie F ξ' t → ∃ c₀, t c₀ ≠ 0 ∧ ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), ∃ h ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac | exact GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac.chartRing_frac <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationTangentComb
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationTangentComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem grpPull_mul (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f)
    (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact hφ.2 T x y x₀ y₀ hx hy

theorem grpPull_one (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (1 : T ⟶ G'))
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have h := hφ.2 T 1 1 e e rfl rfl
  rw [_root_.mul_one] at h
  have h2 : e * e = e := Over.OverMorphism.ext h
  have h3 : e = 1 := mul_eq_left.1 h2
  exact (congrArg (fun q : Over.mk (T.hom ≫ f) ⟶ G => q.left) h3).symm

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Same

variable {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}

theorem sameVec_one (Y : Model Xo c β) (y : Sp F ⟶ Xo.XF c) : SameVec Y y 1 1 := by
  let T : Over (Xo.XF c) := epsAt y
  refine ⟨(1 : T ⟶ Y.oF.t.G).left, Over.w _, ?_, ?_⟩
  · exact (grpPull_one Y.m0.cart T (Category.assoc _ _ _).symm).symm
  · exact (grpPull_one Y.m.cart T (Category.assoc _ _ _).symm).symm

theorem sameVec_mul {a b : epsAt (under y) ⟶ Xo.univ.t.G} {a' b' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y a a') (h₂ : SameVec Y y b b') : SameVec Y y (a * b) (a' * b') := by
  obtain ⟨u₁, p₁, q₁, r₁⟩ := h₁
  obtain ⟨u₂, p₂, q₂, r₂⟩ := h₂
  let T : Over (Xo.XF c) := epsAt y
  let x₁ : T ⟶ Y.oF.t.G := Over.homMk u₁ p₁
  let x₂ : T ⟶ Y.oF.t.G := Over.homMk u₂ p₂
  refine ⟨(x₁ * x₂).left, Over.w (x₁ * x₂), ?_, ?_⟩
  · exact (grpPull_mul Y.m0.cart T (Category.assoc _ _ _).symm x₁ x₂ a b q₁.symm q₂.symm).symm
  · exact (grpPull_mul Y.m.cart T (Category.assoc _ _ _).symm x₁ x₂ a' b' r₁.symm r₂.symm).symm

theorem sameVec_scale {a u : epsAt (under y) ⟶ Xo.univ.t.G} {a' : epsAt (y ≫ Y.j) ⟶ Y.t.G} (h : SameVec Y y a a')
    (r : F) (hu : u.left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ a.left) :
    SameVec Y y u (LieTangent.epsScale (y ≫ Y.j) r ≫ a') := by
  obtain ⟨u₀, p, q, t⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ u₀, ?_, ?_, ?_⟩
  · rw [Category.assoc, p, ← Category.assoc, LieTangent.spec_eps_alg]
  · rw [Category.assoc, q, hu]
  · rw [Category.assoc, t]
    rfl

end Same

theorem valFam_sum {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hg : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) {n : ℕ} (e : Fin n → Z.V)
    (u : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G))
    (h : ∀ j, ∃ a, Z.M.ValAt (y ≫ Y.j) (e j) a ∧ SameVec Y y (u j) a) :
    ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, e j) w' ∧ SameVec Y y (List.ofFn u).prod w' := by
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa using Z.M.valAt_zero hg
    · simpa using sameVec_one Y y
  | succ n ih =>
    obtain ⟨a, ha, hb⟩ := h 0
    obtain ⟨w', hw, hs⟩ := ih (fun i => e i.succ) (fun i => u i.succ) fun i => h i.succ
    refine ⟨a * w', ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      exact ha.add hw
    · rw [List.ofFn_succ, List.prod_cons]
      exact sameVec_mul hb hs

theorem valFam_sum_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ y n b v s r w hg h hs hw
  obtain ⟨u, hu, rfl⟩ := hw
  refine valFam_sum Z y hg _ u fun j => ?_
  obtain ⟨h1, t, e1, e2⟩ := hs j
  obtain ⟨a, ha, hb⟩ := h j
  have h2 := ha.smul h1 t
  rw [e1, e2] at h2
  exact ⟨_, h2, sameVec_scale hb (r j) (hu j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationTangentCombStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_specialization_tangent_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb | exact GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordChartsMatchRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordChartsMatchRegular
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.FracPts

variable {Ω : Type} [Field Ω]

theorem exists_prime_of_subset {k : Type} [CommRing k] [Algebra k Ω] (S : Subalgebra k Ω) (R : Subring Ω)
    (hR : IsLocalRing R) (h : ∀ s ∈ S, s ∈ R) :
    ∃ I : Ideal S, I.IsPrime ∧ ∀ s : S, s ∉ I ↔ ((s : Ω) ≠ 0 ∧ (s : Ω) ∈ R ∧ (s : Ω)⁻¹ ∈ R) := by
  let f : S →+* R := (S.val : S →+* Ω).codRestrict R (fun s => h s s.2)
  refine ⟨(IsLocalRing.maximalIdeal R).comap f, Ideal.IsPrime.comap f, fun s => ?_⟩
  have hs : (f s : Ω) = (s : Ω) := rfl
  rw [Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have h1 : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have hu' : ((u : R) : Ω) = (s : Ω) := by rw [hu, hs]
    rw [hu'] at h1
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, h s s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact (((u⁻¹ : Rˣ) : R)).2
  · rintro ⟨h0, h1, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : R) (Subtype.ext ?_)
    change (s : Ω) * (s : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ h0

variable {X : Scheme.{0}}

theorem mem_regAt_of_unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (h : s * a ∈ regAt ξ p) : a ∈ regAt ξ p := by
  have : a = s⁻¹ * (s * a) := by rw [inv_mul_cancel_left₀ hs.1]
  rw [this]
  exact (regAt ξ p).mul_mem hs.2.2 h

theorem unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (ha : unitAt ξ p a) : unitAt ξ p (s * a) := by
  refine ⟨mul_ne_zero hs.1 ha.1, (regAt ξ p).mul_mem hs.2.1 ha.2.1, ?_⟩
  rw [mul_inv]
  exact (regAt ξ p).mul_mem hs.2.2 ha.2.2

variable (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F]
  [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω]


include F in
theorem algebraMap_ne_zero {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

theorem adjoin_subset (S : Set Ω) : ∀ a ∈ Algebra.adjoin o S, a ∈ Algebra.adjoin F S := by
  have : Algebra.adjoin o S ≤ (Algebra.adjoin F S).restrictScalars o :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact fun a ha => this ha

theorem exists_mul_mem_adjoin (S : Set Ω) (b : Ω) (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ algebraMap o Ω d * b ∈ Algebra.adjoin o S := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := o) r
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨d, hd0, ?_⟩
    have hF : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd0
    have : algebraMap o Ω d * algebraMap F Ω (algebraMap o F n / algebraMap o F d) = algebraMap o Ω n := by
      rw [IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, mul_div_cancel₀ _ hF,
        ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact Subalgebra.algebraMap_mem _ n
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x + y) =
        algebraMap o Ω e * (algebraMap o Ω d * x) + algebraMap o Ω d * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ e) h) (mul_mem (Subalgebra.algebraMap_mem _ d) h')
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x * y) = (algebraMap o Ω d * x) * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact mul_mem h h'

variable {W : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ W}
  {κ : Type} {t : κ → Ω}

theorem unitAt_algebraMap (hF : CoordTie F ξ' t) {c : κ} {p' : Cpt ξ'} (hc : InChart ξ' t c p') {d : o}
    (hd : d ≠ 0) : unitAt ξ' p' (algebraMap o Ω d) := by
  have hF0 : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd
  have hmem : ∀ r : F, algebraMap F Ω r ∈ regAt ξ' p' := fun r =>
    (hF.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  refine ⟨algebraMap_ne_zero o F hd, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply o F Ω]
    exact hmem _
  · rw [IsScalarTower.algebraMap_apply o F Ω, ← map_inv₀]
    exact hmem _

theorem regAt_eq_of_units (hA : CoordTie o ξ t) (hF : CoordTie F ξ' t) {c : κ} {p : Cpt ξ} {p' : Cpt ξ'}
    (hc : InChart ξ t c p) (hc' : InChart ξ' t c p')
    (hu : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), unitAt ξ p s ↔ unitAt ξ' p' s) :
    regAt ξ p = regAt ξ' p' := by
  have hB : ∀ b ∈ Algebra.adjoin F (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    (hF.ring c hc'.1 b).1 hb p' hc'
  have hA' : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    hB b (adjoin_subset o F _ b hb)
  have hAp : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ p := fun b hb =>
    (hA.ring c hc.1 b).1 hb p hc
  ext a
  constructor
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).1 ha
    exact mem_regAt_of_unitAt_mul ((hu s hs).1 hsu) (hA' _ hsa)
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization W Ω ξ' F κ t hF c p' hc' a).1 ha
    obtain ⟨d, hd, hds⟩ := exists_mul_mem_adjoin o F _ s hs
    obtain ⟨e, he, hes⟩ := exists_mul_mem_adjoin o F _ _ hsa
    have hunit : unitAt ξ' p' (algebraMap o Ω e * (algebraMap o Ω d * s)) :=
      unitAt_mul (unitAt_algebraMap o F hF hc' he) (unitAt_mul (unitAt_algebraMap o F hF hc' hd) hsu)
    have hmemA : algebraMap o Ω e * (algebraMap o Ω d * s) ∈
        Algebra.adjoin o (Set.range fun j => t j / t c) :=
      mul_mem (Subalgebra.algebraMap_mem _ e) hds
    refine (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).2
      ⟨_, hmemA, (hu _ hmemA).2 hunit, ?_⟩
    have : algebraMap o Ω e * (algebraMap o Ω d * s) * a =
        algebraMap o Ω d * (algebraMap o Ω e * (s * a)) := by ring
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ d) hes

theorem regAt_frac :
    ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω]
      [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (X W : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ W) (κ : Type)
      (t : κ → Ω), CoordTie o ξ t → CoordTie F ξ' t →
      (∀ p' : Cpt ξ', ∃ p : Cpt ξ, regAt ξ p = regAt ξ' p') ∧
        ∀ p : Cpt ξ, (∀ d : o, d ≠ 0 → unitAt ξ p (algebraMap o Ω d)) → ∃ p' : Cpt ξ', regAt ξ p = regAt ξ' p' := by
  intro o F _ _ _ _ _ Ω _ _ _ _ X W ξ ξ' κ t hA hF
  constructor
  · intro p'
    obtain ⟨c, hc⟩ := hF.cover p'
    have hloc : IsLocalRing (regAt ξ' p') := (regAt_isLocalRing_isFractionRing_stalk W Ω ξ' hF.gen p').1
    have hsub : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), s ∈ regAt ξ' p' := fun s hs =>
      (hF.ring c hc.1 s).1 (adjoin_subset o F _ s hs) p' hc
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ' p') hloc hsub
    obtain ⟨p, ⟨hp, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ o κ t hA c hc.1 I hI
    refine ⟨p, regAt_eq_of_units o F hA hF hp hc fun s hs => ?_⟩
    exact (hpu ⟨s, hs⟩).symm.trans (hIu ⟨s, hs⟩)
  · intro p hd
    obtain ⟨c, hc⟩ := hA.cover p
    have hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hA.gen p).1
    have hsub : ∀ s ∈ Algebra.adjoin F (Set.range fun j => t j / t c), s ∈ regAt ξ p := fun s hs => by
      obtain ⟨d, hd0, hds⟩ := exists_mul_mem_adjoin o F _ s hs
      exact mem_regAt_of_unitAt_mul (hd d hd0) ((hA.ring c hc.1 _).1 hds p hc)
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ p) hloc hsub
    obtain ⟨p', ⟨hp', hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point W Ω ξ' F κ t hF c hc.1 I hI
    refine ⟨p', regAt_eq_of_units o F hA hF hc hp' fun s hs => ?_⟩
    have hsB := adjoin_subset o F _ s hs
    exact (hIu ⟨s, hsB⟩).symm.trans (hpu ⟨s, hsB⟩)

end GlobalTheory.CompanionTheory.Ar.SncBase.FracPts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordChartsMatchRegularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_charts_match_regular : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (X W : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω), CoordTie o ξ t → CoordTie F ξ' t → (∀ p' : Cpt ξ', ∃ p : Cpt ξ, regAt ξ p = regAt ξ' p') ∧ ∀ p : Cpt ξ, (∀ d : o, d ≠ 0 → unitAt ξ p (algebraMap o Ω d)) → ∃ p' : Cpt ξ', regAt ξ p = regAt ξ' p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac | exact GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac <;> assumption)
end
end

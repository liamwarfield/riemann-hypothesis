module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicSections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticParamInverse
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsChartWithParameters
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.RelChart

open GlobalTheory.TangentOrigin

theorem evalPt_appLE {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem top_le_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage]
  exact fun _ hp => e (hV hp)

theorem dual_ext {P R : Type} [CommRing P] [CommRing R] (ψ : P →+* R) (hψ : ψ.Etale)
    (F F' : R →+* DualNumber ℂ) (h : ∀ a, F (ψ a) = F' (ψ a)) (h0 : ∀ r, fstC (F r) = fstC (F' r)) : F = F' := by
  let _ := ψ.toAlgebra
  let _ : Algebra P (DualNumber ℂ) := (F'.comp ψ).toAlgebra
  have _ : Algebra.Etale P R := hψ
  let G : R →ₐ[P] DualNumber ℂ := { F with commutes' := h }
  let G₀ : R →ₐ[P] DualNumber ℂ := { F' with commutes' := fun _ => rfl }
  have hnil : IsNilpotent (RingHom.ker fstC) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' fstC hnil G G₀ h0
  exact RingHom.ext fun r => AlgHom.congr_fun hG r

theorem exists_chart_with_parameters :
    (∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x) → (∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') := by
  classical
  intro hring m g Z X p B y b₀ z₀ hp hB hb₀ hy hz₀
  obtain ⟨V, hV, U, hU, hz, hle, hsm⟩ :=
    hp.exists_isStandardSmoothOfRelativeDimension (z₀ (default : PrimeSpectrum ℂ))
  obtain ⟨ψ, hψC, hψ⟩ := hsm.exists_etale_mvPolynomial
  have hC : ∀ a, ψ (MvPolynomial.C a) = (p.appLE V U hle).hom a := fun a => RingHom.congr_fun hψC a
  have hzU : ⊤ ≤ z₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem z₀ U).2 hz
  have hy₀ : ⊤ ≤ y b₀ ⁻¹ᵁ V := hz₀ ▸ top_le_comp z₀ p hle hzU
  let φ : (Fin m → ℂ) → (Γ(X, V) →+* ℂ) := fun b =>
    if h : ⊤ ≤ y b ⁻¹ᵁ V then evalPt (y b) V h else evalPt (y b₀) V hy₀
  have hφ : ∀ b, ⊤ ≤ y b ⁻¹ᵁ V → ∀ a, φ b a = valAt' (y b) V a := fun b h a => by
    simp only [φ, dif_pos h, valAt'_eq_evalPt _ _ h]
  have hover : ∀ b (x : Sp ℂ ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = y b →
      ∀ a, evalPt x U hx (ψ (MvPolynomial.C a)) = φ b a := fun b x hx hxb a => by
    rw [hφ b (hxb ▸ top_le_comp x p hle hx), hC, ← valAt'_eq_evalPt, valAt'_appLE _ _ _ _ _ _ hx, hxb]
  obtain ⟨N, σ, n, f, O, hN, hO, h₀, hσd, hσ, hrec⟩ := hring m g Γ(X, V) Γ(Z, U) ψ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ V} φ b₀
    (evalPt z₀ U hzU) hψ (hy V 0).1 ⟨hb₀, hy₀⟩
    (fun a => (hy V a).2.congr fun b hb => hφ b hb.2 a) (hover b₀ z₀ hzU hz₀)
  choose s hsU hs using fun q => exists_evalPt_eq hU (σ q)
  have hval : ∀ q a, valAt' (s q) U a = σ q a := fun q a => by
    rw [valAt'_eq_evalPt _ _ (hsU q), hs]
  refine ⟨U, fun i => ψ (MvPolynomial.X i), n, f, N, O, s, hN, hO, hzU, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [valAt'_eq_evalPt _ _ hzU] using h₀
  · intro W a
    refine holFamily_of_affine valAt'_rules N Z s (fun q _ => ⟨U, hU, hsU q, ?_, fun r => ?_⟩) W a
    · simp only [hsU, and_true]
      exact hN
    · simp only [hsU, and_true, hval]
      exact hσd r
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hσ q hq
    refine ⟨ext_evalPt hV (top_le_comp _ p hle (hsU q)) h1.2 (RingHom.ext fun a => ?_), hsU q,
      fun i => (hval _ _).trans (h3 i)⟩
    rw [← evalPt_appLE _ p V U hle a (hsU q), hs, ← hC, h2, hφ _ h1.2, valAt'_eq_evalPt]
  · intro b x hxb hx hxO
    simp only [valAt'_eq_evalPt _ _ hx] at hxO ⊢
    obtain ⟨h1, h2⟩ := hrec b (evalPt x U hx) (hover b x hx hxb) hxO
    exact ⟨h1, ext_evalPt hU (hsU _) hx ((hs _).trans h2)⟩
  · intro v v' h h' hvp hv0 hvt
    refine ext_evalPt hU h h' (dual_ext ψ hψ _ _ (fun a => ?_) fun r => ?_)
    · have : (evalPt v U h).comp ψ = (evalPt v' U h').comp ψ := by
        refine MvPolynomial.ringHom_ext (fun c => ?_) hvt
        simp only [RingHom.comp_apply, hC]
        rw [evalPt_appLE v p V U hle c h (top_le_comp v p hle h),
          evalPt_appLE v' p V U hle c h' (top_le_comp v' p hle h')]
        simp only [hvp]
      exact RingHom.congr_fun this a
    · rw [← evalPt_spMap_comp fstC v U h ((top_le_preimage_iff v U).1 h),
        ← evalPt_spMap_comp fstC v' U h' ((top_le_preimage_iff v' U).1 h')]
      have hv0' : spMap fstC ≫ v = spMap fstC ≫ v' := hv0
      simp only [hv0']

end GlobalTheory.RelChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AnalyticAtCoordinateZero
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallyEqOfAdditiveOfHasFDerivAt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelExp

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}

def HolAt (a : E → (Sp ℂ ⟶ Z)) (w₀ : E) : Prop := ∃ W, IsOpen W ∧ w₀ ∈ W ∧ IsHolTo W a

theorem isHolTo_mono {a : E → (Sp ℂ ⟶ Z)} {W W' : Set E} (h : IsHolTo W a) (hW' : IsOpen W') (hs : W' ⊆ W) :
    IsHolTo W' a := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.mono fun w hw => ⟨hs hw.1, hw.2⟩⟩
  convert hW'.inter h1 using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, hs hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩

namespace HolAt

variable {a a' : E → (Sp ℂ ⟶ Z)} {w₀ : E}

theorem eventually_mem (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) : ∀ᶠ w in 𝓝 w₀, ⊤ ≤ a w ⁻¹ᵁ U := by
  obtain ⟨W, -, hw, h⟩ := h
  filter_upwards [(h U 0).1.mem_nhds ⟨hw, hU⟩] with w hw using hw.2

theorem analyticAt [FiniteDimensional ℂ E] (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) (f : Γ(Z, U)) :
    AnalyticAt ℂ (fun w => valAt' (a w) U f) w₀ := by
  obtain ⟨W, -, hw, h⟩ := h
  exact SCV.analyticAt_of_differentiableOn (h U f).2 ((h U f).1.mem_nhds ⟨hw, hU⟩)

theorem analyticAt_pi [FiniteDimensional ℂ E] (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) {κ : Type}
    [Fintype κ] (f : κ → Γ(Z, U)) : AnalyticAt ℂ (fun w i => valAt' (a w) U (f i)) w₀ :=
  analyticAt_pi_iff.mpr fun i => h.analyticAt hU (f i)

theorem eventually (h : HolAt a w₀) : ∀ᶠ w in 𝓝 w₀, HolAt a w := by
  obtain ⟨W, hW, hw, h⟩ := h
  filter_upwards [hW.mem_nhds hw] with w hw using ⟨W, hW, hw, h⟩

theorem congr (h : HolAt a w₀) (e : a =ᶠ[𝓝 w₀] a') : HolAt a' w₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  obtain ⟨S, hS, hSo, hS0⟩ := eventually_nhds_iff.1 e
  have h' := isHolTo_mono h (hW.inter hSo) Set.inter_subset_left
  refine ⟨W ∩ S, hW.inter hSo, ⟨hw, hS0⟩, fun U f => ?_⟩
  have : {b ∈ W ∩ S | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ W ∩ S | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [hS b hb.2]
  rw [this]
  exact ⟨(h' U f).1, (h' U f).2.congr fun b hb => by rw [hS b hb.1.2]⟩

theorem comp [CompleteSpace E] {φ : E' → E} {v₀ : E'} (h : HolAt a (φ v₀)) (hφ : AnalyticAt ℂ φ v₀) :
    HolAt (fun v => a (φ v)) v₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  obtain ⟨S, hS, hSo, hS0⟩ := eventually_nhds_iff.1
    (hφ.eventually_analyticAt.and (hφ.continuousAt.eventually (hW.mem_nhds hw)))
  have hd : DifferentiableOn ℂ φ S := fun v hv => (hS v hv).1.differentiableAt.differentiableWithinAt
  refine ⟨S, hSo, hS0, fun U f => ?_⟩
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.comp (hd.mono fun w hw => hw.1) fun w hw => ⟨(hS w hw.1).2, hw.2⟩⟩
  convert hd.continuousOn.isOpen_inter_preimage hSo h1 using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, (hS w hw.1).2, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩

theorem post (h : HolAt a w₀) (q : Z ⟶ Y) : HolAt (fun w => a w ≫ q) w₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  refine ⟨W, hW, hw, fun U f => ?_⟩
  obtain ⟨h1, h2⟩ := h (q ⁻¹ᵁ U) ((q.app U).hom f)
  exact ⟨h1, h2.congr fun w _ => (valAt'_comp _ _ _ _).symm⟩

end HolAt

theorem isHolTo_of_holAt {a : E → (Sp ℂ ⟶ Z)} {W : Set E} (hW : IsOpen W) (h : ∀ w ∈ W, HolAt a w) :
    IsHolTo W a := by
  intro U f
  have key : ∀ w ∈ {b ∈ W | ⊤ ≤ a b ⁻¹ᵁ U}, {b ∈ W | ⊤ ≤ a b ⁻¹ᵁ U} ∈ 𝓝 w := fun w hw =>
    Filter.Eventually.and (hW.mem_nhds hw.1) ((h w hw.1).eventually_mem hw.2)
  refine ⟨isOpen_iff_mem_nhds.2 key, fun w hw => ?_⟩
  obtain ⟨W', -, hw', h'⟩ := h w hw.1
  exact ((h' U f).2.differentiableAt ((h' U f).1.mem_nhds ⟨hw', hw.2⟩)).differentiableWithinAt

theorem holAt_of_isPullback {S X : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)} {w₀ : E} (ha : HolAt (fun w => c w ≫ p) w₀)
    (hb : HolAt (fun w => c w ≫ q) w₀) : HolAt c w₀ := by
  obtain ⟨W₁, hW₁, hw₁, ha⟩ := ha
  obtain ⟨W₂, hW₂, hw₂, hb⟩ := hb
  have hW := hW₁.inter hW₂
  replace ha := isHolTo_mono ha hW Set.inter_subset_left
  replace hb := isHolTo_mono hb hW Set.inter_subset_right
  refine ⟨W₁ ∩ W₂, hW, ⟨hw₁, hw₂⟩, fun U f => ?_⟩
  generalize W₁ ∩ W₂ = W at ha hb
  refine holFamily_of_affine valAt'_rules W Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨S₀, hS₀, hx₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := (c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨U₁, hU₁, hx₁, h₁⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := s ⁻¹ᵁ S₀)
    (x := (c w₀ ≫ p) (default : PrimeSpectrum ℂ)) hx₀
  obtain ⟨U₂, hU₂, hx₂, h₂⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := t ⁻¹ᵁ S₀)
    (x := (c w₀ ≫ q) (default : PrimeSpectrum ℂ)) (by rw [H.w] at hx₀; exact hx₀)
  have h₁' : U₁ ≤ s ⁻¹ᵁ S₀ := h₁
  have h₂' : U₂ ≤ t ⁻¹ᵁ S₀ := h₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hS₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := S₀) (UT := U₂) (UX := U₁) h₂' h₁'
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := S₀) (UT := U₂) (UX := U₁) h₂' h₁' hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hS₀ hU₂ hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨V, hV, (hiff w₀).2 ⟨(top_le_preimage_iff_mem _ _).2 hx₁, (top_le_preimage_iff_mem _ _).2 hx₂⟩, ?_,
    fun g => ?_⟩
  · convert (ha U₁ 0).1.inter (hb U₂ 0).1 using 1
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hiff]
    tauto
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ((ha U₁ y).2.mono fun w (hw : w ∈ {w ∈ W | ⊤ ≤ c w ⁻¹ᵁ V}) => ⟨hw.1, ((hiff w).1 hw.2).1⟩).congr fun w hw =>
          valAt'_appLE _ _ _ _ _ _ hw.2
      · exact ((hb U₂ y).2.mono fun w (hw : w ∈ {w ∈ W | ⊤ ≤ c w ⁻¹ᵁ V}) => ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE _ _ _ _ _ _ hw.2
    | zero => simp only [valAt'_zero]; exact differentiableOn_const _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => simp only [valAt'_add]; exact hx.add hy
    | neg x _ hx => simp only [valAt'_neg]; exact hx.neg
    | mul x y _ _ hx hy => simp only [valAt'_mul]; exact hx.mul hy

section Group

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : E → (Sp ℂ ⟶ X)} {w₀ : E}

theorem HolAt.mul {a b : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀)
    (hb : HolAt (Z := G.left) (fun w => (b w).left) w₀) :
    HolAt (Z := G.left) (fun w => (a w * b w).left) w₀ := by
  have h1 : ∀ w, (lift (a w) (b w)).left ≫ (fst G G).left = (a w).left := fun w => by
    rw [← Over.comp_left, lift_fst]
  have h2 : ∀ w, (lift (a w) (b w)).left ≫ (snd G G).left = (b w).left := fun w => by
    rw [← Over.comp_left, lift_snd]
  have H : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback G.hom G.hom
  exact (holAt_of_isPullback H (c := fun w => (lift (a w) (b w)).left)
    (ha.congr (Eventually.of_forall fun w => (h1 w).symm))
    (hb.congr (Eventually.of_forall fun w => (h2 w).symm))).post μ[G].left

theorem HolAt.inv {a : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀) :
    HolAt (Z := G.left) (fun w => ((a w)⁻¹).left) w₀ :=
  ha.post (GrpObj.inv (X := G)).left

theorem HolAt.one (hy : HolAt y w₀) : HolAt (Z := G.left) (fun w => (1 : Over.mk (y w) ⟶ G).left) w₀ :=
  hy.post η[G].left

theorem HolAt.pow {a : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀) (n : ℕ) :
    HolAt (Z := G.left) (fun w => (a w ^ n).left) w₀ := by
  induction n with
  | zero => simpa only [pow_zero, mul_inv_cancel] using ha.mul ha.inv
  | succ n ih => simpa only [pow_succ] using ih.mul ha

end Group

section Additive

variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]

theorem exists_addMonoidHom_eqOn_ball {g : V → A} {r : ℝ} (hr : 0 < r)
    (hg : ∀ x ∈ Metric.ball (0 : V) r, ∀ x' ∈ Metric.ball (0 : V) r, g (x + x') = g x + g x') :
    ∃ e : V →+ A, ∀ x ∈ Metric.ball (0 : V) r, e x = g x := by
  obtain ⟨e, he⟩ := exists_addMonoidHom_eventuallyEq (g := g) (by
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds (0 : V) hr) (Metric.ball_mem_nhds (0 : V) hr)] with p hp
    exact hg _ hp.1 _ hp.2)
  refine ⟨e, fun x hx => ?_⟩
  have hball : ∀ k : ℕ, (2⁻¹ : ℝ) ^ k • x ∈ Metric.ball (0 : V) r := fun k => by
    rw [mem_ball_zero_iff] at hx ⊢
    rw [norm_smul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (by norm_num))).trans_lt hx
  have hstep : ∀ k : ℕ, e ((2⁻¹ : ℝ) ^ k • x) = g ((2⁻¹ : ℝ) ^ k • x) → e x = g x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro h
      apply ih
      have : (2⁻¹ : ℝ) ^ k • x = (2⁻¹ : ℝ) ^ (k + 1) • x + (2⁻¹ : ℝ) ^ (k + 1) • x := by
        rw [← add_smul, pow_succ]; congr 1; ring
      rw [this, map_add (f := _), hg _ (hball _) _ (hball _), h]
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const x
  obtain ⟨k, hk⟩ := (ht.eventually he).exists
  exact hstep k hk

end Additive

theorem eventuallyEq_of_additive_of_hasFDerivAt {ζ : E → E'} {T : E →L[ℂ] E'} (hT : HasFDerivAt ζ T 0)
    (hζ : ∀ᶠ p in 𝓝 (0 : E × E), ζ (p.1 + p.2) = ζ p.1 + ζ p.2) : ζ =ᶠ[𝓝 0] T := by
  obtain ⟨l, hl⟩ := exists_addMonoidHom_eventuallyEq (V := E) hζ
  have h1 : HasFDerivAt l T 0 := hT.congr_of_eventuallyEq hl
  have hc : Continuous l := continuous_of_continuousAt_zero l h1.continuousAt
  have h2 : (l.toRealLinearMap hc) = T.restrictScalars ℝ :=
    (l.toRealLinearMap hc).hasFDerivAt.unique (h1.restrictScalars ℝ)
  filter_upwards [hl] with v hv
  rw [← hv]
  exact DFunLike.congr_fun h2 v

end GlobalTheory.RelExp
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelExp

variable {X : Scheme.{0}} {G : Over X}

abbrev pt {x : Sp ℂ ⟶ X} (a : Over.mk x ⟶ G) : Sp ℂ ⟶ G.left := a.left

abbrev crd {Z : Scheme.{0}} (U : Z.Opens) {κ : Type} (t : κ → Γ(Z, U)) (z : Sp ℂ ⟶ Z) : κ → ℂ :=
  fun i => valAt' z U (t i)

variable [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} {U : G.left.Opens}
  {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}

abbrev crd0 (t : Fin g → Γ(G.left, U)) {x : Sp ℂ ⟶ X} (a : Over.mk x ⟶ G) : Fin g → ℂ :=
  crd U t (pt a) - crd U t (pt (1 : Over.mk x ⟶ G))

theorem exists_centred_chart (hy : HolAt y b₀) {N : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} (hN : IsOpen N)
    (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U) (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O)
    (hσ : IsHolTo N σ) (hσN : ∀ q ∈ N, σ q ≫ G.hom = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i)
    (hinv : ∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ G.left), x ≫ G.hom = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, crd U f x) ∈ O →
      (b, crd U t x) ∈ N ∧ σ (b, crd U t x) = x) :
    ∃ s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G),
      HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2) ∧
      ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a := by
  classical
  let c : (Fin m → ℂ) → (Fin g → ℂ) := fun b => crd U t (pt (1 : Over.mk (y b) ⟶ G))
  have hc : AnalyticAt ℂ c b₀ := (HolAt.one (G := G) hy).analyticAt_pi hU t
  let τ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) := fun q => (q.1, q.2 + c q.1)
  have hτ : AnalyticAt ℂ τ (b₀, 0) :=
    analyticAt_fst.prod (analyticAt_snd.add (AnalyticAt.comp (g := c) hc analyticAt_fst))
  have hτ0 : τ (b₀, 0) ∈ N := by
    have := (hinv b₀ _ (Over.w (1 : Over.mk (y b₀) ⟶ G)) hU hO).1
    simpa only [τ, zero_add] using this
  let s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G) := fun b w =>
    if h : τ (b, w) ∈ N then Over.homMk (σ (τ (b, w))) (hσN _ h).1 else 1
  have hs : ∀ q, τ q ∈ N → pt (s q.1 q.2) = σ (τ q) := fun q hq => by
    have : s q.1 q.2 = Over.homMk (σ (τ q)) (hσN _ hq).1 := dif_pos hq
    rw [this]; rfl
  have hev : ∀ᶠ q in 𝓝 (b₀, (0 : Fin g → ℂ)), τ q ∈ N := hτ.continuousAt.eventually (hN.mem_nhds hτ0)
  refine ⟨s, (HolAt.comp ⟨N, hN, hτ0, hσ⟩ hτ).congr (hev.mono fun q hq => (hs q hq).symm), hev.mono fun q hq => ?_,
    fun b a ha hf => ?_⟩
  · have : crd U t (pt (s q.1 q.2)) = q.2 + c q.1 := by
      rw [hs q hq]; exact funext (hσN _ hq).2.2
    exact sub_eq_iff_eq_add.2 this
  · obtain ⟨h1, h2⟩ := hinv b _ (Over.w a) ha hf
    have e : τ (b, crd0 t a) = (b, crd U t (pt a)) := Prod.ext rfl (sub_add_cancel _ _)
    refine Over.OverMorphism.ext ((hs (b, crd0 t a) (e ▸ h1)).trans ?_)
    rw [e]; exact h2

section Family

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {β : E → (Fin m → ℂ)}
  {a : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : E}

omit [FiniteDimensional ℂ E] in
theorem HolAt.one_of (ha : HolAt (fun w => pt (a w)) w₀) :
    HolAt (fun w => pt (1 : Over.mk (y (β w)) ⟶ G)) w₀ := by
  simpa only [pow_zero] using ha.pow 0

theorem HolAt.analyticAt_coordinate_zero (ha : HolAt (fun w => pt (a w)) w₀) (h1 : a w₀ = 1)
    (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U) : AnalyticAt ℂ (fun w => crd0 t (a w)) w₀ :=
  (ha.analyticAt_pi (by rw [h1]; exact hU) t).sub (ha.one_of.analyticAt_pi hU t)

theorem HolAt.eventually_near (ha : HolAt (fun w => pt (a w)) w₀) (hβ : ContinuousAt β w₀) (h1 : a w₀ = 1)
    (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U)
    (hO : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O) :
    ∀ᶠ w in 𝓝 w₀, ⊤ ≤ pt (a w) ⁻¹ᵁ U ∧ (β w, crd U f (pt (a w))) ∈ O := by
  have hU' : ⊤ ≤ pt (a w₀) ⁻¹ᵁ U := by simpa only [h1] using hU
  refine (ha.eventually_mem hU').and ((hβ.prodMk (ha.analyticAt_pi hU' f).continuousAt).eventually
    (hOo.mem_nhds ?_))
  simpa only [h1] using hO

end Family

set_option maxHeartbeats 16000000 in
theorem exists_local_exp [IsCommMonObj G]
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hy : HolAt y b₀) (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U)
    (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O) {s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hs1 : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0))
    (hs2 : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2)
    (hs3 : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a) :
    ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧
      (∀ᶠ b in 𝓝 b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧
      ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
        s q.1 (E (q.1, q.2.1 + q.2.2)) = s q.1 (E (q.1, q.2.1)) * s q.1 (E (q.1, q.2.2)) := by
  have hs0 : ∀ᶠ b in 𝓝 b₀, s b 0 = 1 := by
    filter_upwards [HolAt.eventually_near (β := fun b => b) (a := fun _ => 1) (HolAt.one hy) continuousAt_id rfl
      hOo hU hO] with b hb
    simpa only [crd0, sub_self] using hs3 b 1 hb.1 hb.2
  have hprod : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2.1 * s q.1 q.2.2))
      (b₀, 0, 0) := by
    have k1 := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.1)) (v₀ := (b₀, 0, 0))
      hs1 (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
    have k2 := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.2)) (v₀ := (b₀, 0, 0))
      hs1 (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd))
    exact HolAt.mul (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => y q.1)
      (a := fun q => s q.1 q.2.1) (b := fun q => s q.1 q.2.2) k1 k2
  have h11 : s b₀ 0 * s b₀ 0 = 1 := by rw [hs0.self_of_nhds, _root_.mul_one]
  let M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun q => crd0 t (s q.1 q.2.1 * s q.1 q.2.2)
  have hMa : AnalyticAt ℂ M (b₀, 0, 0) :=
    HolAt.analyticAt_coordinate_zero (β := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => q.1)
      (a := fun q => s q.1 q.2.1 * s q.1 q.2.2) hprod h11 hU
  have hM : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
      s q.1 (M q) = s q.1 q.2.1 * s q.1 q.2.2 :=
    (HolAt.eventually_near (β := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => q.1)
      (a := fun q => s q.1 q.2.1 * s q.1 q.2.2) hprod
      continuousAt_fst h11 hOo hU hO).mono fun q hq => hs3 _ _ hq.1 hq.2
  obtain ⟨E, L, hE, hL, h0, hLE, hadd⟩ := hexp m g b₀ M hMa (by
      filter_upwards [hs2, (continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually hs0] with q h1 h2
      show crd0 t (s q.1 q.2 * s q.1 0) = q.2
      rw [h2, _root_.mul_one, h1])
    (Eventually.of_forall fun q => by simp only [M, mul_comm]) (by
      have t1 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        (q.1, q.2.1, q.2.2.1)) (by fun_prop) (b₀, 0, 0, 0)
      have t2 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        (q.1, q.2.2.1, q.2.2.2)) (by fun_prop) (b₀, 0, 0, 0)
      filter_upwards [t1.eventually hM, t2.eventually hM] with q h1 h2
      show crd0 t (s q.1 (M _) * s q.1 q.2.2.2) = crd0 t (s q.1 q.2.1 * s q.1 (M _))
      rw [h1, h2, _root_.mul_assoc])
  refine ⟨E, L, hE, hL, h0, hLE, ?_⟩
  have hEt : Tendsto E (𝓝 (b₀, 0)) (𝓝 0) := by
    have := hE.continuousAt.tendsto
    rwa [h0.self_of_nhds.1] at this
  have t1 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.1))
    (by fun_prop) (b₀, 0, 0)
  have t2 := Continuous.tendsto (f := fun q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (q.1, q.2.2))
    (by fun_prop) (b₀, 0, 0)
  have t3 := ((continuous_fst.tendsto (b₀, (0 : Fin g → ℂ), (0 : Fin g → ℂ))).prodMk_nhds
    ((hEt.comp t1).prodMk_nhds (hEt.comp t2)))
  filter_upwards [hadd, t3.eventually hM] with q h1 h2
  rw [h1]
  exact h2

theorem exists_global_exp [IsCommMonObj G]
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    {B : Set (Fin m → ℂ)} (hB : B ∈ 𝓝 b₀)
    (hy : HolAt y b₀) (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U)
    (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O) {s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hs1 : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0))
    (hs2 : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2)
    (hs3 : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a) :
    ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ)
      (Q : Set ((Fin m → ℂ) × (Fin g → ℂ))) (L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ 0 < r ∧ IsOpen Q ∧ (∀ b z w, e b (z + w) = e b z * e b w) ∧
      (∀ b ∈ B', (∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (b, z)) ∧
        ⊤ ≤ pt (1 : Over.mk (y b) ⟶ G) ⁻¹ᵁ U ∧ (b, crd U f (pt (1 : Over.mk (y b) ⟶ G))) ∈ O ∧ (b, 0) ∈ Q ∧
        HasFDerivAt (fun z => crd U t (pt (e b z))) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
        L (b, 0) = 0 ∧ AnalyticAt ℂ L (b, 0) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧
      ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → (b, crd0 t a) ∈ Q →
        e b (L (b, crd0 t a)) = a := by
  obtain ⟨E, L, hE, hL, h0, hLE, hadd⟩ := exists_local_exp hexp hy hOo hU hO hs1 hs2 hs3
  have hE0 : E (b₀, 0) = 0 := h0.self_of_nhds.1
  have hL0 : L (b₀, 0) = 0 := by
    have := hLE.self_of_nhds.1
    rwa [hE0] at this
  have hτ : AnalyticAt ℂ (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, E q)) (b₀, 0) := analyticAt_fst.prod hE
  have hψ : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 (E q))) (b₀, 0) := by
    have := HolAt.comp (a := fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2))
      (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, E q)) (v₀ := (b₀, 0)) (by simpa only [hE0] using hs1) hτ
    exact this
  have hcE : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 (E q)) = E q := by
    have := hτ.continuousAt.tendsto
    simp only [hE0] at this
    exact this.eventually hs2

  obtain ⟨r₁, hr₁, h₁⟩ := Metric.eventually_nhds_iff_ball.1 (hψ.eventually.and (hcE.and hLE))
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff_ball.1 hadd
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  set r := min r₁ r₂ with hrdef
  have k₁ : ∀ b ∈ Metric.ball b₀ r, ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r,
      HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 (E q))) (b, v) ∧
      crd0 t (s b (E (b, v))) = E (b, v) ∧
      (L (b, E (b, v)) = v ∧ E (b, L (b, v)) = v) := fun b hb v hv =>
    h₁ (b, v) (Metric.ball_subset_ball (min_le_left _ _) (by rw [← ball_prod_same]; exact ⟨hb, hv⟩))
  have hex : ∀ b, ∃ ε : (Fin g → ℂ) →+ Additive (Over.mk (y b) ⟶ G), b ∈ Metric.ball b₀ r →
      ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, (ε v).toMul = s b (E (b, v)) := by
    intro b
    by_cases hb : b ∈ Metric.ball b₀ r
    · obtain ⟨ε, hε⟩ := exists_addMonoidHom_eqOn_ball (g := fun v => Additive.ofMul (s b (E (b, v)))) hr
        fun v hv v' hv' => congrArg Additive.ofMul (h₂ (b, v, v') (Metric.ball_subset_ball (min_le_right _ _)
          (by rw [← ball_prod_same, ← ball_prod_same]; exact ⟨hb, hv, hv'⟩)))
      exact ⟨ε, fun _ v hv => congrArg Additive.toMul (hε v hv)⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose ε hε using hex
  obtain ⟨Q, hQ, hQo, hQ0⟩ := eventually_nhds_iff.1 (hL.eventually_analyticAt.and (hLE.and
    (((continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually (Metric.ball_mem_nhds b₀ hr)).and
      (hL.continuousAt.eventually (by rw [hL0]; exact Metric.ball_mem_nhds 0 hr)))))
  have hQb : ∀ᶠ b in 𝓝 b₀, (b, (0 : Fin g → ℂ)) ∈ Q :=
    (Continuous.tendsto (f := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (by fun_prop) b₀).eventually
      (hQo.mem_nhds hQ0)
  obtain ⟨B', hB', hB'o, hB'0⟩ := eventually_nhds_iff.1 (Filter.Eventually.and hB (h0.and (hQb.and
    (HolAt.eventually_near (β := fun b => b) (a := fun _ => 1) (HolAt.one hy) continuousAt_id rfl hOo hU hO))))
  refine ⟨B', fun b v => (ε b v).toMul, r, Q, L, hB'o, hB'0, fun b hb => (hB' b hb).1, hr, hQo,
    fun b z w => congrArg Additive.toMul ((ε b).map_add z w), fun b hb => ?_, fun b a ha hf hq => ?_⟩
  · obtain ⟨-, ⟨hEb, hEd⟩, hbQ, hbU, hbO⟩ := hB' b hb
    have hbr : b ∈ Metric.ball b₀ r := (hQ _ hbQ).2.2.1
    have hLb : L (b, 0) = 0 := by
      have := (hQ _ hbQ).2.1.1
      rwa [hEb] at this
    refine ⟨fun z => ?_, hbU, hbO, hbQ, ?_, hLb, (hQ _ hbQ).1, fun z hz h1 => ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_gt (‖z‖ / r)
      have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr.le) hk
      have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
      have hz : (k : ℂ)⁻¹ • z ∈ Metric.ball (0 : Fin g → ℂ) r := by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_lt_iff₀ hk0]
        rwa [div_lt_iff₀ hr] at hk
      have hφ : AnalyticAt ℂ (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, (k : ℂ)⁻¹ • q.2)) (b, z) :=
        analyticAt_fst.prod (analyticAt_snd.const_smul (c := (k : ℂ)⁻¹))
      have h0' := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, (k : ℂ)⁻¹ • q.2)) (v₀ := (b, z))
        (k₁ b hbr _ hz).1 hφ
      have h1 := (HolAt.pow (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) => y q.1)
        (a := fun q => s q.1 (E (q.1, (k : ℂ)⁻¹ • q.2))) h0' k)
      refine h1.congr ?_
      filter_upwards [hφ.continuousAt.eventually (prod_mem_nhds (Metric.isOpen_ball.mem_nhds hbr)
        (Metric.isOpen_ball.mem_nhds hz))] with q hq
      rw [← hε q.1 hq.1 _ hq.2, ← toMul_nsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hkc]
    · refine (hEd.add_const (crd U t (pt (1 : Over.mk (y b) ⟶ G)))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Fin g → ℂ) hr] with v hv
      rw [hε b hbr v hv]
      exact sub_eq_iff_eq_add.1 (k₁ b hbr v hv).2.1
    · have hz' := mem_ball_zero_iff.2 hz
      have h2 := (k₁ b hbr z hz').2
      have h3 : s b (E (b, z)) = 1 := (hε b hbr z hz').symm.trans h1
      have h4 : E (b, z) = 0 := by
        rw [← h2.1]
        simp only [h3, crd0, sub_self]
      have h5 := h2.2.1
      simp only [h4, hLb] at h5
      exact h5.symm
  · obtain ⟨-, h1, h2, h3⟩ := hQ _ hq
    refine (hε b h2 _ h3).trans ?_
    rw [h1.2]
    exact hs3 b a ha hf

end GlobalTheory.RelExp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.RelExp

theorem exists_lift {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {U : G.left.Opens} {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {Q : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)} (hO : IsOpen O) (hQ : IsOpen Q)
    (hadd : ∀ b z w, e b (z + w) = e b z * e b w)
    (hinv : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → (b, crd0 t a) ∈ Q →
      e b (L (b, crd0 t a)) = a)
    {k : ℕ} {β : (Fin k → ℂ) → (Fin m → ℂ)} {x : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : Fin k → ℂ} {z₀ : Fin g → ℂ}
    (hβ : AnalyticAt ℂ β w₀) (hx : HolAt (fun w => pt (x w)) w₀) (h0 : e (β w₀) z₀ = x w₀)
    (he : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (β w₀, z₀))
    (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U) (hO₀ : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O)
    (hQ₀ : (β w₀, 0) ∈ Q) (hL0 : L (β w₀, 0) = 0) (hL : AnalyticAt ℂ L (β w₀, 0)) :
    ∃ ζ : (Fin k → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in 𝓝 w₀, e (β w) (ζ w) = x w := by
  have h1 := HolAt.comp (φ := fun w => (β w, z₀)) (v₀ := w₀) he (hβ.prod analyticAt_const)
  have h2 := HolAt.inv (y := fun w => y (β w)) (a := fun w => e (β w) z₀) h1
  have ha : HolAt (fun w => pt (x w * (e (β w) z₀)⁻¹)) w₀ :=
    HolAt.mul (y := fun w => y (β w)) (a := x) (b := fun w => (e (β w) z₀)⁻¹) hx h2
  have ha0 : x w₀ * (e (β w₀) z₀)⁻¹ = 1 := by rw [h0, mul_inv_cancel]
  have hc : AnalyticAt ℂ (fun w => (β w, crd0 t (x w * (e (β w) z₀)⁻¹))) w₀ :=
    hβ.prod (HolAt.analyticAt_coordinate_zero (a := fun w => x w * (e (β w) z₀)⁻¹) ha ha0 hU)
  have hc0 : (β w₀, crd0 t (x w₀ * (e (β w₀) z₀)⁻¹)) = (β w₀, 0) := by
    rw [ha0]; exact Prod.ext rfl (sub_self _)
  refine ⟨fun w => L (β w, crd0 t (x w * (e (β w) z₀)⁻¹)) + z₀, ?_, ?_, ?_⟩
  · simp only [hc0, hL0, zero_add]
  · exact (AnalyticAt.comp (g := L) (hc0 ▸ hL) hc).add analyticAt_const
  · filter_upwards [HolAt.eventually_near (a := fun w => x w * (e (β w) z₀)⁻¹) ha hβ.continuousAt ha0 hO hU hO₀,
      hc.continuousAt.eventually (hQ.mem_nhds (by simpa only [hc0] using hQ₀))] with w h3 h4
    rw [hadd, hinv _ _ h3.1 h3.2 h4, inv_mul_cancel_right]

theorem exists_relative_exp_of_parts
    (hchart : ∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v')
    (htan : ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)))
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hsub : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤) :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  intro k _ σ₀ X s₀ G _ g m B y b₀ e₀ _ hab hsm hB hb₀ _ hy ⟨he₀add, _, he₀hol, _, he₀tan⟩
  have := hab.comm
  have hy₀ : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hσinv, hunr⟩ :=
    hchart m g G.left X G.hom B y b₀ (pt (1 : Over.mk (y b₀) ⟶ G)) hsm hB hb₀ hy (Over.w _)
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart hy₀ hN hU hO₀ hσ hσN hσinv
  obtain ⟨B', e, r, Q, L, hB', hb', hB'B, hr, hQ, hadd, hfib, hinv⟩ :=
    exists_global_exp hexp (hB.mem_nhds hb₀) hy₀ hO hU hO₀ hs1 hs2 hs3
  have hzero : ∀ {x : Sp ℂ ⟶ X} {u : (Fin g → ℂ) → (Over.mk x ⟶ G)}, (∀ z w, u (z + w) = u z * u w) → u 0 = 1 :=
    fun {x u} h => by
      have := h 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
  have he₀0 : e₀ 0 = 1 := hzero he₀add
  have he₀U : ⊤ ≤ pt (e₀ 0) ⁻¹ᵁ U := by rw [he₀0]; exact hU
  have hinj := ((htan X G (y b₀) g e₀ he₀hol).2 U t he₀U hunr).1 he₀tan
  set T₀ : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fderiv ℂ (fun z => crd U t (pt (e₀ z))) 0 with hT₀
  have hsurj : Function.Surjective T₀ :=
    (LinearMap.injective_iff_surjective (f := (T₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))).1 hinj
  let T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := ContinuousLinearEquiv.ofBijective T₀ (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hT : ∀ z, T z = T₀ z := fun _ => rfl
  have hhol : ∀ b ∈ B', ∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 (T₀ q.2))) (b, z) :=
    fun b hb z => by
      have := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, T₀ q.2)) (v₀ := (b, z))
        ((hfib b hb).1 (T₀ z)) (analyticAt_fst.prod ((T₀.analyticAt _).comp analyticAt_snd))
      exact this
  refine ⟨B', fun b z => e b (T₀ z), r / (‖T₀‖ + 1), hB', hb', hB'B, ?_, by positivity,
    isHolTo_of_holAt (hB'.prod isOpen_univ) fun q hq => hhol q.1 hq.1 q.2, fun b hb => ?_, ?_⟩
  ·
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b₀ hb'
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (β := fun _ : Fin g → ℂ => b₀) (x := e₀) (w₀ := 0)
      (z₀ := 0) analyticAt_const ⟨Set.univ, isOpen_univ, trivial, he₀hol⟩ ((hzero (hadd b₀)).trans he₀0.symm)
      (h1 0) h2 h3 h4 h6 h7
    have hd : HasFDerivAt ζ T₀ 0 := by
      have k1 := HasFDerivAt.comp (f := ζ) (0 : Fin g → ℂ) (hζ0.symm ▸ h5) hζ.differentiableAt.hasFDerivAt
      have k2 : HasFDerivAt (fun z => crd U t (pt (e₀ z))) _ 0 := k1.congr_of_eventuallyEq
        (hζe.mono fun z hz => by simp only [Function.comp, hz])
      rw [hT₀, k2.fderiv, ContinuousLinearMap.id_comp]
      exact hζ.differentiableAt.hasFDerivAt
    have tζ : Tendsto ζ (𝓝 0) (𝓝 0) := by simpa only [ContinuousAt, hζ0] using hζ.continuousAt
    have t1 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
    have t2 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
    have t3 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1 + p.2) (𝓝 0) (𝓝 0) := by simpa using t1.add t2
    have t4 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (𝓝 0) (𝓝 0) := by
      simpa using (tζ.comp t3).sub ((tζ.comp t1).add (tζ.comp t2))
    have hζT := eventuallyEq_of_additive_of_hasFDerivAt hd (by
      filter_upwards [t1.eventually hζe, t2.eventually hζe, t3.eventually hζe,
        t4.eventually (Metric.ball_mem_nhds 0 hr)] with p k1 k2 k3 k4
      refine sub_eq_zero.1 (h8 _ (mem_ball_zero_iff.1 k4) ?_)
      have k5 := hadd b₀ (ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (ζ p.1 + ζ p.2)
      rw [sub_add_cancel, hadd b₀ (ζ p.1), k1, k2, k3, he₀add] at k5
      exact mul_eq_right.1 k5.symm)
    have key := addMonoidHom_eq_of_eventuallyEq
      (e := AddMonoidHom.mk' (fun z => Additive.ofMul (e b₀ (T₀ z))) fun z w => by rw [map_add (f := _), hadd]; rfl)
      (e' := AddMonoidHom.mk' (fun z => Additive.ofMul (e₀ z)) fun z w => by rw [he₀add]; rfl) (by
        filter_upwards [hζT, hζe] with z k1 k2
        exact congrArg Additive.ofMul (by rw [← k1]; exact k2))
    exact funext fun z => congrArg Additive.toMul (DFunLike.congr_fun key z)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b hb
    have hH : IsHolTo Set.univ (fun z => pt (e b (T₀ z))) := isHolTo_of_holAt isOpen_univ fun z _ => by
      have := HolAt.comp (φ := fun z : Fin g → ℂ => (b, z)) (v₀ := z) (hhol b hb z)
        (analyticAt_const.prod analyticAt_id)
      exact this
    have hadd' : ∀ z w, e b (T₀ (z + w)) = e b (T₀ z) * e b (T₀ w) := fun z w => by rw [map_add (f := _), hadd]
    obtain ⟨k1, k2⟩ := htan X G (y b) g (fun z => e b (T₀ z)) hH
    refine ⟨⟨hadd', ?_, hH, k1, (k2 U t ?_ hunr).2 ?_⟩, fun z hz h => ?_⟩
    · refine Function.Surjective.comp (g := e b) ?_ hsurj
      let ε : (Fin g → ℂ) →+ Additive (Over.mk (y b) ⟶ G) :=
        AddMonoidHom.mk' (fun z => Additive.ofMul (e b z)) fun z w => by rw [hadd]; rfl
      have hc : Continuous fun u : Fin n ⊕ Fin g → ℂ => (b, fun j => u (Sum.inl j)) := by fun_prop
      have hc' : Continuous fun u : Fin n ⊕ Fin g → ℂ =>
        (b, (fun j => u (Sum.inr j)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) := by fun_prop
      have := hsub X G (y b) (AddSubgroup.toSubgroup' ε.range) U (Fin n ⊕ Fin g) (Sum.elim f t) _ hab.smooth
        hab.geomConnected ((hO.preimage hc).inter (hQ.preimage hc')) h2
        ⟨h3, by simpa only [Set.mem_preimage, Sum.elim_inr, sub_self] using h4⟩
        fun a ha hb => ⟨_, congrArg Additive.ofMul (hinv b a ha hb.1 hb.2)⟩
      intro a
      obtain ⟨z, hz⟩ : a ∈ AddSubgroup.toSubgroup' ε.range := this ▸ Subgroup.mem_top a
      exact ⟨z, congrArg Additive.toMul hz⟩
    · rw [hzero (u := fun z => e b (T₀ z)) hadd']; exact h2
    · have := HasFDerivAt.comp (f := T₀) (0 : Fin g → ℂ) (by rw [map_zero]; exact h5) T₀.hasFDerivAt
      have k3 : fderiv ℂ (fun z => crd U t (pt (e b (T₀ z)))) 0 = _ := this.fderiv
      rw [ContinuousLinearMap.id_comp] at k3
      exact k3.symm ▸ hinj
    · refine hinj ((h8 _ ((T₀.le_opNorm z).trans_lt ?_) h).trans (map_zero T₀).symm)
      rw [lt_div_iff₀ (by positivity)] at hz
      nlinarith [norm_nonneg z]
  · intro j W β x w₀ z₀ hW hw₀ hβ hβW hx h0
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib _ (hβW hw₀)
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (x := x)
      (SCV.analyticAt_of_differentiableOn hβ (hW.mem_nhds hw₀)) ⟨W, hW, hw₀, hx⟩ h0 (h1 _) h2 h3 h4 h6 h7
    refine ⟨fun w => T.symm (ζ w), by simp only [hζ0, ← hT, T.symm_apply_apply], (T.symm.analyticAt _).comp hζ, ?_⟩
    filter_upwards [hζe] with w hw
    rw [← hT, T.apply_symm_apply, hw]

theorem exists_relative_exp :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w :=
  exists_relative_exp_of_parts (RelChart.exists_chart_with_parameters EtaleFamily.exists_holomorphic_sections)
    vertical_derivative_in_coordinates exists_param_exp_log_pi OpenSubgroupPts.subgroup_eq_top_of_nhds_one

end GlobalTheory.RelExp

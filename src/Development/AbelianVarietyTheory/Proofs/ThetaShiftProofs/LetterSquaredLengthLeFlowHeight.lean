module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSubspaceIsometric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmMetrisedLineLengthsEqSectionLieNorms
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SplitBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormRsmulRight
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb relab
open scoped LaurentSeries
open scoped Classical

namespace GlobalTheory.ArchLen

theorem hermForm_eq_sum {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z w = ∑ i, ∑ j, z i * Hm i j * (starRingEnd ℂ) (w j) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rfl

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp only [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (a • z) w = a * hermForm Hm z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem hermForm_rsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm (a • z) w = a * hermForm Hm z w := by
  rw [← hermForm_smul_left]; rfl

theorem hermForm_rsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = a * hermForm Hm z w := by
  simp only [hermForm_eq_sum, Finset.mul_sum, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem im_eq_on_span {g : ℕ} (Hm Hm' : Matrix (Fin g) (Fin g) ℂ)
    (A B A' B' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (S : Set (Fin g → ℂ))
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm Hm' (A' z) (B' w)).im = (hermForm Hm (A z) (B w)).im) :
    ∀ z ∈ Submodule.span ℝ S, ∀ w ∈ Submodule.span ℝ S,
      (hermForm Hm' (A' z) (B' w)).im = (hermForm Hm (A z) (B w)).im := by
  intro z hz w hw
  induction hz, hw using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact h x hx y hy
  | zero_left y _ => simp [hermForm]
  | zero_right x _ => simp [hermForm]
  | add_left x y z _ _ _ h1 h2 => simp only [map_add (f := _), hermForm_add_left, Complex.add_im, h1, h2]
  | add_right x y z _ _ _ h1 h2 => simp only [map_add (f := _), hermForm_add_right, Complex.add_im, h1, h2]
  | smul_left r x y _ _ h1 => simp only [map_smul, hermForm_rsmul_left, Complex.im_ofReal_mul, h1]
  | smul_right r x y _ _ h1 => simp only [map_smul, hermForm_rsmul_right, Complex.im_ofReal_mul, h1]

theorem hermForm_block {g : ℕ} {ι : Type} (ty : Fin g → ι) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hb : ∀ i j, ty i ≠ ty j → Hm i j = 0) (p : ι → Prop) [DecidablePred p] (z : Fin g → ℂ) :
    hermForm Hm (fun j => if p (ty j) then z j else 0) (fun j => if p (ty j) then z j else 0) =
      ∑ i, if p (ty i) then ∑ j, z i * Hm i j * (starRingEnd ℂ) (z j) else 0 := by
  rw [hermForm_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : p (ty i)
  · simp only [hi, if_true]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : p (ty j)
    · simp only [hj, if_true]
    · have : ty i ≠ ty j := fun h => hj (h ▸ hi)
      simp [hb i j this]
  · simp [hi]

variable {E : Type} [Field E] [NumberField E]

theorem emb_ext {ρ ρ' : E →+* ℂ} (h : ∀ a : 𝓞 E, ρ (a : E) = ρ' (a : E)) : ρ = ρ' := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_
  ext a
  exact h a

theorem emb_of_norm_eq {ρ ρ' : E →+* ℂ} (h : ∀ a : 𝓞 E, ‖ρ (a : E)‖ = ‖ρ' (a : E)‖) :
    ρ = ρ' ∨ ComplexEmbedding.conjugate ρ = ρ' := by
  rw [← InfinitePlace.mk_eq_iff]
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  change ‖ρ _‖ = ‖ρ' _‖
  rw [map_div₀, map_div₀, norm_div, norm_div]
  exact congrArg₂ (· / ·) (h a) (h b)

noncomputable def sqAbs (ρ : E →+* ℂ) : 𝓞 E →* ℝ where
  toFun a := ‖ρ (a : E)‖ ^ 2
  map_one' := by simp
  map_mul' a b := by simp [mul_pow]

theorem coeff_eq (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (m m' : Ψ → ℝ) (h : ∀ a : 𝓞 E, ∑ τ : Ψ, ‖τ.1 (a : E)‖ ^ 2 * m τ = ∑ τ : Ψ, ‖τ.1 (a : E)‖ ^ 2 * m' τ) :
    m = m' := by
  have hinj : Function.Injective (fun τ : Ψ => sqAbs τ.1) := by
    intro τ τ' hh
    have h1 : ∀ a : 𝓞 E, ‖τ.1 (a : E)‖ = ‖τ'.1 (a : E)‖ := fun a => by
      have : ‖τ.1 (a : E)‖ ^ 2 = ‖τ'.1 (a : E)‖ ^ 2 := DFunLike.congr_fun hh a
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    rcases emb_of_norm_eq h1 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd (h2 ▸ τ'.2) ((hΨ τ.1).1 τ.2)
  have hli := (linearIndependent_monoidHom (𝓞 E) ℝ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext τ
  have := hli (m - m') (by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    have := h a
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    exact Finset.sum_congr rfl fun τ _ => by
      change _ * ‖τ.1 (a : E)‖ ^ 2 = _
      ring) τ
  exact sub_eq_zero.1 this

theorem block_le {g : ℕ} (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (ty : Fin g → (E →+* ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hb : ∀ i j, ty i ≠ ty j → Hm i j = 0) (z : Fin g → ℂ) (m : Ψ → ℝ)
    (h : ∀ a : 𝓞 E, (hermForm Hm (fun j => ty j (a : E) * z j) (fun j => ty j (a : E) * z j)).re =
      ∑ τ : Ψ, ‖τ.1 (a : E)‖ ^ 2 * m τ) (ρ : E →+* ℂ) (τ' : Ψ)
    (hρ : τ'.1 = ρ ∨ ComplexEmbedding.conjugate τ'.1 = ρ) :
    (hermForm Hm (fun j => if ty j = ρ then z j else 0) (fun j => if ty j = ρ then z j else 0)).re ≤ m τ' := by
  have hnn : ∀ z : Fin g → ℂ, 0 ≤ (hermForm Hm z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz, hermForm]
    · exact (hpos z hz).le
  have cc2 : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := fun φ => by
    ext a; simp
  let π : (E →+* ℂ) → Ψ := fun φ => if hφ : φ ∈ Ψ then ⟨φ, hφ⟩ else
    ⟨ComplexEmbedding.conjugate φ, by by_contra h'; exact hφ ((hΨ φ).2 h')⟩
  have hπ : ∀ φ (a : E), ‖(π φ).1 a‖ = ‖φ a‖ := fun φ a => by
    by_cases hφ : φ ∈ Ψ
    · simp [π, hφ]
    · simp [π, hφ]
  have hπρ : π ρ = τ' := by
    rcases hρ with h1 | h1
    · subst h1; simp [π, τ'.2]
    · subst h1
      have := (hΨ τ'.1).1 τ'.2
      simp only [π, this, dif_neg, not_false_eq_true]
      exact Subtype.ext (cc2 _)
  set q : Fin g → ℂ := fun i => ∑ j, z i * Hm i j * (starRingEnd ℂ) (z j) with hq
  have key : m = fun τ => ∑ i, if π (ty i) = τ then (q i).re else 0 := by
    refine coeff_eq Ψ hΨ _ _ fun a => ?_
    rw [← h a, hermForm_eq_sum]
    have e1 : ∀ i, ∑ j, ty i (a : E) * z i * Hm i j * (starRingEnd ℂ) (ty j (a : E) * z j) =
        ((‖ty i (a : E)‖ ^ 2 : ℝ) : ℂ) * q i := fun i => by
      simp only [hq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : ty i = ty j
      · rw [← hij, map_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; ring
      · simp [hb i j hij]
    simp only [e1, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hπ]
  have h1 := hermForm_block ty Hm hb (fun φ => φ = ρ) z
  have h2 := hermForm_block ty Hm hb (fun φ => π φ = τ' ∧ φ ≠ ρ) z
  have h3 := hnn (fun j => if π (ty j) = τ' ∧ ty j ≠ ρ then z j else 0)
  have h4 : m τ' = (∑ i, if ty i = ρ then q i else 0).re + (∑ i, if π (ty i) = τ' ∧ ty i ≠ ρ then q i else 0).re := by
    rw [key, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ty i = ρ
    · simp [hi, hπρ]
    · by_cases hi' : π (ty i) = τ' <;> simp [hi, hi']
  have h5 : (∑ i, if π (ty i) = τ' ∧ ty i ≠ ρ then q i else 0).re ≥ 0 := by
    rw [h2] at h3
    exact h3
  have h6 : hermForm Hm (fun j => if ty j = ρ then z j else 0) (fun j => if ty j = ρ then z j else 0) =
      ∑ i, if ty i = ρ then q i else 0 := by convert h1
  rw [h6, h4]; linarith

variable [IsCMField E]

theorem emb_cc (ρ : E →+* ℂ) (x : E) : ρ (cc x) = (starRingEnd ℂ) (ρ x) :=
  IsCMField.complexEmbedding_complexConj E ρ x

theorem herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G (a • x) y = a * herm G x y := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem herm_smul_right {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G x (a • y) = cc a * herm G x y := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, cc, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermC_smul_left {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (x y : Fin r → ℂ) :
    hermC τ G (a • x) y = a * hermC τ G x y := by
  simp only [hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermC_smul_right {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (x y : Fin r → ℂ) :
    hermC τ G x (a • y) = (starRingEnd ℂ) a * hermC τ G x y := by
  simp only [hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem maj_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (a : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (a • v) = ‖a‖ ^ 2 * X.maj x τ v := by
  have e : ((‖a‖ ^ 2 : ℝ) : ℂ) = a * (starRingEnd ℂ) a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : X.posPart x τ (a • v) = ‖a‖ ^ 2 * X.posPart x τ v := by
    simp only [Data.posPart]
    rw [← Complex.re_ofReal_mul, e]
    congr 1
    simp only [hermC_smul_left, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : (hermC τ.1 X.Gm (a • v) (a • v)).re = ‖a‖ ^ 2 * (hermC τ.1 X.Gm v v).re := by
    rw [← Complex.re_ofReal_mul, e, hermC_smul_left, hermC_smul_right, mul_assoc]
  simp only [Data.maj, h1, h2]; ring

noncomputable def diagMul {g : ℕ} (d : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z := fun j => d j * z j
  map_add' z w := by funext j; simp [mul_add]
  map_smul' a z := by funext j; simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply]; ring

theorem block_of_adjoint {g : ℕ} (ty : Fin g → (E →+* ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ (a : 𝓞 E) (z w : Fin g → ℂ), (hermForm Hm (fun j => ty j (a : E) * z j) w).im =
      (hermForm Hm z (fun j => ty j (cc (a : E)) * w j)).im) (i j : Fin g) (hij : ty i ≠ ty j) : Hm i j = 0 := by
  by_contra hne
  refine hij (emb_ext fun a => ?_)
  have key : ∀ s : ℂ, (s * (ty i (a : E) * Hm i j)).im = (s * (ty j (a : E) * Hm i j)).im := fun s => by
    have := h a (Pi.single i s) (Pi.single j 1)
    simp only [hermForm_eq_sum, Pi.single_apply, mul_ite, ite_mul, mul_zero, zero_mul, apply_ite (starRingEnd ℂ),
      map_zero, map_one, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, emb_cc, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have : ty i (a : E) * Hm i j = ty j (a : E) * Hm i j := by
    apply Complex.ext
    · simpa using key Complex.I
    · simpa using key 1
  exact mul_right_cancel₀ hne this

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_inj (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := by
  intro τ τ' h
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_rt (hσ : GoodEmb c σ) (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    relab c σ τ (H.rt : E) = H.rt0 := by
  have h2 : embF c τ (H.rt : E) = (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ := Subtype.ext h
  change σ (embF c τ (H.rt : E)) = _
  rw [h2]; exact hσ

theorem period_flow (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x x' : (U.X k).dom)
    (s : (U.X k).Ψ → ℂ) (hσ : GoodEmb c σ) (hU : IsUnf U) (hξ : (U.X k).IsIso ξ')
    (hx : x'.1 = (U.X k).flow ξ' s x.1) (v : (Uw.F.Di (Uw.ik k)).La)
    (hv : herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0) : Uw.Pm k x' v = Uw.Pm k x v := by
  funext j
  rw [Uw.Pm_eq, Uw.Pm_eq, hx]
  have hf := (GlobalTheory.T.framePeriods_along_isotropic_flow_and_block_change E r (U.X k)).1 ξ' hξ.2.1 s x.1 x.2 (Uw.φ k v : Fin r → E)
  by_cases hm : relab c σ (Uw.e j).1 ∈ (U.X k).Ψ
  · have := (hf ⟨_, hm⟩ (Uw.e j).2).1
    simpa [hv] using this
  · have hm' : conjEmb (relab c σ (Uw.e j).1) ∈ (U.X k).Ψ := by
      by_contra h'
      exact hm (((U.X k).cmType _).2 h')
    have hcc : conjEmb (conjEmb (relab c σ (Uw.e j).1)) = relab c σ (Uw.e j).1 := by
      ext a; simp [conjEmb]
    have hne : ¬ (Uw.e j).1 (H.rt : E) = H.rt0 := fun h =>
      hm (((hU.2.1 k).2 _).2 (relab_rt hσ _ h))
    have hlt : ((Uw.e j).2 : ℕ) < (U.X k).p0 := by
      have h1 := (Uw.e j).2.2
      have h2 : Dw.mult (Uw.e j).1 = Dw.q := if_neg hne
      rw [(hU.2.1 k).1, ← h2]; exact h1
    have := (hf ⟨_, hm'⟩ (Uw.e j).2).2 hlt
    simpa [hv, hcc] using this

theorem riem_block (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom)
    (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (hH : IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm) (i j : Fin Uw.g)
    (hij : relab c σ (Uw.e i).1 ≠ relab c σ (Uw.e j).1) : Hm i j = 0 := by
  refine block_of_adjoint (fun j => relab c σ (Uw.e j).1) Hm (fun a z w => ?_) i j hij
  obtain ⟨hlin, -, -, hspan, -⟩ := Uw.period k x
  let a' : 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv a
  have ha' : (a' : E) = cc (a : E) := rfl
  refine im_eq_on_span Hm Hm LinearMap.id (diagMul fun j => relab c σ (Uw.e j).1 (cc (a : E)))
    (diagMul fun j => relab c σ (Uw.e j).1 (a : E)) LinearMap.id (Set.range (Uw.Pm k x)) ?_ z
    (hspan ▸ Submodule.mem_top) w (hspan ▸ Submodule.mem_top)
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  have e1 : diagMul (fun j => relab c σ (Uw.e j).1 (a : E)) (Uw.Pm k x u) = Uw.Pm k x (a • u) := by
    funext j; exact (hlin a u j).symm
  have e2 : diagMul (fun j => relab c σ (Uw.e j).1 (cc (a : E))) (Uw.Pm k x v) = Uw.Pm k x (a' • v) := by
    funext j; exact (hlin a' v j).symm
  rw [e1, e2, LinearMap.id_apply, LinearMap.id_apply, hH.2.2, hH.2.2]
  have : (((Uw.F.Di (Uw.ik k)).EF (a • u) v : ℤ) : ℚ) = (((Uw.F.Di (Uw.ik k)).EF u (a' • v) : ℤ) : ℚ) := by
    rw [Uw.iso, Uw.iso, map_smul, map_smul]
    have s1 : ((a • Uw.φ k u : (U.X k).Λ) : Fin r → E) = (a : E) • (Uw.φ k u : Fin r → E) := rfl
    have s2 : ((a' • Uw.φ k v : (U.X k).Λ) : Fin r → E) = (a' : E) • (Uw.φ k v : Fin r → E) := rfl
    rw [s1, s2, herm_smul_left, herm_smul_right, ha']
    simp [cc]
  exact_mod_cast this

theorem lengths_along_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x x' : (U.X k).dom) (s : (U.X k).Ψ → ℂ) (Hm Hm' : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x'.1 = (U.X k).flow ξ' s x.1 → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x') Hm' → (∀ V : Submodule ℂ (Fin Uw.g → ℂ), (∀ z ∈ V, z ∈ Submodule.span ℝ {p | ∃ v, herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0 ∧ p = Uw.Pm k x v}) → ∀ z ∈ V, hermForm Hm' z z = hermForm Hm z z) ∧ ∀ t, (Uw.φ k t : Fin r → E) = ξ' → ∀ (τ : E →+* ℂ) (τ' : (U.X k).Ψ), (τ'.1 = relab c σ τ ∨ conjEmb τ'.1 = relab c σ τ) → (hermForm Hm' (fun j => if (Uw.e j).1 = τ then Uw.Pm k x t j else 0) (fun j => if (Uw.e j).1 = τ then Uw.Pm k x t j else 0)).re ≤ ((U.X k).tt ξ' x'.1 τ')⁻¹ := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k ξ' x x' s Hm Hm' hσ hU hξ hx hH hH'
  have hper := period_flow U Uw k ξ' x x' s hσ hU hξ hx
  refine ⟨fun V hV z hz => ?_, fun t ht τ τ' hτ => ?_⟩
  · have him := im_eq_on_span Hm Hm' LinearMap.id LinearMap.id LinearMap.id LinearMap.id
      {p | ∃ v, herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0 ∧ p = Uw.Pm k x v} (by
        rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
        simp only [LinearMap.id_apply]
        rw [hH.2.2, ← hper u hu, ← hper v hv, hH'.2.2])
    simp only [LinearMap.id_apply] at him
    apply Complex.ext
    · have := him _ (hV _ (V.smul_mem Complex.I hz)) _ (hV _ hz)
      simpa [hermForm_smul_left] using this
    · exact him _ (hV _ hz) _ (hV _ hz)
  · rw [← hper t (by rw [ht]; exact hξ.2.1)]
    have hmaj := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x' Hm' hσ hU hH').1
    have hlin := (Uw.period k x').1
    have key := block_le (U.X k).Ψ (U.X k).cmType (fun j => relab c σ (Uw.e j).1) Hm' hH'.2.1
      (riem_block U Uw k x' Hm' hH') (Uw.Pm k x' t)
      (fun τ => (U.X k).c τ * (U.X k).maj x'.1 τ (Data.emb τ.1 ξ')) (fun a => by
        have e1 : (fun j => relab c σ (Uw.e j).1 (a : E) * Uw.Pm k x' t j) = Uw.Pm k x' (a • t) := by
          funext j; exact (hlin a t j).symm
        rw [e1, hmaj]
        refine Finset.sum_congr rfl fun τ _ => ?_
        have e2 : Data.emb τ.1 (Uw.φ k (a • t) : Fin r → E) = τ.1 (a : E) • Data.emb τ.1 ξ' := by
          rw [map_smul, ← ht]
          funext b
          exact map_mul τ.1 (a : E) _
        rw [e2, maj_smul]; ring) (relab c σ τ) τ' hτ
    simp only [(relab_inj c σ).eq_iff] at key
    rw [Data.tt, one_div, inv_inv]
    exact key

end GlobalTheory.ArchLen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnVecTorusLetter
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb relab
open scoped LaurentSeries
open scoped Classical

namespace GlobalTheory.ArcQ.TorusLetter

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem valR_eq_mul {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht' : t'.IsGen) {F : Type} [Field F] (r : Sp F ⟶ Y) (r' : Sp F ⟶ Y')
    (h : ∀ k, r ≫ φ k = r' ≫ φ' k) (c : F)
    (hv : ∀ z J, Good L z J → (val t r z J).val = TorusExt.stalkConst z c * (val t' r' z J).val)
    (j : K → L.ι) (hj : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) :
    ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j ∧ valR r _ (t.s j).val = c * valR r' _ (t'.s j).val := by
  have hj' : ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j := fun z hz => Set.mem_iInter.2 fun k => by
    have : (r ≫ φ k) z ∈ L.U (j k) := Set.mem_iInter.1 (hj hz) k
    rw [h k] at this
    exact this
  let z : Sp F := IsLocalRing.closedPoint F
  choose J hJ using fun q : Sp F ⟶ X => exists_chart hL (q z)
  replace hJ : Good L z J := hJ
  refine ⟨hj', (TorusExt.stalkConst z).injective ?_⟩
  have e₁ : TorusExt.stalkConst z (valR r _ (t.s j).val) = (gm r z (LB.wchart L φ j) (t.s j)).val :=
    (TorusExt.gs_eq_stalkConst r z hj _).symm.trans (gs_unit r z _ (hj trivial) _)
  have e₂ : TorusExt.stalkConst z (valR r' _ (t'.s j).val) = (gm r' z (LB.wchart L φ' j) (t'.s j)).val :=
    (TorusExt.gs_eq_stalkConst r' z hj' _).symm.trans (gs_unit r' z _ (hj' trivial) _)
  have e₃ : trF φ ε r z j (fun k => J (r ≫ φ k)) = trF φ' ε r' z j (fun k => J (r' ≫ φ' k)) :=
    Finset.prod_congr rfl fun k _ =>
      congrArg (fun q => gm q z (L.U (j k) ⊓ L.U (J q)) (L.g (j k) (J q)) ^ ε k) (h k)
  rw [map_mul, e₁, e₂, gen_trans ht r z (hj trivial) (hJ.mem φ r), gen_trans ht' r' z (hj' trivial) (hJ.mem φ' r'),
    e₃, Units.val_mul, Units.val_mul]
  exact (congrArg (_ * ·) (hv z J hJ)).trans (mul_left_comm _ _ _)

theorem gtφT_eq {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (x : D.X)
    (k : Fin 4) : Out.DegPre.gtφT D T b x k = b.left ≫ Out.DegPre.gtφT D D.P.A (𝟙 _) x k := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · change (toUnit _ ≫ D.c x * b).left = (b ≫ (toUnit _ ≫ D.c x * 𝟙 D.P.A)).left
    rw [MonObj.comp_mul, h, Category.comp_id]
  · change (toUnit _ ≫ D.c x).left = (b ≫ toUnit _ ≫ D.c x).left
    rw [h]
  · exact (Category.comp_id _).symm
  · change (toUnit _ ≫ η[D.P.A]).left = (b ≫ toUnit _ ≫ η[D.P.A]).left
    rw [h]

theorem zeroT_left {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (T : Over (Sp R)) :
    (Out.DegPre.zeroT D T).left = T.hom ≫ (η[D.P.A]).left := by
  have := Over.w (toUnit T)
  exact congrArg (· ≫ (η[D.P.A]).left) ((Category.comp_id _).symm.trans this)

theorem tf_hom [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] :
    (show Sp ℂ ⟶ Sp ℂ from (Out.TF (R := ℂ) ℂ).hom) = 𝟙 (Sp ℂ) := by
  refine (Spec.map_comp _ _).symm.trans ?_
  refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
  ext x
  exact (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm

theorem fderiv_of_exp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ} (hf : DifferentiableAt ℂ f 0)
    (v : V) (m : ℂ) (h : ∀ s : ℂ, f (s • v) = eTwoPi (s * m) * f 0) :
    fderiv ℂ f 0 v = 2 * Real.pi * Complex.I * m * f 0 := by
  have h₁ : HasDerivAt (fun s : ℂ => f (s • v)) (fderiv ℂ f 0 v) 0 := by
    have a : HasDerivAt (fun s : ℂ => s • v) v 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
    exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hf.hasFDerivAt a (zero_smul _ _).symm
  have h₂ : HasDerivAt (fun s : ℂ => eTwoPi (s * m) * f 0) (2 * Real.pi * Complex.I * m * f 0) 0 := by
    have := ((((hasDerivAt_id (0 : ℂ)).mul_const m).const_mul (2 * Real.pi * Complex.I)).cexp).mul_const (f 0)
    refine HasDerivAt.congr_deriv this ?_
    simp
  rw [funext h] at h₁
  exact h₁.unique h₂

theorem sum_dual_mul {E : Type} [Field E] [NumberField E] (τ ρ : E →+* ℂ) :
    ∑ i, τ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) i) *
      ρ (integralBasis E i) = if τ = ρ then 1 else 0 := by
  have := idempotent_evaluation E ℂ _ (integralBasis E) ρ τ
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [TB.evAt, TB.idemOf, TB.trDual, map_sum, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, RingHom.toRatAlgHom_apply] using this

end GlobalTheory.ArcQ.TorusLetter

namespace GlobalTheory.ArcQ

open TorusLetter MonoidalCategory CartesianMonoidalCategory MonObj

theorem anVec_torusLetter : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (ξ : Module.Dual ℤ a.D₀.X) (t : (Fu.Di Ha.i).La) (τ : E →+* ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)), (∀ v', -(Fu.Di Ha.i).EF t v' = ξ (Ha.y v')) → GtTanR ν → ν.b = Out.DegPre.zeroT a.D₀ (epsR ℂ) → (∀ x, DlogTan ν x (xiVal τ ξ x)) → AnVec Ha ν (fun j => if ty j = conjEmb τ then (2 * Real.pi * Complex.I)⁻¹ * Ha.P₀ t j else 0) := by
  intro _ E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha ξ t τ ν ht hν hb hd
  obtain ⟨nn, hN, -, -, hnn, -, -⟩ := holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  let b := RingOfIntegers.basis E
  let cf := fun i => τ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) i)
  have hbar : ∀ u : 𝓞 E, H.bar (H.bar u) = u := fun u => Subtype.ext (by
    change ((H.bar (H.bar u) : 𝓞 E) : E) = (u : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  have hEF : ∀ i v', -(Fu.Di Ha.i).EF (H.bar (b i) • t) v' = ξ (b i • Ha.y v') := fun i v' => by
    rw [(Fu.Di Ha.i).adj, hbar, ht, map_smul]
  have hr := fun i => (Ha.riemann (H.bar (b i) • t)).1 fun v' hv' => by
    have := hEF i v'
    rwa [hv', smul_zero, map_zero, neg_eq_zero] at this
  have htor : ∀ i (s : ℂ), IsTorusPt (Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t)))
      (fun x => eTwoPi (s * (ξ (b i • x) : ℤ))) := fun i s => by
    obtain ⟨x, hx, hx'⟩ := (hr i).2 s
    have hxe : x = fun z => eTwoPi (s * (ξ (b i • z) : ℤ)) := funext fun z => by
      obtain ⟨v', rfl⟩ := Ha.y_onto z
      rw [hx', ← hEF]
      congr 1
      push_cast
      ring
    exact hxe ▸ hx
  have hyt : Ha.y t = 0 := ((Ha.riemann t).1 fun v' hv' => by
    have := ht v'
    rwa [hv', map_zero, neg_eq_zero] at this).1
  have hP : ∀ (u : 𝓞 E) j, Ha.P₀ (u • t) j = ty j (u : E) * Ha.P₀ t j := fun u j => by
    have h := (Ha.period (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) (by simp)).1 u t j
    rwa [Ha.Pw_eq, Ha.Pw_eq, hN, hN, hnn t hyt, hnn _ (by rw [map_smul, hyt, smul_zero]), map_zero, smul_zero,
      add_zero, add_zero] at h
  have hz : (fun j => if ty j = conjEmb τ then (2 * Real.pi * Complex.I)⁻¹ * Ha.P₀ t j else 0) =
      ∑ i, ((2 * Real.pi * Complex.I)⁻¹ * cf i) • Ha.P₀ (H.bar (b i) • t) := funext fun j => by
    have h := sum_dual_mul τ (conjEmb (ty j))
    have e : ∀ i, ty j ((H.bar (b i) : 𝓞 E) : E) = conjEmb (ty j) (integralBasis E i) := fun i => by
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, integralBasis_apply]
      rfl
    have hc : ty j = conjEmb τ ↔ τ = conjEmb (ty j) := by
      constructor <;> (intro q; rw [q]; ext u; simp [conjEmb])
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hP, e]
    calc _ = (2 * Real.pi * Complex.I)⁻¹ * (if τ = conjEmb (ty j) then 1 else 0) * Ha.P₀ t j := by
          simp only [hc]; split_ifs <;> simp
      _ = _ := by
          rw [← h, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by simp only [cf]; ring
  rw [hz]
  have h0 : (Ha.ex₀ 0).IsZero := (Ha.ker 0).2 ⟨0, map_zero _, (map_zero _).symm⟩
  have hzF : ∀ p : Out.GtPtF a.D₀ ℂ, p.b = Out.DegPre.zeroF a.D₀ ℂ →
      (show Sp ℂ ⟶ _ from p.b.left) = (η[a.D₀.P.A]).left := fun p hp => by
    rw [hp]
    exact (zeroT_left a.D₀ _).trans ((congrArg (· ≫ (η[a.D₀.P.A]).left) tf_hom).trans (Category.id_comp _))
  have hνb : ν.b.left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (η[a.D₀.P.A]).left := by
    rw [hb]; exact zeroT_left a.D₀ _
  obtain ⟨g₀, hg₀, hp⟩ := hν
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν.b.left = (Ha.ex₀ 0).b.left := by
    rw [← hp.1, hg₀.1]
    exact (zeroT_left a.D₀ _).trans ((Category.id_comp _).trans (hzF _ h0.1).symm)
  refine ⟨⟨hfst, fun U hU f => ?_⟩, fun x j hj => ?_⟩
  · have hU0 : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ 0).b.left) ⁻¹ᵁ U :=
      hfst ▸ (ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom _ U hU).1
    have hdf : DifferentiableAt ℂ (fun z => valAt' (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) U f) 0 :=
      (Ha.hol_b U f).2.differentiableAt ((Ha.hol_b U f).1.mem_nhds ⟨trivial, hU0⟩)
    have hl : valR (A := DualNumber ℂ) ν.b.left U f = algebraMap ℂ _ (valR (A := ℂ) (η[a.D₀.P.A]).left U f) := by
      rw [hνb]
      exact (ZH.CrdCalc.valR_spMap _ _ U (hzF _ h0.1 ▸ hU0)).2 f
    refine (congrArg TrivSqZeroExt.snd ((ZH.CrdCalc.valR_eq _ U hU f).symm.trans hl)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Eq.trans rfl (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [map_smul, fderiv_of_exp hdf _ 0 fun s => ?_]
    · simp
    · rw [hzF _ (htor i s).1, hzF _ h0.1]
      simp [eTwoPi]
  · have hL := a.D₀.P.isLB
    obtain ⟨-, hv0⟩ := (isZero_iff _).1 h0
    obtain ⟨hj0, e0⟩ := valR_eq_mul hL (ν.isGen x) ((Ha.ex₀ 0).isGen x)
      (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (𝟙 (Sp ℂ)) (fun k => by
        rw [gtφT_eq, ← Category.assoc, hfst]
        exact (gtφT_eq a.D₀ (Ha.ex₀ 0).b x k).symm.trans (Category.id_comp _).symm) 1 (fun z J hJ => by
        have e₁ := (val_corr hJ (hg₀.2 x) (𝟙 _)).trans (val_one _)
        have e₂ := (val_corr hJ (hp.2 x) (𝟙 _)).trans (val_pull hJ _ _ _)
        rw [Category.id_comp] at e₂
        rw [map_one, _root_.one_mul]
        exact congrArg Units.val ((e₂.symm.trans e₁).trans (hv0 x z J hJ).symm)) j (fun z _ => hj trivial)
    have hf : TrivSqZeroExt.fst (valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val) = chiVal (Ha.ex₀ 0) x j := by
      have := (ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _)
        (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j) hj).2 ((ν.s x).s j).val
      rw [Category.comp_id] at this
      exact this.symm.trans (e0.trans (_root_.one_mul _))
    have hset : ∀ z, (⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ z).b x) j) ↔
        ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) ⁻¹ᵁ
          LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x) j := fun z => by
      have e : Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ z).b x =
          fun k => (Ha.ex₀ z).b.left ≫ Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x k :=
        funext fun k => gtφT_eq a.D₀ (Ha.ex₀ z).b x k
      rw [e]
      exact ⟨fun h y _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h trivial) k,
        fun h y _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h trivial) k⟩
    have hdf : DifferentiableAt ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 := by
      refine (Ha.hol_chi x j).differentiableAt (IsOpen.mem_nhds ?_ hj0)
      simpa only [hset, Set.mem_univ, true_and] using
        (Ha.hol_b (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x) j) 0).1
    have hder : ∀ i, fderiv ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 (Ha.P₀ (H.bar (b i) • t)) =
        2 * Real.pi * Complex.I * (ξ (b i • x) : ℤ) * chiVal (Ha.ex₀ 0) x j := fun i =>
      fderiv_of_exp hdf _ _ fun s => by
        obtain ⟨hb₁, hv₁⟩ := (TorusExt.isTorusPtF_iff_val _ _).1
          ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (htor i s))
        have hφ : Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t))).b x =
            Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ 0).b x := by rw [(htor i s).1, h0.1]
        exact (valR_eq_mul hL ((Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t))).isGen x) ((Ha.ex₀ 0).isGen x)
          (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (fun k => by rw [hφ]) _ (fun z J hJ => (hv₁ x z J hJ).trans
            ((_root_.mul_one _).symm.trans (congrArg₂ (fun p q : (Sp ℂ).presheaf.stalk z => p * q) rfl
              (congrArg Units.val (hv0 x z J hJ)).symm))) j
          (by rw [hφ]; exact hj0)).2
    refine TrivSqZeroExt.ext (by simpa using hf) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hd x j hj, hf, map_sum]
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_smul, hder,
      smul_eq_mul, xiVal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.two_pi_I_ne_zero
    simp only [cf, b]
    field_simp

end GlobalTheory.ArcQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LetterSquaredLengthLeFlowHeight
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb relab
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.LetterLen

section Scale

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : DegPre A}
  {D₁ : DegPre A'} (p : IsPullDeg f D₀ D₁)

theorem isPull_scale {a : A} {ν ω : GtPt D₀ (epsR A)} {ν₁ ω₁ : GtPt D₁ (epsR A')} (h : LetBC p ν ν₁)
    (h' : LetBC p ω ω₁) (hs : GtPt.IsPull (spMap (epsScaleR a)) ν ω) :
    GtPt.IsPull (spMap (epsScaleR (f a))) ν₁ ω₁ := by
  have gp := pull_grp p
  rw [ArcQBC.letBC_iff] at h h'
  have e : spMap (dualMap f) ≫ spMap (epsScaleR a) = spMap (epsScaleR (f a)) ≫ spMap (dualMap f) :=
    LieCombBaseChange.dualMap_epsScale f a
  have o : spMap (epsScaleR (f a)) ≫ (epsR A').hom = (epsR A').hom :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by
      simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]))
  have hb : ω₁.b.left = spMap (epsScaleR (f a)) ≫ ν₁.b.left := by
    refine gp.1.hom_ext ?_ ?_
    · refine h'.1.trans ?_
      rw [hs.1, ← Category.assoc, e, Category.assoc, ← h.1]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, Over.w, Over.w, o]
  refine ⟨hb, fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
  have e₁ := ConstFam.pmaps_val (h'.2 χ).1 (h'.2 χ).2 (𝟙 _) hJ hJ'
  have e₂ := ConstFam.pmaps_val (h.2 χ).1 (h.2 χ).2 (𝟙 _ ≫ spMap (epsScaleR (f a))) hJ hJ'
  have e₃ := (val_corr hJ (hs.2 (p.xe χ)) (𝟙 _ ≫ spMap (dualMap f))).trans (val_pull hJ _ _ _)
  have g : ∀ k, (𝟙 _ ≫ spMap (epsScaleR (f a))) ≫ DegPre.gtφT D₁ (epsR A') ν₁.b χ k =
      𝟙 _ ≫ DegPre.gtφT D₁ (epsR A') ω₁.b χ k := fun k => by
    rw [TorusCoord.gtφT_eq ω₁.b]
    exact (TorusCoord.comp_eq_of_left ν₁.b ω₁.b _ _
      ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hb.symm))).1 χ k
  have m : (𝟙 _ ≫ spMap (dualMap f)) ≫ spMap (epsScaleR a) =
      (𝟙 _ ≫ spMap (epsScaleR (f a))) ≫ spMap (dualMap f) := by rw [Category.assoc, e, Category.assoc]
  simp only [g] at e₂
  have e₄ := e₁.symm.trans (e₃.trans ((congrArg (fun r => val (ν.s (p.xe χ)) r y J) m).trans e₂))
  exact (mul_left_cancel e₄).trans (val_pull hJ' _ _ _).symm

theorem exists_vec (v : epsR A ⟶ D₀.P.A) (hv : IsTangent v) :
    ∃ v₁ : epsR A' ⟶ D₁.P.A, v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left ∧ IsTangent v₁ := by
  have gp := pull_grp p
  have w : (spMap (dualMap f) ≫ v.left) ≫ D₀.P.A.hom = (epsR A').hom ≫ spMap f := by
    rw [Category.assoc, Over.w, ArcQBC.dual_base]
  have e := gp.1.lift_fst _ _ w
  exact ⟨Over.homMk (gp.1.lift _ _ w) (gp.1.lift_snd _ _ w), e, IsVecOver.isTangent gp e hv⟩

end Scale


open Classical in
theorem map_proj {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ (a : 𝓞 E), ∀ v ∈ S, L (fun j => ty j (a : E) * v j) = fun j => ty j (a : E) * L v j) (ρ : E →+* ℂ)
    (v : Fin g → ℂ) : L (fun j => if ty j = ρ then v j else 0) = fun j => if ty j = ρ then L v j else 0 := by
  have h₁ : ∀ (a : 𝓞 E) v, L (fun j => ty j (a : E) * v j) = fun j => ty j (a : E) * L v j := fun a v => by
    have hv : v ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => exact h a x hx
    | zero => funext j; simp [show (fun _ : Fin g => (0 : ℂ)) = 0 from rfl]
    | add x y _ _ hx hy =>
      have : (fun j => ty j (a : E) * (x + y) j) = (fun j => ty j (a : E) * x j) + fun j => ty j (a : E) * y j := by
        funext j; simp [mul_add]
      rw [this, map_add (f := _), map_add (f := _), hx, hy]
      funext j; simp [mul_add]
    | smul r x _ hx =>
      have : (fun j => ty j (a : E) * (r • x) j) = (r : ℂ) • (fun j => ty j (a : E) * x j) := by
        funext j; simp; ring
      rw [this, map_smul, hx, show r • x = (r : ℂ) • x from rfl, map_smul]
      funext j; simp; ring
  have h₂ : ∀ i j, ty i ≠ ty j → L (Pi.single j 1) i = 0 := fun i j hij => by
    by_contra hne
    refine hij (ArchLen.emb_ext fun a => mul_right_cancel₀ hne ?_)
    have := congrFun (h₁ a (Pi.single j 1)) i
    have e : (fun k => ty k (a : E) * (Pi.single j 1 : Fin g → ℂ) k) = ty j (a : E) • (Pi.single j 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [e, map_smul] at this
    exact this.symm
  have h₃ : ∀ u : Fin g → ℂ, ∀ i, L u i = ∑ j, u j * L (Pi.single j 1) i := fun u i => by
    rw [LinearMap.pi_apply_eq_sum_univ L u, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (fun k => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
      funext k; simp [Pi.single_apply, eq_comm]
    rw [this]; rfl
  funext i
  rw [h₃, h₃ v]
  split_ifs with hi
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · rw [h₂ i j (fun q => hj (q.symm.trans hi))]; simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hj
    · rw [h₂ i j (fun q => hi (q.trans hj))]; simp
    · simp

theorem exists_pull_form {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Hm'.IsHermitian ∧ ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := by
  obtain ⟨B, rfl⟩ := Matrix.toLin'.surjective L
  refine ⟨B.transpose * Hm * B.transpose.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose _ hH, fun z w => ?_⟩
  simp only [hermForm, Matrix.toLin'_apply]
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z,
    Matrix.vecMul_transpose, ← Matrix.mulVec_transpose]
  rfl

theorem eq_zero_of_trace {E : Type} [Field E] [NumberField E] {x : E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * x) = 0) : x = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 x fun y => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (integralBasis E).sum_repr y, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, Algebra.traceForm_apply, integralBasis_apply, _root_.mul_comm x]
  exact smul_eq_zero_of_right _ (h _)

theorem herm_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (u v : Fin r → E) :
    herm X.Gm v u = cc (herm X.Gm u v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← X.Gm_herm a b, cc]
  ring

theorem le_sq_of_log {y b m : ℝ} (hb : 0 < b) (hm : 1 ≤ m) (h : Real.log y / 2 ≤ Real.log b) : y ≤ (b * m) ^ 2 := by
  have h₁ : y ≤ b ^ 2 := by
    by_contra hn
    have := Real.log_lt_log (pow_pos hb 2) (not_le.1 hn)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  exact h₁.trans (pow_le_pow_left₀ hb.le (le_mul_of_one_le_right hb.le hm) 2)

theorem letter_length_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (aC : ArcIn Dw l β ℂ (σ.comp β)) (p : Out.IsPullDeg em a.D₀ aC.D₀) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y aC χ) (Ha : HolArc Y σ aC χ W Uw.F) (k : U.Comp) (ξ' : Fin r → E) (x x'' : (U.X k).dom) (sf : (U.X k).Ψ → ℂ) (w₁ : ℂ) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La) (ep : ℝ) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), σ = em.comp (algebraMap c.F K₁) → GoodEmb c σ → IsUnf U → InBC em (a.restrict β) aC p → 1 ≤ La → 0 < ep → (U.X k).IsIso ξ' → Ha.T < w₁.im → (∀ v, Uw.Pm k x (gm v) = L (Ha.Pw w₁ v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (gm v) (gm v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = s.ξ (p.xe (Ha.y v'))) ∧ (Uw.φ k (gm t) : Fin r → E) = ξ') → x''.1 = (U.X k).flow ξ' sf x.1 → (∀ τ, (U.X k).tt ξ' x''.1 τ = ep) → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x'') Hm → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (eC : Out.GtPt aC.D₀ (epsR ℂ)) (z : Fin Uw.g → ℂ), LetBC p (e τ i) eC → AnVec Ha eC z → Real.pi * (hermForm Hm (L z) (L z)).re ≤ (La * Real.sqrt (max 1 ep⁻¹) * (s.line τ i).n em) ^ 2 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ a e th jj n' La c₁ s em _ _ σ r U Uw O _ β Y aC p χ W Ha k ξ' x x'' sf w₁ L gm
    ep Hm hσ hG hU hBC hLa hep hξ hw hP hEF ⟨t, ht, htξ⟩ hx htt hH τ i eC z hL hz
  classical
  letI := H.starRing
  have hGl : Out.GlobalFnsSt := hK.laws.globalFns
  obtain ⟨hlin, -, -, -, Hm₀, hH₀⟩ := Uw.period k x
  obtain ⟨hlin', -, -, hspan', -⟩ := Ha.period w₁ hw
  obtain ⟨hab, htor⟩ := ArchLen.lengths_along_flow E H Dw l Xo c σ r U Uw k ξ' x x'' sf Hm₀ Hm hG hU hξ hx hH₀ hH
  obtain ⟨nn, hN, -, -, hnn, hy, -⟩ := holArc_nilpotent E H Dw l Xo c σ O β Y aC χ W _ _ Uw.F Ha
  have hPw : ∀ v, Ha.y v = 0 → Ha.Pw w₁ v = Ha.P₀ v := fun v hv => by
    rw [Ha.Pw_eq, hN, hnn v hv, map_zero, smul_zero, add_zero]
  have ht0 : ∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF t v' = 0 := fun v' hv' => by
    have := ht v'
    rwa [hv', map_zero, map_zero, neg_eq_zero] at this
  have hm : 1 ≤ Real.sqrt (max 1 ep⁻¹) := Real.one_le_sqrt.2 (le_max_left _ _)
  have htan : GtTanR eC := ArcQBC.gtTanR_of_letBC p hGl hL (s.tan τ i)
  unfold CMIn.line
  cases hk : s.kind τ i with
  | none =>
    obtain ⟨hb, hd⟩ := s.xi τ i hk
    obtain ⟨hsm, hadd, -⟩ := pairE_properties E a.D₀.X s.ξ
    let φ₀ : a.D₀.X →+ K₁ := AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE s.ξ x))) fun x y => by
      rw [hadd]; simp [cc]
    obtain ⟨b₂, d₂⟩ := (TorusTangent.main hGl K₁ a.D₀).2.2 ℂ aC.D₀ em p φ₀ (e τ i) eC hb hd hL
    let ξC : Module.Dual ℤ aC.D₀.X := s.ξ.comp p.xe.toIntLinearEquiv.toLinearMap
    have hpair : ∀ y, pairE (E := E) ξC y = pairE s.ξ (p.xe y) := fun y =>
      Finset.sum_congr rfl fun j _ => congrArg (fun q => _ * ((s.ξ q : ℤ) : E)) (hBC.2.1 _ y)
    have hv : ∀ y, xiVal (conjEmb (relab c σ τ)) ξC y = em (φ₀ (p.xe y)) := fun y => by
      rw [(pairE_properties E aC.D₀.X ξC).2.2.2.2, hpair]
      refine (ArchLen.emb_cc (relab c σ τ) _).symm.trans ?_
      exact RingHom.congr_fun hσ _
    have ha := anVec_torusLetter hGl E H Dw l Xo c σ O β Y aC χ W _ _ Uw.F Ha ξC t (conjEmb (relab c σ τ)) eC ht htan b₂
      fun y j hj => (d₂ y j hj).trans (congrArg _ (hv y).symm)
    have hcc : conjEmb (conjEmb (relab c σ τ)) = relab c σ τ := by ext u; simp [conjEmb]
    rw [hcc] at ha
    have hz' := ((ExpTan.anVec_bijective hGl E H Dw l Xo c σ O β Y aC χ W _ _ Uw.F Ha).1 eC htan).unique hz ha
    have hLz : L z = (2 * Real.pi * Complex.I : ℂ)⁻¹ • fun j => if (Uw.e j).1 = τ then Uw.Pm k x (gm t) j else 0 := by
      have := map_proj (fun j => relab c σ (Uw.e j).1) L.toLinearMap _ hspan' (by
        rintro u _ ⟨v, rfl⟩
        funext j
        have e₁ : (fun j => relab c σ (Uw.e j).1 (u : E) * Ha.Pw w₁ v j) = Ha.Pw w₁ (u • v) :=
          funext fun j => (hlin' u v j).symm
        rw [e₁, LinearEquiv.coe_coe, ← hP, ← hP, map_smul, hlin]) (relab c σ τ) (Ha.Pw w₁ t)
      simp only [(ArchLen.relab_inj c σ).eq_iff, LinearEquiv.coe_coe] at this hz'
      rw [hP, ← this, ← map_smul, hz', hPw t (hy t ht0)]
      congr 1
      funext j
      by_cases h : (Uw.e j).1 = τ <;> simp [h, Pi.smul_apply, smul_eq_mul]
    obtain ⟨τ', hτ'⟩ : ∃ τ' : (U.X k).Ψ, τ'.1 = relab c σ τ ∨ conjEmb τ'.1 = relab c σ τ := by
      by_cases hm : relab c σ τ ∈ (U.X k).Ψ
      · exact ⟨⟨_, hm⟩, Or.inl rfl⟩
      · refine ⟨⟨conjEmb (relab c σ τ), ?_⟩, Or.inr hcc⟩
        by_contra h'
        exact hm (((U.X k).cmType _).2 h')
    have key := htor (gm t) htξ τ τ' hτ'
    rw [htt] at key
    have hs : ∀ (q : ℂ) (u : Fin Uw.g → ℂ), (hermForm Hm (q • u) (q • u)).re = ‖q‖ ^ 2 * (hermForm Hm u u).re :=
      fun q u => by
        rw [← Complex.re_ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        congr 1
        rw [Complex.star_def]; ring
    have hn : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      simp [abs_of_pos Real.pi_pos]
    rw [hLz, hs, hn]
    have hπ := Real.pi_gt_three
    have h1 : Real.pi * (2 * Real.pi)⁻¹ ^ 2 ≤ 1 := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
      nlinarith
    have h2 : (0 : ℝ) ≤ Real.pi * (2 * Real.pi)⁻¹ ^ 2 := by positivity
    have h3 : ep⁻¹ ≤ max 1 ep⁻¹ := le_max_right _ _
    have h4 : max 1 ep⁻¹ ≤ (La * Real.sqrt (max 1 ep⁻¹) * 1) ^ 2 := by
      rw [_root_.mul_one, mul_pow, Real.sq_sqrt (by positivity)]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hLa)
    refine le_trans ?_ (h3.trans h4)
    rw [← _root_.mul_assoc]
    refine (mul_le_mul_of_nonneg_left ?_ h2).trans (mul_le_of_le_one_left (inv_pos.2 hep).le h1)
    convert key
  | some m =>
    obtain ⟨w, hw₁, hw₂⟩ := s.eta τ i m hk
    have htw : IsTangent w := by
      obtain ⟨w', hw1, hw2⟩ := s.L_good.2.2.1 m
      obtain rfl : w = w' := by
        refine Over.OverMorphism.ext (s.good.2.2.2.1.1.1.hom_ext ?_ ((Over.w w).trans (Over.w w').symm))
        unfold LamLetters.IsLetter at hw₁ hw1
        cases hq : s.L.src m with
        | inl q => rw [hq] at hw₁ hw1; exact hw₁.trans hw1.symm
        | inr q => rw [hq] at hw₁ hw1; exact hw₁.trans hw1.symm
      exact GlobalTheory.Reg.isTangent_of_isLieComb s.basis.1 hw2
    have hpos : 0 < (s.L.ℓ m).n em := by
      have := s.L_good.2.2.2 m
      cases hq : s.L.src m with
      | inl q => rw [hq] at this; exact this ▸ (s.good.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q.2).1.2 em
      | inr q => rw [hq] at this; exact this ▸ (s.good.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q.2).1.2 em
    obtain ⟨wC, hwC, htC⟩ := exists_vec p w htw
    obtain ⟨hc, -⟩ := (TauCanPull.tauCan_iff_of_isPullDeg hK K₁ ℂ em a.D₀ aC.D₀ p n' em.injective a.bimult
      aC.bimult).1 s.tau
    obtain ⟨sC, hsC⟩ := exists_isSplit hK ℂ aC.D₀ n' s.n_pos hc
    have hsc := isPull_scale p (SplitBC.split_baseChange hK K₁ ℂ em a.D₀ aC.D₀ p n' s.sB sC em.injective s.split hsC
      w wC hwC).2 hL hw₂
    rw [map_inv₀, map_natCast] at hsc
    obtain ⟨V, hV, hV'⟩ := AbelianLetters.exists_subspace_isometric hK.laws hK.laws2 E H Dw l Xo c σ O β Y aC χ W _ _
      Uw.F Ha n' sC s.n_pos hsC.1 hsC.2.1 hsC.2.2
    obtain ⟨hzV, hlen⟩ := hV' wC eC z htC hsc hz
    obtain ⟨y, hy₁, hy₂⟩ := ((NormTie.lengths_eq_norms hK E H Dw l c K₁ a e th jj n' La c₁ s em).2.2.2 aC.D₀ p).2
      m w wC hw₁ hwC
    obtain ⟨Hm₁, hh, hf⟩ := exists_pull_form Hm₀ hH₀.1 L.toLinearMap
    simp only [LinearEquiv.coe_coe] at hf
    have hy₃ := hlen w₁ Hm₁ y hw ⟨hh, fun u hu => hf u u ▸ hH₀.2.1 _ (L.map_ne_zero_iff.2 hu), fun u v => by
      rw [hf, ← hP, ← hP, hH₀.2.2, hEF]⟩ hy₁
    have horth : ∀ v, Ha.y v = 0 → herm (U.X k).Gm (Uw.φ k (gm v) : Fin r → E) ξ' = 0 := fun v hv => by
      have := eq_zero_of_trace (x := cc (-(U.X k).ξ0) * herm (U.X k).Gm (Uw.φ k (gm v) : Fin r → E) ξ') fun u => by
        have e₁ := Uw.iso k (gm t) (gm (u • v))
        rw [hEF, ht0 _ (by rw [map_smul, hv, smul_zero]), htξ, map_smul, map_smul] at e₁
        have s1 : ((u • Uw.φ k (gm v) : (U.X k).Λ) : Fin r → E) = (u : E) • (Uw.φ k (gm v) : Fin r → E) := rfl
        rw [s1, herm_swap, ArchLen.herm_smul_left] at e₁
        have e₂ := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ)
          ((u : E) * (cc (-(U.X k).ξ0) * herm (U.X k).Gm (Uw.φ k (gm v) : Fin r → E) ξ'))
        rw [← e₂]
        refine Eq.trans ?_ (e₁.symm.trans (by simp))
        congr 1
        simp only [cc, AlgEquiv.coe_restrictScalars', map_mul, IsCMField.complexConj_apply_apply]
        ring
      exact (mul_eq_zero.1 this).resolve_left
        ((map_ne_zero (IsCMField.complexConj E)).2 (neg_ne_zero.2 (U.X k).ξ0_ne))
    have hsame := hab (V.map L.toLinearMap) (by
      rintro _ ⟨u, hu, rfl⟩
      refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span (L.toLinearMap.restrictScalars ℝ) (hV u hu))
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨gm v, horth v hv, by rw [hP, hPw v hv]; rfl⟩) (L z) ⟨z, hzV, rfl⟩
    rw [hsame, ← hf, mul_right_comm]
    have hLa' : 0 < La := one_pos.trans_le hLa
    exact le_sq_of_log (mul_pos hLa' hpos) hm (hy₃ ▸ hy₂ hLa')

end GlobalTheory.LetterLen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LetterSquaredLengthLeFlowHeightStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb relab
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letter_squaredLength_le_flow_height : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (aC : ArcIn Dw l β ℂ (σ.comp β)) (p : Out.IsPullDeg em a.D₀ aC.D₀) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y aC χ) (Ha : HolArc Y σ aC χ W Uw.F) (k : U.Comp) (ξ' : Fin r → E) (x x'' : (U.X k).dom) (sf : (U.X k).Ψ → ℂ) (w₁ : ℂ) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La) (ep : ℝ) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), σ = em.comp (algebraMap c.F K₁) → GoodEmb c σ → IsUnf U → InBC em (a.restrict β) aC p → 1 ≤ La → 0 < ep → (U.X k).IsIso ξ' → Ha.T < w₁.im → (∀ v, Uw.Pm k x (gm v) = L (Ha.Pw w₁ v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (gm v) (gm v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = s.ξ (p.xe (Ha.y v'))) ∧ (Uw.φ k (gm t) : Fin r → E) = ξ') → x''.1 = (U.X k).flow ξ' sf x.1 → (∀ τ, (U.X k).tt ξ' x''.1 τ = ep) → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x'') Hm → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (eC : Out.GtPt aC.D₀ (epsR ℂ)) (z : Fin Uw.g → ℂ), LetBC p (e τ i) eC → AnVec Ha eC z → Real.pi * (hermForm Hm (L z) (L z)).re ≤ (La * Real.sqrt (max 1 ep⁻¹) * (s.line τ i).n em) ^ 2 := by
  first | exact @GlobalTheory.LetterLen.letter_length_le | exact GlobalTheory.LetterLen.letter_length_le | (intros; apply GlobalTheory.LetterLen.letter_length_le <;> assumption)
end

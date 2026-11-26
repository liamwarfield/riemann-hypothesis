module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermCompletionEquiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

namespace GermCompletionEquiv

theorem factorPow_evalₐ {R : Type} [CommRing R] (J : Ideal R) {k l : ℕ} (h : k ≤ l) (x : AdicCompletion J R) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J l x) = AdicCompletion.evalₐ J k x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk J h]

variable {σ : Type} [Fintype σ] (w : σ → ℂ)

theorem sub_polyGerm_C_mem (f : holGerms w) :
    f - polyGerm w (C (holGermValue w f)) ∈ holGermPointIdeal w := by
  rw [holGermPointIdeal, RingHom.mem_ker, map_sub, holGermValue_polyGerm, eval_C, sub_self]

theorem exists_sub_polyGerm_mem (hH : HolGermPointIdealSpan.Statement) (k : ℕ) (f : holGerms w) :
    ∃ q : MvPolynomial σ ℂ, f - polyGerm w q ∈ holGermPointIdeal w ^ k := by
  induction k generalizing f with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih f
    have hkey : holGermPointIdeal w ^ k =
        Ideal.span (polyGerm w '' ↑(Ideal.span (Set.range fun i : σ => (X i - C (w i) : MvPolynomial σ ℂ)) ^ k)) := by
      have e : Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i))) =
          (Ideal.span (Set.range fun i : σ => (X i - C (w i) : MvPolynomial σ ℂ))).map (polyGerm w) := by
        rw [Ideal.map_span, ← Set.range_comp]; rfl
      rw [hH σ w, e, ← Ideal.map_pow]; rfl
    have step : ∀ g ∈ holGermPointIdeal w ^ k,
        ∃ q' : MvPolynomial σ ℂ, g - polyGerm w q' ∈ holGermPointIdeal w ^ (k + 1) := by
      intro g hg
      rw [hkey] at hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, -, rfl⟩ := hx
        exact ⟨p, by simp⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ h1 h2 =>
        obtain ⟨q1, h1⟩ := h1
        obtain ⟨q2, h2⟩ := h2
        refine ⟨q1 + q2, ?_⟩
        rw [map_add (f := _)]
        convert add_mem h1 h2 using 1
        ring
      | smul a x hx h =>
        obtain ⟨q1, h1⟩ := h
        have hx' : x ∈ holGermPointIdeal w ^ k := hkey ▸ hx
        refine ⟨C (holGermValue w a) * q1, ?_⟩
        have e : a • x - polyGerm w (C (holGermValue w a) * q1) =
            polyGerm w (C (holGermValue w a)) * (x - polyGerm w q1) +
              (a - polyGerm w (C (holGermValue w a))) * x := by
          rw [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ h1) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (sub_polyGerm_C_mem w a) hx'
    obtain ⟨q', hq'⟩ := step _ hq
    exact ⟨q + q', by rw [map_add (f := _), ← sub_sub]; exact hq'⟩

variable (I : Ideal (MvPolynomial σ ℂ))

theorem exists_sub_polyGerm_mem_of_mem_map (hH : HolGermPointIdealSpan.Statement) (k : ℕ) {x : holGerms w}
    (hx : x ∈ I.map (polyGerm w)) :
    ∃ i ∈ I, x - polyGerm w i ∈ holGermPointIdeal w ^ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, by simp⟩
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨i1, hi1, h1⟩ := h1
    obtain ⟨i2, hi2, h2⟩ := h2
    refine ⟨i1 + i2, I.add_mem hi1 hi2, ?_⟩
    rw [map_add (f := _)]
    convert add_mem h1 h2 using 1
    ring
  | smul a x _ h =>
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨q0, hq0⟩ := exists_sub_polyGerm_mem w hH k a
    refine ⟨q0 * i, I.mul_mem_left _ hi, ?_⟩
    have e : a • x - polyGerm w (q0 * i) =
        (a - polyGerm w q0) * x + polyGerm w q0 * (x - polyGerm w i) := by
      rw [smul_eq_mul, map_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hq0) (Ideal.mul_mem_left _ _ h)

def phi : MvPolynomial σ ℂ ⧸ I →+* holGerms w ⧸ I.map (polyGerm w) :=
  Ideal.quotientMap _ (polyGerm w) Ideal.le_comap_map

theorem phi_mk (q : MvPolynomial σ ℂ) :
    phi w I (Ideal.Quotient.mk I q) = Ideal.Quotient.mk _ (polyGerm w q) :=
  Ideal.quotientMap_mk

theorem pow_le_comap (k : ℕ) :
    polyPointIdeal I w ^ k ≤ (germQuotPointIdeal I w ^ k).comap (phi w I) := by
  refine (Ideal.pow_right_mono ?_ k).trans (Ideal.le_comap_pow _ k)
  rw [polyPointIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro q hq
  rw [Ideal.mem_comap, RingHom.comp_apply, phi_mk, germQuotPointIdeal]
  exact Ideal.mem_map_of_mem _ (by rw [holGermPointIdeal, RingHom.mem_ker, holGermValue_polyGerm]; exact hq)

def psi (k : ℕ) : (MvPolynomial σ ℂ ⧸ I) ⧸ polyPointIdeal I w ^ k →+*
    (holGerms w ⧸ I.map (polyGerm w)) ⧸ germQuotPointIdeal I w ^ k :=
  Ideal.quotientMap _ (phi w I) (pow_le_comap w I k)

theorem psi_mk (k : ℕ) (q : MvPolynomial σ ℂ) :
    psi w I k (Ideal.Quotient.mk _ (Ideal.Quotient.mk I q)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (polyGerm w q)) := by
  rw [psi, Ideal.quotientMap_mk, phi_mk]

theorem psi_surjective (hH : HolGermPointIdealSpan.Statement) (k : ℕ) : Function.Surjective (psi w I k) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨q, hq⟩ := exists_sub_polyGerm_mem w hH k f
  refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk I q), ?_⟩
  rw [psi_mk, Ideal.Quotient.eq, germQuotPointIdeal, ← Ideal.map_pow, ← map_sub]
  exact Ideal.mem_map_of_mem _ (by rw [← neg_sub]; exact neg_mem hq)

theorem psi_injective (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) (k : ℕ) :
    Function.Injective (psi w I k) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [psi_mk, Ideal.Quotient.eq_zero_iff_mem, germQuotPointIdeal, ← Ideal.map_pow,
    Ideal.mem_quotient_iff_mem_sup, Submodule.mem_sup] at hy
  obtain ⟨μ, hμ, ι, hι, he⟩ := hy
  obtain ⟨i, hi, hi'⟩ := exists_sub_polyGerm_mem_of_mem_map w I hH k hι
  have hqi : polyGerm w (q - i) ∈ holGermPointIdeal w ^ k := by
    rw [map_sub, ← he]
    convert add_mem hμ hi' using 1
    ring
  have hq := hP σ w k (q - i) hqi
  have e : q = (q - i) + i := by ring
  rw [Ideal.Quotient.eq_zero_iff_mem, polyPointIdeal, ← Ideal.map_pow, e, map_add (f := _),
    Ideal.Quotient.eq_zero_iff_mem.2 hi, add_zero]
  exact Ideal.mem_map_of_mem _ hq

theorem psi_factorPow {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h).comp (psi w I l) =
      (psi w I k).comp (Ideal.Quotient.factorPow (polyPointIdeal I w) h) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [RingHom.comp_apply, psi_mk, Ideal.Quotient.factor_mk]

def psiEquiv (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) (k : ℕ) :
    (MvPolynomial σ ℂ ⧸ I) ⧸ polyPointIdeal I w ^ k ≃+*
      (holGerms w ⧸ I.map (polyGerm w)) ⧸ germQuotPointIdeal I w ^ k :=
  RingEquiv.ofBijective (psi w I k) ⟨psi_injective w I hH hP k, psi_surjective w I hH k⟩

variable (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement)

theorem toCompl_compat {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h).comp
        ((psi w I l).comp (AdicCompletion.evalₐ (polyPointIdeal I w) l).toRingHom) =
      (psi w I k).comp (AdicCompletion.evalₐ (polyPointIdeal I w) k).toRingHom := by
  refine RingHom.ext fun x => ?_
  change Ideal.Quotient.factorPow (germQuotPointIdeal I w) h
      (psi w I l (AdicCompletion.evalₐ (polyPointIdeal I w) l x)) =
    psi w I k (AdicCompletion.evalₐ (polyPointIdeal I w) k x)
  rw [← RingHom.comp_apply (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h), psi_factorPow,
    RingHom.comp_apply, factorPow_evalₐ]

def toCompl : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) →+*
    AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) :=
  AdicCompletion.liftRingHom (germQuotPointIdeal I w)
    (fun k => (psi w I k).comp (AdicCompletion.evalₐ (polyPointIdeal I w) k).toRingHom)
    (fun h => toCompl_compat w I h)

theorem evalₐ_toCompl (k : ℕ) (x : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I)) :
    AdicCompletion.evalₐ (germQuotPointIdeal I w) k (toCompl w I x) =
      psi w I k (AdicCompletion.evalₐ (polyPointIdeal I w) k x) := by
  rw [toCompl, AdicCompletion.evalₐ_liftRingHom _ _ (fun h => toCompl_compat w I h)]
  try rfl

theorem fromCompl_compat {k l : ℕ} (h : k ≤ l)
    (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    Ideal.Quotient.factorPow (polyPointIdeal I w) h
        ((psiEquiv w I hH hP l).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) l x)) =
      (psiEquiv w I hH hP k).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) k x) := by
  apply (psiEquiv w I hH hP k).injective
  rw [RingEquiv.apply_symm_apply]
  change psi w I k _ = _
  rw [← RingHom.comp_apply (psi w I k), ← psi_factorPow w I h, RingHom.comp_apply]
  change Ideal.Quotient.factorPow (germQuotPointIdeal I w) h
    ((psiEquiv w I hH hP l) ((psiEquiv w I hH hP l).symm _)) = _
  rw [RingEquiv.apply_symm_apply, factorPow_evalₐ]

def fromCompl : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) →+*
    AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) :=
  AdicCompletion.liftRingHom (polyPointIdeal I w)
    (fun k => (psiEquiv w I hH hP k).symm.toRingHom.comp
      (AdicCompletion.evalₐ (germQuotPointIdeal I w) k).toRingHom)
    (fun h => RingHom.ext fun x => fromCompl_compat w I hH hP h x)

theorem evalₐ_fromCompl (k : ℕ) (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    AdicCompletion.evalₐ (polyPointIdeal I w) k (fromCompl w I hH hP x) =
      (psiEquiv w I hH hP k).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) k x) := by
  rw [fromCompl, AdicCompletion.evalₐ_liftRingHom _ _
    (fun h => RingHom.ext fun x => fromCompl_compat w I hH hP h x)]
  try rfl

theorem fromCompl_toCompl (x : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I)) :
    fromCompl w I hH hP (toCompl w I x) = x :=
  AdicCompletion.ext_evalₐ fun k => by
    rw [evalₐ_fromCompl, evalₐ_toCompl]
    exact (psiEquiv w I hH hP k).symm_apply_apply _

theorem toCompl_fromCompl (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    toCompl w I (fromCompl w I hH hP x) = x :=
  AdicCompletion.ext_evalₐ fun k => by
    rw [evalₐ_toCompl, evalₐ_fromCompl]
    exact (psiEquiv w I hH hP k).apply_symm_apply _

end GermCompletionEquiv


open GermCompletionEquiv in
theorem GermCompletionEquiv.proof (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) :
    GermCompletionEquiv.Statement := by
  intro σ _ I w
  refine ⟨RingEquiv.ofRingHom (fromCompl w I hH hP) (toCompl w I)
    (RingHom.ext fun x => fromCompl_toCompl w I hH hP x) (RingHom.ext fun x => toCompl_fromCompl w I hH hP x),
    fun q => ?_⟩
  change fromCompl w I hH hP _ = _
  refine AdicCompletion.ext_evalₐ fun k => ?_
  rw [evalₐ_fromCompl, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, RingEquiv.symm_apply_eq]
  exact (psi_mk w I k q).symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermsIntegrallyClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem HolGermsIntegrallyClosed.proof (hU : HolGermsUFD.Statement) : HolGermsIntegrallyClosed.Statement := by
  intro d y
  have := hU (Fin d) y
  exact ⟨HolGermsDomain.proof (Fin d) y, inferInstance⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionSheetsDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteProjectionSheetsDense.proof (hP : IrreducibleGermPrimitiveForm.Statement)
    (hG : PrimitiveFormSheetedOffDiscriminant.Statement) (hD : FiniteProjectionOffZerosDense.Statement) :
    FiniteProjectionSheetsDense.Statement := by
  intro σ _ X w d A hX hI hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hP σ X w d A hX hI hiso hinj
  obtain ⟨M, hM, hsh⟩ := hG σ X w d A hX hI hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  obtain ⟨N', hN', hcl⟩ := hD σ X w d A hX hI hiso hinj δ hδ hδ0
  refine ⟨interior M ∩ N', Filter.inter_mem (interior_mem_nhds.2 hM) hN', ?_⟩
  rintro z ⟨hzX, hzM, hzN⟩
  have hzc := hcl ⟨hzX, hzN⟩
  rw [mem_closure_iff_nhds] at hzc ⊢
  intro U hU
  obtain ⟨y, ⟨hyU, hyM⟩, hyX, hyδ⟩ :=
    hzc (U ∩ interior M) (Filter.inter_mem hU (isOpen_interior.mem_nhds hzM))
  exact ⟨y, hyU, hyX, hsh y ⟨hyX, interior_subset hyM⟩ hyδ⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionOffZerosDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteProjectionOffZerosDense.proof (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement)
    (hCl : FiniteProjectionSheetedClosureEquations.Statement) :
    FiniteProjectionOffZerosDense.Statement := by
  intro σ _ X w d A hX hirr hiso hinj δ hδ hδne
  obtain ⟨ℓ, N, a, δ₀, q, ha, hδ₀, hq, hδ₀ne, hp, hsep, hcoord⟩ := hPF σ X w d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X w d A hX hirr hiso hinj ℓ N a δ₀ q ha hδ₀ hq hδ₀ne hp hsep hcoord
  obtain ⟨m, c, hc, hcY, hcl⟩ := hCl σ X w d A hX hiso hinj (fun y => δ₀ y * δ y) (hδ₀.mul hδ)
    ⟨M, hM, fun y hy hne => hMsh y hy (left_ne_zero_of_mul hne)⟩
  have hcomp : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → AnalyticAt ℂ (fun z => f (A z)) w :=
    fun hf => hf.comp (A.analyticAt w)
  have hnot : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → (¬ ∀ᶠ y in 𝓝 (A w), f y = 0) →
      ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f (A z) = 0 := fun hf hne h => hne (hinj _ hf h)
  have hvan : ∀ k, ∀ᶠ z in 𝓝 w, z ∈ X → c k z = 0 := by
    intro k
    have h1 : ∀ᶠ z in 𝓝 w, z ∈ X → (c k z * δ₀ (A z)) * δ (A z) = 0 := by
      filter_upwards [hcY] with z hz hzX
      by_cases h : δ₀ (A z) * δ (A z) = 0
      · rw [mul_assoc, h, mul_zero]
      · rw [hz hzX h k, zero_mul, zero_mul]
    rcases hirr.2 (fun z => c k z * δ₀ (A z)) (fun z => δ (A z)) ((hc k).mul (hcomp hδ₀)) (hcomp hδ)
      h1 with h2 | h2
    · rcases hirr.2 (c k) (fun z => δ₀ (A z)) (hc k) (hcomp hδ₀) h2 with h3 | h3
      · exact h3
      · exact absurd h3 (hnot hδ₀ hδ₀ne)
    · exact absurd h2 (hnot hδ hδne)
  have hall : ∀ᶠ z in 𝓝 w, z ∈ X → ∀ k, c k z = 0 := by
    filter_upwards [Filter.eventually_all.2 hvan] with z hz hzX k using hz k hzX
  refine ⟨_, hall.and hcl, ?_⟩
  rintro z ⟨hzX, hz1, hz2⟩
  refine closure_mono ?_ (hz2 hzX (hz1 hzX))
  rintro x ⟨hx, hne⟩
  exact ⟨hx, right_ne_zero_of_mul hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZariskiAnalyticNormality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

theorem holGerms_isUnit_of_value_ne_zero {σ : Type} [Fintype σ] {w : σ → ℂ} (φ : holGerms w)
    (hφ : holGermValue w φ ≠ 0) : IsUnit φ := by
  rcases φ with ⟨_, f, hf, rfl⟩
  have hfw : f w ≠ 0 := hφ
  let ψ : holGerms w := ⟨((fun z => (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hf.inv hfw, rfl⟩
  refine IsUnit.of_mul_eq_one ψ (Subtype.ext ?_)
  change ((fun z => f z * (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((fun _ => (1 : ℂ) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
  exact Germ.coe_eq.2 ((hf.continuousAt.eventually_ne hfw).mono fun z hz => mul_inv_cancel₀ hz)

theorem holGermPointIdeal_le_jacobson {σ : Type} [Fintype σ] (w : σ → ℂ) :
    holGermPointIdeal w ≤ (⊥ : Ideal (holGerms w)).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  apply holGerms_isUnit_of_value_ne_zero
  have hx0 : holGermValue w x = 0 := RingHom.mem_ker.1 hx
  simp [map_add (f := _), map_mul, hx0]

theorem germQuotPointIdeal_le_jacobson {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    germQuotPointIdeal I w ≤ (⊥ : Ideal (holGerms w ⧸ I.map (polyGerm w))).jacobson := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu := Ideal.mem_jacobson_bot.1 (holGermPointIdeal_le_jacobson w hx') y'
  simpa [map_add (f := _), map_mul] using hu.map (Ideal.Quotient.mk (I.map (polyGerm w)))

theorem ZariskiAnalyticNormality.proof (hN : HolGermsNoetherian.Statement)
    (hD : CompletionNormalDescent.Statement) (hA : AffineCompletionNormal.Statement)
    (hE : GermCompletionEquiv.Statement) : ZariskiAnalyticNormality.Statement := by
  intro σ _ I w hI hIC hw
  have := hN σ w
  obtain ⟨e, -⟩ := hE σ I w
  obtain ⟨hdom, hic⟩ := hA σ I (polyPointIdeal I w) hI hIC (polyPointIdeal_isMaximal I w hw)
  have hdom' : IsDomain (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    e.toMulEquiv.isDomain
  have hic' : IsIntegrallyClosed
      (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    IsIntegrallyClosed.of_equiv e.symm
  obtain ⟨hB, hBic⟩ := hD _ (germQuotPointIdeal I w) inferInstance
    (germQuotPointIdeal_le_jacobson I w) hdom' hic'
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).1 hB, hBic⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyProjectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem VarietyProjectionMass.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hD : ComplexSets.DiscriminantCover.Statement) (hL : LocalGraphProjectionMass.Statement) :
    VarietyProjectionMass.Statement := by
  intro n d J hJ hd U hU B hB
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨W, hW, hWfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame W hW
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := W.submatrix (I₀.orderEmbOfFin hI₀) id
  have hAfin : ComplexSets.IsFiniteProjection J A := by
    simpa using hWfin 0 (I₀.orderEmbOfFin hI₀).toEmbedding
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd hAfin
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| hAfin.injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    NullSmaller.proof n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ B ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B := by
    rintro z ⟨hz, hzB⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzB⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J W b hb I₀ hI₀ P
    (fun y hy x hx => (hP y hy).2.2 x hx)) U hU B hB
  have hGZ : G ∩ B ⊆ zeroSetEuc J ∩ B := Set.inter_subset_inter_left _ Set.inter_subset_left
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B) :=
        measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := measure_union_le _ _
    _ = μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := by rw [hbad, zero_add]
    _ ≤ _ := hgood
    _ ≤ _ := by
      refine Finset.sum_le_sum fun s _ => mul_le_mul' (iSup_mono fun x => ?_)
        (measure_mono (Set.image_mono hGZ))
      exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hGZ hz.1, hz.2⟩)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassDivisionAtPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

variable {τ : Type} [DecidableEq τ]

def lastToCoordinate (c : τ) : (Option {c' // c' ≠ c} → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' =>
    if h : c' = c then ContinuousLinearMap.proj none else ContinuousLinearMap.proj (some ⟨c', h⟩)

def coordinateToLast (c : τ) : (τ → ℂ) →L[ℂ] (Option {c' // c' ≠ c} → ℂ) :=
  ContinuousLinearMap.pi fun o =>
    match o with
    | none => ContinuousLinearMap.proj c
    | some c' => ContinuousLinearMap.proj c'.1

theorem lastToCoordinate_apply (c : τ) (w : Option {c' // c' ≠ c} → ℂ) (c' : τ) :
    lastToCoordinate c w c' = if h : c' = c then w none else w (some ⟨c', h⟩) := by
  by_cases h : c' = c <;> simp [lastToCoordinate, h]

omit [DecidableEq τ] in
theorem coordinateToLast_none (c : τ) (y : τ → ℂ) : coordinateToLast c y none = y c := rfl

omit [DecidableEq τ] in
theorem coordinateToLast_some (c : τ) (y : τ → ℂ) (c' : {c' // c' ≠ c}) :
    coordinateToLast c y (some c') = y c'.1 := rfl

theorem lastToCoordinate_coordinateToLast (c : τ) (y : τ → ℂ) :
    lastToCoordinate c (coordinateToLast c y) = y := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem lastToCoordinate_pointWithLast (c : τ) (s : ℂ) :
    lastToCoordinate c (pointWithLast 0 s) = Pi.single c s := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; simp [pointWithLast]
  · simp [pointWithLast, h]

theorem WeierstrassDivisionAtPoint.proof (hW : WeierstrassDivision.Statement) :
    WeierstrassDivisionAtPoint.Statement := by
  intro τ _ _ y₀ c d F g hF hg hord
  have hA : ∀ h : (τ → ℂ) → ℂ, AnalyticAt ℂ h y₀ →
      AnalyticAt ℂ (fun w => h (y₀ + lastToCoordinate c w)) 0 := by
    intro h hh
    exact AnalyticAt.fun_comp_of_eq hh (analyticAt_const.add ((lastToCoordinate c).analyticAt 0)) (by simp)
  have hord' : analyticOrderAt
      (fun t => (fun w => F (y₀ + lastToCoordinate c w)) (pointWithLast 0 t)) 0 = d := by
    simpa only [lastToCoordinate_pointWithLast] using hord
  obtain ⟨q, a, hq, ha, heq⟩ := hW {c' // c' ≠ c} d _ _ (hA F hF) (hA g hg) hord'
  refine ⟨fun y => q (coordinateToLast c (y - y₀)), fun j u => a j (fun c' => u c'.1 - y₀ c'.1), ?_, ?_, ?_⟩
  · exact AnalyticAt.fun_comp_of_eq hq
      (((coordinateToLast c).analyticAt _).comp (analyticAt_id.sub analyticAt_const)) (by simp)
  · intro j
    have hR : AnalyticAt ℂ (fun u : τ → ℂ => fun c' : {c' // c' ≠ c} => u c'.1 - y₀ c'.1) (zeroCoordinate c y₀) := by
      have hL := ((ContinuousLinearMap.pi fun c' : {c' // c' ≠ c} =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c'.1).analyticAt (zeroCoordinate c y₀)).sub
          (analyticAt_const (v := fun c' : {c' // c' ≠ c} => y₀ c'.1))
      convert hL using 1
      funext u c'
      rfl
    refine AnalyticAt.fun_comp_of_eq (ha j) hR ?_
    funext c'
    simp [zeroCoordinate_apply, c'.2]
  · have hT : Tendsto (fun y => coordinateToLast c (y - y₀)) (𝓝 y₀) (𝓝 0) := by
      have hc : Continuous fun y : τ → ℂ => coordinateToLast c (y - y₀) :=
        (coordinateToLast c).continuous.comp (continuous_id.sub continuous_const)
      simpa using hc.tendsto y₀
    filter_upwards [hT.eventually heq] with y hy
    have hy' : y₀ + lastToCoordinate c (coordinateToLast c (y - y₀)) = y := by
      rw [lastToCoordinate_coordinateToLast]; abel
    simp only [hy'] at hy
    rw [hy]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun i : {c' // c' ≠ c} => coordinateToLast c (y - y₀) (some i)) =
        fun c' => zeroCoordinate c y c'.1 - y₀ c'.1 := by
      funext c'
      rw [coordinateToLast_some, zeroCoordinate_apply, if_neg c'.2, Pi.sub_apply]
    rw [h1, coordinateToLast_none, Pi.sub_apply]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCompletionNormalDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open AdicCompletion Polynomial

section

variable {R : Type} [CommRing R] (J : Ideal R)

theorem CompletionNormalDescent.evalₐ_algebraMap (n : ℕ) (x : R) :
    evalₐ J n (algebraMap R (AdicCompletion J R) x) = Ideal.Quotient.mk (J ^ n) x := by
  rw [(evalₐ J n).commutes]
  rfl

variable [IsNoetherianRing R]

theorem CompletionNormalDescent.algebraMap_injective (hJ : J ≤ (⊥ : Ideal R).jacobson) :
    Function.Injective (algebraMap R (AdicCompletion J R)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have H : IsHausdorff J R := IsHausdorff.of_le_jacobson J R (by simpa only [Ideal.jacobson_bot] using hJ)
  refine H.haus a fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have := CompletionNormalDescent.evalₐ_algebraMap J n a
  rw [ha, _root_.map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

theorem CompletionNormalDescent.dvd_of_dvd_completion (hJ : J ≤ (⊥ : Ideal R).jacobson) (a b : R)
    (x : AdicCompletion J R)
    (h : algebraMap R (AdicCompletion J R) a = algebraMap R (AdicCompletion J R) b * x) : b ∣ a := by
  have H : IsHausdorff J (R ⧸ Ideal.span {b}) := IsHausdorff.of_le_jacobson J _ (by simpa only [Ideal.jacobson_bot] using hJ)
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
  have h1 := congrArg (evalₐ J n) h
  rw [map_mul, CompletionNormalDescent.evalₐ_algebraMap, CompletionNormalDescent.evalₐ_algebraMap, ← hr,
    ← map_mul, Ideal.Quotient.eq] at h1
  have h2 : Ideal.Quotient.mk (Ideal.span {b}) a = Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) := by
    rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b), zero_mul,
      sub_zero]
  have h3 : Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) =
      (a - b * r) • (Ideal.Quotient.mk (Ideal.span {b}) 1) := by
    rw [Algebra.smul_def, _root_.map_one, mul_one]
    rfl
  rw [h2, h3]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

end

theorem CompletionNormalDescent.proof : CompletionNormalDescent.Statement := by
  intro R _ J _ hJ hD hIC
  have hinj := CompletionNormalDescent.algebraMap_injective J hJ
  have : IsDomain R := hinj.isDomain (algebraMap R (AdicCompletion J R))
  refine ⟨inferInstance, ?_⟩
  set f := algebraMap R (AdicCompletion J R) with hf
  let L := FractionRing (AdicCompletion J R)
  let g : R →+* L := (algebraMap (AdicCompletion J R) L).comp f
  have hg : Function.Injective g := (IsFractionRing.injective (AdicCompletion J R) L).comp hinj
  let φ : FractionRing R →+* L := IsFractionRing.lift hg
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap (AdicCompletion J R) L (f r) :=
    fun r => IsFractionRing.lift_algebraMap hg r
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro z hz
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R (FractionRing R) b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
    exact hb0

  have hint : IsIntegral (AdicCompletion J R) (φ (algebraMap R (FractionRing R) a /
      algebraMap R (FractionRing R) b)) := by
    obtain ⟨p, hp, hpz⟩ := hz
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [eval₂_map]
    have : (algebraMap (AdicCompletion J R) L).comp f = φ.comp (algebraMap R (FractionRing R)) := by
      ext r; exact (hφ r).symm
    rw [this, ← hom_eval₂, hpz, _root_.map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hay : f a = f b * y := by
    apply IsFractionRing.injective (AdicCompletion J R) L
    rw [map_mul, hy, map_div₀, hφ, hφ]
    have hfb : algebraMap (AdicCompletion J R) L (f b) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (AdicCompletion J R) L),
        map_eq_zero_iff _ hinj]
      exact hb0
    exact (mul_div_cancel₀ _ hfb).symm
  obtain ⟨r, rfl⟩ := CompletionNormalDescent.dvd_of_dvd_completion J hJ a b y hay
  refine ⟨r, ?_⟩
  rw [map_mul]
  exact (mul_div_cancel_left₀ _ hbK).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionLocalCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionLocalCover.proof (hR : ProperOpenProjectionLocalUnbranched.Statement) :
    ProperOpenProjectionLocalCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨U₁, g, hU₁o, hy₀U₁, hU₁D, hg, hgd, hsec⟩ :=
    hR σ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU₁o y₀ hy₀U₁
  set U := Metric.ball y₀ r with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball
  have hy₀U : y₀ ∈ U := Metric.mem_ball_self hr
  have hUD : U ⊆ D := hball.trans hU₁D
  have hgU : AnalyticOnNhd ℂ g U := hg.mono hball
  have hgdU : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0 :=
    fun W hW hWU hWne => hgd W hW (hWU.trans hball) hWne

  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ A x ∈ U} with hYdef
  have hfib : ∀ y ∈ U, {x | x ∈ Y ∧ A x = y} = {x | x ∈ X ∩ B ∧ A x = y} := by
    intro y hy
    ext x
    simp only [hYdef, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx, _⟩, hAx⟩
      exact ⟨hx, hAx⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨⟨hx, hAx ▸ hy⟩, hAx⟩
  have hYmaps : Set.MapsTo A Y U := fun x hx => hx.2
  have hYprop : ∀ K ⊆ U, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKU hK
    have : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ B ∧ A x ∈ K} := by
      ext x
      simp only [hYdef, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKU h.2⟩, h.2⟩⟩
    rw [this]
    exact hprop K (hKU.trans hUD) hK
  have hYsec : ∀ x ∈ Y, g (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O := by
    intro x hx hgx
    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hXV⟩ := hsec (A x) (hball hx.2) hgx x hx.1 rfl
    refine ⟨O ∩ U, V ∩ A ⁻¹' U, h, hO.inter hUo, hV.inter (hUo.preimage A.continuous), ⟨hxV, hx.2⟩,
      hh.continuousOn.mono Set.inter_subset_left, fun y hy => hAh y hy.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨hzXB, hzU⟩, hzV, -⟩
      have : z ∈ h '' O := hXV ▸ ⟨hzXB, hzV⟩
      obtain ⟨y, hyO, rfl⟩ := this
      exact ⟨y, ⟨hyO, by rwa [hAh y hyO] at hzU⟩, rfl⟩
    · rintro ⟨y, ⟨hyO, hyU⟩, rfl⟩
      have hmem : h y ∈ X ∩ B ∩ V := hXV ▸ ⟨y, hyO, rfl⟩
      have hAy : A (h y) ∈ U := by rw [hAh y hyO]; exact hyU
      exact ⟨⟨hmem.1, hAy⟩, hmem.2, hAy⟩

  obtain ⟨n, hn⟩ := UnbranchedProperCountConstant.proof UnbranchedProperCountLocallyConstant.proof
    ManifoldZerosComplementConnected.proof σ Y d A U g hUo (convex_ball y₀ r).isPreconnected hYmaps hYprop
    hgU hYsec
  have hcount : ∀ y ∈ U, g y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = n := by
    intro y hy hgy
    rw [← hfib y hy]
    exact hn y hy hgy

  have hle : ∀ y ∈ U, {x | x ∈ X ∩ B ∧ A x = y}.encard ≤ n := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    have hn1 : ((n + 1 : ℕ) : ℕ∞) ≤ {x | x ∈ X ∩ B ∧ A x = y}.encard := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt hlt
    obtain ⟨T, hTF, hTcard⟩ := Set.exists_subset_encard_eq hn1
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
    obtain ⟨S, hS, hSdisj⟩ := hTfin.t2_separation
    have hW : U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x) ∈ 𝓝 y := by
      refine Filter.inter_mem (hUo.mem_nhds hy) ((Filter.biInter_mem hTfin).2 fun x hx => ?_)
      have hxF := hTF hx
      have := hopen x hxF.1 (S x) ((hS x).2.mem_nhds (hS x).1)
      rwa [hxF.2] at this
    obtain ⟨t, ⟨htW, hgt⟩⟩ := hgdU (interior (U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x))) isOpen_interior
      (interior_subset.trans Set.inter_subset_left) ⟨y, mem_interior_iff_mem_nhds.2 hW⟩
    have htW' := interior_subset htW
    have htU : t ∈ U := htW'.1
    have hpick : ∀ x ∈ T, ∃ z, z ∈ X ∩ B ∩ S x ∧ A z = t := by
      intro x hx
      have := Set.mem_iInter₂.1 htW'.2 x hx
      obtain ⟨z, hz, hAz⟩ := this
      exact ⟨z, hz, hAz⟩
    choose! z hz hAz using hpick
    have hinj : Set.InjOn z T := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.1 (hSdisj ha hb hne) (hz a ha).2 (hab ▸ (hz b hb).2)
    have hsub : z '' T ⊆ {x | x ∈ X ∩ B ∧ A x = t} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hz x hx).1, hAz x hx⟩
    have := (Set.encard_le_encard hsub).trans_eq (hcount t htU hgt)
    rw [hinj.encard_image, hTcard] at this
    exact absurd this (by norm_cast; omega)
  refine ⟨U, g, n, hUo, hy₀U, hUD, hgU, hgdU, hle, fun y hy hgy => ⟨hcount y hy hgy, ?_⟩⟩
  intro x hx hAx
  exact hsec y (hball hy) hgy x hx hAx

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

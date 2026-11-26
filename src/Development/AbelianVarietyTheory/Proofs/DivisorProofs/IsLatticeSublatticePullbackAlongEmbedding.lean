module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesTwistedUnitIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativ

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisRest
namespace GlobalTheory.HermitianEigenvalueInequality

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩
    have e : ((b : NumberField.RingOfIntegers E) * d) • (c • y) = a • (d • y) := by
      simp only at hab
      rw [← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a,
        ← algebraMap_smul E d, smul_smul, smul_smul, map_mul, ]
      congr 1
      rw [← hab]
      ring
    rw [e]
    exact L.smul_mem _ h

end GlobalTheory.HermitianEigenvalueInequality
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbedding
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew

theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.HermitianEigenvalueInequality.main
  | exact _root_.GlobalTheory.HermitianEigenvalueInequality.main
  | (apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianEigenvalueInequality.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianEigenvalueInequality.main ..)

theorem isLattice_lowLat : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  intro E _ _ n n₁ L ι hL hι
  have hfg : L.FG := Submodule.IsLattice.fg (self := hL)
  refine ⟨?_, ?_⟩
  · let f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E)
    have hf : Function.Injective f := hι
    have hle : (lowLat ι L).map f ≤ L := Submodule.map_comap_le f L
    have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hfg
    have hm : ((lowLat ι L).map f).FG := (isNoetherian_submodule.mp hN) _ hle
    exact Submodule.fg_of_fg_map_injective f hf hm
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.PlaneSkew
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbeddingStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  first | exact @GlobalTheory.PlaneSkew.isLattice_lowLat | exact GlobalTheory.PlaneSkew.isLattice_lowLat | (intros; apply GlobalTheory.PlaneSkew.isLattice_lowLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalComplementHyperbolicPlaneLatticeSelfDu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalComplementHyperbolicPlaneLatticeSelfDu
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkewDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  unfold form
  have : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + (fun i => σ (c i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) (s : E) :
    form σ J a (s • b) = σ s * form σ J a b := by
  unfold form
  have : (fun i => σ ((s • b) i)) = σ s • (fun i => σ (b i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_restrict (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (u u' : Fin n₁ → E) : form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  unfold form
  have h : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ (fun i => σ (u' i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) ι u' i
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end GlobalTheory.PlaneSkewDual

namespace GlobalTheory.PlaneSkewDual

theorem lowLat_selfDual (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) :
    ∀ u, u ∈ lowLat ι L ↔ ∀ u' ∈ lowLat ι L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (ιᵀ * J * ι.map σ) u u')) := by
  intro u
  simp only [mem_lowLat, form_restrict]
  constructor
  · intro hu u' hu' o
    exact (hL _).1 hu _ hu' o
  · intro h
    refine (hL _).2 fun z hz o => ?_
    obtain ⟨s, t, u', -, -, hu', rfl⟩ := hsplit z hz
    have hz' : form σ J (ι *ᵥ u) (s • x + ι *ᵥ u' + t • y) = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
      rw [form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1, (horth u).2]
      ring
    rw [hz']
    exact h u' hu' o

end GlobalTheory.PlaneSkewDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalComplementHyperbolicPlaneLatticeSelfDuStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E),
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    ∀ u, u ∈ lowLat ι L ↔ ∀ u' ∈ lowLat ι L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (ιᵀ * J * ι.map σ) u u')) := by
  first | exact @GlobalTheory.PlaneSkewDual.lowLat_selfDual | exact GlobalTheory.PlaneSkewDual.lowLat_selfDual | (intros; apply GlobalTheory.PlaneSkewDual.lowLat_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtension
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.CMTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 w.embedding x
    rw [hc x] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (h.2.1.isComplex w)) hr

def sigE {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Gal(E/F) :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun x => sig_sig h x) (AlgHom.ext fun x => sig_sig h x)

theorem trace_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  have hne : (1 : Gal(E/F)) ≠ sigE h := by
    intro h1
    obtain ⟨x, hx⟩ := sig_ne_id h
    exact hx (congrArg (fun g : Gal(E/F) => g x) h1).symm
  have hle : Nat.card Gal(E/F) ≤ 2 := by
    calc Nat.card Gal(E/F) ≤ Nat.card (E →ₐ[F] E) :=
          Nat.card_le_card_of_injective (fun g => (g : E →ₐ[F] E)) (fun a b hab => AlgEquiv.coe_algHom_injective hab)
      _ ≤ Module.finrank F E := card_algHom_le_finrank F E E
      _ = 2 := h.2.2.1
  have hall : ∀ g : Gal(E/F), g = 1 ∨ g = sigE h := by
    classical
    have hc : (({1, sigE h} : Finset Gal(E/F))).card = 2 := Finset.card_pair hne
    have hu : ({1, sigE h} : Finset Gal(E/F)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc]
      rw [← Nat.card_eq_fintype_card]
      have : 2 ≤ Nat.card Gal(E/F) := by
        rw [Nat.card_eq_fintype_card, ← hc]; exact Finset.card_le_univ _
      omega
    intro g
    have := Finset.mem_univ g
    rw [← hu] at this
    simpa using this
  have hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [h.2.2.1]
    apply le_antisymm hle
    classical
    rw [Nat.card_eq_fintype_card, ← Finset.card_pair hne]
    exact Finset.card_le_univ _
  rw [trace_eq_sum_automorphisms]
  classical
  rw [Fintype.sum_eq_add 1 (sigE h) hne (fun g hg => absurd (hall g) (by tauto))]
  rfl

end GlobalTheory.CMTrace

namespace GlobalTheory.CMTrace

theorem adele_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : AF F, Algebra.trace (AF F) (AE F E) (algebraMap (AF F) (AE F E) x) = 2 * x) ∧ ∀ c : AE F E, algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) c) = c + cA σ c := by
  intro F E _ _ _ _ _ σ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h.2.2.1, nsmul_eq_mul, Nat.cast_ofNat]
  · have htm : ∀ (a : AF F) (e : E), Algebra.trace (AF F) (AE F E) (a ⊗ₜ[F] e) =
        a * algebraMap F (AF F) (Algebra.trace F E e) := by
      intro a e
      have h1 : a ⊗ₜ[F] e = a • ((1 : AF F) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]; abel
    | tmul a e =>
      rw [htm, Algebra.TensorProduct.algebraMap_apply, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        ← TensorProduct.tmul_add, ← trace_eq h, mul_comm, ← Algebra.smul_def, Algebra.algebraMap_self,
        RingHom.id_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CMTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhiIndep


open ReciprocityTheory.ChartRestriction.G.FD in
theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)


open ReciprocityTheory.ChartRestriction.G.FD in
theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    apply mul_left_cancel₀ (mul_ne_zero (hν g) (bchar_ne_zero (la k) hb))
    rw [mul_zero, Finset.mul_sum, ← h]
    exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]


set_option maxHeartbeats 1000000 in
theorem phiJ_indep (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) (m : ℕ) (b : Fin m → T.R j)
    (hs : ∀ k, b k ∈ sec (T.Q.Xo j) T.Q.c a n) (hb : LinearIndependent T.Q.c.F b) :
    LinearIndependent ℂ fun k => T.phiJ j σ a (b k) := by
  obtain ⟨th, hr, -, hD⟩ := h.dictU j hj σ hσ
  have hI := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ a n hd m b hs hb
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along (T.U j σ).X (laU (T.U j σ) a n) (T.dict j σ) hD.2.2.2.2.1 (h.chiTriv j hj σ hσ a n hd)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g)) ?_
    (fun k => rdU (T.U j σ) (b k)) (fun i k => (h.unf j hj σ hσ).2.2.2.2.1 a n hd _ (hs i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [h.cUnit j hj σ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(h.muUnit j hj σ hσ).2.1]; exact one_ne_zero)
  · intro i g
    simp only [CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

theorem phiC_indep_of (D : D7) (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (b : Fin m → T.R j)
    (H : LinearIndependent ℂ fun k => T.phiJ j σ a (b k)) :
    LinearIndependent ℂ fun k => phiC T hV a (b k) := by
  subst hV
  exact H


set_option maxHeartbeats 1000000 in
theorem phiC_indep : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  intro D T κ h i σ hσ hV m b hb
  refine phiC_indep_of D T hV _ (fun k => (b k : T.R ((i : ℕ) + 1))) ?_
  exact phiJ_indep D T h _ (inR i) σ hσ _ (κ i).n (dom_wtA (κ i)) m _
    (fun k => cusp_le_sec _ _ _ _ _ (b k).2)
    (hb.map' (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype (Submodule.ker_subtype _))

end GlobalTheory.PhiIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbeddingStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormAdelicFunctions_independent_goodEmbedding : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.PhiIndep.phiC_indep | exact GlobalTheory.PhiIndep.phiC_indep | (intros; apply GlobalTheory.PhiIndep.phiC_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.DualExact

variable {X : Scheme.{0}}

theorem exists_local_section {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {s : ℕ} (hG : IsVB G s)
    {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens), U ≤ V ∧ x ∈ U ∧
      ∃ σ : ∀ W : X.Opens, W ≤ U → (Γ(G, W) →ₗ[Γ(X, W)] Γ(F, W)),
        (∀ (W W' : X.Opens) (h : W ≤ U) (h' : W' ≤ W) (t : Γ(G, W)),
          σ W' (h'.trans h) (resM G h' t) = resM F h' (σ W h t)) ∧
        ∀ (W : X.Opens) (h : W ≤ U) (t : Γ(G, W)), φ.app W (σ W h t) = t := by
  obtain ⟨U, e, -, hxU, hle, he⟩ := hG.exists_affine hx
  choose T hT hxT a ha using fun i => exists_app_eq_of_epi φ (e i) hxU
  let U' : X.Opens := U ⊓ Finset.univ.inf T
  have hx' : x ∈ U' := ⟨hxU, by rw [Opens.coe_finset_inf]; simpa using hxT⟩
  have hU' (i) : U' ≤ T i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  have hU : U' ≤ U := inf_le_left
  refine ⟨U', hU.trans hle, hx', fun W h =>
    (he.basis (h.trans hU)).constr Γ(X, W) fun i => resM F (h.trans (hU' i)) (a i),
    fun W W' h h' t => ?_, fun W h t => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
      resM_smul, resM_resM]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← he.repr_resM (h.trans hU) h']
  · rw [← appLinear_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
      map_smul, appLinear_apply, app_resM, ha, resM_resM]
    conv_rhs => rw [← (he.basis (h.trans hU)).sum_repr t]
    simp only [IsFrame.basis_apply]

theorem exact_of_locally (S : ShortComplex X.Modules)
    (H : ∀ (V : X.Opens) (x : X), x ∈ V → ∃ U : X.Opens, U ≤ V ∧ x ∈ U ∧
      ∀ t : Γ(S.X₂, U), S.g.app U t = 0 → ∃ u, S.f.app U u = t) : S.Exact := by
  refine (QCoh.exact_iff_stalkLinear S).2 fun x t => ⟨fun ht => ?_, ?_⟩
  · obtain ⟨V, hV, t, rfl⟩ := S.X₂.presheaf.exists_germ_eq t
    rw [QCoh.stalkLinear_germ, ← map_zero (S.X₃.presheaf.germ V x hV).hom] at ht
    obtain ⟨V', hV', i₁, i₂, e⟩ := S.X₃.presheaf.germ_eq x hV hV _ _ ht
    have e' : resM S.X₃ i₁.le (S.g.app V t) = 0 := e.trans (map_zero _)
    obtain ⟨U, hU, hxU, HU⟩ := H V' x hV'
    obtain ⟨u, hu⟩ := HU (resM S.X₂ (hU.trans i₁.le) t) (by
      rw [app_resM, ← resM_resM i₁.le hU, e', map_zero])
    exact ⟨S.X₁.presheaf.germ U x hxU u, by rw [QCoh.stalkLinear_germ, hu, germ_resM]⟩
  · rintro ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, S.zero, QCoh.stalkLinear_zero,
      LinearMap.zero_apply]

theorem shortExact_dual : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (s : ℕ),
    S.ShortExact → IsVB S.X₃ s → (ShortComplex.mk (dualMap S.g) (dualMap S.f)
      (by rw [← dualMap_comp, S.zero, dualMap_zero])).ShortExact := by
  intro X S s hS h₃
  have := hS.mono_f
  have := hS.epi_g
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  have hz (W : X.Opens) (u : Γ(S.X₁, W)) : S.g.app W (S.f.app W u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W _).2 ⟨u, rfl⟩
  have hinj (W : X.Opens) : Function.Injective (appLinear S.f W) :=
    QCoh.injective_app_of_mono S.f W
  refine ShortComplex.ShortExact.mk' (exact_of_locally _ fun V x hx => ?_)
    (mono_dualMap S.g) (QCoh.epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    refine ⟨U, hU, hxU, fun (l : Γ(dual S.X₂, U)) (hl : (dualMap S.f).app U l = 0) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ σ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hσ W W' h h', dualApp_resM]
    · refine dual_ext fun W h t => ?_
      change dualApp l h (σ W h (S.g.app W t)) = _
      obtain ⟨u, hu⟩ := hex W (t - σ W h (S.g.app W t)) (by rw [map_sub, hg, sub_self])
      have := dualApp_dualMap S.f l h u
      rw [hl, hu, map_sub, dualApp_zero, LinearMap.zero_apply, eq_comm, sub_eq_zero] at this
      exact this.symm
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    let ρ (W : X.Opens) (h : W ≤ U) : Γ(S.X₂, W) →ₗ[Γ(X, W)] Γ(S.X₁, W) :=
      LinearMap.codRestrictOfInjective (LinearMap.id - σ W h ∘ₗ appLinear S.g W)
        (appLinear S.f W) (hinj W) fun t => hex W _ (by
          change S.g.app W (t - σ W h (S.g.app W t)) = 0
          rw [map_sub, hg, sub_self])
    have hρ (W : X.Opens) (h : W ≤ U) (t : Γ(S.X₂, W)) :
        S.f.app W (ρ W h t) = t - σ W h (S.g.app W t) :=
      LinearMap.codRestrictOfInjective_comp_apply _ (appLinear S.f W) _ _ t
    refine ⟨U, hxU, hU, fun (l : Γ(dual S.X₁, U)) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ ρ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← dualApp_resM]
      congr 1
      apply hinj W'
      rw [appLinear_apply, appLinear_apply, app_resM, hρ, hρ, map_sub, app_resM, hσ W W' h h']
    · refine dual_ext fun W h u => ?_
      change dualApp l h (ρ W h (S.f.app W u)) = _
      congr 1
      apply hinj W
      rw [appLinear_apply, appLinear_apply, hρ, hz, map_zero, sub_zero]

end GlobalTheory.DualExact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv

theorem map_starT {A R' C : Type} [CommRing A] [Algebra ℚ A] [CommRing R'] [Algebra ℚ R'] [Ring C] [Algebra ℚ C]
    (σ : C →+* Cᵐᵒᵖ) (f : A →ₐ[ℚ] R') (y : A ⊗[ℚ] C) :
    Algebra.TensorProduct.map f (AlgHom.id ℚ C) (starT σ A y).unop =
      (starT σ R' (Algebra.TensorProduct.map f (AlgHom.id ℚ C) y)).unop := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul]; rfl
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem map_conj_ext {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] {L : Type} [Field L]
    [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L) (β₁ : G.Cˣ)
    (hc : ∀ x, ι (c x) = β₁ * sh G (ι x) * ((β₁⁻¹ : G.Cˣ) : G.C)) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) =
      ((1 : K) ⊗ₜ[ℚ] (β₁ : G.C)) * (starT G.star K (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι z)).unop *
        ((1 : K) ⊗ₜ[ℚ] ((β₁⁻¹ : G.Cˣ) : G.C)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, AlgHom.id_apply,
      AlgHom.id_apply, hc]
    rfl
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy, mul_add, add_mul]

theorem map_invol {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] (c : L →ₐ[ℚ] L)
    (hcc : ∀ x, c (c x) = x) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) c (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hcc]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem selfDual_conj_eq_one {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing B] [Algebra R B]
    (ι : B →+* A) (hιR : ∀ r, ι (algebraMap R B r) = algebraMap R A r) (σ : A →+* Aᵐᵒᵖ) (cc : B →+* B) (β₁ : Aˣ)
    (X X₁ : Aˣ) (t t₁ : Rˣ) (a' : B) (m : Bˣ)
    (hc : ι (cc m) = ↑β₁ * (σ (ι m)).unop * ↑β₁⁻¹)
    (h1 : (X : A) * (ι a' * β₁) * (σ X).unop = algebraMap R A t)
    (h2 : (X₁ : A) * β₁ * (σ X₁).unop = algebraMap R A t₁) :
    ((X : A) * ι m * ↑X₁⁻¹) * ((X₁ : A) * ι (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * ↑X₁⁻¹) *
      (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = 1 := by
  have hs1 : (σ (X₁ : A)).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht1 : algebraMap R A ((t₁⁻¹ : Rˣ) : R) * algebraMap R A (t₁ : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have k1 : ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * β₁ := by
    calc ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop
        = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (((X₁⁻¹ : Aˣ) : A) * algebraMap R A (t₁ : R) *
            (σ ((X₁⁻¹ : Aˣ) : A)).unop) := by
          rw [← Algebra.commutes (t₁ : R), ← mul_assoc, ← mul_assoc, ht1, one_mul]
      _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((((X₁⁻¹ : Aˣ) : A) * X₁) * β₁ *
            ((σ X₁).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop)) := by
          rw [← h2]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs1, one_mul, mul_one]
  have hβ : (β₁ : A) * (σ (ι m)).unop = ι (cc m) * β₁ := by
    rw [hc, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  have hcm : cc (m : B) * cc ((m⁻¹ : Bˣ) : B) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hmE : (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m =
      algebraMap R B (↑t⁻¹ * ↑t₁) * a' := by
    calc (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m
        = algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (((m : B) * ↑m⁻¹) * (cc (m : B) * cc ↑m⁻¹)) := by ring
      _ = _ := by rw [Units.mul_inv, hcm, one_mul, mul_one]
  have hR : ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R) = 1 := by
    calc ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R)
        = (((t₁⁻¹ : Rˣ) : R) * (t₁ : R)) * (((t⁻¹ : Rˣ) : R) * (t : R)) := by ring
      _ = 1 := by rw [Units.inv_mul, Units.inv_mul, one_mul]
  set E := algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹) with hE
  clear_value E
  have eσ : (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = (σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop := by
    simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [eσ]
  calc (X : A) * ι m * ↑X₁⁻¹ * (↑X₁ * ι E * ↑X₁⁻¹) *
        ((σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop)
      = (X : A) * ι m * (((X₁⁻¹ : Aˣ) : A) * X₁) * ι E * (((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop) *
          (σ (ι m)).unop * (σ X).unop := by simp only [mul_assoc]
    _ = (X : A) * ι m * ι E * (algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (β₁ * (σ (ι m)).unop)) * (σ X).unop := by
          rw [Units.inv_mul, k1, mul_one]; simp only [mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((X : A) * (ι ((m : B) * E * cc m) * β₁) * (σ X).unop) := by
          rw [hβ, show ι ((m : B) * E * cc m) = ι m * ι E * ι (cc m) by rw [map_mul, map_mul]]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (algebraMap R A (((t⁻¹ : Rˣ) : R) * (t₁ : R)) *
          ((X : A) * (ι a' * β₁) * (σ X).unop)) := by
          rw [hmE, map_mul, hιR]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = 1 := by rw [h1, ← mul_assoc, ← map_mul, ← map_mul, hR, map_one]

theorem exists_finset_of_eventually {p : ℕ} {Q : AwayP p → Prop}
    (h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), Q v) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v : AwayP p, v.1 ∉ S → Q v := by
  rw [Filter.eventually_cofinite] at h
  refine ⟨(h.image Subtype.val).toFinset, fun v hv => ?_⟩
  by_contra hq
  exact hv ((Set.Finite.mem_toFinset _).2 ⟨v, hq, rfl⟩)

theorem finite_above (p : ℕ) :
    ({v : HeightOneSpectrum ℤ | v.asIdeal = Ideal.span {(p : ℤ)}} : Set (HeightOneSpectrum ℤ)).Finite :=
  Set.Subsingleton.finite fun v hv w hw => HeightOneSpectrum.ext (hv.trans hw.symm)

theorem sh_mul' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh]

theorem sh_sh {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_unit {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have h : sh G β * sh G ((β⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one_eq]
  rw [hβ] at h
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((β : G.C) * sh G ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]


end GlobalTheory.LocTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansion
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.AdExt

section Mat
variable {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ}

theorem conj_form (hx : IsUnit x.det) (h : xᴴ * G * x = S) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (x * A * x⁻¹)ᴴ * G * (x * B * x⁻¹) = x⁻¹ᴴ * (Aᴴ * S * B) * x⁻¹ := by
  rw [← h]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem conj_mem_lie (hx : IsUnit x.det) (h : xᴴ * G * x = S) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Zᴴ * S + S * Z = 0) : (x * Z * x⁻¹)ᴴ * G + G * (x * Z * x⁻¹) = 0 := by
  have h1 := conj_form hx h Z 1
  have h2 := conj_form hx h 1 Z
  rw [Matrix.mul_one, mul_nonsing_inv _ hx] at h1 h2
  rw [Matrix.mul_one] at h1
  rw [conjTranspose_one, Matrix.one_mul] at h2
  rw [h1, h2, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hZ]
  simp

theorem conj_mem_unitary (hx : IsUnit x.det) (h : xᴴ * G * x = S) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * S * A = S) : (x * A * x⁻¹)ᴴ * G * (x * A * x⁻¹) = G := by
  have h2 := conj_form hx h 1 1
  rw [Matrix.mul_one, mul_nonsing_inv _ hx, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one] at h2
  rw [conj_form hx h, hA, ← h2]

theorem diag_unitary (s : Fin n → ℂ) (t : Fin n → ℝ) :
    (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I))ᴴ * diagonal s *
      (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I)) = diagonal s := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext c
  have : star (Complex.exp ((t c : ℂ) * Complex.I)) * Complex.exp ((t c : ℂ) * Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Pi.star_apply]
  linear_combination s c * this

theorem half_mem_lie (hG : Gᴴ = G) (hd : IsUnit G.det) (W : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G)))ᴴ * G + G * ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G))) = 0 := by
  have e1 : (G⁻¹ * Wᴴ * G)ᴴ * G = G * W := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hd, Matrix.mul_one]
  have e2 : G * (G⁻¹ * Wᴴ * G) = Wᴴ * G := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd]
  have e3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, e3, smul_mul_assoc, mul_smul_comm, ← smul_add, conjTranspose_add, conjTranspose_neg,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2]
  simp

theorem conj_eq_of_mem_lie (hd : IsUnit G.det) {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ * G + G * W = 0) :
    -(G⁻¹ * Wᴴ * G) = W := by
  rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hW, Matrix.mul_neg, neg_neg, nonsing_inv_mul_cancel_left _ _ hd]

end Mat

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem atTau_spec (R : RealPoints θ V) (ρ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V ρ * g = gramAt D V ρ) : IsAtTau θ V ρ g (atTau θ V ρ g) := by
  have h : ∃ k, IsAtTau θ V ρ g k := by
    obtain ⟨k, hk, h⟩ := R.2.1 (fun τ => if τ = ρ then g else 1) fun τ => by
      change _ᴴ * _ * _ = _
      split_ifs with c
      · subst c; exact hg
      · simp
    exact ⟨k, hk, by simpa using h ρ, fun τ c => by simpa [c] using h τ⟩
  rw [atTau, dif_pos h]
  exact h.choose_spec

def toLie (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) : Frame Ψ V.rank →ₗ[ℝ] LieN V where
  toFun Z := fun ρ => ⟨(1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)),
    half_mem_lie (R.1 ρ).1 (R.1 ρ).2 _⟩
  map_add' Z Z' := funext fun ρ => Subtype.ext (by
    have : mat (Z + Z') (σ ρ) = mat Z (σ ρ) + mat Z' (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = (1 / 2 : ℂ) • _ + (1 / 2 : ℂ) • _
    simp only [this, conjAt, Matrix.mul_add, Matrix.add_mul, conjTranspose_add]
    module)
  map_smul' c Z := funext fun ρ => Subtype.ext (by
    have : mat (c • Z) (σ ρ) = c • mat Z (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = c • (1 / 2 : ℂ) • _
    simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, star_trivial]
    module)

theorem toLie_val (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ Z ρ).1 =
    (1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := rfl

theorem toLie_I (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ (Complex.I • Z) ρ).1 =
    (Complex.I / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ - conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := by
  have : mat (Complex.I • Z) (σ ρ) = Complex.I • mat Z (σ ρ) := rfl
  rw [toLie_val]
  simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  module

theorem fderiv_atPlace (R : RealPoints θ V) {φ : GA D V → ℂ} (g : GA D V)
    (hf : DifferentiableAt ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0) (ρ : D.what₂.Tau) (Y : LieAt V ρ) :
    fderiv ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0 (atPlace V ρ Y : LieN V) = Rder θ V ρ Y.1 φ g := by
  rw [Rder_eq R]
  have h1 : ∀ Y' : LieN V, HasDerivAt (fun t : ℝ => t • Y') Y' 0 := fun Y' => by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y'
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (h1 (atPlace V ρ Y)) (zero_smul ℝ _).symm
  exact h2.deriv.symm

theorem mat_unitFr {Ψ : Finset (D.host.E →+* ℂ)} {r : ℕ} (τ τ' : Ψ) (c d : Fin r) :
    mat (unitFr τ c d) τ' = if τ' = τ then Matrix.single c d 1 else 0 := by
  ext a b
  by_cases h : τ' = τ
  · simp [mat, unitFr, h, Matrix.single, eq_comm]
  · simp [mat, unitFr, h]

end GlobalTheory.HolRead.AdExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Set (UA σ W.J) :=
  {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1
  rw [← Units.val_mul]
  show (((g⁻¹ * g : UA σ J) : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1
  simp

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    mat (1 : UA σ J) = 1 := rfl

def carrierSub (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := carrierSet σ W H'
  one_mem' := ⟨by rw [mat_one, Matrix.one_mulVec], fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, ha, Matrix.mulVec_smul, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h1 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem unip_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    unip σ W H' = carrierSub σ W H' := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun u hu => hu
  · intro u hu
    exact Subgroup.subset_closure hu

section Top

variable [T2Space (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))] [IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))]

theorem isClosed_line {d : ℕ} (x : Fin d → E) : IsClosed {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} := by
  by_cases hx : x = 0
  · have : {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} = {0} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have h0 : incV F x = 0 := by
        funext i
        simp [incV, hx]
      simp [h0]
    rw [this]
    exact isClosed_singleton
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    have hinv : incV F x i * inclR (F := F) (AF F) (x i)⁻¹ = 1 := by
      simp only [incV, ← map_mul, mul_inv_cancel₀ hi, map_one]
    have : {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} =
        {w | w = (w i * inclR (F := F) (AF F) (x i)⁻¹) • incV F x} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hinv, mul_one]
      · intro h
        exact ⟨_, h⟩
    rw [this]
    exact isClosed_eq continuous_id
      (((continuous_apply i).mul continuous_const).smul continuous_const)

end Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)] in
theorem isClosed_carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed (carrierSet σ W H') := by
  have hm : Continuous fun u : UA σ W.J => mat u := Units.continuous_val.comp continuous_subtype_val
  have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} :=
    isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
  have h2 : ∀ z : Fin d₁ → AE F E, IsClosed {u : UA σ W.J | ∃ a : AE F E,
      mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    intro z
    have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
        (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹'
          {w | ∃ a : AE F E, w = a • incV F H'.x} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']
    rw [this]
    exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)
  have : carrierSet σ W H' = {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z : Fin d₁ → AE F E, {u : UA σ W.J | ∃ a : AE F E,
        mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u
    simp [carrierSet]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

theorem isClosed_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d d₁ W H'
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  rw [unip_eq]
  exact isClosed_carrierSet σ W H'

end GlobalTheory.ThK.UnipClosed
end
end

module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpen
public import Development.WeilBound.CoreStatements.SesquilinearFractions.LieNormSquareOfFamily

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSquareOfFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSquareOfFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  first | exact @PositivityTheory.Xgf.lie_norm_square_of_family | exact PositivityTheory.Xgf.lie_norm_square_of_family
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSquareOfFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family | exact GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSqBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSqBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem lieNormSq_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  intro E _ _ _ H R R' _ _ ω ω' C C' f φ σ r h
  exact (GlobalTheory.CM.EllComp.isLieNormSq_iff h.2.1 h.2.2.1 σ r).symm

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSqBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_norm_sq_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.lieNormSq_baseChange | exact GlobalTheory.CompanionTheory.Ar.Fl.lieNormSq_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.lieNormSq_baseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualBasisHermitianSum
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualBasisHermitianSum
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.KForm

section Embeddings

variable {E : Type} [Field E] [NumberField E]


open Classical in
theorem sum_dual_mul (σ τ : E →+* ℂ) :
    ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = if τ = σ then 1 else 0 := by
  let ρ : 𝓞 E →+* Module.End ℂ ℂ :=
    (Algebra.lmul ℂ ℂ).toRingHom.comp (τ.comp (algebraMap (𝓞 E) E))
  have hρ : ∀ (a : 𝓞 E) (z : ℂ), ρ a z = τ (a : E) * z := fun a z => rfl
  have hmem : (1 : ℂ) ∈ HT.eigSp ρ τ := HT.LatBasic.mem_eigSp.2 fun a => by
    rw [hρ, smul_eq_mul]
  have hP : HT.eigProj ρ σ 1 =
      ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
    simp [HT.eigProj, LinearMap.sum_apply, hρ]
  rw [← hP]
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem hmem
  · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) hmem

theorem trace_cast (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ z := by
  have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  simpa using this

end Embeddings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem kappa_form {ε : ℤˣ} {h : D.La → D.La → OK H} {σ : E →+* ℂ} {κ : OK H →+* ℂ}
    (hh : IsKForm D ε h) (hκ : κ (wK H) = σ (H.w0 : E)) (X Y : D.La) :
    κ (h X Y) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) := by
  obtain ⟨hT, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have e1 : h X Y = (((ε : ℤ) * (D.EF (H.w0 • X) Y - D.EF X Y) : ℤ) : OK H) +
      (((ε : ℤ) * D.EF X Y : ℤ) : OK H) * wK H := by
    apply Subtype.ext
    simpa [wK] using hh X Y
  have t1 : ((D.EF (H.w0 • X) Y : ℤ) : ℂ) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) := by
    have := congrArg (fun q : ℚ => (q : ℂ)) (hT H.w0 X Y)
    simp only [trace_cast, map_mul] at this
    rw [this]
    simp
  have t0 : ((D.EF X Y : ℤ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) := by
    have h1 : Algebra.trace ℚ E (sesq D X Y) = (D.EF X Y : ℚ) := by simpa using hT 1 X Y
    rw [← trace_cast, h1]
    simp
  have hs : ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) - ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) +
        (∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y)) * σ (H.w0 : E) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_add κ, map_mul, map_intCast, map_intCast, hκ, hs]
  push_cast
  rw [t1, t0]
  ring

theorem sigma_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  classical
  intro E _ _ _ H D ε h σ κ n e x y hh hκ
  obtain ⟨-, -, -, hL, hR, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D

  have hform : ∀ a c : 𝓞 E, κ (h (a • x) (c • y)) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (a : E) * starRingEnd ℂ (τ (c : E)) *
        (τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E))) := by
    intro a c
    rw [kappa_form hh hκ]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hc : τ (IsCMField.complexConj E (c : E)) = starRingEnd ℂ (τ (c : E)) :=
      IsCMField.complexEmbedding_complexConj E (τ : E →+* ℂ) (c : E)
    rw [hL, hR, map_mul, map_mul, hc]
    ring

  set S : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    ∑ k : Fin n, σ (HT.dualInt E (e k)) * τ ((RingOfIntegers.basis E (e k) : 𝓞 E) : E) with hSdef
  have hS : ∀ τ : E →ₐ[ℚ] ℂ, S τ = if (τ : E →+* ℂ) = σ then 1 else 0 := by
    intro τ
    have := sum_dual_mul σ (τ : E →+* ℂ)
    rw [← Equiv.sum_comp e] at this
    exact this
  set c : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) with hcdef
  have hexp : ∑ k, ∑ k', σ (HT.dualInt E (e k)) *
        κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) *
        starRingEnd ℂ (σ (HT.dualInt E (e k'))) =
      ((ε : ℤ) : ℂ) * ∑ τ : E →ₐ[ℚ] ℂ, S τ * starRingEnd ℂ (S τ) * c τ := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hform, hSdef, hcdef, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, Finset.sum_eq_single σ.toRatAlgHom]
  · have h1 : S σ.toRatAlgHom = 1 := by
      rw [hS]
      exact if_pos (RingHom.ext fun _ => rfl)
    have h2 : σ (H.rt : E) = 2 * σ (H.w0 : E) - 1 := by
      have h3 := congrArg (fun a : 𝓞 E => σ (algebraMap (𝓞 E) E a)) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add (f := _), map_one, map_ofNat] at h3
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]
      linear_combination -h3
    rw [h1, map_one, map_mul, h2]
    simp only [hcdef]
    change _ * (1 * 1 * (σ (sesq D x y) * (σ (H.w0 : E) - 1 + σ (H.w0 : E)))) = _
    ring
  · intro τ _ hτ
    have h0 : S τ = 0 := by
      rw [hS]
      refine if_neg fun hc => hτ (AlgHom.ext fun z => ?_)
      exact congrArg (fun f : E →+* ℂ => f z) hc
    rw [h0]
    simp
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end GlobalTheory.CompanionTheory.Ar.Fl.KForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualBasisHermitianSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_basis_hermitian_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | exact GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramInvariantPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramInvariantPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  first | exact @PositivityTheory.Xgf.hodge_gram_invariant_pullback | exact PositivityTheory.Xgf.hodge_gram_invariant_pullback
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramInvariantPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_gram_invariant_pullback | exact GlobalTheory.CompanionTheory.Relay.hodge_gram_invariant_pullback | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_gram_invariant_pullback <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem dualMap_comp_alg (f : R →+* R') :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul (f : R →+* R') (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (epsMul c) = (epsMul (f c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, mul_comm]

theorem fst_comp_dualMap (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem dualMap_comp_dualMap (f : R →+* R') (g : R' →+* R'') :
    (GlobalTheory.CompanionTheory.Ar.dualMap g).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = GlobalTheory.CompanionTheory.Ar.dualMap (g.comp f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem epsMul_zero_eq : epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

def bar (f : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap f ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = spMap (algebraMap R' (DualNumber R')) ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem exists_bc {G : Over S} (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    (u : epsAt x ⟶ G) : ∃ u' : epsAt x' ⟶ G, u'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ u.left := by
  subst hx
  exact ⟨bar f x ≫ u, rfl⟩

theorem isComb_bc {G : Over S} [GrpObj G] (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    {n : ℕ} (c : Fin n → R)
    (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G))
    (w' : epsAt x' ⟶ G) (hv : ∀ i, (v' i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (v i).left)
    (hw : w'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w.left) (h : Fl.IsComb c v w) :
    Fl.IsComb (fun i => f (c i)) v' w' := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := h
  let φ : (epsAt x ⟶ G) →* (epsAt (spMap f ≫ x) ⟶ G) :=
    { toFun := fun y => bar f x ≫ y
      map_one' := comp_one _
      map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => φ (u i), fun i => ?_, ?_⟩
  · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_epsMul]
  · have e : w' = φ (List.ofFn u).prod := Over.OverMorphism.ext hw
    rw [e, map_list_prod, List.map_ofFn]
    rfl

theorem one_left {G : Over S} [GrpObj G] {T : Scheme.{0}} (x : T ⟶ S) : (1 : Over.mk x ⟶ G).left = x ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left]
  rfl

theorem isComb_pad {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Sp R ⟶ S} {m M : ℕ} {c : Fin m → R}
    {v : Fin m → (epsAt x ⟶ G)} {w : epsAt x ⟶ G} (C : Fin M → R) (V : Fin M → (epsAt x ⟶ G)) (jj : Fin m → Fin M)
    (hj : Function.Injective jj) (hc : ∀ j, C (jj j) = c j) (hv : ∀ j, V (jj j) = v j)
    (h0 : ∀ q, q ∉ Set.range jj → C q = 0) (ht : ∀ q, IsTanAt G x (V q)) (h : Fl.IsComb c v w) :
    Fl.IsComb C V w := by
  classical
  obtain ⟨u, hu, rfl⟩ := h
  let U : Fin M → (epsAt x ⟶ G) := fun q => if hq : ∃ j, jj j = q then u hq.choose else 1
  have hU : ∀ j, U (jj j) = u j := fun j => by
    have hq : ∃ j', jj j' = jj j := ⟨j, rfl⟩
    simp only [U, dif_pos hq]
    rw [hj hq.choose_spec]
  have hU1 : ∀ q, q ∉ Set.range jj → U q = 1 := fun q hq => by
    simp only [U]
    exact dif_neg hq
  refine ⟨U, fun q => ?_, ?_⟩
  · by_cases hq : q ∈ Set.range jj
    · obtain ⟨j, rfl⟩ := hq
      rw [hU, hu, hc, hv]
    · rw [hU1 q hq, h0 q hq, epsMul_zero_eq, ← spMap_comp_spMap, Category.assoc]
      have := ht q
      unfold IsTanAt at this
      erw [this]
      rw [one_left, one_left]
      rfl
  · rw [List.prod_ofFn, List.prod_ofFn]
    exact Fintype.prod_of_injective jj hj _ _ (fun q hq => hU1 q hq) (fun j => (hU j).symm)

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tan_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) (v' : epsAt x' ⟶ t'.G) (v : epsAt x ⟶ t.G)
    (h : v.left = v'.left ≫ m.φ) : IsTanAt t'.G x' v' ↔ IsTanAt t.G x v := by
  subst hx
  have he : eSec t'.G ≫ m.φ = f ≫ eSec t.G := PolBaseChange.eSec_comm m.cart
  unfold IsTanAt
  rw [one_left, one_left, h]
  constructor
  · intro e
    rw [← Category.assoc, e, Category.assoc, he, Category.assoc]
  · intro e
    refine m.cart.1.hom_ext ?_ ?_
    · have he' : eSec t'.G ≫ m.cm.F = f ≫ eSec t.G := he
      rw [Category.assoc, e, Category.assoc, Category.assoc, he']
    · have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x' := Over.w v'
      have h2 : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, Category.assoc, h1, h2]
      refine Eq.trans ?_ (Category.comp_id x').symm
      erw [← Category.assoc, spMap_comp_spMap]
      have : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
        refine RingHom.ext fun a => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      show Spec.map (𝟙 _) ≫ x' = x'
      rw [Spec.map_id, Category.id_comp]

theorem exists_vec {G : Over (Sp R)} [GrpObj G] (σ : R →+* R') (w : epsR R ⟶ G) :
    ∃ U : epsAt (spMap σ) ⟶ G, U.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left ∧ (IsTangent w → IsTanAt G (spMap σ) U) := by
  have h1 : w.left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := Over.w w
  refine ⟨Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left) (by
    show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ
    rw [Category.assoc, h1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), rfl, fun ht => ?_⟩
  unfold IsTanAt
  rw [one_left]
  unfold IsTangent at ht
  show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left = _
  rw [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, ht]
  rfl

theorem mono_alg (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {c : Coeff l} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

abbrev sg (X : CMPack Z c FU i hP) (s : X.K →+* ℂ) : 𝓞 X.K →+* ℂ := s.comp (algebraMap (𝓞 X.K) X.K)

theorem exists_lift (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b))
    (u : epsAt (under X.y) ⟶ Xo.univ.t.G) (hu : X.IsImage b a u) (s : X.K →+* ℂ)
    (Ux : epsAt (spMap (sg X s)) ⟶ X.B.t.G)
    (hUx : Ux.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (sg X s)) ≫ (X.C b).v.left ≫ (X.ψ b a).left) :
    ∃ U' : epsAt (spMap s) ⟶ X.t.G, U'.left ≫ X.m.φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ u.left ∧ U'.left ≫ X.m'.φ = Ux.left := by
  obtain ⟨ρ, h1, h2⟩ := hu
  have hm := mono_alg X.K
  have hw : ρ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
    rw [← cancel_mono (spMap (algebraMap (𝓞 X.K) X.K)), Category.assoc, ← X.m'.cart.1.w, ← Category.assoc, h2,
      Category.assoc, Category.assoc, Over.w (X.ψ b a)]
    have e1 : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K))) := Over.w (X.C b).v
    rw [e1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]
  refine ⟨Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) (by
    show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) ≫ X.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap s
    rw [Category.assoc, hw, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), ?_, ?_⟩
  · show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) ≫ X.m.φ = _
    rw [Category.assoc, h1]
  · show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) ≫ X.m'.φ = _
    rw [Category.assoc, h2, hUx, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMap]

theorem one_tangent (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)) :
    IsTangent ((X.C b).v ≫ X.ψ b a) := by
  have h1 : IsTangent (X.C b).v := (X.C b).basis.1 0
  have h2 : IsMonHom (X.ψ b a) := ((X.fam b).1 a).isMonHom
  unfold IsTangent at h1 ⊢
  rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, IsMonHom.one_hom]

theorem w_eq (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ) :
    s (X.β (tauE c τ (H.w0 : E))) = sg X s (X.ω b) := by
  show s _ = s _
  congr 1
  refine Subtype.ext ?_
  have e1 := (X.map b).1
  have e2 := (Z b).hω
  have e3 : 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := by
    have h0 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add (f := _), map_one, map_ofNat] at this
      exact this
    have := congrArg τ h0
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have e4 : (((X.ω b : 𝓞 X.K) : X.K) : ℂ) = (((Z b).ω : (Z b).M) : ℂ) := by rw [← e1]; rfl
  have e5 : ((X.β (tauE c τ (H.w0 : E)) : X.K) : ℂ) = τ (H.w0 : E) := rfl
  rw [e4, e5]
  rw [hτ, ← e2] at e3
  linear_combination (1/2 : ℂ) * e3

def kap (X : CMPack Z c FU i hP) (τ : E →+* ℂ) (s : X.K →+* ℂ) : OK H →+* ℂ :=
  (s.comp (X.β.comp (tauE c τ))).comp ((algebraMap (𝓞 E) E).comp (OK H).val.toRingHom)

theorem gram_family (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ)
    (r : ℝ) (hr : IsLieNormSq (Z b).C.P (Z b).C.v
      ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r)
    {M : ℕ} (aq : Fin M → PureType.lat hP (sgnRt H b)) (Wq : Fin M → (epsAt (under X.y) ⟶ Xo.univ.t.G))
    (hW : ∀ q, X.IsImage b (aq q) (Wq q)) (V : Fin M → (epsAt (under (spMap s ≫ X.y)) ⟶ Xo.univ.t.G))
    (hV : ∀ q, (V q).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ (Wq q).left) :
    (∀ q, IsTanAt Xo.univ.t.G (under (spMap s ≫ X.y)) (V q)) ∧
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under (spMap s ≫ X.y)) V
      (Matrix.of fun q q' => r * kap X τ s (X.h b (aq q) (aq q'))) := by
  have hU := fun q => exists_vec (sg X s) ((X.C b).v ≫ X.ψ b (aq q))
  choose U hUl hUt using hU
  have hU' := fun q => exists_lift X b (aq q) (Wq q) (hW q) s (U q) (hUl q)
  choose U' h1 h2 using hU'
  have hnorm : IsLieNormSq (X.C b).P (X.C b).v (sg X s) r :=
    (T.lie_norm_sq_base_change E H _ _ _ _ (Z b).C (X.C b) _ (X.φ b) (sg X s) r (X.map b)).1 hr
  have hk : kap X τ s (wK H) = sg X s (X.ω b) := w_eq X b τ hτ s
  have g0 : IsHodgeGram X.B.t.G X.B.t.PP.L (spMap (sg X s)) U
      (Matrix.of fun q q' => r * kap X τ s (X.h b (aq q) (aq q'))) := by
    let C := X.C b
    let T := X.B
    let ψ := X.ψ b
    let σ := sg X s
    let κ := kap X τ s
    let h := X.h b
    let L := PureType.lat hP (sgnRt H b)
    let ω := X.ω b
    have hu (k : Fin M) : (U k).left =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ C.v.left ≫ (ψ (aq k)).left := by
      rw [← Over.comp_left]
      exact hUl k
    obtain ⟨hlin, -, -, hlam⟩ := X.fam b
    obtain ⟨P', φ, v', uC, Hm, χ, w, ⟨hg', hpb, hLB⟩, hvo, hAH, hdw, hrr⟩ := hnorm
    have laws := abelianSchemeLaws_all.1
    obtain ⟨Q, ψQ, hQg, hQpb, hQLB⟩ := exists_isPolFibre laws.polBaseChange σ T.pol
    obtain ⟨rig0, hrig0⟩ := P'.rigid
    obtain ⟨u0, Hm0, χ0, -, hAH0, -, -, d20, hend0, -⟩ := thetaUnifAV_all P' rig0 hrig0
    obtain ⟨rigT, hrigT⟩ := Q.rigid
    obtain ⟨uT, HmT, χT, -, hAHT, -, -, d2T, -, -⟩ := thetaUnifAV_all Q rigT hrigT
    have := T.t.comm
    have := C.P.isAb.comm
    have hψm : ∀ b, IsMonHom (ψ b) := fun b => (hlin b).isMonHom
    choose f hfm hfc using fun a : L =>
      @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hQpb (ψ a) (hψm a)
    choose e hem hec using fun c : OK H =>
      @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hpb (C.act.act c) (C.act.hom c)
    choose F hFl using fun a : L =>
      @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ uT u0 (f a) (hfm a)
    choose G hGl using fun c : OK H => hend0 (e c) (hem c)
    obtain ⟨K, hK⟩ := @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ u0 uC (𝟙 P'.A) inferInstance
    have hv'T : IsTangent v' := IsVecOver.isTangent hpb hvo (C.basis.1 0)
    have hd0 : u0.IsDiff (K w) v' := by
      simpa using HodgeUniq.isDiff_comp u0 uC d20 (𝟙 P'.A) K hK hv'T hdw
    have hKH : ∀ z z', hermForm Hm0 (K z) (K z') = hermForm Hm z z' :=
      (_root_.GlobalTheory.T.weilEq_iff_hermForm_eq_complex thetaUnifAV_all laws P' P' P' P' uC uC u0 uC Hm0 Hm χ0 χ hAH0 hAH (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
        K K LinearMap.id LinearMap.id hK hK (fun z => by simp) (fun z => by simp)).1 (fun _ _ _ _ _ _ _ => Iff.rfl)
    have hkey : ∀ b b' : L, ∀ z z',
        hermForm HmT (F b z) (F b' z') = hermForm Hm0 (G (h b b') z) z' := by
      intro b b' z z'
      have W0 := (PairingFibre.lamEq_weilEq_over_ring laws (𝓞 X.K) C.P C.P T.pol C.P (ψ b) (ψ b') (C.act.act (h b b'))
        (𝟙 _) (hψm b) (hψm b') (C.act.hom _) inferInstance ℂ σ).1 (hlam b b')
      have hId : (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ =
          φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left := by
        exact (Category.id_comp φ).trans (Category.comp_id φ).symm
      have W1 := (PairingFibre.weilEq_iff hpb hpb hQpb hpb T.t.PP.isLB C.P.isLB Q.isLB P'.isLB
        (LBIso.symm hQLB) (LBIso.symm hLB) (hfc b) (hfc b') (hec (h b b')) hId (𝟙 (Sp ℂ))).2
        (by rw [Category.id_comp]; exact W0)
      have := (_root_.GlobalTheory.T.weilEq_iff_hermForm_eq_complex thetaUnifAV_all laws P' P' Q P' u0 u0 uT u0 HmT Hm0 χT χ0 hAHT hAH0 (f b) (f b')
        (e (h b b')) (𝟙 _) (F b) (F b') (G (h b b')) LinearMap.id (hFl b) (hFl b') (hGl _) (fun z => by simp)).1 W1 z z'
      simpa using this
    have hg1 : P'.g = 1 := hg'.trans C.dim
    choose c hc using fun x : OK H => CurveAdjoint.exists_scalar hg1 (G x)
    have pa : ∀ (b : OK H) (p : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A),
        Geo.Tor.pushHom hpb _ (p ≫ e b) = Geo.Tor.pushHom hpb _ p ≫ C.act.act b := fun b p =>
      Over.OverMorphism.ext (by
        show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
        rw [Category.assoc, hec, Category.assoc])
    have inj : ∀ p q : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, Geo.Tor.pushHom hpb _ p = Geo.Tor.pushHom hpb _ q → p = q :=
      fun p q e' => SymBaseChange.pushPt_injective hpb e'
    have sc : ∀ (b : OK H) (s : ℂ) (Gs : (Fin P'.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z, Gs z = s • z) →
        (∀ z, u0.ex (G b z) = u0.ex (Gs z)) → c b = s := fun b s Gs hG hh => by
      have e' := congrFun ((hc b 1).symm.trans ((LinearMap.congr_fun (CurveAdjoint.linear_eq_of_ex u0 _ _ hh) 1).trans
        (hG 1))) ⟨0, by omega⟩
      simpa using e'
    let j : OK H →+* ℂ := RingHom.mk'
      { toFun := c
        map_one' := sc 1 1 LinearMap.id (fun z => by simp) fun z => inj _ _ (by
          rw [hGl, pa, C.act.one, Category.comp_id, LinearMap.id_apply])
        map_mul' := fun b b' => sc _ _ (G b' ∘ₗ G b) (fun z => by
          rw [LinearMap.comp_apply, hc, hc, smul_smul, mul_comm]) fun z => inj _ _ (by
            rw [LinearMap.comp_apply, hGl, hGl, hGl, pa, pa, pa, C.act.mul, Category.assoc]) }
      fun b b' => sc _ _ (G b + G b') (fun z => by
        rw [LinearMap.add_apply, hc, hc, ← add_smul]; rfl) fun z => inj _ _ (by
          rw [LinearMap.add_apply, u0.ex_add, map_mul, hGl, hGl, hGl, pa, pa, pa, C.act.add, Hom.mul_def, Hom.mul_def,
            ← Category.assoc, comp_lift])
    have heig : C.v ≫ C.act.act (wK H) = CMCurveTest.scaleVec ω C.v := by
      obtain ⟨u_, hu_, hprod⟩ := C.eig
      rw [hprod]
      apply Over.OverMorphism.ext
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
      exact hu_ 0
    have hover : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (v' ≫ e (wK H)) := by
      show (v' ≫ e _).left ≫ φ = _
      rw [Over.comp_left, Category.assoc, hec, ← Category.assoc, hvo, Over.comp_left, Category.assoc]
    have hsc : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (CMCurveTest.scaleVec (σ ω) v') := by
      rw [heig]
      exact CMCurveTest.isVecOver_scaleVec hvo ω
    have hvv : v' ≫ e (wK H) = CMCurveTest.scaleVec (σ ω) v' :=
      (existsUnique_isVecOver hpb.1 (C.v ≫ C.act.act (wK H))).unique hover hsc
    have hGw : G (wK H) (K w) = σ ω • K w := by
      have := hem (wK H)
      have h1 := HodgeUniq.isDiff_comp u0 u0 d20 (e (wK H)) (G (wK H)) (hGl _) hv'T hd0
      have h2 := CMCurveTest.isDiff_scaleVec u0 hd0 (σ ω)
      rw [← hvv] at h2
      exact HodgeUnique.eq_of_isDiff u0 (Fl.lie_norm_square_of_family.isTangent_comp hv'T (e (wK H))) h1 h2
    have hjk : K w ≠ 0 → ∀ x, c x = κ x := by
      intro hne x
      have hw : c (wK H) = σ ω := by
        have e' : (c (wK H) - σ ω) • K w = 0 := by rw [sub_smul, ← hc, hGw, sub_self]
        exact sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_right hne)
      obtain ⟨⟨m, k⟩, hx, -⟩ := existsUnique_coord H x
      have hw' : j (wK H) = κ (wK H) := hw.trans hk.symm
      change j x = κ x
      rw [hx, j.map_add, κ.map_add, j.map_mul, κ.map_mul, map_intCast j m, map_intCast j k,
        map_intCast κ m, map_intCast κ k, hw']
    refine ⟨Q, ψQ, fun k => v' ≫ f (aq k), uT, HmT, χT, fun k => F (aq k) (K w), hQpb, hQLB, hAHT,
      fun k => ⟨?_, ?_⟩, fun k k' => ?_⟩
    · rw [Over.comp_left, Category.assoc, hfc, ← Category.assoc, hvo, hu k, Category.assoc]
      rfl
    · have := hfm (aq k)
      exact HodgeUniq.isDiff_comp uT u0 d2T (f (aq k)) (F (aq k)) (hFl _) hv'T hd0
    · simp only [Matrix.of_apply]
      rw [hkey, hc, Fl.lie_norm_square_of_family.hermForm_smul_left, hKH]
      obtain ⟨t, ht⟩ : ∃ t : ℝ, hermForm Hm w w = t := ⟨_, Fl.lie_norm_square_of_family.hermForm_self_eq_re hAH.1 w⟩
      rw [ht] at hrr ⊢
      simp only [Complex.ofReal_re] at hrr
      by_cases hne : K w = 0
      · have h0 : (t : ℂ) = 0 := by rw [← ht, ← hKH, hne]; simp [hermForm]
        have h0' : t = 0 := by exact_mod_cast h0
        rw [hrr, h0']
        simp
      · rw [hjk hne, hrr]
        push_cast
        ring
  have hx1 : spMap (sg X s) = spMap s ≫ spMap (algebraMap (𝓞 X.K) X.K) := (spMap_comp_spMap _ _).symm
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  have hV2 : ∀ q, (V q).left = (U' q).left ≫ X.m.φ := fun q => (hV q).trans (h1 q).symm
  have hU2 : ∀ q, (U q).left = (U' q).left ≫ X.m'.φ := fun q => (h2 q).symm
  have g1 := (T.hodge_gram_invariant_pullback E H _ _ X.B.t X.t _ X.m' (spMap s) (spMap (sg X s)) M U' U _ hx1 hU2).2 g0
  have g2 := (T.hodge_gram_invariant_pullback E H _ _ Xo.univ.t X.t _ X.m (spMap s) (under (spMap s ≫ X.y)) M U' V _ hx2 hV2).1 g1
  refine ⟨fun q => ?_, g2⟩
  exact (tan_iff X.m hx2 (U' q) (V q) (hV2 q)).1
    ((tan_iff X.m' hx1 (U' q) (U q) (hU2 q)).2 (hUt q (one_tangent X b (aq q))))

theorem mat_id {n M : ℕ} {I : Type} [Fintype I] [DecidableEq I] (e : Fin M ≃ Fin n × I) (x : I → ℂ)
    (G : Fin n × I → Fin n × I → ℂ) (A : Matrix (Fin n) (Fin M) ℂ)
    (hA : ∀ k q, A k q = if (e q).1 = k then x (e q).2 else 0) (k k' : Fin n) :
    (A * Matrix.of (fun q q' => G (e q) (e q')) * Aᴴ) k k' =
      ∑ m, ∑ m', x m * G (k, m) (k', m') * starRingEnd ℂ (x m') := by
  have hl : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, A k q * F q = ∑ m, x m * F' (k, m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  have hr : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, F q * star (A k q) = ∑ m, F' (k, m) * starRingEnd ℂ (x m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [hr k' _ (fun p' => ∑ m, x m * G (k, m) p') (fun q' => hl k _ (fun p => G p (e q')) fun q => rfl)]
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

theorem hodgeGram_cmVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ n a v s y' v' r hτ hv hy hv' hr
  classical
  subst hy
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  let e0 : Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFin _).symm
  let e : Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃
      Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) e0)
  choose nk ek uk h1 h2 using hv
  let W₂ : Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (epsAt (under X.y) ⟶ Xo.univ.t.G) :=
    fun k m => uk k ((ek k).symm m)
  have hW₂ : ∀ k m, X.IsImage b (RingOfIntegers.basis E m • a k) (W₂ k m) := fun k m => by
    have := h1 k ((ek k).symm m)
    rwa [Equiv.apply_symm_apply] at this
  have hVex := fun q => exists_bc (G := Xo.univ.t.G) s (under X.y) hx2 (W₂ (e q).1 (e q).2)
  choose V hV using hVex
  obtain ⟨ht, hg⟩ := gram_family X b τ hτ s r hr (fun q => RingOfIntegers.basis E (e q).2 • a (e q).1)
    (fun q => W₂ (e q).1 (e q).2) (fun q => hW₂ _ _) V hV
  let x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ := fun m => s (X.β (tauE c τ (HT.dualInt E m)))
  let A : Matrix (Fin n) (Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))) ℂ :=
    Matrix.of fun k q => if (e q).1 = k then x (e q).2 else 0
  have hcomb : ∀ k, Fl.IsComb (A k) V (v' k) := fun k => by
    have b1 := isComb_bc s (under X.y) hx2 _ (uk k) (v k) (fun j => V (e.symm (k, ek k j))) (v' k)
      (fun j => by
        rw [hV]
        simp only [Equiv.apply_symm_apply, W₂, Equiv.symm_apply_apply]) (hv' k) (h2 k)
    refine isComb_pad (A k) V (fun j => e.symm (k, ek k j)) (fun j j' hj => ?_) (fun j => ?_) (fun _ => rfl)
      (fun q hq => ?_) ht b1
    · have := e.symm.injective hj
      exact (ek k).injective (Prod.ext_iff.1 this).2
    · simp [A, x]
    · by_contra hne
      have hk : (e q).1 = k := by
        by_contra hk
        exact hne (by simp [A, hk])
      refine hq ⟨(ek k).symm (e q).2, ?_⟩
      simp only [Equiv.apply_symm_apply]
      rw [← hk]
      exact e.symm_apply_apply q
  have g3 := T.hodge_gram_linear_combination _ _ _ _ _ _ V v' _ A ht hg hcomb
  convert g3 using 1
  ext k k'
  have m1 := mat_id e x (fun p p' => (r : ℂ) * kap X τ s (X.h b
    ((RingOfIntegers.basis E p.2 • a p.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La)
    ((RingOfIntegers.basis E p'.2 • a p'.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La))) A (fun _ _ => rfl) k k'
  have m2 := T.dual_basis_hermitian_sum E H (FU.Di i) (X.ε b) (X.h b) (s.comp (X.β.comp (tauE c τ))) (kap X τ s) _ e0 (a k) (a k')
    (X.kform b) rfl
  dsimp only at m1
  have m3 : ∑ m, ∑ m', x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m') =
      ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k')))) := by
    refine Eq.trans ?_ m2
    rw [← Equiv.sum_comp e0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp e0]
    rfl
  refine Eq.trans ?_ m1.symm
  rw [Matrix.of_apply, _root_.mul_assoc, ← m3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  show (r : ℂ) * (x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m')) =
    x m * ((r : ℂ) * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La)))) * starRingEnd ℂ (x m')
  ring

end GlobalTheory.CompanionTheory.Ar.Fl.GInf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_period_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | exact GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmNumberField
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.InfPlace

theorem log_norm_det_scaled {E : Type} [Field E] (σ : E →+* ℂ) (rt : E) (d : ℕ) (hd : 0 < d)
    (hrt : rt ^ 2 = -(d : E)) (r : ℝ) (hr : 0 < r) (ε : ℤˣ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (hM : M.det ≠ 0) (Γ : Matrix (Fin n) (Fin n) ℂ)
    (hΓ : ∀ k k', Γ k k' = (r : ℂ) * ((ε : ℤ) : ℂ) * σ (rt * M k k')) :
    Real.log ‖Γ.det‖ = (n : ℝ) * (Real.log r + Real.log d / 2) + Real.log ‖σ M.det‖ := by
  have hΓ' : Γ = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) • (σ.mapMatrix M) := by
    ext k k'
    simp only [hΓ, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    ring
  have hdet : Γ.det = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n * σ M.det := by
    rw [hΓ', Matrix.det_smul, Fintype.card_fin, RingHom.map_det]
  have hε : ‖((ε : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hs : ‖σ rt‖ ^ 2 = d := by
    have h1 : σ rt ^ 2 = -(d : ℂ) := by
      rw [← map_pow, hrt]
      simp
    have h2 := congrArg norm h1
    simpa [norm_pow] using h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : ‖σ rt‖ ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 : (d : ℝ) = 0 := by simpa using hs.symm
    linarith
  have hlog : Real.log ‖σ rt‖ = Real.log d / 2 := by
    have h3 := congrArg Real.log hs
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hσM : σ M.det ≠ 0 := (map_ne_zero σ).2 hM
  have hpos : ‖((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n‖ ≠ 0 := by
    rw [norm_pow, norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one]
    exact pow_ne_zero _ (mul_ne_zero hr.ne' hs0)
  rw [hdet, norm_mul, Real.log_mul hpos (norm_ne_zero_iff.2 hσM), norm_pow, norm_mul, norm_mul, hε,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one, Real.log_pow,
    Real.log_mul hr.ne' hs0, hlog]

theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main hd hz

theorem hasInfNorm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r s n n' t hty hτ hU hline he hconst hr hrz hn hn' hLt hLf hinf
  classical
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ k inferInstance hty hτ
  have hxli : LinearIndependent (𝓞 E) x := hloc.1
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hTdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hTne := hTdet hxli
  have hGe := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  obtain ⟨hfram, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hU hline he
    hconst hxli hT hfr
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ (IntermediateField.inclusion hkK).toRingHom s
  have hs'a : ∀ a : k, s' (IntermediateField.inclusion hkK a) = s a := fun a => DFunLike.congr_fun hs' a
  have hβ : s'.comp X.β = s.comp (IntermediateField.inclusion hc).toRingHom := by
    ext a
    exact hs'a (IntermediateField.inclusion hc a)
  have hMs : ∀ b, s'.comp (IntermediateField.inclusion (X.hM b)).toRingHom =
      s.comp (IntermediateField.inclusion (hM b)).toRingHom := by
    intro b
    ext a
    exact hs'a (IntermediateField.inclusion (hM b) a)

  let y' : Sp ℂ ⟶ Xo.XF c := spMap s' ≫ X.y
  have hy' : under y' = spMap s' ≫ under X.y := Category.assoc _ _ _
  obtain ⟨⟨v', hv'⟩, hvI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hy'
  obtain ⟨⟨w', hw'⟩, hwI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hy'
  have hfram' : IsFramed U τ (s.comp (IntermediateField.inclusion hc).toRingHom) y' v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hβ]
      simp only [y', Category.assoc, hfram.1]
      simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]
    · rintro _ ⟨u, rfl⟩
      apply hfram.2.1
      exact ⟨(spMap s') u, by simp [y']⟩
    · rw [← hβ, RingHom.comp_assoc]
      exact (hvI v' hv').1 hfram.2.2.1
    · rw [← hβ, RingHom.comp_assoc]
      exact (hwI w' hw').1 hfram.2.2.2
  have hconjτ : ComplexEmbedding.conjugate τ (H.rt : E) = sgnRt H false := by
    simp only [sgnRt, ComplexEmbedding.conjugate_coe_eq, hτ]
    exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hΓ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X true τ D.p (fun a => ⟨x (.inl a), hx.1 a⟩) v s' y' v' n
    (by simpa [sgnRt] using hτ) hfr.1 rfl hv' (by rw [hMs]; exact hLt)
  have hΔ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) D.q
    (fun a => ⟨x (.inr a), hx.2 a⟩) w s' y' w' n' hconjτ hfr.2 rfl hw' (by rw [hMs]; exact hLf)
  have hmain := hinf y' v' w' _ _ hfram' hΓ hΔ
  rw [hline.nat X.K ℂ s' X.β X.y v w y' v' w' hfram rfl hv' hw'] at hmain

  have hblock : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 b) (hx.2 a)).2
    · rfl
  have hdet1 : (gramE (FU.Di i) x).det =
      (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₁₂]
  have hdet2 : (gramE (FU.Di i) x).det =
      T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    have hc' : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) T).symm
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc']
  have hconjne : IsCMField.complexConj E T.det ≠ 0 := by
    simpa using hTne
  have hG : (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    rw [← hdet1, hdet2]
    exact mul_ne_zero (mul_ne_zero hTne hGe) hconjne
  have hG1 := left_ne_zero_of_mul hG
  have hG2 := right_ne_zero_of_mul hG

  let σ : E →+* ℂ := s'.comp (X.β.comp (tauE c τ))
  let σ' : E →+* ℂ := s'.comp (X.β.comp (tauE c (ComplexEmbedding.conjugate τ)))
  have hσ' : ∀ a, ‖σ' a‖ = ‖σ a‖ := by
    intro a
    have h1 : tauE c (ComplexEmbedding.conjugate τ) a = tauE c τ (IsCMField.complexConj E a) := by
      apply Subtype.ext
      change ComplexEmbedding.conjugate τ a = τ (IsCMField.complexConj E a)
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    have h2 : σ' a = σ (IsCMField.complexConj E a) := by
      simp only [σ', σ, RingHom.comp_apply, h1]
    rw [h2, IsCMField.complexEmbedding_complexConj, RCLike.norm_conj]
  have hrt : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hlΓ := log_norm_det_scaled σ (H.rt : E) H.d H.d_prime.pos hrt n hn (X.ε true)
    (gramE (FU.Di i) (x ∘ Sum.inl)) hG1
    (Matrix.of fun a a' => (n : ℂ) * ((X.ε true : ℤ) : ℂ) *
      s' (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (x (.inl a)) (x (.inl a')))))) (fun _ _ => rfl)
  have hlΔ := log_norm_det_scaled σ' (H.rt : E) H.d H.d_prime.pos hrt n' hn' (X.ε false)
    (gramE (FU.Di i) (x ∘ Sum.inr)) hG2
    (Matrix.of fun a a' => (n' : ℂ) * ((X.ε false : ℤ) : ℂ) *
      s' (X.β (tauE c (ComplexEmbedding.conjugate τ) ((H.rt : E) * sesq (FU.Di i) (x (.inr a)) (x (.inr a')))))) (fun _ _ => rfl)
  rw [hσ'] at hlΔ

  have hz := GlobalTheory.T.curve_z_ne_zero E H _ (Z true)
  have hval2 : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    apply mul_right_cancel₀ (pow_ne_zero D.p hz)
    rw [hval, ← hrz]
    ring
  have hK : (φ X.K X.y v w) * X.β (tauE c τ T.det) =
      IntermediateField.inclusion hkK r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
    Subtype.ext hval2
  have hS : s' (φ X.K X.y v w) * σ T.det = s r * σ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    have := congrArg s' hK
    rw [map_mul, map_mul, hs'a] at this
    exact this
  have hφ0 : s' (φ X.K X.y v w) ≠ 0 := (map_ne_zero s').2 (hline.ne X.K X.β X.y v w hfram)
  have hσT : σ T.det ≠ 0 := (map_ne_zero σ).2 hTne
  have hσG2 : σ (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := (map_ne_zero σ).2 hG2
  have hσG1 : σ (gramE (FU.Di i) (x ∘ Sum.inl)).det ≠ 0 := (map_ne_zero σ).2 hG1
  have hσGe : σ (gramE (FU.Di i) e).det ≠ 0 := (map_ne_zero σ).2 hGe
  have hsr : s r ≠ 0 := (map_ne_zero s).2 hr
  have hl1 : Real.log ‖s' (φ X.K X.y v w)‖ + Real.log ‖σ T.det‖ =
      Real.log ‖s r‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hφ0) (norm_ne_zero_iff.2 hσT),
      ← Real.log_mul (norm_ne_zero_iff.2 hsr) (norm_ne_zero_iff.2 hσG2), ← norm_mul, ← norm_mul, hS]
  have hl2 : Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inl)).det‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ =
      2 * Real.log ‖σ T.det‖ + Real.log ‖σ (gramE (FU.Di i) e).det‖ := by
    have h1 := congrArg σ (hdet1.symm.trans hdet2)
    rw [map_mul, map_mul, map_mul, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_mul (norm_ne_zero_iff.2 hσG1) (norm_ne_zero_iff.2 hσG2),
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)) (norm_ne_zero_iff.2 hσT),
      Real.log_mul (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)] at h3
    linarith
  have hlast : s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det) =
      σ (gramE (FU.Di i) e).det :=
    (DFunLike.congr_fun hβ (tauE c τ (gramE (FU.Di i) e).det)).symm
  rw [hlast]
  rw [hlΓ, hlΔ] at hmain
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl.InfPlace
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmNumberFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_cm_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.InfPlace.hasInfNorm_value | exact GlobalTheory.CompanionTheory.Ar.Fl.InfPlace.hasInfNorm_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.InfPlace.hasInfNorm_value <;> assumption)
end

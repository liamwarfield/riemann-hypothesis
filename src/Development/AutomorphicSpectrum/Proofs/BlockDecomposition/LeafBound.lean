module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalKTypeFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.LeafB

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_infOf (hD : DiscInf) (hT : TopInf) (τ : E →+* ℂ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → ∃ m', t.InfOf τ m' := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, hV, -⟩
    · exact ⟨_, 0, hT E τ, rfl⟩
    · obtain ⟨m₀, hm₀⟩ := hD E _ V hV τ
      exact ⟨_, m₀, hm₀, rfl⟩
  | node t₁ t₂ i₁ i₂ =>
    intro h
    obtain ⟨m₁, h₁⟩ := i₁ h.1
    obtain ⟨m₂, h₂⟩ := i₂ h.2
    exact ⟨_, m₁, m₂, h₁, h₂, rfl⟩

theorem leaf_entries (hD : DiscInf) (hT : TopInf) (B : ℝ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → (∀ τ m', t.InfOf τ m' → ∀ x ∈ m', ‖x‖ ≤ B) →
      LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
        ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro h hb hM
    rcases h with ⟨h0, -, -⟩ | ⟨-, hV, -⟩
    · omega
    · refine ⟨hV, fun τ m₀ hm₀ x hx => ?_⟩
      exact hb τ (m₀.map (· + z)) ⟨m₀, hm₀, rfl⟩ _ (Multiset.mem_map_of_mem _ hx)
  | node t₁ t₂ i₁ i₂ =>
    intro h hb
    refine ⟨i₁ h.1 fun τ m₁ h₁ x hx => ?_, i₂ h.2 fun τ m₂ h₂ x hx => ?_⟩
    · obtain ⟨m₂, h₂⟩ := exists_infOf hD hT τ h.2
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inl hx))
    · obtain ⟨m₁, h₁⟩ := exists_infOf hD hT τ h.1
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inr hx))

theorem norm_sum_le (s : Multiset ℂ) (B : ℝ) (h : ∀ x ∈ s, ‖x‖ ≤ B) :
    ‖s.sum‖ ≤ (Multiset.card s : ℝ) * B := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.card_cons]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have h3 := norm_add_le a s.sum
    push_cast
    linarith

theorem sum_map_add_const (s : Multiset ℂ) (z : ℂ) :
    (s.map (· + z)).sum = s.sum + (Multiset.card s : ℂ) * z := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    ring

theorem leaf_bound (hD : DiscInf) {M : ℕ} (hM : 0 < M) {V : Submodule ℂ (Sm E M)} (hV : GlobalTheory.UnitaryBC.IsDiscrete V) {z : ℂ} {B : ℝ}
    (hb : ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) :
    InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B := by
  choose m₀ hm₀ using hD E M V hV
  have htr : ∑ τ, (m₀ τ).sum = 0 := GlobalTheory.CompanionTheory.TotalTrace.total_trace_eq_zero hV hm₀
  have hcard : ∀ τ, Multiset.card (m₀ τ) = M := fun τ => (hm₀ τ).1
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hd : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos_iff.2 ⟨τ₀⟩
  have hB : 0 ≤ B := by
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard τ₀]; exact hM)
    exact (norm_nonneg _).trans (hb τ₀ _ (hm₀ τ₀) x hx)
  have hsum : ∑ τ, ((m₀ τ).map (· + z)).sum = (Fintype.card (E →+* ℂ) : ℂ) * ((M : ℂ) * z) := by
    simp only [sum_map_add_const, hcard, Finset.sum_add_distrib, htr, zero_add, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hle : ‖∑ τ, ((m₀ τ).map (· + z)).sum‖ ≤ (Fintype.card (E →+* ℂ) : ℝ) * ((M : ℝ) * B) := by
    refine (norm_sum_le_of_le Finset.univ (n := fun _ => (M : ℝ) * B) fun τ _ => ?_).trans_eq (by simp)
    have := norm_sum_le ((m₀ τ).map (· + z)) B (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
      exact hb τ _ (hm₀ τ) x hx)
    simpa [hcard] using this
  have hz : ‖z‖ ≤ B := by
    rw [hsum, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast] at hle
    have hdM : (0 : ℝ) < (Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ) := by positivity
    have : ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * ‖z‖ ≤ ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * B := by
      nlinarith [hle]
    exact le_of_mul_le_mul_left this hdM
  refine ⟨fun τ => ⟨m₀ τ, hm₀ τ, fun x hx => ?_⟩, by linarith⟩
  have h1 := hb τ _ (hm₀ τ) x hx
  have h2 : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by simpa using norm_sub_le (x + z) z
  linarith

theorem leaves_of_entries (hD : DiscInf) (B : ℝ) : ∀ {N : ℕ} {t : Tr E N},
    LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
      ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t →
    LeafZ (fun M V z => 0 < M → InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro key hM
    obtain ⟨hV, hb⟩ := key hM
    exact leaf_bound hD hM hV hb
  | node t₁ t₂ i₁ i₂ => exact fun key => ⟨i₁ key.1, i₂ key.2⟩

theorem leafBound : DiscInf → TopInf → InfOfEq → LeafBound := by
  intro hD hT hQ E _ _ _ N t ψ m B hI hG hψ hψ0 hC hB
  refine leaves_of_entries hD B (leaf_entries hD hT B hG fun τ m' hm' x hx => ?_)
  rw [hQ E N t ψ m τ m' hI hm' hψ hψ0 hC] at hx
  exact hB τ x hx

end GlobalTheory.CompanionTheory.EGlue.LeafB

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBoundStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leaf_bound_alt : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.LeafBound := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | exact GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | (intros; apply GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalCharacterKernelScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalCharacterKernelScaling
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest

theorem trace_tmul_eq {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)
      = LinearMap.baseChange R (Algebra.lmul F E e) := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, Algebra.trace_apply]
  simp

theorem inNOh_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (N : ℕ) {α : Af F} (hα : α ∈ Oh F) (k : Fin d) :
    InNOh b N (((N : Af F) * α) ⊗ₜ[F] b k) := by
  intro j
  by_cases h : j = k
  · subst h
    exact ⟨α, hα, by simp [Algebra.TensorProduct.basis_repr_tmul]⟩
  · refine ⟨0, fun v => zero_mem _, ?_⟩
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, Ne.symm h]

theorem exists_common_denom {E : Type} [Field E] [NumberField E] {d : ℕ} (ε : Fin d → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ k, IsIntegral ℤ ((y : E) * ε k) := by
  have hex : ∀ k, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * ε k) := by
    intro k
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (ε k)))
    exact ⟨y, hy, by simpa [zsmul_eq_mul] using h⟩
  choose y hy hint using hex
  refine ⟨∏ k, y k, Finset.prod_ne_zero_iff.mpr fun k _ => hy k, fun k => ?_⟩
  have h1 : (((∏ j, y j : ℤ)) : E) * ε k
      = ((∏ j ∈ Finset.univ.erase k, y j : ℤ) : E) * ((y k : E) * ε k) := by
    rw [← mul_assoc, ← Int.cast_mul, mul_comm (∏ j ∈ Finset.univ.erase k, y j) (y k),
      Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [h1]
  have h2 : IsIntegral ℤ (((∏ j ∈ Finset.univ.erase k, y j : ℤ)) : E) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (∏ j ∈ Finset.univ.erase k, y j : ℤ))
  exact h2.mul (hint k)

theorem rat_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∀ N : ℕ, 0 < N → ∀ D : ℕ, 0 < D → (∀ f : F,
      (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f) →
    ∃ t : F, t ≠ 0 ∧ ∀ w : E, (∀ x : Af F ⊗[F] E, InNOh b N x →
        psiFin F ψ (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F) w)) = 1) →
      ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = t • w := by
  intro F E _ _ _ _ _ σ hCM d b ψ hψ N hN D hD hDint
  have hF : IsTotallyReal F := hCM.1
  obtain ⟨ρ, e, h1, h2, h3, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  obtain ⟨a, ha, -, ψf, hstd, hpsi⟩ := GlobalTheory.T.adelic_character_archimedean_form F hF ρ e h1 h2 h3 ψ hψ
  have hbeta := ((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.2
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  let b' : Module.Basis (Fin d) F E := b.map τ.toLinearEquiv
  have hb' : ∀ k, b' k = σ (b k) := fun k => by simp [b', τ]
  let ε := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b'
  obtain ⟨y, hy, hyint⟩ := exists_common_denom (fun k => ε k)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hDF : (D : F) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy
  refine ⟨(y : F) * ((D : F) * (a * (N : F))), mul_ne_zero hyF (mul_ne_zero hDF (mul_ne_zero ha hNF)), ?_⟩
  intro w hw

  have hcoord : ∀ k, ∃ o : 𝓞 F, (o : F) = (D : F) * (a * (N : F) * ε.repr w k) := by
    intro k
    have hrepr : ε.repr w k = Algebra.trace F E (σ (b k) * w) := by
      rw [LinearMap.BilinForm.dualBasis_repr_apply, hb', Algebra.traceForm_apply, mul_comm]
    refine hDint _ ((hbeta _).mp fun α hα => ?_)
    have hx := hw (((N : Af F) * α) ⊗ₜ[F] b k) (inNOh_tmul b N hα k)
    have e1 : sigR (Af F) σ (((N : Af F) * α) ⊗ₜ[F] b k) * inclR (Af F) w
        = ((N : Af F) * α) ⊗ₜ[F] (σ (b k) * w) := by
      change (((N : Af F) * α) ⊗ₜ[F] σ (b k)) * ((1 : Af F) ⊗ₜ[F] w) = _
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1, trace_tmul_eq] at hx
    change ψ (pairA F 0 _) = 1 at hx
    rw [hpsi] at hx
    rw [hrepr, ← hx]
    congr 1
    simp only [map_mul, map_natCast]
    ring
  choose o ho using hcoord
  rw [← IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := ℤ), ← ε.sum_repr w, Finset.smul_sum]
  refine IsIntegral.sum _ fun k _ => ?_
  have e2 : ((y : F) * ((D : F) * (a * (N : F)))) • (ε.repr w k • ε k)
      = algebraMap F E (o k : F) * ((y : E) * ε k) := by
    have e3 : (y : F) * ((D : F) * (a * (N : F))) * ε.repr w k
        = (y : F) * ((D : F) * (a * (N : F) * ε.repr w k)) := by ring
    rw [smul_smul, Algebra.smul_def, e3, ho k, map_mul, map_intCast]
    ring
  rw [e2]
  exact (IsIntegral.algebraMap (RingOfIntegers.isIntegral_coe (o k))).mul (hyint k)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalCharacterKernelScalingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_character_kernel_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∀ N : ℕ, 0 < N → ∀ D : ℕ, 0 < D → (∀ f : F,
      (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f) →
    ∃ t : F, t ≠ 0 ∧ ∀ w : E, (∀ x : Af F ⊗[F] E, InNOh b N x →
        psiFin F ψ (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F) w)) = 1) →
      ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = t • w := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectors
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectors
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.TypeSpace

section Abstract

variable {K X : Type*} [Group K] [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def restrictRep (π : K →* (X →L[ℂ] X)) (Y : Submodule ℂ X) (hY : ∀ g, ∀ v ∈ Y, π g v ∈ Y) :
    Representation ℂ K Y where
  toFun g := ((π g : X →L[ℂ] X) : X →ₗ[ℂ] X).restrict (hY g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

theorem span_orbit_stable' (π : K →* (X →L[ℂ] X)) (F : X) (g : K) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun k : K => π k F),
      π g v ∈ Submodule.span ℂ (Set.range fun k : K => π k F) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul]
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

end Abstract

theorem exists_typeSpace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  intro E _ _ _ a μ _ _ H hH hI F hFH hK
  obtain ⟨hSo, hfd⟩ := hK
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a

  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | R (latticeGL E a) μ (finGL E a k) F = F}
      mul_mem' := fun {x y} hx hy => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        have hy' : R (latticeGL E a) μ (finGL E a y) F = F := hy
        change R (latticeGL E a) μ (finGL E a (x * y)) F = F
        rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hy', hx']
      one_mem' := by
        change R (latticeGL E a) μ (finGL E a 1) F = F
        simp
      inv_mem' := fun {x} hx => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        change R (latticeGL E a) μ (finGL E a x⁻¹) F = F
        conv_lhs => rw [← hx']
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel]
        simp }
  have hSo' : IsOpen (S : Set (GL (Fin a) (Af E))) := hSo
  let U : Subgroup (GL (Fin a) (Af E)) := K0 ⊓ S
  have hUo : IsOpen (U : Set (GL (Fin a) (Af E))) := hK0o.inter hSo'
  have hUc : IsCompact (U : Set (GL (Fin a) (Af E))) := hK0c.inter_right (S.isClosed_of_isOpen hSo')

  let π : Kinf E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) :=
    (R (latticeGL E a) μ).comp ((infGL E a).comp Unitary.toUnits)
  have hcomm : ∀ (u : GL (Fin a) (Af E)) (k : Kinf E a) (v : L2 (latticeGL E a) μ),
      R (latticeGL E a) μ (finGL E a u) (π k v) = π k (R (latticeGL E a) μ (finGL E a u) v) := by
    intro u k v
    have e := congrArg (fun g => R (latticeGL E a) μ g v) (infGL_comm (E := E) (a := a) (Unitary.toUnits k) u)
    simp only [map_mul, ContinuousLinearMap.mul_apply] at e
    exact e.symm
  let Y : Submodule ℂ (L2 (latticeGL E a) μ) := Submodule.span ℂ (Set.range fun k : Kinf E a => π k F)
  haveI : FiniteDimensional ℂ Y := hfd
  have hYs : ∀ g, ∀ v ∈ Y, π g v ∈ Y := span_orbit_stable' π F
  have hFY : F ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hYP : ∀ v ∈ Y, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨hI.1.2 _ _ hFH, fun u hu => ?_⟩
      exact (hcomm u k F).trans (congrArg (π k) hu.2)
    | zero => exact ⟨H.zero_mem, fun _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      exact ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
    | smul c x _ hx =>
      exact ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩
  let ρ : Representation ℂ (Kinf E a) Y := restrictRep π Y hYs
  let C : (Y →ₗ[ℂ] L2 (latticeGL E a) μ) → Prop := fun T =>
    (∀ k w, T (ρ k w) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w)) ∧
      ∀ w, T w ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (T w) = T w
  let X : Submodule ℂ (L2 (latticeGL E a) μ) := ⨆ (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T), LinearMap.range T
  have hXf : FiniteDimensional ℂ X := GlobalTheory.T.cuspidal_K_type_finite E a μ H hH hI U hUo Y ρ
  have hmem : ∀ T, C T → ∀ w, T w ∈ X := fun T hT w =>
    (le_iSup₂_of_le (f := fun (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T) => LinearMap.range T) T hT le_rfl)
      ⟨w, rfl⟩
  have hXP : ∀ v ∈ X, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    let P : Submodule ℂ (L2 (latticeGL E a) μ) :=
      { carrier := {v | v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v}
        zero_mem' := ⟨H.zero_mem, fun _ _ => map_zero _⟩
        add_mem' := fun {x y} hx hy =>
          ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
        smul_mem' := fun c x hx => ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩ }
    have hle : X ≤ P := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      exact hT.2 w
    exact hle hv
  refine ⟨U, hUo, hUc, X, hXf, ?_, fun v hv => (hXP v hv).1, ?_, fun u hu v hv => (hXP v hv).2 u hu, ?_⟩
  · exact hmem Y.subtype ⟨fun k w => rfl, fun w => hYP _ w.2⟩ ⟨F, hFY⟩
  · intro k v hv
    have hle : X ≤ X.comap ((R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) :
        L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
      iSup₂_le fun T hT => by
        rintro _ ⟨w, rfl⟩
        change R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w) ∈ X
        rw [← hT.1 k w]
        exact hmem T hT _
    exact hle hv
  · intro B hB1 hB2 v hv
    have hle : X ≤ X.comap B := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      refine hmem (B ∘ₗ T) ⟨fun k w => ?_, fun w => hB2 _ (hT.2 w).1 (hT.2 w).2⟩ w
      change B (T (ρ k w)) = _
      rw [hT.1 k w, hB1]
      rfl
    exact hle hv

end GlobalTheory.CompanionTheory.TypeSpace

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectorsStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_finite_irreducible_fixed_vectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  first | exact @GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | exact GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | (intros; apply GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingVolumeByUnit
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapPiScale
open MeasureTheory in
theorem UpperTheory.Reformulated.B.MapPiScale.map_pi_scale :
    ∀ {ι : Type} [inst : Fintype ι] {α : ι → Type}
    [inst_1 : (i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)] (g : (i : ι) → α i → α i),
    (∀ (i : ι), Measurable (g i)) →
      ∀ (c : ι → ENNReal),
        (∀ (i : ι), c i ≠ (0 : ENNReal)) →
          (∀ (i : ι), c i ≠ ⊤) →
            (∀ (i : ι), MeasureTheory.Measure.map (g i) (μ i) = c i • μ i) →
              MeasureTheory.Measure.map (fun (x : (i : ι) → α i) (i : ι) ↦ g i (x i)) (MeasureTheory.Measure.pi μ) =
                (∏ i : ι, c i) • MeasureTheory.Measure.pi μ := by
  intro ι _ α _ μ _ g hg c _ hc h
  have hs : ∀ i, SigmaFinite ((μ i).map (g i)) := by
    intro i
    rw [h i, ← ENNReal.coe_toNNReal (hc i)]
    exact (inferInstance : SigmaFinite ((c i).toNNReal • μ i))
  rw [Measure.pi_map_pi (fun i => (hg i).aemeasurable)]
  refine Measure.pi_eq fun s _ => ?_
  simp only [h, Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingVolumeByUnit
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.UnitScale

theorem map_pi_scale {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, α i → α i) (hg : ∀ i, Measurable (g i))
    (c : ι → ℝ≥0∞) (hc0 : ∀ i, c i ≠ 0) (hct : ∀ i, c i ≠ ⊤)
    (h : ∀ i, (μ i).map (g i) = c i • μ i) :
    (Measure.pi μ).map (fun x i => g i (x i)) = (∏ i, c i) • Measure.pi μ :=
  _root_.UpperTheory.Reformulated.B.MapPiScale.map_pi_scale μ g hg c hc0 hct h

end GlobalTheory.CompanionTheory.AvgFree.UnitScale


open GlobalTheory.CompanionTheory.AvgFree.UnitScale in
theorem GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n M : ℕ) (l : Fin n) (D : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), MeasurableSet D → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) {X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) ∈ D} = ((θ : ℝ≥0∞) ^ M)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) D := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv s θ hθ n M l D hD
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := hlv.1
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hK
  set μ := GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv with hμ
  haveI : SigmaFinite μ := inferInstance
  let g : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun x => (s : Fv F v ⊗[F] E) * x
  have hgm : Measurable g := (continuous_const.mul continuous_id).measurable
  have hgs : Function.Surjective g := fun y =>
    ⟨((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * y, by simp [g]⟩
  have hθ0 : (θ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have h1 := hθ Set.univ
    rw [h0, zero_mul] at h1
    have h2 : (fun x => (s : Fv F v ⊗[F] E) * x) '' Set.univ = Set.univ := Set.image_univ_of_surjective hgs
    rw [h2] at h1
    exact (IsOpen.measure_pos μ isOpen_univ ⟨0, trivial⟩).ne' h1
  have hθt : (θ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hmap : μ.map g = (θ : ℝ≥0∞)⁻¹ • μ := by
    ext Y hY
    rw [Measure.map_apply hgm hY, Measure.smul_apply, smul_eq_mul]
    have h1 := hθ (g ⁻¹' Y)
    have h2 : (fun x => (s : Fv F v ⊗[F] E) * x) '' (g ⁻¹' Y) = Y := Set.image_preimage_eq Y hgs
    rw [h2] at h1
    rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hθ0 hθt, one_mul]

  have hvec : (Measure.pi fun _ : Fin M => μ).map (fun x i => g (x i)) =
      ((θ : ℝ≥0∞)⁻¹ ^ M) • Measure.pi fun _ : Fin M => μ := by
    have := GlobalTheory.CompanionTheory.AvgFree.UnitScale.map_pi_scale (fun _ : Fin M => μ) (fun _ => g) (fun _ => hgm) (fun _ => (θ : ℝ≥0∞)⁻¹)
      (fun _ => ENNReal.inv_ne_zero.2 hθt) (fun _ => ENNReal.inv_ne_top.2 hθ0) (fun _ => hmap)
    simpa using this
  have hvm : Measurable (fun (x : Fin M → Fv F v ⊗[F] E) i => g (x i)) :=
    Measurable.of_eval fun i => hgm.comp (measurable_pi_apply i)
  let gV : Fin n → (Fin M → Fv F v ⊗[F] E) → (Fin M → Fv F v ⊗[F] E) := fun a =>
    if a = l then (fun x i => g (x i)) else id
  let c : Fin n → ℝ≥0∞ := fun a => if a = l then (θ : ℝ≥0∞)⁻¹ ^ M else 1
  have hgV : ∀ a, Measurable (gV a) := fun a => by
    by_cases h : a = l
    · simpa [gV, h] using hvm
    · simpa [gV, h] using measurable_id
  have hc0 : ∀ a, c a ≠ 0 := fun a => by
    by_cases h : a = l
    · simpa [c, h, hθt] using fun _ => hθt
    · simp [c, h]
  have hct : ∀ a, c a ≠ ⊤ := fun a => by
    by_cases h : a = l
    · simpa [c, h] using ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hθ0)
    · simp [c, h]
  have hmapV : ∀ a, (Measure.pi fun _ : Fin M => μ).map (gV a) = c a • Measure.pi fun _ : Fin M => μ :=
    fun a => by
    by_cases h : a = l
    · simpa [gV, c, h] using hvec
    · simp [gV, c, h]
  have htup := GlobalTheory.CompanionTheory.AvgFree.UnitScale.map_pi_scale (fun _ : Fin n => Measure.pi fun _ : Fin M => μ) gV hgV c hc0 hct hmapV
  have hT : Measurable (fun (x : Fin n → Fin M → Fv F v ⊗[F] E) a => gV a (x a)) :=
    Measurable.of_eval fun a => (hgV a).comp (measurable_pi_apply a)
  have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E |
      GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : Fv F v ⊗[F] E)) ∈ D} =
      (fun (x : Fin n → Fin M → Fv F v ⊗[F] E) a => gV a (x a)) ⁻¹' D := by
    ext X
    have : GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : Fv F v ⊗[F] E)) = fun a => gV a (X a) := by
      funext a i
      by_cases h : a = l
      · subst h
        simp [GlobalTheory.CompanionTheory.SW.rmul, dMat, Matrix.diagonal_apply, gV, g, mul_comm]
      · simp [GlobalTheory.CompanionTheory.SW.rmul, dMat, Matrix.diagonal_apply, gV, h]
    simp [this]
  have hprod : (∏ a, c a) = ((θ : ℝ≥0∞) ^ M)⁻¹ := by
    simp [c, ENNReal.inv_pow]
  show (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => μ) _ = _ *
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => μ) D
  rw [hset, ← Measure.map_apply hT hD, htup, hprod, Measure.smul_apply, smul_eq_mul]
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingVolumeByUnitStatement
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_scaling_volume_by_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n M : ℕ) (l : Fin n) (D : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), MeasurableSet D → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) {X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) ∈ D} = ((θ : ℝ≥0∞) ^ M)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) D := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale | exact GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale | (intros; apply GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateNormCyclotomic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateNormCyclotomic
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTNorm

variable {l : ℕ} [Fact l.Prime]

attribute [-instance] GroundTheory.PAdicHodge.subfield_valuativeRel GroundTheory.PAdicHodge.subfield_compatible GroundTheory.PAdicHodge.subfield_isValuativeTopology GroundTheory.PAdicHodge.subfield_isNontrivial GroundTheory.PAdicHodge.isNonarchimedeanLocalField_intermediateField GroundTheory.PAdicHodge.isNonarchimedeanLocalField_tower GroundTheory.PAdicHodge.valuativeExtension_padic GroundTheory.PAdicHodge.valuativeExtension_intermediateField GroundTheory.PAdicHodge.subfield_isUltrametricDist

theorem unramifiedDegree_eq_one_of_fix (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (g : Om l ≃ₐ[↥K.1] Om l)
    (h : ∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) :
    unramifiedDegree ↥K.1 (Om l) g = 1 := by
  rw [unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, GlobalTheory.CompanionTheory.LTLink.natCast_residue_eq_zero (l := l) (F := ↥K.1), zero_mul]
  exact h _ (GroundTheory.PAdicHodge.mem_unramifiedClosure_of_pow_eq_one (Nat.pos_of_ne_zero hm0)
    (((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hcop).symm) hζm)

theorem exists_norm_unit (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (u : 𝒪[↥K.1]ˣ) :
    ∃ v : ℤ_[l]ˣ, ((v : ℤ_[l]) : ℚ_[l]) = Algebra.norm ℚ_[l] ((u : 𝒪[↥K.1]) : ↥K.1) := by
  have hint : ∀ a : 𝒪[↥K.1], ∃ y : ℤ_[l], (y : ℚ_[l]) = Algebra.norm ℚ_[l] (a : ↥K.1) := by
    intro a
    have h1 : IsIntegral ℤ_[l] (a : ↥K.1) :=
      (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr
        ((GlobalTheory.CompanionTheory.LTHodge.UnitAct.valuation_le_one_iff (a : ↥K.1)).mp a.2)
    have h2 : IsIntegral ℤ_[l] (Algebra.norm ℚ_[l] (a : ↥K.1)) := Algebra.isIntegral_norm ℚ_[l] h1
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hint (u : 𝒪[↥K.1])
  obtain ⟨y', hy'⟩ := hint ((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1])
  have hm : ((y * y' : ℤ_[l]) : ℚ_[l]) = 1 := by
    rw [PadicInt.coe_mul, hy, hy', ← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]
    simp
  have hm1 : y * y' = 1 := by
    apply Subtype.ext
    exact hm
  exact ⟨⟨y, y', hm1, by rw [mul_comm]; exact hm1⟩, hy⟩

theorem toZModPow_eq_of_pow (a b : ℤ_[l])
    (h : ∀ (n : ℕ) (ζ : Om l), ζ ^ l ^ n = 1 →
      ζ ^ (PadicInt.toZModPow n a).val = ζ ^ (PadicInt.toZModPow n b).val) : a = b := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  have hl : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have : NeZero (l ^ n) := ⟨hl.ne'⟩
  have : NeZero ((l ^ n : ℕ) : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ z : Om l, IsPrimitiveRoot z (l ^ n) :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n)
  have h1 := h n ζ hζ.pow_eq_one
  have h2 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
  exact ZMod.val_injective _ h2

theorem mem_maximalAbelian {n : ℕ} {ζ : Om l} (hζ : ζ ^ l ^ n = 1) :
    ζ ∈ maximalAbelianExtension ℚ_[l] (Om l) := by
  rw [GroundTheory.LocalField.Padic.maximalAbelianExtension_eq_adjoin_rootsOfUnity l (Om l)]
  exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, hζ⟩

theorem norm_eq_cyclo : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ), IsLTChar K χ →
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  intro l _ K χ hχ _ g hg hfix
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hR : Set.range (algebraMap ↥K.1 (Om l)) = (K.1 : Set (Om l)) := Subtype.range_coe
  obtain ⟨π, hπ, hmain⟩ := GlobalTheory.CompanionTheory.LTHodge.UnitAct.main hχ (F := ↥K.1) hR
  let g' : ↥(GK K) := ⟨g, hg⟩
  let τ : Om l ≃ₐ[↥K.1] Om l := GlobalTheory.CompanionTheory.LTHodge.CharEx.gal K g'
  obtain ⟨u, huχ, hact⟩ := hmain τ g' (fun y => rfl)
  have hdeg : unramifiedDegree ↥K.1 (Om l) τ = 1 := unramifiedDegree_eq_one_of_fix K τ hfix
  have hart := GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia hπ (isLubinTateSeries_ltPoly π) u τ hdeg hact
  obtain ⟨v, hv⟩ := exists_norm_unit K u
  have hχu : ((χ g' : (↥K.1)ˣ) : ↥K.1) = ((u : 𝒪[↥K.1]) : ↥K.1) := Subtype.ext huχ.symm
  change Algebra.norm ℚ_[l] ((χ g' : (↥K.1)ˣ) : ↥K.1) = _
  rw [hχu, ← hv]

  let x : (↥K.1)ˣ := unitsIncl ↥K.1 u⁻¹
  let w : ℚ_[l]ˣ := normUnits ℚ_[l] ↥K.1 x
  have hw : (w : ℚ_[l]) = (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * (l : ℚ_[l]) ^ (0 : ℤ) := by
    have e1 : (w : ℚ_[l]) = Algebra.norm ℚ_[l] ((x : (↥K.1)ˣ) : ↥K.1) := coe_normUnits x
    have e2 : ((x : (↥K.1)ˣ) : ↥K.1) * ((u : 𝒪[↥K.1]) : ↥K.1) = 1 := by
      have h := congrArg (fun c : 𝒪[↥K.1] => (c : ↥K.1)) (Units.inv_mul u)
      simpa [x, unitsIncl] using h
    have e3 : (w : ℚ_[l]) * ((v : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [e1, hv, ← map_mul, e2, map_one]
    have e4 : ((v : ℤ_[l]) : ℚ_[l]) * (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
    rw [zpow_zero, mul_one]
    calc (w : ℚ_[l]) = (w : ℚ_[l]) * (((v : ℤ_[l]) : ℚ_[l]) * (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) := by
          rw [e4, mul_one]
      _ = _ := by rw [← mul_assoc, e3, one_mul]
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (localReciprocityLimit ℚ_[l] (Om l) w)
  have key : ∀ (n : ℕ) (ζ : Om l), ζ ^ l ^ n = 1 → g ζ = σ ζ := by
    intro n ζ hζ
    have hy := mem_maximalAbelian hζ
    have h1 := hart ζ (maximalAbelianExtension_le_restrictScalars K.1 hy)
    have h2 := localArtinMap_apply_of_mem K.1 x hy
    have h3 : localArtinMap ℚ_[l] (Om l) (normUnits ℚ_[l] ↥K.1 x) =
        topologicalAbelianizationEquiv ℚ_[l] (Om l) (σ : TopologicalAbelianization (Om l ≃ₐ[ℚ_[l]] Om l)) := by
      rw [localArtinMap_apply]
      exact congrArg _ hσ.symm
    rw [h3, topologicalAbelianizationEquiv_mk_apply] at h2
    exact h1.symm.trans h2
  have hfin : (v : ℤ_[l]) = ((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) := by
    refine toZModPow_eq_of_pow _ _ fun n ζ hζ => ?_
    have h1 := GroundTheory.PAdicHodge.cycloChar_spec (K := ⊥) (Formalism.Per6.toBot g) hζ
    have h2 := GroundTheory.LocalField.Padic.apply_of_pow_eq_one_of_prime_pow l w v⁻¹ 0 hw hσ hζ
    rw [inv_inv] at h2
    rw [← h2, ← key n ζ hζ]
    exact h1
  rw [hfin]

end GlobalTheory.CompanionTheory.LTNorm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateNormCyclotomicStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_norm_cyclotomic : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ), IsLTChar K χ →
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  first | exact @GlobalTheory.CompanionTheory.LTNorm.norm_eq_cyclo | exact GlobalTheory.CompanionTheory.LTNorm.norm_eq_cyclo | (intros; apply GlobalTheory.CompanionTheory.LTNorm.norm_eq_cyclo <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderStableIntegralStructure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderStableIntegralStructure
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.ElemHerm

theorem cjPre_haar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (n : ℕ) (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure)
    (O : Subring (R ⊗[F] E)) (hOc : IsCompact (O : Set (R ⊗[F] E))) (hOo : IsOpen (O : Set (R ⊗[F] E)))
    (hOs : ∀ x ∈ O, sigR R σ x ∈ O) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hgg : g * g' = 1)
    (hg : ∀ i j, g i j ∈ O) (hg' : ∀ i j, g' i j ∈ O) (Y : Set (HermR R σ n)) (hY : MeasurableSet Y) :
    MeasurableSet (cjPre R σ g Y) ∧ ν (cjPre R σ g Y) = ν Y := by
  obtain ⟨hTK, hLK, hSK, hTK2, hsc, -, -, -, hcl, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  have hinv : ∀ x, sigR R σ (sigR R σ x) = x :=
    GlobalTheory.CompanionTheory.AvgFree.sigR_sigR R σ (GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ)
  have hg2 : g' * g = 1 := mul_eq_one_comm.mp hgg
  let t : HermR R σ n ≃+ HermR R σ n :=
    { toFun := fun S => ⟨cjM R σ g S, cjM_mem R σ hinv g S S.2⟩
      invFun := fun S => ⟨cjM R σ g' S, cjM_mem R σ hinv g' S S.2⟩
      left_inv := fun S => Subtype.ext (by
        show cjM R σ g' (cjM R σ g S) = S
        rw [← cjM_mul, hgg, cjM_one])
      right_inv := fun S => Subtype.ext (by
        show cjM R σ g (cjM R σ g' S) = S
        rw [← cjM_mul, hg2, cjM_one])
      map_add' := fun S T => Subtype.ext (by
        simp only [cjM, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]) }
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun S : HermR R σ n => cjM R σ h (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have htc : Continuous t := (hcj g).subtype_mk _
  have hts : Continuous t.symm := (hcj g').subtype_mk _
  have hpre : ∀ Z : Set (HermR R σ n), cjPre R σ g Z = t ⁻¹' Z := by
    intro Z
    ext y
    constructor
    · rintro ⟨z, hz, e⟩
      have : t y = z := Subtype.ext e
      show t y ∈ Z
      rwa [this]
    · intro h
      exact ⟨t y, h, rfl⟩

  have hent : ∀ (h : Matrix (Fin n) (Fin n) (R ⊗[F] E)), (∀ i j, h i j ∈ O) →
      ∀ y : Matrix (Fin n) (Fin n) (R ⊗[F] E), (∀ i j, y i j ∈ O) → ∀ i j, cjM R σ h y i j ∈ O := by
    intro h hh y hy i j
    simp only [cjM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact O.sum_mem fun k _ => O.mul_mem (O.sum_mem fun m _ => O.mul_mem (hOs _ (hh _ _)) (hy _ _)) (hh _ _)
  let C : Set (HermR R σ n) := {y | ∀ i j, (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j ∈ O}
  have hCv : C = Subtype.val ⁻¹'
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set (R ⊗[F] E)) :
        Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    ext y
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hCc : IsCompact C := by
    rw [hCv]
    exact (hcl n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc)
  have hCo : IsOpen C := by
    have hval : Continuous fun y : HermR R σ n => (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val
    have e : C = ⋂ i, ⋂ j, {y : HermR R σ n | (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j ∈ O} := by
      ext y
      simp only [C, Set.mem_iInter, Set.mem_setOf_eq]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hOo.preimage ((continuous_apply_apply i j).comp hval)
  have hC0 : (0 : HermR R σ n) ∈ C := fun i j => O.zero_mem
  have htC : t ⁻¹' C = C := by
    ext y
    constructor
    · intro h
      have e : t.symm (t y) = y := t.symm_apply_apply y
      rw [← e]
      exact hent g' hg' _ h
    · intro h
      exact hent g hg _ h
  haveI hνt : (ν.map t).IsAddHaarMeasure := t.isAddHaarMeasure_map ν htc hts
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν.map t = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hCpos : ν C ≠ 0 := hCo.measure_ne_zero ν ⟨0, hC0⟩
  have hCfin : ν C ≠ ⊤ := hCc.measure_lt_top.ne
  have hc1 : c = 1 := by
    have h1 : ν.map t C = ν C := by
      rw [Measure.map_apply htc.measurable hCo.measurableSet, htC]
    rw [hc, Measure.coe_nnreal_smul_apply] at h1
    have h2 : (c : ℝ≥0∞) * ν C = 1 * ν C := by
      rw [one_mul]
      exact h1
    have h3 := (ENNReal.mul_left_inj hCpos hCfin).1 h2
    exact_mod_cast h3
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact htc.measurable hY
  · rw [hpre, ← Measure.map_apply htc.measurable hY, hc, hc1, one_smul]

end GlobalTheory.CompanionTheory.AvgFree.ElemHerm

theorem GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) = (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O hOc hOo hOs n l a ha hl Y hY
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hlv.1
  obtain ⟨-, -, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  have he : ∀ (w : Fin n → Fv F v ⊗[F] E), (∀ i, w i ∈ O) → ∀ i j, eMat (Fv F v) l w i j ∈ O := by
    intro w hw i j
    simp only [eMat, Matrix.updateCol_apply, Matrix.one_apply]
    split_ifs
    · exact hw i
    · exact O.one_mem
    · exact O.zero_mem
  have hn : ∀ i, negCol (Fv F v) l a i ∈ O := by
    intro i
    simp only [negCol]
    split_ifs
    · exact O.one_mem
    · exact O.neg_mem (ha i)
  exact GlobalTheory.CompanionTheory.AvgFree.ElemHerm.cjPre_haar F E σ hσ (Fv F v) n _ (hH n) O hOc hOo hOs _ _
    (eMat_mul_negCol (Fv F v) l a hl) (he a ha) (he _ hn) Y hY
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderStableIntegralStructureStatement
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_stable_integral_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) = (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | exact GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | (intros; apply GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat <;> assumption)
end
end

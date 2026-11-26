module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulSmulMemRange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
namespace GlobalTheory.CompanionTheory.TwistedCent

open PositivityTheory.Rg.Tf.Loc

theorem mem_twCent_twConj_iff {G : Type} [Group G] (θ : Monoid.End G) (g δ x : G) :
    x ∈ twCent θ (twConj θ g δ) ↔ g * x * g⁻¹ ∈ twCent θ δ := by
  rw [mem_twCent, mem_twCent]
  simp only [twConj, map_mul, map_inv]
  constructor
  · intro h
    calc (g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)
        = g * (x⁻¹ * (g⁻¹ * δ * θ g) * θ x) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g) * (θ g)⁻¹ := by rw [h]
      _ = δ := by group
  · intro h
    calc x⁻¹ * (g⁻¹ * δ * θ g) * θ x
        = g⁻¹ * ((g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by group
      _ = g⁻¹ * δ * θ g := by rw [h]

theorem h3 : PositivityTheory.Rg.Tf.Loc.H3 := fun _ _ θ g δ x => mem_twCent_twConj_iff θ g δ x

end GlobalTheory.CompanionTheory.TwistedCent
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdPropertyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_third_property : PositivityTheory.Rg.Tf.Loc.H3 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedCent.h3 | exact GlobalTheory.CompanionTheory.TwistedCent.h3 | (intros; apply GlobalTheory.CompanionTheory.TwistedCent.h3 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AltAlt
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem alt_alt (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) (n : ℕ) (z : K n) :
    alt (δ (n + 1)) (alt (δ n) z) = 0 := by
  have hrel : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)),
      δ (n + 1) (j.succAbove i) (δ n (i.predAbove j) z) = δ (n + 1) j (δ n i z) := fun j i =>
    DFunLike.congr_fun (coface_rel A B K ι δ hwp hδ n j i) z
  have hexp : alt (δ (n + 1)) (alt (δ n) z) = ∑ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (p.1 : ℕ) * (-1 : ℤ) ^ (p.2 : ℕ)) • δ (n + 1) p.1 (δ n p.2 z) := by
    rw [Fintype.sum_prod_type]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
      map_zsmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    rw [hrel, GlobalTheory.CatH.DSq.sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

end GlobalTheory.CompanionTheory.WpCoface
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoUnif
open PositivityTheory.Rg.BcB.E1
open scoped Pointwise Topology

namespace GlobalTheory.CompanionTheory.TwoSidedUnif

theorem twoUnif : TwoUnif := by
  intro X φ ε hφ hε
  obtain ⟨hc, hs⟩ := hφ
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have hS : IsCompact (tsupport φ) := hs
  have hK : IsCompact (N⁻¹ * tsupport φ * N⁻¹) := (hNc.inv.mul hS).mul hNc.inv
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hf : Continuous fun q : (X.G × X.G) × X.G => ‖φ (q.1.1 * q.2 * q.1.2) - φ q.2‖ := by
    have : Continuous fun q : (X.G × X.G) × X.G => q.1.1 * q.2 * q.1.2 := by fun_prop
    exact ((hc.comp this).sub (hc.comp continuous_snd)).norm
  have hev : ∀ᶠ p : X.G × X.G in 𝓝 ((1 : X.G), (1 : X.G)), ∀ y ∈ N⁻¹ * tsupport φ * N⁻¹,
      ‖φ (p.1 * y * p.2) - φ y‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h0 : ‖φ ((((1 : X.G), (1 : X.G)), y).1.1 * (((1 : X.G), (1 : X.G)), y).2 *
        (((1 : X.G), (1 : X.G)), y).1.2) - φ (((1 : X.G), (1 : X.G)), y).2‖ < ε := by
      simpa using hε
    exact hf.continuousAt.eventually (Iio_mem_nhds h0)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hev
  refine ⟨U ∩ V ∩ N, Filter.inter_mem (Filter.inter_mem hU hV) hN1, ?_⟩
  rintro z ⟨⟨hzU, -⟩, hzN⟩ w ⟨⟨-, hwV⟩, hwN⟩ y
  by_cases hy : y ∈ N⁻¹ * tsupport φ * N⁻¹
  · exact (hUV (Set.mk_mem_prod hzU hwV) y hy).le
  · have hy0 : φ y = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨1 * y, Set.mem_mul.2 ⟨1, ?_, y, hys, rfl⟩, 1, ?_, by simp⟩
      · simpa using h1N
      · simpa using h1N
    have hzy0 : φ (z * y * w) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨z⁻¹ * (z * y * w), Set.mem_mul.2 ⟨z⁻¹, ?_, z * y * w, hys, rfl⟩, w⁻¹, ?_, by group⟩
      · exact Set.inv_mem_inv.2 hzN
      · exact Set.inv_mem_inv.2 hwN
    simpa [hy0, hzy0] using hε.le

end GlobalTheory.CompanionTheory.TwoSidedUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpEx
open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.Bump

theorem bumpEx : BumpEx := by
  intro X W hW
  obtain ⟨N, hNn, hNW, hNc⟩ := local_compact_nhds hW
  have h1 : (1 : X.G) ∈ interior N := mem_interior_iff_mem_nhds.mpr hNn
  obtain ⟨b, hb1, hb0, hbc, hbI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : X.G))) isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h h1))
  have hbnn : ∀ z, 0 ≤ b z := fun z => (hbI z).1
  have hb11 : b 1 = 1 := hb1 (Set.mem_singleton _)
  have hsupp : Function.support b ⊆ N := by
    intro x hx
    by_contra hxN
    exact hx (hb0 (fun hi => hxN (interior_subset hi)))
  have hts : tsupport b ⊆ N := closure_minimal hsupp hNc.isClosed
  have hcc : Continuous fun z : X.G => b z⁻¹ := b.continuous.comp continuous_inv
  have hcs : HasCompactSupport fun z : X.G => b z⁻¹ :=
    hbc.comp_homeomorph (Homeomorph.inv X.G)
  have hI : 0 < ∫ z, b z⁻¹ ∂X.μ :=
    hcc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => hbnn _)
      (x := 1) (by simp [hb11])
  set I := ∫ z, b z⁻¹ ∂X.μ with hIdef
  have hnorm : ∀ z, ‖((b z / I : ℝ) : ℂ)‖ = b z / I := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hbnn z) hI.le)]
  have hsub : Function.support (fun z => ((b z / I : ℝ) : ℂ)) ⊆ Function.support b := by
    intro x hx h0
    apply hx
    simp [h0]
  refine ⟨fun z => ((b z / I : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Complex.continuous_ofReal.comp (b.continuous.div_const I)
  · exact hbc.mono hsub
  · intro z
    simp only [hnorm]
  · simp only [hnorm]
    rw [integral_div, ← hIdef, div_self hI.ne']
  · exact (closure_mono hsub).trans (hts.trans hNW)

end GlobalTheory.CompanionTheory.Bump
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaurentEqToLaurentSubInvert
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem laurent_eq_toLaurent_sub_invert {K : Type} [CommRing K] (h : K[T;T⁻¹]) :
    ∃ α β : Polynomial K, h = Polynomial.toLaurent α -
      LaurentPolynomial.invert (Polynomial.toLaurent β) := by
  induction h using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨α₁, β₁, rfl⟩ := hf
    obtain ⟨α₂, β₂, rfl⟩ := hg
    refine ⟨α₁ + α₂, β₁ + β₂, ?_⟩
    simp only [map_add (f := _)]
    ring
  | C_mul_T n a =>
    rcases le_total 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨Polynomial.monomial m a, 0, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T]
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)
      refine ⟨0, -Polynomial.monomial m a, ?_⟩
      have hn' : n = -(m : ℤ) := by omega
      subst hn'
      simp [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_T,
        LaurentPolynomial.invert_C]

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ _ h₁ h₂ h₃ e₁ e₂ y
  obtain ⟨k, h, hy⟩ := h₃.pow y
  obtain ⟨α, β, rfl⟩ := laurent_eq_toLaurent_sub_invert h
  obtain ⟨-, -, root₁, -, -⟩ := pf_facts p K₁ h₁.pf
  obtain ⟨-, -, root₂, -, -⟩ := pf_facts p K₂ h₂.pf
  obtain ⟨-, -, -, inj₃, -⟩ := pf_facts p K₃ h₃.pf
  obtain ⟨b₁, hb₁⟩ := root₁ k (i₁ α)
  obtain ⟨b₂, hb₂⟩ := root₂ k (i₂ β)
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K₃ h₃.pf.char k
  refine ⟨b₁, b₂, inj₃ k _ _ ?_⟩
  have key : (ρ₁ b₁ - ρ₂ b₂) ^ p ^ k = ρ₁ (b₁ ^ p ^ k) - ρ₂ (b₂ ^ p ^ k) := by
    rw [← hF (ρ₁ b₁ - ρ₂ b₂), map_sub F, hF, hF, map_pow, map_pow]
  rw [hy, key, hb₁, hb₂, e₁, e₂, map_sub]

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqZeroOfCPowMemSpan
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem mul_eq_zero_of_C_pow_mem_span (K : Type) [CommRing K]
    (hred : ∀ (x : K) (n : ℕ), x ^ n = 0 → x = 0) (f g a : K) (n : ℕ)
    (h : (Polynomial.C a) ^ n ∈
      Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) : g * a = 0 := by
  let L := Localization.Away g
  let u : L := IsLocalization.Away.invSelf g
  have hu : algebraMap K L g * u = 1 := IsLocalization.Away.mul_invSelf g
  let φ : Polynomial K →+* L := Polynomial.eval₂RingHom (algebraMap K L) (u * algebraMap K L f)
  have h0 : φ (Polynomial.C f - Polynomial.X * Polynomial.C g) = 0 := by
    have e1 : φ (Polynomial.C f) = algebraMap K L f := by simp [φ]
    have e2 : φ Polynomial.X = u * algebraMap K L f := by simp [φ]
    have e3 : φ (Polynomial.C g) = algebraMap K L g := by simp [φ]
    rw [map_sub, map_mul, e1, e2, e3]
    linear_combination (-(algebraMap K L f)) * hu
  have h1 : φ ((Polynomial.C a) ^ n) = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hc, map_mul, h0, mul_zero]
  have h2 : algebraMap K L (a ^ n) = 0 := by
    have e : φ ((Polynomial.C a) ^ n) = algebraMap K L (a ^ n) := by simp [φ]
    rw [← e, h1]
  obtain ⟨⟨m, hm⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) L _).1 h2
  obtain ⟨M, rfl⟩ := hm
  have e' : g ^ M * a ^ n = 0 := e
  apply hred _ (M + n)
  calc (g * a) ^ (M + n) = g ^ n * a ^ M * (g ^ M * a ^ n) := by ring
    _ = 0 := by rw [e', mul_zero]

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁]
    (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂)
    (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} →
    PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) →
    PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) →
    ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := by
  intro p _ K _ K₁ _ K₂ _ f g i₁ i₂ r N hK hr hN h₁ h₂ a ha₁ ha₂
  obtain ⟨-, hred, -, -, hroots⟩ := pf_facts p K hK
  obtain ⟨k₁, hk₁⟩ := (h₁.ker _).1 ha₁
  obtain ⟨k₂, hk₂⟩ := (h₂.ker _).1 ha₂
  have hg : g * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred f g a _ hk₁
  have hf : f * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred g f a _ hk₂
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hN
  have h0 : r 0 ^ N * a = 0 := by
    rw [← huv]
    linear_combination u * hf + v * hg
  exact (hroots r hr).2.2 N a h0

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenCharacterAnnihilator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenCharacterAnnihilator
open Matrix Topology

namespace GlobalTheory.CompanionTheory.AnnihOpen

theorem isOpen_annihilator_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)),
      IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ n A hA
  let H : AddSubgroup (Fin n → k) :=
    { carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
      zero_mem' := by
        intro a _
        simp
      add_mem' := by
        intro x y hx hy a ha
        rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
      neg_mem' := by
        intro x hx a ha
        rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one] }
  have hdot : Continuous fun p : (Fin n → k) × (Fin n → k) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_iff_le_induced.mpr fun U a ↦ a
  have hcont : Continuous fun p : (Fin n → k) × (Fin n → k) =>
      ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ :=
    ((hcoe.comp (hψ.comp hdot)).sub continuous_const).norm
  have hU : IsOpen {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} :=
    isOpen_lt hcont continuous_const
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    simp
  obtain ⟨V, W, hV, -, h0V, hAW, hVW⟩ := generalized_tube_lemma isCompact_singleton hA hU hsub
  have hmem : (H : Set (Fin n → k)) ∈ 𝓝 (0 : Fin n → k) := by
    refine Filter.mem_of_superset (hV.mem_nhds (h0V rfl)) ?_
    intro ξ hξ a ha
    apply GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
    intro m
    have hma : m • a ∈ (A : Set (Fin n → k)) := SetLike.mem_coe.mpr (A.nsmul_mem ha m)
    have h1 := hVW (Set.mk_mem_prod hξ (hAW hma))
    rw [Set.mem_setOf_eq, dotProduct_smul, AddChar.map_nsmul_eq_pow, Circle.coe_pow] at h1
    exact h1
  exact AddSubgroup.isOpen_of_mem_nhds H hmem

end GlobalTheory.CompanionTheory.AnnihOpen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenCharacterAnnihilatorStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_character_annihilator : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | exact GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeftEqRTensor
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem prodLeft_eq_rTensor {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] (w : (B₁ × B₂) ⊗[A] K) :
    TensorProduct.prodLeft A A B₁ B₂ K w =
      ((LinearMap.fst A B₁ B₂).rTensor K w, (LinearMap.snd A B₁ B₂).rTensor K w) := by
  induction w with
  | tmul b k =>
    obtain ⟨b₁, b₂⟩ := b
    simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Prod.mk_add_mk]

theorem tensor_prod_ext {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] {w w' : (B₁ × B₂) ⊗[A] K}
    (h₁ : (LinearMap.fst A B₁ B₂).rTensor K w = (LinearMap.fst A B₁ B₂).rTensor K w')
    (h₂ : (LinearMap.snd A B₁ B₂).rTensor K w = (LinearMap.snd A B₁ B₂).rTensor K w') :
    w = w' := by
  apply (TensorProduct.prodLeft A A B₁ B₂ K).injective
  rw [prodLeft_eq_rTensor, prodLeft_eq_rTensor, h₁, h₂]

theorem mv_prod : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B₁ : Type) [CommRing B₁] [Algebra A B₁] (B₂ : Type) [CommRing B₂] [Algebra A B₂] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ₁ : B₁ →ₐ[A] D) (ρ₂ : B₂ →ₐ[A] D), IsRt p r → Pf p D → (∀ y, ∃ b₁ b₂, y = ρ₁ b₁ - ρ₂ b₂) → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B₁) ⊗ₜ[A] a) = 0 → ((1 : B₂) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ (w₁ : B₁ ⊗[A] K) (w₂ : B₂ ⊗[A] K), Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) w₁ = Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) w₂ → ∃ a : K, w₁ = (1 : B₁) ⊗ₜ[A] a ∧ w₂ = (1 : B₂) ⊗ₜ[A] a) → Cov p r (B₁ × B₂) := by
  intro p _ A _ B₁ _ _ B₂ _ _ D _ _ r ρ₁ ρ₂ hr hD hsurj hK
  let ρ : (B₁ × B₂) →ₗ[A] D :=
    ρ₁.toLinearMap ∘ₗ LinearMap.fst A B₁ B₂ - ρ₂.toLinearMap ∘ₗ LinearMap.snd A B₁ B₂
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨b₁, b₂, rfl⟩ := hsurj y
    exact ⟨(b₁, b₂), by simp [ρ]⟩
  have h1 : ρ 1 = 0 := by simp [ρ]
  refine mv_cov p A (B₁ × B₂) D r ρ hr hD hρ h1 ?_
  intro K _ _ hPK
  obtain ⟨hinj, hker⟩ := hK K hPK
  have hf : ∀ a : K, (LinearMap.fst A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₁) ⊗ₜ[A] a := by
    intro a; simp
  have hs : ∀ a : K, (LinearMap.snd A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₂) ⊗ₜ[A] a := by
    intro a; simp
  refine ⟨fun a ha => hinj a ?_ ?_, fun w hw => ?_⟩
  · rw [← hf, ha, map_zero]
  · rw [← hs, ha, map_zero]
  · have hcomm : ∀ t : (B₁ × B₂) ⊗[A] K, ρ.rTensor K t =
        Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) ((LinearMap.fst A B₁ B₂).rTensor K t) -
          Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) ((LinearMap.snd A B₁ B₂).rTensor K t) := by
      intro t
      induction t with
      | tmul b k => simp [ρ, TensorProduct.sub_tmul]
      | add x y hx hy =>
        simp only [map_add (f := _), hx, hy]
        abel
    have heq := hcomm w
    rw [hw, eq_comm, sub_eq_zero] at heq
    obtain ⟨a, ha₁, ha₂⟩ := hker _ _ heq
    exact ⟨a, tensor_prod_ext (by rw [ha₁, hf]) (by rw [ha₂, hs])⟩

end GlobalTheory.CompanionTheory.SnakeCov
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableModSquareLocalization
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompMod

theorem exists_eq_add_of_mem_span_quot {S : Type} [CommRing S] (ϖ x y : S)
    (h : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) x ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) y}) :
    ∃ c d : S, x = y * c + ϖ ^ 2 * d := by
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul] at hc'
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hc')
  exact ⟨c, d, by linear_combination hd⟩

theorem mem_span_or_mem_span {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (h0 : Val0 (S := S ⧸ Ideal.span {ϖ ^ 2}))
    (P : Ideal S) (hP : P.IsPrime) (f g : S ⧸ compI P) :
    f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨
      g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨ε, hε, h1, h2⟩ := h0 (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)
  obtain ⟨e, ⟨he, rfl⟩, -⟩ :=
    IdemLift.existsUnique_idempotent_lift ϖ 2 two_ne_zero ε hε
  rw [← map_mul] at h1
  have h2' : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 - e) * b) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) a} := by
    simpa [map_mul, map_sub, map_one] using h2
  obtain ⟨c, d, hcd⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h1
  obtain ⟨c', d', hcd'⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h2'
  have key : ∀ t : S, IsIdempotentElem t → t ∈ P →
      Ideal.Quotient.mk (compI P) t = 0 := fun t ht htP =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨ht, htP⟩)
  by_cases heP : e ∈ P
  · right
    have hz := key e he heP
    have hb := congrArg (Ideal.Quotient.mk (compI P)) hcd'
    simp only [map_mul, map_add (f := _), map_sub, map_one, map_pow, hz, sub_zero, one_mul] at hb
    rw [hb]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c', Ideal.Quotient.mk _ d', by ring⟩
  · left
    have hmul : e * (1 - e) ∈ P := by
      have : e * (1 - e) = 0 := by
        have he' : e * e = e := he
        linear_combination -he'
      rw [this]
      exact P.zero_mem
    have h1e : 1 - e ∈ P := (hP.mem_or_mem hmul).resolve_left heP
    have hz := key (1 - e) he.one_sub h1e
    have hz' : Ideal.Quotient.mk (compI P) e = 1 := by
      rw [map_sub, map_one] at hz
      exact (sub_eq_zero.1 hz).symm
    have ha := congrArg (Ideal.Quotient.mk (compI P)) hcd
    simp only [map_mul, map_add (f := _), map_pow, hz', one_mul] at ha
    rw [ha]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c, Ideal.Quotient.mk _ d, by ring⟩

end GlobalTheory.CompanionTheory.CompMod
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecNormOfVecClose
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem ker_zero (X : Ctx) (x y : X.G) : ker X.Γ (0 : X.G → ℂ) x y = 0 := by
  simp [ker]

theorem isVec_zero (X : Ctx) {ι : Type} [Fintype ι] (y : X.G) (j : ι) :
    X.IsVec (0 : Matrix ι ι (X.G → ℂ)) y j (0 : X.Hs ι) := by
  intro l
  have h : (((0 : X.Hs ι) l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν] 0 := Lp.coeFn_zero ℂ 2 X.ν
  refine h.trans (Filter.Eventually.of_forall fun z => ?_)
  exact (ker_zero X z y).symm

theorem tst_zero (X : Ctx) : Tst (0 : X.G → ℂ) :=
  ⟨continuous_const, HasCompactSupport.zero⟩

theorem exists_bound (X : Ctx) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ))
    (hΦ : ∀ i j, Tst (Φ i j)) : ∃ ε : ℝ, ∀ l j z, ‖Φ l j z‖ ≤ ε := by
  have h : ∀ i j, ∃ B : ℝ, ∀ z, ‖Φ i j z‖ ≤ B := fun i j => by
    obtain ⟨B, hB⟩ := ((hΦ i j).1.norm).bddAbove_range_of_hasCompactSupport (hΦ i j).2.norm
    exact ⟨B, fun z => hB ⟨z, rfl⟩⟩
  choose B hB using h
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => (norm_nonneg _).trans (hB i j 1)
  refine ⟨∑ i, ∑ j, B i j, fun l j z => (hB l j z).trans ?_⟩
  calc B l j ≤ ∑ j, B l j :=
        Finset.single_le_sum (f := fun j => B l j) (fun j _ => hB0 l j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, B i j :=
        Finset.single_le_sum (f := fun i => ∑ j, B i j)
          (fun i _ => Finset.sum_nonneg fun j _ => hB0 i j) (Finset.mem_univ l)

theorem vecNorm_of_vecClose : VecClose → VecNorm := by
  intro hV X ι _ Φ hΦ
  obtain ⟨ε, hε⟩ := exists_bound X Φ hΦ
  set Ω₀ : Set X.G := ⋃ i, ⋃ j, tsupport (Φ i j) with hΩ₀
  have hc : IsCompact Ω₀ := isCompact_iUnion fun i => isCompact_iUnion fun j => (hΦ i j).2
  have hci : IsCompact Ω₀⁻¹ := hc.inv
  refine ⟨(Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal ε ^ 2 * X.μ Ω₀⁻¹), Ω₀⁻¹ * Ω₀, ?_,
    hci.mul hc, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hci.measure_lt_top.ne)
  · intro y j k hk
    have h := hV X ι Φ 0 Ω₀ ε y j k 0 hc (fun l => ⟨hΦ l j, tst_zero X, ?_, ?_, ?_⟩) hk
      (isVec_zero X y j)
    · simpa [mul_assoc] using h
    · exact (subset_tsupport _).trans
        (Set.subset_iUnion_of_subset l (Set.subset_iUnion_of_subset j subset_rfl))
    · simp
    · intro z
      simpa using hε l j z

end GlobalTheory.CompanionTheory.KernelColumns

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WpPf
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)),
    IsWP ι → Pf p A → Pf p B → Pf p K := by
  intro p _ A _ B _ _ K _ _ n ι hW hA hB
  obtain ⟨⟨FA, hFA⟩, -⟩ := pf_facts p A hA
  obtain ⟨⟨FB, hFB⟩, -⟩ := pf_facts p B hB
  have hchar : (p : K) = 0 := by
    have := congrArg (algebraMap A K) hA.char
    simpa using this
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K hchar 1
  have hF' : ∀ x, F x = x ^ p := fun x => by rw [hF, pow_one]
  have hcompat : ∀ i, (((ι i : B →+* K)).comp (FB.symm : B →+* B)).comp (algebraMap A B) =
      (algebraMap A K).comp (FA.symm : A →+* A) := by
    intro i
    ext a
    obtain ⟨b, rfl⟩ := FA.surjective a
    have h1 : algebraMap A B (FA b) = FB (algebraMap A B b) := by
      rw [hFA, hFB, map_pow]
    simp [h1]
  obtain ⟨z, hz1, hz2⟩ := hW.ex K ((algebraMap A K).comp (FA.symm : A →+* A))
    (fun i => ((ι i : B →+* K)).comp (FB.symm : B →+* B)) hcompat
  have hz1' : ∀ a, z (algebraMap A K a) = algebraMap A K (FA.symm a) := fun a => by
    simpa using congrArg (fun f : A →+* K => f a) hz1
  have hz2' : ∀ i b, z (ι i b) = ι i (FB.symm b) := fun i b => by
    simpa using congrArg (fun f : B →+* K => f b) (hz2 i)
  have hFa : ∀ a, F (algebraMap A K a) = algebraMap A K (FA a) := fun a => by
    rw [hF', hFA, map_pow]
  have hFb : ∀ i b, F (ι i b) = ι i (FB b) := fun i b => by
    rw [hF', hFB, map_pow]
  have hFz : F.comp z = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  have hzF : z.comp F = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  refine ⟨hchar, ?_, ?_⟩
  · intro x y hxy
    have h : F x = F y := by rw [hF', hF']; exact hxy
    have := congrArg z h
    have hx : ∀ w, z (F w) = w := fun w => by
      simpa using congrArg (fun f : K →+* K => f w) hzF
    rwa [hx, hx] at this
  · intro y
    refine ⟨z y, ?_⟩
    have : F (z y) = y := by simpa using congrArg (fun f : K →+* K => f y) hFz
    simpa [hF'] using this

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSecondProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSecondProperty
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.Tf.Loc

theorem isUnitIntegral_of_conj_mem_unitGL {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (γ g : GL (Fin n) F) (h : g⁻¹ * γ * g ∈ unitGL (n := Fin n) F) : IsUnitIntegral γ := by
  obtain ⟨u, hu⟩ := h
  have hcp : (γ : Matrix (Fin n) (Fin n) F).charpoly =
      ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly).map (intO F).subtype := by
    have h1 : ((g⁻¹ * γ * g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).charpoly =
        (γ : Matrix (Fin n) (Fin n) F).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    rw [← h1, ← hu, ← Matrix.charpoly_map]
    rfl
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact SetLike.coe_mem _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (u : Matrix (Fin n) (Fin n) (intO F)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    have hc : IsUnit ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly.coeff 0) := by
      rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    exact hint.isUnit_iff_valuation_eq_one.1 hc

theorem normGL_mem_unitGL {k E : Type} [Field k] [Field E] [ValuativeRel E] [Algebra k E] {n : ℕ}
    (σ : E ≃ₐ[k] E)
    (hστ : ∀ (τ : E ≃ₐ[k] E) (g : GL (Fin n) E),
      sigmaGL τ g ∈ unitGL (n := Fin n) E ↔ g ∈ unitGL (n := Fin n) E)
    {u : GL (Fin n) E} (hu : u ∈ unitGL (n := Fin n) E) :
    normGL σ u ∈ unitGL (n := Fin n) E := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [← sigmaGL_pow]
  exact (hστ _ _).2 hu

theorem stableLattice_unitIntegral : D0a → L2 := by
  intro hD
  refine ⟨?_, ?_⟩
  · rintro F _ _ _ _ n γ ⟨g, hg⟩
    exact isUnitIntegral_of_conj_mem_unitGL γ g hg
  · intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n δ g hmem
    have hστ := (hD k E hun σ hgen).2.2.2.1
    have hℓ : σ ^ Module.finrank k E = 1 := by
      rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
    have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
      rw [← sigmaGL_pow, hℓ, sigmaGL_one]
    have h := normGL_mem_unitGL σ (hστ · n ·) hmem
    rw [normGL, twNorm_twConj_of_pow_eq_one _ hθ] at h
    exact h

end GlobalTheory.CompanionTheory.Tf.Loc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSecondPropertyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_second_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.L2 := by
  first | exact @GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral | exact GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral | (intros; apply GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMemRangeLTensorOfLTensorEqZero
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_mem_range_lTensor_of_lTensor_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R)
      (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀]
      (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂]
      (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂)
      (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) →
      (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) →
      (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) →
      (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) →
      ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := by
  intro p _ R _ _ _ r N _ _ K₀ _ _ K₁ _ _ K₂ _ _ K₃ _ _ d₀ d₁ d₂ hr hdd h1 h2 h3 w hw k
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : ∀ k, r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    intro k
    rw [← pow_two, ← pow_add, Nat.sub_add_cancel hp]
    exact (hr k).symm
  have hsat : ∀ (a : R) (x : K₂), a ≠ 0 → a • x ∈ LinearMap.range d₁ →
      ∀ k, r k • x ∈ LinearMap.range d₁ := by
    rintro a x ha ⟨y, hy⟩ k
    have hax : a • d₂ x = 0 := by
      rw [← map_smul, ← hy, hdd]
    have h0 : d₂ (r (k + 1) • x) = 0 := by
      rw [map_smul]
      exact h3 a _ ha hax (k + 1)
    have h4 := h2 _ h0 (k + 1)
    rw [hrk k, mul_smul, mul_smul]
    exact Submodule.smul_mem _ _ h4
  have hsub : (LinearMap.range d₁).subtype ∘ₗ d₁.rangeRestrict = d₁ := by
    ext x
    rfl
  have hw' : (LinearMap.range d₁).subtype.lTensor N (d₁.rangeRestrict.lTensor N w) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsub]
    exact hw
  have h5 := smul_eq_zero_of_lTensor_subtype_eq_zero R r N K₂ (LinearMap.range d₁) hsat _ hw' (k + 1)
  have h6 : d₁.rangeRestrict.lTensor N (r (k + 1) • w) = 0 := by
    rw [map_smul]
    exact h5
  have hex : Function.Exact (LinearMap.ker d₁).subtype d₁.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hx' : d₁ x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Subtype.ext z.2
  obtain ⟨u, hu⟩ := (lTensor_exact N hex d₁.surjective_rangeRestrict _).1 h6
  have h7 : ∀ u : N ⊗[R] LinearMap.ker d₁,
      r (k + 1) • (LinearMap.ker d₁).subtype.lTensor N u ∈ LinearMap.range (d₀.lTensor N) := by
    intro u
    induction u with
    | tmul n z =>
      obtain ⟨y, hy⟩ := h1 z z.2 (k + 1)
      exact ⟨n ⊗ₜ y, by simp [hy, TensorProduct.tmul_smul]⟩
    | add a b ha hb =>
      rw [map_add (f := _), smul_add]
      exact Submodule.add_mem _ ha hb
  rw [hrk k, mul_smul, mul_smul, ← hu]
  exact Submodule.smul_mem _ _ (h7 u)

end GlobalTheory.CompanionTheory.Dblock
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecLimOf
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem exists_delta (c : ℝ≥0∞) (hc : c ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ^ 2 * c ≤ ENNReal.ofReal ε ^ 2 := by
  have hpos : 0 < Real.sqrt (c.toReal + 1) := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε / Real.sqrt (c.toReal + 1), div_pos hε hpos, ?_⟩
  have hδ : 0 ≤ ε / Real.sqrt (c.toReal + 1) := (div_pos hε hpos).le
  rw [← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_pow hε.le]
  have hct : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
  calc ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * c
      = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * ENNReal.ofReal c.toReal := by
        rw [← hct]
    _ = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2 * c.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (ε ^ 2) := ?_
  apply ENNReal.ofReal_le_ofReal
  have hsq : Real.sqrt (c.toReal + 1) ^ 2 = c.toReal + 1 := Real.sq_sqrt (by positivity)
  rw [div_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : 0 ≤ ε ^ 2 := by positivity
  nlinarith

theorem vecLim_of (hCnt : CntBasic) (hCv : CvTest) (hCol : ColOp) (hA : ApproxU) (hVC : VecClose) :
    VecLim := by
  intro X ι _ Φ T y j k ε hΦ hT hk hε
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  set Ω₀ : Set X.G := ⋃ l, tsupport (Φ l j) with hΩ₀
  have hΩ₀c : IsCompact Ω₀ := isCompact_iUnion fun l => (hΦ l j).2.isCompact
  set Ω : Set X.G := Ω₀ * N with hΩ
  have hΩc : IsCompact Ω := hΩ₀c.mul hNc
  set c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y) with hc
  have hctop : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ ?_)
    · exact hΩc.inv.measure_lt_top.ne
    · exact (hCnt X).1 _ (hΩc.inv.mul hΩc) y
  obtain ⟨δ, hδ, hδc⟩ := exists_delta c hctop ε hε
  choose Wl hWl hWlP using fun l => hA X (Φ l j) δ (hΦ l j) hδ
  refine ⟨N ∩ ⋂ l, Wl l, Filter.inter_mem hN1 (Filter.iInter_mem.2 hWl), ?_⟩
  intro ψ hψ hsupp u hu
  have hsN : tsupport ψ ⊆ N := hsupp.trans Set.inter_subset_left
  have hsl : ∀ l, tsupport ψ ⊆ Wl l := fun l =>
    hsupp.trans (Set.inter_subset_right.trans (Set.iInter_subset _ l))
  have hvec : X.IsVec (fun l j => cv X.μ (Φ l j) ψ) y j (T u) := fun l =>
    (((hCol X ι ψ hψ.1).2 Φ T hΦ hT y j u hu).1 l)
  have hfin := hVC X ι (fun l j => cv X.μ (Φ l j) ψ) Φ Ω δ y j (T u) k hΩc (fun l => by
    have hcv := hCv X (Φ l j) ψ (hΦ l j) hψ.1
    refine ⟨hcv.1, hΦ l j, ?_, ?_, fun z => ((hWlP l ψ hψ (hsl l) z).1)⟩
    · exact hcv.2.1.trans (Set.mul_subset_mul (Set.subset_iUnion (fun l => tsupport (Φ l j)) l) hsN)
    · intro z hz
      exact ⟨z, Set.subset_iUnion (fun l => tsupport (Φ l j)) l (subset_tsupport _ hz), 1, h1N, mul_one z⟩)
    hvec hk
  have hle : ‖T u - k‖ₑ ^ 2 ≤ ENNReal.ofReal ε ^ 2 := by
    refine hfin.trans (le_trans (le_of_eq ?_) hδc)
    rw [hc]; ring
  have hle' : ‖T u - k‖ₑ ≤ ENNReal.ofReal ε := (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hε.le] at hle'
  exact hle'

end GlobalTheory.CompanionTheory.KernelColumns

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecCloseOfKerBasicColSq
open PositivityTheory.Rg.BcB.E1

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem ker_sub_of_kerBasic (hK : KerBasic) (X : Ctx) {φ φ' : X.G → ℂ} (h : Tst φ) (h' : Tst φ')
    (x y : X.G) :
    ker X.Γ (fun z => φ z - φ' z) x y = ker X.Γ φ x y - ker X.Γ φ' x y := by
  unfold ker
  exact finsum_sub_distrib ((hK X φ h).1 x y) ((hK X φ' h').1 x y)

theorem enorm_sq_Lp_two {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : Lp ℂ 2 ν) :
    ‖f‖ₑ ^ 2 = ∫⁻ z, ‖(f : α → ℂ) z‖ₑ ^ 2 ∂ν := by
  rw [Lp.eNorm_def]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (f : α → ℂ)) (μ := ν) (p := 2)
    (by norm_num) (Lp.aestronglyMeasurable f)
  simpa using h

theorem enorm_sq_piLp_two {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : PiLp 2 E) :
    ‖f‖ₑ ^ 2 = ∑ l, ‖f l‖ₑ ^ 2 := by
  have h : ‖f‖₊ ^ 2 = ∑ l, ‖f l‖₊ ^ 2 := by
    apply NNReal.coe_injective
    push_cast
    simpa using PiLp.norm_sq_eq_of_L2 E f
  simp only [eNorm_eq_nnNorm]
  exact_mod_cast congrArg (fun t : NNReal => (t : ℝ≥0∞)) h

theorem vecClose_of_kerBasic_colSq : KerBasic → ColSq → VecClose := by
  intro hK hC X ι _ Φ Φ' Ω ε y j k k' hΩ hΦ hk hk'
  set R : ℝ≥0∞ := ENNReal.ofReal ε ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y with hR
  have key : ∀ l, ‖(k - k') l‖ₑ ^ 2 ≤ R := by
    intro l
    obtain ⟨t, t', s, s', hd⟩ := hΦ l
    have hT : Tst (fun z => Φ l j z - Φ' l j z) :=
      ⟨t.1.sub t'.1, t.2.sub t'.2⟩
    have hS : Function.support (fun z => Φ l j z - Φ' l j z) ⊆ Ω := by
      intro z hz
      by_contra hn
      have h1 : Φ l j z = 0 := by
        by_contra h0
        exact hn (s h0)
      have h2 : Φ' l j z = 0 := by
        by_contra h0
        exact hn (s' h0)
      exact hz (by simp [h1, h2])
    have hcol := hC X (fun z => Φ l j z - Φ' l j z) ε Ω hT hd hΩ hS y
    have hae : ((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν]
        fun z => ker X.Γ (fun w => Φ l j w - Φ' l j w) z y := by
      filter_upwards [Lp.coeFn_sub (k l) (k' l), hk l, hk' l] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ker_sub_of_kerBasic hK X t t']
    have hsub : (k - k') l = k l - k' l := rfl
    rw [hsub, enorm_sq_Lp_two]
    calc ∫⁻ z, ‖((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) z‖ₑ ^ 2 ∂X.ν
        = ∫⁻ z, ‖ker X.Γ (fun w => Φ l j w - Φ' l j w) z y‖ₑ ^ 2 ∂X.ν :=
          lintegral_congr_ae (hae.mono fun z hz => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) hz)
      _ ≤ R := hcol
  rw [enorm_sq_piLp_two]
  calc ∑ l, ‖(k - k') l‖ₑ ^ 2 ≤ ∑ _l : ι, R := Finset.sum_le_sum fun l _ => key l
    _ = Fintype.card ι * R := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.KernelColumns

end
end

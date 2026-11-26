module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHasSumEqIntegralIndicatorHasSumStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.EllTrace
open GlobalTheory.TruncKer

theorem countable_GF {D : D7} (V : HSp D) : Countable (GF V) := by
  haveI : Countable D.host.E :=
    (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    (show Countable (Fin V.rank → Fin V.rank → D.host.E) from inferInstance)
  haveI : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  infer_instance

theorem kernel_diag_hasSum {D : D7} (V : HSp D) {f : GA D V → ℂ} (hf : f ∈ CcGA V) (x : GA D V) :
    (Function.support fun δ : GF V => f (x⁻¹ * rat V δ * x)).Finite ∧
    HasSum (fun δ : GF V => f (x⁻¹ * rat V δ * x)) (GlobalTheory.AutomorphicL2Unitary.kernel (GQ V) f x x) := by
  have hcs := continuous_of_mem_ccAd hf
  have hr : (ratEmb D.sp.cm.sig V.gram).range = GQ V := by rw [range_ratEmb]; rfl
  let e : GF V ≃* GQ V :=
    (MonoidHom.ofInjective (ratEmb_injective D.sp.cm.sig V.gram)).trans (MulEquiv.subgroupCongr hr)
  have he : ∀ δ : GF V, ((e δ : GQ V) : GA D V) = rat V δ := fun δ => rfl
  refine ⟨?_, ?_⟩
  · have hC : IsCompact ((fun g : GA D V => x * g * x⁻¹) '' tsupport f) :=
      hcs.2.isCompact.image (by fun_prop)
    have hfin := finite_mem_compact (Γ := GQ V) hC
    refine (hfin.preimage e.injective.injOn).subset fun δ hδ => ?_
    refine ⟨x⁻¹ * rat V δ * x, subset_tsupport _ hδ, ?_⟩
    simp only [he]
    group
  · have := hasSum_kernel (Γ := GQ V) hcs.2 x x
    exact (e.toEquiv.hasSum_iff (f := fun γ : GQ V => f (x⁻¹ * (γ : GA D V) * x))).2 this

theorem charpoly_eq_of_isConj {D : D7} {V : HSp D} {a b : GF V} (h : IsConj a b) :
    a.1.1.charpoly = b.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  change a.1.1.charpoly = ((c.1 : GL _ _) * a.1 * (c.1)⁻¹ : GL _ _).1.charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.CompanionTheory.EllTrace
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroup
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormClassNorm

theorem norm_mem_normGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k]
    [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r)
    (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k →
    Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  intro E _ _ _ k _ _ r Q x hx
  obtain ⟨z, hz⟩ : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hθ : IsCMField.complexConj E (z - IsCMField.complexConj E z) =
      -(z - IsCMField.complexConj E z) := by
    rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  obtain ⟨b, B, hB⟩ := GlobalTheory.TraceClasses.exists_bases Q (sub_ne_zero.2 hz.symm) hθ
  have h1 : Isometric Q k (GlobalTheory.TraceClasses.gramRat Q B 1)
      ((1 : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q) := by
    have := (GlobalTheory.TraceClasses.isometric_tmul_iff Q B k (GlobalTheory.TraceClasses.gramRat Q B 1) 1).2
      (GlobalTheory.HermLocal.CongrOver.of_congr ⟨1, by simp, by simp⟩)
    simpa [Algebra.TensorProduct.one_def] using this
  have h2 := Isometric.of_norm Q k hx h1
  rw [one_mul] at h2
  have h3 := GlobalTheory.TraceClasses.norm_div_mem Q hB k (δ := 1) (by simp) h2
  have h4 : GlobalTheory.QuadSymbol.toUnits (maximalRealSubfield E) k 1 = 1 := map_one _
  rwa [h4, div_one] at h3

end GlobalTheory.CompanionTheory.NormClassNorm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroupStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_mem_norm_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  first | exact @GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | exact GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | (intros; apply GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialIn
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialIn
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.FormRatio

theorem exists_eq_mul_aeval (K : Type) [Field K] (σ : K →+* K) (n : ℕ)
    (A H₀ H : Matrix (Fin n) (Fin n) K) (_hA : IsUnit A.det) (hs : A.charpoly.Separable)
    (hH₀ : H₀.det ≠ 0) (e₀ : cT σ A * H₀ * A = H₀) (e : cT σ A * H * A = H) :
    ∃ m : K[X], H = H₀ * aeval A m := by
  have hH₀' : IsUnit H₀.det := isUnit_iff_ne_zero.mpr hH₀
  have hB : IsUnit (cT σ A).det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hH₀ ?_
    have h1 := congrArg Matrix.det e₀
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at h1
    exact h1.symm
  have k1 : H * A = (cT σ A)⁻¹ * H := by
    calc H * A = ((cT σ A)⁻¹ * cT σ A) * H * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H := by rw [e]
  have k0 : H₀ * A = (cT σ A)⁻¹ * H₀ := by
    calc H₀ * A = ((cT σ A)⁻¹ * cT σ A) * H₀ * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H₀ * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H₀ := by rw [e₀]
  have k2 : A * H₀⁻¹ = H₀⁻¹ * (cT σ A)⁻¹ := by
    calc A * H₀⁻¹ = H₀⁻¹ * (H₀ * A) * H₀⁻¹ := by
          rw [← mul_assoc H₀⁻¹ H₀ A, Matrix.nonsing_inv_mul _ hH₀', one_mul]
      _ = H₀⁻¹ * ((cT σ A)⁻¹ * H₀) * H₀⁻¹ := by rw [k0]
      _ = H₀⁻¹ * (cT σ A)⁻¹ * (H₀ * H₀⁻¹) := by simp only [mul_assoc]
      _ = H₀⁻¹ * (cT σ A)⁻¹ := by rw [Matrix.mul_nonsing_inv _ hH₀', mul_one]
  have hc : Commute A (H₀⁻¹ * H) := by
    show A * (H₀⁻¹ * H) = H₀⁻¹ * H * A
    calc A * (H₀⁻¹ * H) = A * H₀⁻¹ * H := (mul_assoc _ _ _).symm
      _ = H₀⁻¹ * (cT σ A)⁻¹ * H := by rw [k2]
      _ = H₀⁻¹ * (H * A) := by rw [k1, mul_assoc]
      _ = H₀⁻¹ * H * A := (mul_assoc _ _ _).symm
  obtain ⟨m, hm⟩ := ClsFin.exists_aeval_of_comm A (H₀⁻¹ * H) hs hc
  refine ⟨m, ?_⟩
  rw [← hm, ← mul_assoc, Matrix.mul_nonsing_inv _ hH₀', one_mul]

end GlobalTheory.CompanionTheory.FormRatio
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialInStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_polynomial_in : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := by
  first | exact @GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | exact GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | (intros; apply GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTransversalDoubleCoset
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTransversalDoubleCoset
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem dcos_compact_lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q P : Subgroup G} {x : G}
    (hL : LocSec Q P x) (hP : IsClosed (P : Set G)) (B₀ : Set G) (hB : IsCompact B₀) (hB₁ : B₀ ∈ 𝓝 (1 : G))
    (D : Set G) (hD : IsCompact D) (hDc : D ⊆ dcos Q P x) :
    ∃ C : Set P, IsCompact C ∧ ∀ g ∈ D, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c := by
  obtain ⟨O, hO, hsec⟩ := hL Set.univ Filter.univ_mem B₀ hB₁
  have hemb : Topology.IsClosedEmbedding (Subtype.val : P → G) := hP.isClosedEmbedding_subtypeVal
  have hC₁ : IsCompact ((Subtype.val : P → G) ⁻¹' B₀) := hemb.isCompact_preimage hB
  refine hD.induction_on
    (p := fun T => ∃ C : Set P, IsCompact C ∧ ∀ g ∈ T, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c)
    ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨C, hC, h⟩
    exact ⟨C, hC, fun g hg => h g (hST hg)⟩
  · rintro S T ⟨C, hC, h⟩ ⟨C', hC', h'⟩
    refine ⟨C ∪ C', hC.union hC', ?_⟩
    rintro g (hg | hg)
    · obtain ⟨q, hq, c, hc, e⟩ := h g hg
      exact ⟨q, hq, c, Or.inl hc, e⟩
    · obtain ⟨q, hq, c, hc, e⟩ := h' g hg
      exact ⟨q, hq, c, Or.inr hc, e⟩
  · intro g₀ hg₀
    obtain ⟨q₀, hq₀, p₀, hp₀, e₀⟩ := hDc hg₀
    have hcont : Continuous fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹ := by fun_prop
    have hval : (q₀ * x)⁻¹ * g₀ * p₀⁻¹ = 1 := by
      rw [e₀]; group
    have hU : (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O ∈ 𝓝 g₀ :=
      hcont.continuousAt.preimage_mem_nhds (by rw [hval]; exact hO)
    refine ⟨D ∩ (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O,
      Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
      (fun c : P => c * (⟨p₀, hp₀⟩ : P)) '' ((Subtype.val : P → G) ⁻¹' B₀),
      hC₁.image (by fun_prop), ?_⟩
    rintro g ⟨hgD, hgU⟩
    obtain ⟨q', hq', p', hp', e'⟩ := hDc hgD
    have hxu : x * ((q₀ * x)⁻¹ * g * p₀⁻¹) ∈ dcos Q P x := by
      refine ⟨q₀⁻¹ * q', Q.mul_mem (Q.inv_mem hq₀) hq', p' * p₀⁻¹, P.mul_mem hp' (P.inv_mem hp₀), ?_⟩
      rw [e']; group
    obtain ⟨s, hs, -, p₂, hp₂, hp₂B, e₂⟩ := hsec _ hgU hxu
    refine ⟨q₀ * s, Q.mul_mem hq₀ hs, ⟨p₂, hp₂⟩ * ⟨p₀, hp₀⟩, ⟨⟨p₂, hp₂⟩, hp₂B, rfl⟩, ?_⟩
    have e₃ : g = q₀ * (x * ((q₀ * x)⁻¹ * g * p₀⁻¹)) * p₀ := by group
    rw [e₃, e₂]
    simp [mul_assoc]

end GlobalTheory.CompanionTheory.BZRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTransversalDoubleCosetStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_transversal_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q P : Subgroup G} {x : G}, LocSec Q P x → IsClosed (P : Set G) → ∀ (B₀ : Set G), IsCompact B₀ → B₀ ∈ 𝓝 (1 : G) → ∀ (D : Set G), IsCompact D → D ⊆ dcos Q P x → ∃ C : Set P, IsCompact C ∧ ∀ g ∈ D, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.dcos_compact_lift | exact GlobalTheory.CompanionTheory.BZRes.dcos_compact_lift | (intros; apply GlobalTheory.CompanionTheory.BZRes.dcos_compact_lift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfBlockValue
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfBlockValue
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

theorem ordL_pow_div_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (a b : ℕ) :
    ordL (x ^ b / y ^ a) = (b : ℤ) * ordL x - (a : ℤ) * ordL y := by
  have h : x ^ b / y ^ a =
      (((Units.mk0 x hx) ^ (b : ℤ) * (Units.mk0 y hy) ^ (-(a : ℤ)) : Lˣ) : L) := by
    simp [div_eq_mul_inv]
  rw [h, Units.val_mul, GlobalTheory.CompanionTheory.SwapInt.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
    GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow]
  simp only [Units.val_mk0]
  ring

theorem absHalf_blockDet_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (qV E w : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) := by
  intro E _ _ _ a b w i j m hi hj
  have h1 : m.1.val.det ≠ 0 := by
    have := m.1.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h2 : m.2.val.det ≠ 0 := by
    have := m.2.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hq : 0 < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have ho := ordL_pow_div_pow h1 h2 a b
  rw [hi, hj] at ho
  unfold absHalf
  rw [ho]
  have hs : Real.sqrt ((qV E w : ℝ) ^ (-((b : ℤ) * (i : ℤ) - (a : ℤ) * (j : ℤ)))) =
      (qV E w : ℝ) ^ (-((i : ℝ) * b - (j : ℝ) * a) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast
    ring
  rw [hs, Complex.ofReal_cpow hq.le, Complex.ofReal_natCast]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.CtS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfBlockValueStatement
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_half_block_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (qV E w : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.absHalf_blockDet_value | exact GlobalTheory.CompanionTheory.CtS.absHalf_blockDet_value | (intros; apply GlobalTheory.CompanionTheory.CtS.absHalf_blockDet_value <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullback
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def rightMulEquiv {m r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    Matrix (Fin m) (Fin r) D.host.E ≃ Matrix (Fin m) (Fin r) D.host.E where
  toFun ξ := ξ * a
  invFun ξ := ξ * a⁻¹
  left_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv a hu]
  right_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul a hu]

theorem invPt_mul (V : HSp D) {r : ℕ} (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    GlobalTheory.SiegelFormula.invPt V h (ξ * a) =
      HMul.hMul (GlobalTheory.SiegelFormula.invPt V h ξ) (a.map (incA D)) := by
  unfold GlobalTheory.SiegelFormula.invPt
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem absTheta_pull (V : HSp D) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) (h : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V (pull a φ) h = GlobalTheory.SiegelFormula.absTheta V φ h := by
  unfold GlobalTheory.SiegelFormula.absTheta
  rw [← (rightMulEquiv (m := V.rank) a ha).tsum_eq
    (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)]
  refine tsum_congr fun ξ => ?_
  show ‖φ _‖ₑ = ‖φ (GlobalTheory.SiegelFormula.invPt V h (ξ * a))‖ₑ
  rw [invPt_mul]

theorem absThetaInt_pull (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    GlobalTheory.SiegelFormula.absThetaInt V ν (pull a φ) = GlobalTheory.SiegelFormula.absThetaInt V ν φ := by
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have : GlobalTheory.SiegelFormula.absTheta V (pull a φ) = GlobalTheory.SiegelFormula.absTheta V φ :=
    funext (absTheta_pull V φ a ha)
  rw [this]

theorem hyp_pull : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  intro D r V ψ θ μ lam ν φ a ha ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hli : LinearIndependent D.host.E a :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det a).mpr (isUnit_iff_ne_zero.mpr ha))
  refine ⟨h1, h2, h3, h4, h5, h6, GlobalTheory.T.pullback_schwartz_linear_independent D θ h3 _ _ _ a hli φ h7, ?_⟩
  rw [absThetaInt_pull V ν φ a ha]
  exact h8

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullbackStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypotheses_preserved_by_linear_pullback : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetric
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetric
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem measurable_PintF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, ⟨κ, hκs, hκm⟩, -, -⟩ :=
    GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  haveI : IsSFiniteKernel κ := hκs
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  have hfin := Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner
  have hm'κ : m' = fun S => κ S := funext fun S => (hκm S).symm
  rw [hm'κ]
  exact hfin

end GlobalTheory.CompanionTheory.SW.StageF
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetricStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_symmetric : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | exact GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionFromCompactData
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionFromCompactData
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.TwoOrbit

theorem exists_equivariant_extension :
    ∀ {G : Type} [Group G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (φ : P → W₁) (C : Set P) (K : Subgroup G), (∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c)) → (∀ p : P, φ p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G)) → ∃ f : G → W₁, (∀ (q : Q) (g : G), f ((q : G) * g) = σ q (f g)) ∧ (∀ (g : G), ∀ κ ∈ K, f (g * κ) = f g) ∧ (∀ p : P, f (x * (p : G)) = φ p) ∧ ∀ g : G, f g ≠ 0 → ∃ q : Q, ∃ c ∈ C, ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ := by
  intro G _ W₁ _ _ Q P x σ φ C K h1 h2
  classical
  let Ω : G → Prop := fun g =>
    ∃ (q : Q) (c : P), c ∈ C ∧ ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ
  have wd : ∀ (q q' : Q) (c c' : P), c ∈ C → c' ∈ C → ∀ κ ∈ K, ∀ κ' ∈ K,
      (q : G) * x * (c : G) * κ = (q' : G) * x * (c' : G) * κ' →
        σ q (φ c) = σ q' (φ c') := by
    intro q q' c c' hc hc' κ hκ κ' hκ' e
    have e' : ((q'⁻¹ * q : Q) : G) * x * (c : G) * (κ * κ'⁻¹) = x * (c' : G) := by
      have e2 : (q : G) * x * (c : G) * κ * κ'⁻¹ = (q' : G) * x * (c' : G) := by
        rw [e]; group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc ((q' : G)⁻¹ * q) * x * c * (κ * κ'⁻¹)
          = (q' : G)⁻¹ * ((q : G) * x * (c : G) * κ * κ'⁻¹) := by group
        _ = x * (c' : G) := by rw [e2]; group
    have e3 := h1 c hc (κ * κ'⁻¹) (K.mul_mem hκ (K.inv_mem hκ')) (q'⁻¹ * q) c' e'
    rw [e3, ← Module.End.mul_apply, ← map_mul]
    simp
  let f : G → W₁ := fun g =>
    if h : Ω g then σ h.choose (φ h.choose_spec.choose) else 0
  have hf : ∀ (q : Q) (c : P), c ∈ C → ∀ κ ∈ K,
      f ((q : G) * x * (c : G) * κ) = σ q (φ c) := by
    intro q c hc κ hκ
    have h : Ω ((q : G) * x * (c : G) * κ) := ⟨q, c, hc, κ, hκ, rfl⟩
    simp only [f]
    rw [dite_eq_left h]
    obtain ⟨hc', κ', hκ', e⟩ := h.choose_spec.choose_spec
    exact wd _ _ _ _ hc' hc κ' hκ' κ hκ e.symm
  have h0 : ∀ g, ¬ Ω g → f g = 0 := fun g h => dif_neg h
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro q g
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ, hκ, rfl⟩ := h
      have e : (q : G) * ((q₁ : G) * x * (c : G) * κ)
          = ((q * q₁ : Q) : G) * x * (c : G) * κ := by
        simp only [Subgroup.coe_mul]; group
      rw [e, hf _ _ hc _ hκ, hf _ _ hc _ hκ, map_mul, Module.End.mul_apply]
    · have h' : ¬ Ω ((q : G) * g) := by
        rintro ⟨q₁, c, hc, κ, hκ, e⟩
        refine h ⟨q⁻¹ * q₁, c, hc, κ, hκ, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc g = (q : G)⁻¹ * ((q : G) * g) := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h', map_zero]
  · intro g κ hκ
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ₁, hκ₁, rfl⟩ := h
      have e : (q₁ : G) * x * (c : G) * κ₁ * κ = (q₁ : G) * x * (c : G) * (κ₁ * κ) := by group
      rw [e, hf _ _ hc _ (K.mul_mem hκ₁ hκ), hf _ _ hc _ hκ₁]
    · have h' : ¬ Ω (g * κ) := by
        rintro ⟨q₁, c, hc, κ₁, hκ₁, e⟩
        refine h ⟨q₁, c, hc, κ₁ * κ⁻¹, K.mul_mem hκ₁ (K.inv_mem hκ), ?_⟩
        calc g = (g * κ) * κ⁻¹ := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h']
  · intro p
    by_cases h : Ω (x * (p : G))
    · obtain ⟨q, c, hc, κ, hκ, e⟩ := h
      rw [e, hf _ _ hc _ hκ]
      exact (h1 c hc κ hκ q p e.symm).symm
    · rw [h0 _ h]
      by_contra hne
      obtain ⟨c, hc, q, e⟩ := h2 p (fun hz => hne hz.symm)
      exact h ⟨q, c, hc, 1, K.one_mem, by rw [e, mul_one]⟩
  · intro g hg
    by_contra hcon
    refine hg (h0 g ?_)
    rintro ⟨q, c, hc, κ, hκ, e⟩
    exact hcon ⟨q, c, hc, κ, hκ, e⟩

end GlobalTheory.CompanionTheory.BZRes.TwoOrbit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionFromCompactDataStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_function_from_compact_data : ∀ {G : Type} [Group G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (φ : P → W₁) (C : Set P) (K : Subgroup G), (∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c)) → (∀ p : P, φ p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G)) → ∃ f : G → W₁, (∀ (q : Q) (g : G), f ((q : G) * g) = σ q (f g)) ∧ (∀ (g : G), ∀ κ ∈ K, f (g * κ) = f g) ∧ (∀ p : P, f (x * (p : G)) = φ p) ∧ ∀ g : G, f g ≠ 0 → ∃ q : Q, ∃ c ∈ C, ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension | exact GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension | (intros; apply GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBound
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem orbFin_of_latBound : LatBound → OrbFin := by
  intro hL D θ hθ W m hm x₀ hx N hN
  obtain ⟨C, hC⟩ := hL D θ hθ W W.rank N hN
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨-, g2, g3, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hfd : IsFundamentalDomain (GQ W) (stdDom (GQ W)) m := isFundamentalDomain_stdDom _ m
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W m _ hm hfd
  have hcnt : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  have hNc : Continuous N :=
    (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank W.rank N
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank W.rank N hN)).1
  have hfm : Measurable fun h : GA D W => ‖N (ww W x₀ h)‖ₑ :=
    (hNc.comp (continuous_ww x₀)).enorm.measurable

  classical
  have hu : ∀ γ : GQ W, ∃ u : GL (Fin W.rank) D.host.E, mt W γ.1 = rat u.1 := fun γ => by
    obtain ⟨u, -, hu⟩ := γ.2
    exact ⟨u, (congrArg Units.val hu).symm⟩
  choose u hu using hu
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.2 hx
  have hrk : ∀ γ : GQ W, ((u γ).1 * x₀).rank = W.rank := fun γ => by
    have h1 : IsUnit ((u γ).1 * x₀) := by
      refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (u γ).isUnit).mul hxu
    simpa using Matrix.rank_of_isUnit _ h1
  let e : GQ W → {x : Matrix (Fin W.rank) (Fin W.rank) D.host.E // x.rank = W.rank} :=
    fun γ => ⟨(u γ).1 * x₀, hrk γ⟩
  have he : Function.Injective e := fun γ γ' h => by
    have h1 : (u γ).1 * x₀ = (u γ').1 * x₀ := congrArg Subtype.val h
    have h2 : (u γ).1 = (u γ').1 := by
      have hxi : x₀ * x₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
      calc (u γ).1 = (u γ).1 * x₀ * x₀⁻¹ := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
        _ = (u γ').1 * x₀ * x₀⁻¹ := by rw [h1]
        _ = (u γ').1 := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
    exact Subtype.ext (GlobalTheory.MixModel.mt_injective W (by rw [hu, hu, h2]))
  have hterm : ∀ (γ : GQ W) (h : GA D W), ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ = ‖N (mm (mt W h⁻¹) (rat (e γ).1))‖ₑ := fun γ h => by
    have h1 : (γ⁻¹ • h)⁻¹ = h⁻¹ * γ.1 := by
      change ((γ.1)⁻¹ * h)⁻¹ = _
      rw [mul_inv_rev, inv_inv]
    have h2 : mt W (h⁻¹ * γ.1) = mt W h⁻¹ * mt W γ.1 := rfl
    have h3 : ww W x₀ (γ⁻¹ • h) = mm (mt W h⁻¹) (rat (e γ).1) := by
      simp only [ww, e]
      rw [h1, h2, hu, rat_mul]
      exact Matrix.mul_assoc _ _ _
    rw [h3]
  rw [hfd.lintegral_eq_tsum']
  rw [← lintegral_tsum fun γ => ?_]
  · calc ∫⁻ h in stdDom (GQ W), ∑' γ : GQ W, ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ ∂m
        ≤ ∫⁻ _ in stdDom (GQ W), (C : ℝ≥0∞) ∂m := lintegral_mono fun h => by
          simp only [hterm]
          exact (ENNReal.tsum_comp_le_tsum_of_injective he
            (fun x => ‖N (mm (mt W h⁻¹) (rat x.1))‖ₑ)).trans (hC h)
      _ = C * m (stdDom (GQ W)) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin
  · exact (hfm.comp (measurable_const_smul γ⁻¹)).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_finiteness_of_lattice_bound : LatBound → OrbFin := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound | exact GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakeEigenvaluePairDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakeEigenvaluePairDecomposition
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.SatConv

theorem esymm_cons_succ' (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ']

theorem esymm_add_antidiagonal (s t : Multiset ℂ) (k : ℕ) :
    (s + t).esymm k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, s.esymm p.1 * t.esymm p.2 := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul]
  simp only [coeff_prod_one_add]

theorem esymm_map_mul_unit (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    ((B.map (· * z)).map fun b : ℂˣ => (b : ℂ)).esymm j =
      (z : ℂ) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [Multiset.map_map, Function.comp_def, Units.val_mul, mul_comm _ (z : ℂ)]
  exact h.symm

theorem esymm_eq_zero_of_card_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem satEig_join : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  intro q n a b c Ba Bb hq hab hBa hBb k _
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  subst hab
  rw [pairs, Finset.sum_filter]
  simp only [satEig]
  rw [Multiset.map_add (f := _), esymm_add_antidiagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hp
  have hk : i + j = k := by simpa using hp
  subst hk
  simp only [esymm_map_mul_unit]
  split_ifs with h
  · have hpow : (q : ℂ) ^ ((((i + j : ℕ) : ℂ) * (((a + b : ℕ) : ℂ) - ((i + j : ℕ) : ℂ))) / 2) =
        (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j) *
          ((q : ℂ) ^ (((i : ℂ) * ((a : ℂ) - i)) / 2) * (q : ℂ) ^ (((j : ℂ) * ((b : ℂ) - j)) / 2)) := by
      rw [← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq']
      congr 1
      push_cast
      ring
    rw [hpow, coef]
    simp only [Units.val_pow_eq_pow_val]
    rw [pow_add, pow_mul, pow_mul, pow_right_comm (c : ℂ) i b, pow_right_comm (c : ℂ) j a]
    ring
  · have hz : (Ba.map fun x : ℂˣ => (x : ℂ)).esymm i = 0 ∨ (Bb.map fun x : ℂˣ => (x : ℂ)).esymm j = 0 := by
      by_cases hi : i ≤ a
      · right
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBb]
        by_contra hj
        exact h ⟨hi, by omega⟩
      · left
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBa]
        omega
    rcases hz with hz | hz <;> simp [hz]

end GlobalTheory.CompanionTheory.CtS.SatConv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakeEigenvaluePairDecompositionStatement
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_eigenvalue_pair_decomposition : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join | exact GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join | (intros; apply GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainder
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainder
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.EllCRT

private theorem monic_of_mem_normalizedFactors' {K : Type} [Field K] {P q : K[X]}
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) : q.Monic := by
  have hq0 : q ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq).ne_zero
  rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize hq0

private theorem span_sup_span_eq_unit_ideal_of_ne_normalizedFactors {K : Type} [Field K] {P p q : K[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors P)
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) (hpq : p ≠ q) :
    Ideal.span {p} ⊔ Ideal.span {q} = ⊤ := by
  have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hqi : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
  have hcop : IsCoprime p q := by
    rw [Irreducible.coprime_iff_not_dvd hpi]
    intro hd
    exact hpq (Polynomial.eq_of_monic_of_associated (monic_of_mem_normalizedFactors' hp)
      (monic_of_mem_normalizedFactors' hq) (hpi.associated_of_dvd hqi hd))
  exact (Ideal.sup_eq_top_iff_isCoprime p q).mpr hcop

theorem exists_congr_monic_factors {K : Type} [Field K] {P : K[X]} (hP : P ≠ 0) (t : K[X] → K[X]) :
    ∃ m : K[X], ∀ f : K[X], f.Monic → Irreducible f → f ∣ P → f ∣ m - t f := by
  classical
  let S : Finset K[X] := (UniqueFactorizationMonoid.normalizedFactors P).toFinset
  have hcop : Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {(i : K[X])})) := by
    intro i j hij
    show IsCoprime (Ideal.span {(i : K[X])}) (Ideal.span {(j : K[X])})
    exact Ideal.isCoprime_iff_sup_eq.mpr (span_sup_span_eq_unit_ideal_of_ne_normalizedFactors (Multiset.mem_toFinset.mp i.2)
      (Multiset.mem_toFinset.mp j.2) (fun h => hij (Subtype.ext h)))
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun i : S => t i)
  refine ⟨r, fun f hfm hfi hfP => ?_⟩
  obtain ⟨q, hq, hfq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hP hfi hfP
  have hfeq : f = q := Polynomial.eq_of_monic_of_associated hfm (monic_of_mem_normalizedFactors' hq) hfq
  subst hfeq
  have h := hr ⟨f, Multiset.mem_toFinset.mpr hq⟩
  exact Ideal.mem_span_singleton.mp h

private theorem adjoinRoot_exists_mk_eq {R : Type} [CommRing R] {f : R[X]} (x : AdjoinRoot f) :
    ∃ p : R[X], AdjoinRoot.mk f p = x :=
  AdjoinRoot.mk_surjective x

private theorem adjoinRoot_mk_eq_of_selfRecip_val_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) {r r' : ℕ} (Q : SelfRecip E r)
    (Q' : SelfRecip E r') (hQ : Q'.1 = Q.1) (l : E[X])
    (hl : (AdjoinRoot.mk Q'.1 l : Fld Q') = g r' Q') :
    (AdjoinRoot.mk Q.1 l : Fld Q) = g r Q := by
  have h1 : Q'.1.natDegree = r' := Q'.2.2.2.1
  have h2 : Q.1.natDegree = r := Q.2.2.2.1
  rw [hQ] at h1
  have hrr : r' = r := h1.symm.trans h2
  subst hrr
  obtain rfl : Q' = Q := Subtype.ext hQ
  exact hl

private theorem exists_polynomial_lift_adjoinRoot_selfRecip {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) :
    ∃ t : E[X] → E[X], ∀ (r : ℕ) (Q : SelfRecip E r),
      (AdjoinRoot.mk Q.1 (t Q.1) : Fld Q) = g r Q := by
  classical
  refine ⟨fun f => if h : ∃ Q' : SelfRecip E f.natDegree, Q'.1 = f then
      (adjoinRoot_exists_mk_eq (f := h.choose.1) (g f.natDegree h.choose)).choose else 0, ?_⟩
  intro r Q
  have hex : ∃ Q' : SelfRecip E Q.1.natDegree, Q'.1 = Q.1 :=
    ⟨⟨Q.1, by rw [Q.2.2.2.1]; exact Q.2⟩, rfl⟩
  dsimp only
  rw [dite_eq_left hex]
  exact adjoinRoot_mk_eq_of_selfRecip_val_eq g Q hex.choose hex.choose_spec _
    (adjoinRoot_exists_mk_eq (f := hex.choose.1) (g Q.1.natDegree hex.choose)).choose_spec

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E),
    γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X],
      ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
        (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  intro E _ _ _ n γ₀ _ g
  obtain ⟨t, ht⟩ := exists_polynomial_lift_adjoinRoot_selfRecip g
  obtain ⟨m, hm⟩ := exists_congr_monic_factors (Matrix.charpoly_monic γ₀.val).ne_zero t
  refine ⟨m, fun r Q hQ => ?_⟩
  rw [← ht r Q]
  exact AdjoinRoot.mk_eq_mk.mpr (hm Q.1 Q.2.1 Q.2.2.1 hQ)

end GlobalTheory.CompanionTheory.EllCRT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainderStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_chinese_remainder : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  first | exact @GlobalTheory.CompanionTheory.EllCRT.main | exact GlobalTheory.CompanionTheory.EllCRT.main | (intros; apply GlobalTheory.CompanionTheory.EllCRT.main <;> assumption)
end
end

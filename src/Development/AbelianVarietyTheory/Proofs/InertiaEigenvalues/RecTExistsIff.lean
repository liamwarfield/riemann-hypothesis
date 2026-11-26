module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProduct
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

section Laws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lawsT_iff (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : LawsT a ha rc ↔ UpperTheory.Zero.LLC.LawsT a ha rc :=
  ⟨fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩,
   fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩⟩

end Laws

end GlobalTheory.RecT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralTwistStable
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.RecT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GoodCusp.tw {y : IrrGL (k := k)} (hy : GoodCusp y) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GoodCusp (y.tw χ hχ) := by
  rcases hy with h1 | ⟨hf, y₀, χ₀, hχ₀, hfix, rfl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hf, y₀, χ₀ * χ, hχ₀.mul hχ, hfix, IrrGL.tw_tw _ _ _ _ _⟩

theorem Good.tw {x : IrrGL (k := k)} (hx : Good x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) := by
  obtain ⟨s, hs, hg⟩ := hx
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
  exact (hg y' hy').tw χ hχ

theorem good_tw_iff (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) ↔ Good x :=
  ⟨fun h => by simpa only [IrrGL.tw_tw_inv] using h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩

theorem good_nu_iff (x : IrrGL (k := k)) (s : ℂ) : Good (x.nu s) ↔ Good x := good_tw_iff x _ _

end GlobalTheory.RecT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isUnramChar_of_isCusp_of_isSpherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (x : IrrGL (k := k)), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  intro hG hBZ hZ k _ _ _ _ _ x hx hs
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.T.supercuspidalSupport_unique_GL hG hBZ hZ k x _ _ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSphericalStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  first | exact @GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | exact GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | (intros; apply GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
namespace CrystallineMultiplicity
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.CharInv

theorem isCrys_and_multV_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  intro l _ P AI T K LL μ a hμ hm
  obtain ⟨h1, -, h2⟩ := GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 0
  rw [zpow_zero] at h1
  simp only [zpow_zero] at h2
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (μ g : ↥LL.1) • charRep μ⁻¹ g x :=
    fun g x => by simp [charRep]
  refine ⟨(GlobalTheory.TopSteps.CrysRules.isCrys_iff T K LL _ _ μ hρ hμ).2 h1, fun τ c => ?_⟩
  have hs := GlobalTheory.TopSteps.CrysRules.multV_shift T K LL _ _ μ hρ hμ τ (a τ)
    (fun b => by rw [hm, Multiset.count_singleton]; split_ifs <;> rfl) c
  rw [← hs, h2]
  exact if_congr (by omega) rfl rfl

end GlobalTheory.CompanionTheory.CharInv

end

end CrystallineMultiplicity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
theorem _root_.GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | exact CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | (intros; apply CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv <;> assumption)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNegStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg | exact GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg | (intros; apply GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.GenQuot

open GlobalTheory.PlaceModel

variable {D : D7} {S T : HSp D}

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  induction k with
  | zero => simp only [zero_smul, symplO_zero_left, symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_left, symplO_add_right, ih]

theorem reps_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha hinf k hk
  classical
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T ΛS ΛT ↔ ∀ u' ∈ latH S T ΛS ΛT, ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin : ∀ m : ℕ, 0 < m → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ latH S T ΛS ΛT, ∃ r ∈ R, ∃ u ∈ latH S T ΛS ΛT, t = r + m • u :=
    GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ latH S T ΛS ΛT, b • u ∈ latH S T ΛS ΛT ⊓ half S T b :=
    fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize latH S T ΛS ΛT = Λ at *
  have hc : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  generalize hcdef : cA D a = c at *
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy

  let M : AddSubgroup (WO S T) := half S T c ⊓ Λ.comap (nsmulAddMonoidHom k)
  let N : AddSubgroup (WO S T) := (Λ ⊓ half S T c).map (nsmulAddMonoidHom k)
  have hM : ∀ y, y ∈ M ↔ IsHalf c y ∧ k • y ∈ Λ := fun y => by
    rw [isHalf_iff]; rfl
  have hN : ∀ n, n ∈ N ↔ ∃ u ∈ Λ, IsHalf c u ∧ n = k • u := fun n => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, (isHalf_iff S T).2 hu.2, rfl⟩
    · rintro ⟨u, hu, hu', rfl⟩
      exact ⟨u, ⟨hu, (isHalf_iff S T).1 hu'⟩, rfl⟩
  let N' : AddSubgroup M := N.addSubgroupOf M
  have hq : ∀ y₁ y₂ : M, ((y₁ : M ⧸ N') = y₂ ↔ (y₂ : WO S T) - y₁ ∈ N) := fun y₁ y₂ => by
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [neg_add_eq_sub]

  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)).Finite :=
    (hR2.image _).preimage tf.injOn
  have hcover : ∀ y : M, ∃ z : M, (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2) ∧
      (z : M ⧸ N') = y := by
    rintro ⟨y, hy⟩
    obtain ⟨hyc, hyk⟩ := (hM y).1 hy
    obtain ⟨r, hr, u, hu, hru⟩ := hR2' _ hyk
    have hcu := hsm hc u hu
    have hky : c • (k • y) = k • y := by
      rw [smul_comm]; exact congrArg (k • ·) ((mem_half S T).1 ((isHalf_iff S T).1 hyc))
    have hz : k • (y - k • (c • u)) = c • r := by
      rw [smul_sub, ← hky, hru, smul_add, mul_smul, smul_comm c k (k • u), smul_comm c k u]
      abel
    have hzM : y - k • (c • u) ∈ M := by
      refine (hM _).2 ⟨(isHalf_iff S T).2 ?_, ?_⟩
      · exact sub_mem ((isHalf_iff S T).1 hyc) (nsmul_mem hcu.2 k)
      · rw [smul_sub]
        exact sub_mem hyk (nsmul_mem (nsmul_mem hcu.1 k) k)
    refine ⟨⟨_, hzM⟩, ⟨r, hr, hz.symm⟩, (hq _ _).2 ?_⟩
    show y - (y - k • (c • u)) ∈ N
    rw [sub_sub_cancel]
    exact ⟨c • u, hcu, rfl⟩
  haveI hfinQ : Finite (M ⧸ N') := by
    let P' : Set M := {z | (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)}
    have hP' : P'.Finite := hP.preimage Subtype.val_injective.injOn
    haveI := hP'.to_subtype
    refine Finite.of_surjective (fun z : P' => ((z : M) : M ⧸ N')) fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨z, hz, hzy⟩ := hcover y
      exact ⟨⟨z, hz⟩, hzy⟩
  letI := Fintype.ofFinite (M ⧸ N')
  let rep : M ⧸ N' → WO S T := fun q => ((Quotient.out q : M) : WO S T)
  have hrepM : ∀ q, rep q ∈ M := fun q => (Quotient.out q : M).2
  have hrep : ∀ q, ((⟨rep q, hrepM q⟩ : M) : M ⧸ N') = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q₁ q₂ h => by
    rw [← hrep q₁, ← hrep q₂]
    simp only [h]
  refine ⟨Finset.univ.image rep, ⟨rep 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (hM _).1 (hrepM q)
  · intro y' hy'c hy'k
    have hy'M : y' ∈ M := (hM y').2 ⟨hy'c, hy'k⟩
    refine ⟨rep (⟨y', hy'M⟩ : M), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hN _).1 ?_⟩, ?_⟩
    · exact (hq _ _).1 (hrep _)
    · rintro y ⟨hyY, hyN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyY
      have := (hq ⟨rep q, hrepM q⟩ ⟨y', hy'M⟩).2 ((hN _).2 hyN)
      rw [hrep] at this
      rw [this]
  intro x hx hkx
  have hxfin : ∀ {u : WO S T}, IsHalf a u → u.map (infPart D) = 0 := fun hu =>
    GlobalTheory.PlaceVec.half_infPart hinf ((isHalf_iff S T).1 hu)
  have hkxh : IsHalf a (k • x) := (isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hx) k)
  refine ⟨?_, fun hnot => ?_⟩
  · rintro ⟨u, hu, hua, rfl⟩ y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [symplO_nsmul_swap]
    exact (hdual u (hxfin hua)).1 hu _ ((hM _).1 (hrepM q)).2
  ·
    have hconst : ∀ y₁ y₂ : M, (y₁ : M ⧸ N') = y₂ →
        ψ (symplO S T x (y₂ : WO S T)) = ψ (symplO S T x (y₁ : WO S T)) := fun y₁ y₂ h => by
      obtain ⟨u, hu, -, hu'⟩ := (hN _).1 ((hq _ _).1 h)
      have e : (y₂ : WO S T) = y₁ + k • u := by rw [← hu']; abel
      rw [e, symplO_add_right, AddChar.map_add_eq_mul, ← symplO_nsmul_swap,
        (hdual _ (hxfin hkxh)).1 hkx u hu, mul_one]

    obtain ⟨x', hx'h, hx'⟩ := half_div S T a k hk x ((isHalf_iff S T).1 hx)
    have hx'Λ : x' ∉ Λ := fun h => hnot ⟨x', h, (isHalf_iff S T).2 hx'h, hx'.symm⟩
    have hx'fin := hxfin ((isHalf_iff S T).2 hx'h)
    obtain ⟨l, hl, hψl⟩ : ∃ l ∈ Λ, ψ (symplO S T x' l) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hx'Λ ((hdual x' hx'fin).2 hcon)
    have hl' := hsm hc l hl
    obtain ⟨y₀, hy₀h, hy₀⟩ := half_div S T c k hk _ hl'.2
    have hy₀M : y₀ ∈ M := (hM _).2 ⟨(isHalf_iff S T).2 hy₀h, hy₀ ▸ hl'.1⟩
    have hψ0 : ψ (symplO S T x y₀) ≠ 1 := by
      rw [← hx', symplO_nsmul_swap, hy₀, ← hcdef, ← symplO_smul, (mem_half S T).1 hx'h]
      exact hψl

    have hsum : ∑ y ∈ Finset.univ.image rep, ψ (symplO S T x y) = ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) :=
      Finset.sum_image fun q₁ _ q₂ _ h => hrepinj h
    rw [hsum]
    have hshift : ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) =
        (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * ψ (symplO S T x y₀) := by
      rw [Finset.sum_mul]
      refine (Fintype.sum_equiv (Equiv.addRight ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')) _ _ fun q => ?_).symm
      rw [← AddChar.map_add_eq_mul, ← symplO_add_right]
      have := hconst (⟨rep q, hrepM q⟩ + ⟨y₀, hy₀M⟩) ⟨rep (q + ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')), hrepM _⟩
        (by rw [hrep, QuotientAddGroup.mk_add, hrep])
      simpa using this.symm
    have h0 : (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * (ψ (symplO S T x y₀) - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 hψ0)

end GlobalTheory.DownLift.GenQuot

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  first | exact @GlobalTheory.DownLift.GenQuot.reps_orth | exact GlobalTheory.DownLift.GenQuot.reps_orth | (intros; apply GlobalTheory.DownLift.GenQuot.reps_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatible
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Sums

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem segSum_append_lpSum (rc : IrrGL (k := w.adicCompletion E) → WD h) (l l' : List (Segment (w.adicCompletion E))) :
    segSum rc (l ++ l') = (segSum rc l).lpSum (segSum rc l') := by
  induction l with
  | nil => exact ((WD.lpSum_comm _ _).trans (WD.lpSum_zero _)).symm
  | cons a l ih =>
    have key : ∀ m : List (Segment (w.adicCompletion E)), segSum rc (a :: m) =
        (((rc a.first).lpTw (((a.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) a.len)).lpSum (segSum rc m) := fun _ => rfl
    rw [List.cons_append, key, key, ih, WD.lpSum_assoc]

end Sums

theorem lawsLit_prod : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) := by
  intro hX hM hS E Ω _ _ _ _ _ A w h a ha e rc H r t σ τ π hπ
  have : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨𝔪, h𝔪⟩ := hX _ (cls σ)
  obtain ⟨𝔫, h𝔫⟩ := hX _ (cls τ)
  have hp := GlobalTheory.T.isLanglandsClassification_add_of_irreducible_product hM hS _ r t σ τ π 𝔪 𝔫 (h𝔪.of_equiv (equivRep σ).symm) (h𝔫.of_equiv (equivRep τ).symm) hπ
  rw [H.langlands 𝔪.toList (cls σ) (by rwa [Multiset.coe_toList]),
    H.langlands 𝔫.toList (cls τ) (by rwa [Multiset.coe_toList]),
    H.langlands (𝔪.toList ++ 𝔫.toList) (cls π) (by
      rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]
      exact hp.of_equiv (equivRep π)), segSum_append_lpSum]

end GlobalTheory.LocLanglands

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatibleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_rec_compatible : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) := by
  first | exact @GlobalTheory.LocLanglands.lawsLit_prod | exact GlobalTheory.LocLanglands.lawsLit_prod | (intros; apply GlobalTheory.LocLanglands.lawsLit_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemInt

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

section Val

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
  {la : HeightOneSpectrum (𝓞 K)} {u : R → EReal}

theorem nonneg_of_idem (hu : IsVal la u) {x : R} (hx : x * x = x) : 0 ≤ u x := by
  have h := hu.mul x x
  rw [hx] at h
  rcases eq_or_ne (u x) ⊤ with h0 | h0
  · rw [h0]
    exact le_top
  · have hr : (((u x).toReal : ℝ) : EReal) = u x := EReal.coe_toReal h0 (hu.ne_bot x)
    rw [← hr] at h ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    exact EReal.coe_nonneg.mpr (by linarith)

theorem nonneg_smul (hu : IsVal la u) {a : K} (ha : la.valuation K a ≤ 1) {x : R} (hx : 0 ≤ u x) :
    0 ≤ u (a • x) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_smul, hu.zero]
    exact le_top
  · rw [hu.smul a x ha0]
    have hv0 : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hlog : (la.valuation K a).log ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
      exact ha
    refine add_nonneg ?_ hx
    unfold Formalism.BasicNotions.vAdd
    have hn : (0 : ℤ) ≤ -(la.valuation K a).log := neg_nonneg.mpr hlog
    exact_mod_cast hn

theorem nonneg_sum (hu : IsVal la u) {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, 0 ≤ u (x i)) :
    0 ≤ u (∑ i ∈ s, x i) := by
  refine Finset.sum_induction x (fun y => 0 ≤ u y) (fun a b ha hb => ?_) ?_ hx
  · exact le_trans (le_min ha hb) (hu.add a b)
  · show (0 : EReal) ≤ u 0
    rw [hu.zero]
    exact le_top

end Val

theorem idem_comb_mul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  intro E _ _ _ H Dw l Xo c la m χ v hχ hv f hf u hu
  have hV : IsVal la u := isVal_valSet la u hu
  have h1 : 0 ≤ u (∑ i, v i • χ i) :=
    nonneg_sum hV Finset.univ _ fun i _ => nonneg_smul hV (hv i) (nonneg_of_idem hV (hχ i).2)
  rw [hV.mul]
  exact add_nonneg h1 (hf u hu)

end GlobalTheory.IdemInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlaceStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralComb_idempotentSections_nonneg_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  first | exact @GlobalTheory.IdemInt.idem_comb_mul_nonneg | exact GlobalTheory.IdemInt.idem_comb_mul_nonneg | (intros; apply GlobalTheory.IdemInt.idem_comb_mul_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHom
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvLocalArtin

theorem exists_invLocalArtin : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧ (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) ∧ ∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ A w h art ha
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w
  set f : (w.adicCompletion E)ˣ →* GlobalTheory.HeckeGal.Gab E Ω := art.comp (Neutral.B1.localIdele E w) with hf
  have hfi : Function.Injective f := hinj
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  have ho : ∀ x, ord (w.adicCompletion E) x = Multiplicative.toAdd (o x) := fun _ => rfl
  have unit_iff : ∀ x, Formalism.L2.Host.IsUnitAt w x ↔ ord (w.adicCompletion E) x = 0 := by
    intro x
    unfold Formalism.L2.Host.IsUnitAt
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, ← WithZero.exp_zero, WithZero.exp_inj]
    omega
  have unif_ord : ∀ x, Formalism.L2.Host.IsUnifAt w x → ord (w.adicCompletion E) x = 1 := by
    intro x hx
    unfold Formalism.L2.Host.IsUnifAt at hx
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, WithZero.exp_inj] at hx
    omega

  obtain ⟨π, hπ, hπf⟩ := (ha.frob w A h (GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω)⁻¹)).2 ⟨_, isFrob_frob, rfl⟩
  have hπo : ord (w.adicCompletion E) π = 1 := unif_ord π hπ
  have hπf' : f π⁻¹ = GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω) := by
    rw [map_inv]; show (art (Neutral.B1.localIdele E w π))⁻¹ = _; rw [hπf, map_inv, inv_inv]
  have ordpow : ∀ n : ℤ, ord (w.adicCompletion E) (π⁻¹ ^ n) = -n := by
    intro n
    rw [ho, map_zpow, map_inv, toAdd_zpow, toAdd_inv, ← ho, hπo]; simp
  have hex : ∀ σ : Weil h, ∃ x, ord (w.adicCompletion E) x = -deg σ ∧ f x = GlobalTheory.HeckeGal.toAb E Ω σ := by
    intro σ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    obtain ⟨u, hu, huf⟩ := (ha.ine w A h (GlobalTheory.HeckeGal.toAb E Ω τ)).2 ⟨τ, τ.2, rfl⟩
    refine ⟨π⁻¹ ^ deg σ * u, ?_, ?_⟩
    · rw [SmGL.ord_mul, ordpow, (unit_iff u).1 hu, add_zero]
    · rw [map_mul, map_zpow, hπf']
      show _ * art (Neutral.B1.localIdele E w u) = _
      rw [huf, ← map_zpow, ← map_mul]
      congr 1
      conv_rhs => rw [hτ]
      simp [Subgroup.coe_mul, Subgroup.coe_zpow]
  choose g hgo hgf using hex
  let a : Weil h →* (w.adicCompletion E)ˣ :=
    { toFun := g
      map_one' := hfi (by rw [hgf, map_one, Subgroup.coe_one, map_one])
      map_mul' := fun σ τ => hfi (by rw [hgf, map_mul, hgf, hgf, Subgroup.coe_mul, map_mul]) }
  refine ⟨a, ?_, hgo, fun σ => hgf σ⟩
  intro x
  set n := ord (w.adicCompletion E) x
  have hu : Formalism.L2.Host.IsUnitAt w (x * π⁻¹ ^ n) := by
    rw [unit_iff, SmGL.ord_mul, ordpow]; simp [n]
  obtain ⟨τ, hτ, hτf⟩ := (ha.ine w A h (f (x * π⁻¹ ^ n))).1 ⟨_, hu, rfl⟩
  refine ⟨ineIncl h ⟨τ, hτ⟩ * frob h ^ (-n), hfi ?_⟩
  show f (g _) = f x
  rw [hgf, Subgroup.coe_mul, Subgroup.coe_zpow, coe_ineIncl, map_mul, map_zpow, hτf, ← hπf', ← map_zpow, ← map_mul]
  congr 1
  rw [mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]

end GlobalTheory.InvLocalArtin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHomStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_localArtin_weilGroup_hom : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧ (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) ∧ ∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  first | exact @GlobalTheory.InvLocalArtin.exists_invLocalArtin | exact GlobalTheory.InvLocalArtin.exists_invLocalArtin | (intros; apply GlobalTheory.InvLocalArtin.exists_invLocalArtin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TransportGL

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem map_map_symm (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g :=
  Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)

theorem det_map (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k) :
    GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom g) =
      Units.map i.toRingHom.toMonoidHom (GeneralLinearGroup.det g) := by
  ext
  simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem isCusp_cls {n : ℕ} (π : IrrRep (GL (Fin n) k)) : (cls π).IsCusp ↔ 0 < n ∧ IsCuspidal π.ρ :=
  and_congr Iff.rfl ⟨isCuspidal_of_equiv (equivRep π).symm, isCuspidal_of_equiv (equivRep π)⟩

def transEquiv (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    Representation.Equiv (π.ρ.comp (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) π'.ρ :=
  .mk e fun g => LinearMap.ext fun v => by
    show e (π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) v) = π'.ρ g (e v)
    rw [he, map_map_symm]

theorem symm_rel (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    ∀ g w, e.symm (π'.ρ g w) = π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) (e.symm w) := fun g w => by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply, map_map_symm]

theorem repRel_tw (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v))
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (hc : ∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) :
    RepRel i ((cls π).tw χ hχ) ((cls π').tw χ' hχ') := by
  refine ⟨n, irrTwist π _ hχ.detChar, irrTwist π' _ hχ'.detChar, e, congrArg (Sigma.mk n) (clTwist_cl π _ hχ.detChar),
    congrArg (Sigma.mk n) (clTwist_cl π' _ hχ'.detChar), fun g (v : π.V) => ?_⟩
  show e (GlobalTheory.SmGL.twist π.ρ (detChar _ χ) g v) = GlobalTheory.SmGL.twist π'.ρ (detChar _ χ') (GeneralLinearGroup.map i.toRingHom g) (e v)
  rw [twist_apply, twist_apply, map_smul, he, detChar_apply, detChar_apply, det_map, hc]

end GlobalTheory.LocLanglands.TransportGL


open GlobalTheory.LocLanglands.TransportGL in
theorem GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  have hs := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  refine ⟨fun x x' ⟨n, π, π', e, hx, hx', he⟩ => ?_, fun χ hχ χ' hχ' hc => ?_⟩
  · subst hx hx'
    refine ⟨?_, fun s => repRel_tw i π π' e he _ _ _ _ (hs.2.2.2.2 s)⟩
    rw [isCusp_cls, isCusp_cls]
    refine and_congr Iff.rfl ⟨fun h => isCuspidal_of_equiv (transEquiv i π π' e he)
      (isCuspidal_comp_generalLinearGroupMap i hs.1 _ h), fun h => isCuspidal_of_equiv
      (transEquiv i.symm π' π e.symm (symm_rel i π π' e he)) (isCuspidal_comp_generalLinearGroupMap i.symm hi _ h)⟩
  · refine ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ' hχ', LinearEquiv.refl ℂ ℂ, rfl, rfl, fun g (v : ℂ) => ?_⟩
    show GlobalTheory.SmGL.twist (Representation.trivial ℂ (GL (Fin 1) k) ℂ) (detChar (Fin 1) χ) g v =
      GlobalTheory.SmGL.twist (Representation.trivial ℂ (GL (Fin 1) k') ℂ) (detChar (Fin 1) χ') (GeneralLinearGroup.map i.toRingHom g) v
    rw [twist_apply, twist_apply, detChar_apply, detChar_apply, TransportGL.det_map, hc]
    rfl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_keeps_cuspidal_twists_characters : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  first | exact @GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | exact GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | (intros; apply GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.SuppLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [sumList, charPol_lpZero]
  | cons b l ih =>
    have : sumList (b :: l) = WD.lpSum b (sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

theorem nu_eq {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (H : LawsLit a ha e rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) : rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.twist, H.one, lpChar_lpOfChar, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem charPol_seg {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (H : LawsLit a ha e rc) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, nu_eq H]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

end GlobalTheory.LocLanglands.SuppLaw

namespace GlobalTheory.LocLanglands

theorem charPol_eq_prod_support : LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma →
    BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ)
    (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) s,
    HasSupport x.rep s → ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod := by
  intro hEx hZ hG hBZ E Ω _ _ _ _ _ A w h a ha e rc H x s hs σ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hEx (w.adicCompletion E) x
  have h1 := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZ _ 𝔪 x hm
  obtain rfl : s = msupp 𝔪 := GlobalTheory.T.supercuspidalSupport_unique_GL hG hBZ hZ _ x s _ hs h1
  rw [H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, SuppLaw.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => SuppLaw.charPol_seg H Δ σ)

end GlobalTheory.LocLanglands
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatibleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_rec_compatible : LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) s, HasSupport x.rep s → ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod := by
  first | exact @GlobalTheory.LocLanglands.charPol_eq_prod_support | exact GlobalTheory.LocLanglands.charPol_eq_prod_support | (intros; apply GlobalTheory.LocLanglands.charPol_eq_prod_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertia
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ArtinInvCont

theorem absoluteGaloisAbelianization_t2Space (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    T2Space (GlobalTheory.HeckeGal.Gab E Ω) := by
  unfold GlobalTheory.HeckeGal.Gab TopologicalAbelianization
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

theorem continuous_localIdele' (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    Continuous (Neutral.B1.localIdele E v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) v
  have hs : Continuous (Neutral.B1.finiteSingle E v) := (RestrictedProduct.continuous_inclusion hle).comp hf
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const hs

theorem isCompact_valOne (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1} := by
  rw [Units.isEmbedding_val₀.isInducing.isCompact_iff]
  have e : (Units.val '' {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1}) =
      {y : w.adicCompletion E | Valued.v y = 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  have hK : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  refine hK.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {y : w.adicCompletion E | Valued.v y ≤ 1} := by
      have : {y : w.adicCompletion E | Valued.v y ≤ 1} = (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
        ext y
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).symm
      rw [this]
      exact hK.isClosed
    have h2 : IsOpen {y : w.adicCompletion E | Valued.v y < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      have hz' : Valued.v (z - y) < 1 := by simpa using hz
      have : z = (z - y) + y := by ring
      show Valued.v z < 1
      rw [this]
      exact Valuation.map_add_lt _ hz' hy
    have e2 : {y : w.adicCompletion E | Valued.v y = 1} =
        {y : w.adicCompletion E | Valued.v y ≤ 1} ∩ {y : w.adicCompletion E | Valued.v y < 1}ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
      exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
    rw [e2]
    exact h1.inter h2.isClosed_compl
  · intro y hy
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (le_of_eq hy)

theorem continuous_inv_on_ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (a : Weil h →* (w.adicCompletion E)ˣ), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) → (∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ) → Continuous fun σ : Ine (F := E) A => a (ineIncl h σ) := by
  intro E Ω _ _ _ _ _ A w h art a ha hord hart
  haveI := absoluteGaloisAbelianization_t2Space E Ω
  let K : Set (w.adicCompletion E)ˣ := {x | Valued.v (x : w.adicCompletion E) = 1}
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_valOne E w)
  let f : K → GlobalTheory.HeckeGal.Gab E Ω := fun x => art (Neutral.B1.localIdele E w x.1)
  have hf : Continuous f :=
    (ha.quot.continuous.comp (continuous_localIdele' E w)).comp continuous_subtype_val
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w hxy)
  have hemb := hf.isClosedEmbedding hinj
  have hmem : ∀ σ : Ine (F := E) A, a (ineIncl h σ) ∈ K := by
    intro σ
    have hd : deg (ineIncl h σ) = 0 := by
      rw [deg_eq (a := 0) (b := 0) (actsAs_zero_iff.mpr σ.2)]
      simp
    have ho := hord (ineIncl h σ)
    rw [hd, neg_zero, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at ho
    show Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [← WithZero.exp_log (by simp : Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0),
      ho, WithZero.exp_zero]
  let g : Ine (F := E) A → K := fun σ => ⟨a (ineIncl h σ), hmem σ⟩
  have hg : Continuous g := by
    rw [hemb.isInducing.continuous_iff]
    have e : f ∘ g = fun σ : Ine (F := E) A => GlobalTheory.HeckeGal.toAb E Ω (σ : G E Ω) :=
      funext fun σ => hart (ineIncl h σ)
    rw [e]
    exact continuous_quot_mk.comp continuous_subtype_val
  exact continuous_subtype_val.comp hg

end GlobalTheory.ArtinInvCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertiaStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseLocalArtin_continuousOn_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (a : Weil h →* (w.adicCompletion E)ˣ), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) → (∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ) → Continuous fun σ : Ine (F := E) A => a (ineIncl h σ) := by
  first | exact @GlobalTheory.ArtinInvCont.continuous_inv_on_ine | exact GlobalTheory.ArtinInvCont.continuous_inv_on_ine | (intros; apply GlobalTheory.ArtinInvCont.continuous_inv_on_ine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowAt
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitRowAll

theorem splitRow_at : ∀ D : D7, SplitRow_at D := by
  intro D
  refine ⟨fun l hl => GlobalTheory.T.split_prime_implies_places_split D.host l hl, fun i hi => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    have h2 : D.nd.l i ∉ D.host.small := ((primeClass_eq_splitK_iff _).1 hi.2.2.2.2.2).1
    exact (GlobalTheory.T.K0_eq_and_good_of_ne D i h2 hi.2.2.1 hi.2.2.2.1 w hw).1
  · rintro w hw τ ⟨h1, h2⟩
    rcases GlobalTheory.SplitRowProbe.embIn_xor D i w hw τ with h | h
    · exact h.2 h2
    · exact h.2 h1
  · exact GlobalTheory.T.splitPrime_place_cmType_conjugate D i hi
  · exact GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count D i hi

end GlobalTheory.SplitRowAll
end

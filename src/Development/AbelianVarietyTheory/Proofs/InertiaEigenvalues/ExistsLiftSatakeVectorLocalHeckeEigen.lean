module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramified
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.InertTransferCanon

theorem exists_canonical_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  intro L _ _ _ n F v w hov Dv hs
  obtain ⟨hu, hns, -⟩ := GlobalTheory.InertOfUnramInv.inert_of_isUnramInv L v w hov Dv.σw Dv.ϖ _ hs Dv.unram
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : Dv.σw = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq _ Dv.unram.2.1)
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)

  obtain ⟨i, hic, hi⟩ := F.right w v hov
  have hiy : ∀ y : maximalRealSubfield L,
      i (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) =
        GlobalTheory.LFun.complMap hunder (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) := by
    intro y
    rw [GlobalTheory.LFun.complMap_algebraMap]
    have h1 := hi (algebraMap (maximalRealSubfield L) _ y)
    have h2 : (1 : L) ⊗ₜ[maximalRealSubfield L]
        (algebraMap (maximalRealSubfield L) (FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L)) y) =
        (algebraMap (maximalRealSubfield L) L y) ⊗ₜ 1 := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    rw [h2, F.left] at h1
    exact h1.symm
  have hieq : (i : v.adicCompletion (maximalRealSubfield L) → w.adicCompletion L) = GlobalTheory.LFun.complMap hunder :=
    (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer hic
      (GlobalTheory.LFun.InertChart.continuous_complMap hunder) (funext hiy)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      Dv.σw (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hsc, hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; rfl
    | tmul x a =>
      have hk : F.κ (x ⊗ₜ a) = F.κ (x ⊗ₜ 1) * F.κ (1 ⊗ₜ a) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (compAt L v (x ⊗ₜ a))) = _
      have hm : ∀ p q : FiniteAdeleRing (𝓞 L) L, (p * q) w = p w * q w := fun _ _ => rfl
      rw [hk, F.left, hm, hi, hieq]
      show GlobalTheory.LFun.complMap hunder (a v) * algebraMap L _ x = _
      rw [mul_comm]
      rfl

end GlobalTheory.InertTransferCanon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquivStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  first | exact @GlobalTheory.InertTransferCanon.exists_canonical_equiv | exact GlobalTheory.InertTransferCanon.exists_canonical_equiv | (intros; apply GlobalTheory.InertTransferCanon.exists_canonical_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimage
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem cosetSum_transfer_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H)
    (hψ : Function.Surjective ψ) (hTU : ∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0)
    (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ)
    (ha : ∀ x, ∀ k ∈ K, a (x * k) = a x)
    (hfin : (Function.support fun d : H ⧸ K => a d.out).Finite)
    (hβ : ∀ x, ∀ u ∈ U0, β (x * u) = β x)
    (hφ : ∀ t : T, φ' (ψ t) = lam (β t)) :
    ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0,
      if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  classical
  set F : G ⧸ U0 → V := fun c => if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0 with hF
  let t : H ⧸ K → T := fun d => (hψ d.out).choose
  have ht : ∀ d, ψ (t d) = d.out := fun d => (hψ d.out).choose_spec
  let f : H ⧸ K → G ⧸ U0 := fun d => ((t d : G) : G ⧸ U0)

  have key : ∀ x y : T, ((x : G) : G ⧸ U0) = ((y : G) : G ⧸ U0) →
      ((x : G)⁻¹ * y ∈ U0) ∧ ∃ k ∈ K, ψ y = ψ x * k := by
    intro x y hxy
    rw [QuotientGroup.eq] at hxy
    refine ⟨hxy, ψ (x⁻¹ * y), (hTU _).2 (by simpa using hxy), ?_⟩
    simp [map_mul, map_inv]

  have hinj : Function.Injective f := by
    intro d d' h
    obtain ⟨-, k, hk, hkk⟩ := key _ _ h
    rw [ht, ht] at hkk
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d', QuotientGroup.eq, hkk]
    simpa using hk

  have hcover : ∀ x : T, f ((ψ x : H) : H ⧸ K) = ((x : G) : G ⧸ U0) ∧
      a (((ψ x : H) : H ⧸ K).out) = a (ψ x) := by
    intro x
    set d : H ⧸ K := ((ψ x : H) : H ⧸ K) with hd
    have h1 : d.out⁻¹ * ψ x ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · show (((t d : T) : G) : G ⧸ U0) = ((x : G) : G ⧸ U0)
      rw [QuotientGroup.eq]
      have : ψ ((t d)⁻¹ * x) ∈ K := by simpa [map_mul, map_inv, ht] using h1
      simpa using (hTU _).1 this
    · have := ha d.out _ h1
      simpa using this.symm

  have hval : ∀ d, F (f d) = a d.out • β (t d) := by
    intro d
    have hc : ∃ x : G, (x : G ⧸ U0) = f d ∧ x ∈ T := ⟨t d, rfl, (t d).2⟩
    simp only [hF, dif_pos hc]
    obtain ⟨hU, k, hk, hkk⟩ := key (t d) ⟨hc.choose, hc.choose_spec.2⟩ hc.choose_spec.1.symm
    rw [hkk, ha _ k hk, ht]
    congr 1
    have := hβ (t d : G) _ hU
    simpa using this

  set S : Finset (H ⧸ K) := hfin.toFinset with hS
  have hsupp : Function.support F ⊆ ↑(S.image f) := by
    intro c hc
    rw [Function.mem_support] at hc
    have hc' : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T := by
      by_contra hn
      exact hc (by simp only [hF, dif_neg hn])
    obtain ⟨x, rfl, hx⟩ := hc'
    obtain ⟨h1, h2⟩ := hcover ⟨x, hx⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, ?_, h1⟩)
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support, h2]
    intro h0
    apply hc
    have hF' := hval ((ψ ⟨x, hx⟩ : H) : H ⧸ K)
    rw [h1, h2, h0, zero_smul] at hF'
    exact hF'
  have hL : Function.support (fun d : H ⧸ K => a d.out * φ' d.out) ⊆ ↑S := by
    intro d hd
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hd (by simp only [h0, zero_mul])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun d _ d' _ h => hinj h), map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hval, map_smul, smul_eq_mul, ← hφ, ht]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimageStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_transfer_along_surjection_preimage : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H), Function.Surjective ψ → (∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0) → ∀ (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ), (∀ x, ∀ k ∈ K, a (x * k) = a x) → (Function.support fun d : H ⧸ K => a d.out).Finite → (∀ x, ∀ u ∈ U0, β (x * u) = β x) → (∀ t : T, φ' (ψ t) = lam (β t)) → ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0, if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  first | exact @GlobalTheory.cosetSum_transfer_surj | exact GlobalTheory.cosetSum_transfer_surj | (intros; apply GlobalTheory.cosetSum_transfer_surj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFrameConjUnitaryIntegralIffGLIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFrameConjUnitaryIntegralIffGLIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KUTransfer

theorem ku_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ x, (p x ∈ Formalism.UG.KU σ n ↔ cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  intro L _ _ _ n w σ b hb p hp x
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  have hK : ∀ g : GL (Fin n) (w.adicCompletion L), g ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      g ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := by
    intro g
    show g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L w) ↔ _
    rw [hO]; rfl
  have h1 : p x ∈ Formalism.UG.KU σ n ↔ (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    rw [hK]
    show (p x).val ∈ Formalism.UG.intPts (Formalism.UG.intL _).subtype (Formalism.UG.GU σ n) ↔ _
    exact ⟨fun h => h.2, fun h => ⟨(p x).2, h⟩⟩
  rw [h1, hp]
  have hbi : b⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hb
  constructor
  · intro h
    have := (GlobalTheory.LFun.KGL w (n := n)).mul_mem (( GlobalTheory.LFun.KGL w (n := n)).mul_mem hb h) hbi
    simpa [mul_assoc] using this
  · intro h
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).mul_mem hbi h) hb

end GlobalTheory.KUTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFrameConjUnitaryIntegralIffGLIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_conj_unitaryIntegral_iff_GL_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ x, (p x ∈ Formalism.UG.KU σ n ↔ cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  first | exact @GlobalTheory.KUTransfer.ku_iff | exact GlobalTheory.KUTransfer.ku_iff | (intros; apply GlobalTheory.KUTransfer.ku_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsidePlaceMemDefiniteUnitaryLocalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsidePlaceMemDefiniteUnitaryLocalPoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocMemTransfer

theorem mem_locU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ y : GAf L n, TrivOutside {v} y → F.j y ∈ locU n w := by
  intro L _ _ _ n F v w hw y hy
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  refine Subgroup.mem_inf.2 ⟨F.fin y, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
  ext s t
  rw [F.loc y u s t]
  have h := hy (u.under (𝓞 (maximalRealSubfield L))) (by simpa using hu)
  have h0 : compAt L (u.under (𝓞 (maximalRealSubfield L)))
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) s t - (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = 0 := by
    have hst := congrFun (congrFun h s) t
    rw [Matrix.map_apply] at hst
    rw [map_sub, hst]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have h1 := (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) (GlobalTheory.UnramDict.kappa_tmul F)
    (u.under (𝓞 (maximalRealSubfield L))) _).1 h0 u rfl
  rw [map_sub] at h1
  change F.κ _ u - F.κ _ u = 0 at h1
  rw [sub_eq_zero] at h1
  rw [h1]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp
  rfl

end GlobalTheory.LocMemTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsidePlaceMemDefiniteUnitaryLocalPointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ y : GAf L n, TrivOutside {v} y → F.j y ∈ locU n w := by
  first | exact @GlobalTheory.LocMemTransfer.mem_locU | exact GlobalTheory.LocMemTransfer.mem_locU | (intros; apply GlobalTheory.LocMemTransfer.mem_locU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentMemMaxCompactGLIffMemMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentMemMaxCompactGLIffMemMaxCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocInteg

theorem kappa_mem_int {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (F : FinIso L n)
    (w : HeightOneSpectrum (𝓞 L)) {z : AL L} (hz : z ∈ ALint L) : F.κ z w ∈ w.adicCompletionIntegers L := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩
    · rw [F.left]
      exact GlobalTheory.AdeleBaseChange.algebraMap_int_mem y w
    · have h := GlobalTheory.UnramDict.kappa_tmul F 1 a
      rw [map_one, one_mul] at h
      change F.κ.toRingHom _ w ∈ _
      rw [h]
      exact GlobalTheory.AdeleBaseChange.adMap_int ha w
  | one => rw [map_one]; exact one_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem cLoc_mem_KGL_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w (n := n) ↔ y ∈ Umax L n) := by
  intro L _ _ _ n F w y hy
  constructor
  · intro hK i j
    exact GlobalTheory.UnramDict.mem_ALint F _ fun u => by
      rw [← F.loc]
      exact GlobalTheory.UnramDict.cLoc_entry_mem hy hK u i j
  · intro hyU
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [F.loc]
      exact kappa_mem_int F w (hyU i j)
    · rw [← map_inv, ← map_inv, F.loc]
      exact kappa_mem_int F w ((inv_mem hyU : y⁻¹ ∈ Umax L n) i j)

end GlobalTheory.LocInteg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentMemMaxCompactGLIffMemMaxCompactStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_mem_maxCompactGL_iff_mem_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w (n := n) ↔ y ∈ Umax L n) := by
  first | exact @GlobalTheory.LocInteg.cLoc_mem_KGL_iff | exact GlobalTheory.LocInteg.cLoc_mem_KGL_iff | (intros; apply GlobalTheory.LocInteg.cLoc_mem_KGL_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.InertTransfer

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem tOne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem tMul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

theorem tInv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

def trivSub (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v} x}
  mul_mem' := fun hx hy => tMul hx hy
  one_mem' := tOne v
  inv_mem' := fun hx => tInv hx

theorem heckeVec_frame_eval : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (D : InertDatum L n v w) (U0 : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU D.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ y, D.loc y = b⁻¹ * cLoc w (F.j y) * b) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU D.σw n), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U0, NG.rt L n κ f = f) → ∀ (lam : W →ₗ[ℂ] ℂ) (φ : UA L n → ℂ), (∀ g, φ (F.j g) = lam (f g)) → ∀ g, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU D.σw n).comap p) (fun x => h (p x)) φ (F.j g) = lam (heckeFunI L n U0 D h f g) := by
  intro L _ _ _ n F v w hwv D U0 hU0 b hb p hp hloc h hh W _ _ f hf lam φ hφ g
  have hvw : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hwv
  let T : Subgroup (GAf L n) := trivSub v
  let ψ : T →* locU n w :=
    { toFun := fun t => ⟨F.j t, GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints L n F v w hwv t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hψv : ∀ t : T, ((ψ t : locU n w) : UA L n) = F.j t := fun t => rfl
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := F.onto y.1 (Subgroup.mem_inf.1 y.2).1
    have hxl : F.j x ∈ locU n w := hx ▸ y.2
    have ht : TrivOutside {v} x := hvw ▸ GlobalTheory.UnramDict.trivOutside F hxl
    exact ⟨⟨x, ht⟩, Subtype.ext hx⟩
  set K' : Subgroup (locU n w) := (Formalism.UG.KU D.σw n).comap p with hK'
  have hiff : ∀ t : T, ψ t ∈ K' ↔ (t : GAf L n) ∈ U0 := by
    intro t
    rw [Subgroup.mem_comap, GlobalTheory.T.integralFrame_conj_unitaryIntegral_iff_GL_integral L n w D.σw b hb p hp (ψ t), hψv,
      GlobalTheory.T.localComponent_mem_maxCompactGL_iff_mem_maxCompact L n F w t (GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints L n F v w hwv t t.2), hU0 t t.2]
  have hRi : ∀ (a : Formalism.UG.GU D.σw n) (c : Formalism.UG.KU D.σw n), h (a * c) = h a :=
    fun a c => by simpa using hh.1 1 c a
  have haK : ∀ x, ∀ k ∈ K', h (p (x * k)) = h (p x) := by
    intro x k hk
    rw [map_mul]
    exact hRi (p x) ⟨p k, hk⟩
  have hfinU := Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified D.unram n) hh.2
  let e : locU n w ⧸ K' → Formalism.UG.GU D.σw n ⧸ Formalism.UG.KU D.σw n := fun d => (p d.out : _)
  have he : Function.Injective e := by
    intro d d' hdd
    have h1 := QuotientGroup.eq.1 hdd
    rw [← map_inv, ← map_mul] at h1
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']
    exact QuotientGroup.eq.2 h1
  have heq : ∀ d : locU n w ⧸ K', h (p d.out) = h (e d).out := by
    intro d
    have hk : (p d.out)⁻¹ * (e d).out ∈ Formalism.UG.KU D.σw n :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (e d)).symm
    have := hRi (p d.out) ⟨_, hk⟩
    rw [← this]
    congr 1
    group
  have hsupp : (Function.support fun d : locU n w ⧸ K' => h (p d.out)).Finite := by
    refine (hfinU.preimage he.injOn).subset ?_
    intro d hd
    show h (e d).out ≠ 0
    rw [← heq]; exact hd
  have hβ : ∀ x, ∀ u ∈ U0, f (g * (x * u)) = f (g * x) := by
    intro x u hu
    have := congrFun (hf u hu) (g * x)
    rw [← mul_assoc]; exact this
  have hφ' : ∀ t : T, φ (F.j g * ((ψ t : locU n w) : UA L n)) = lam (f (g * t)) := by
    intro t
    rw [hψv, ← map_mul]; exact hφ _
  have key := GlobalTheory.T.cosetSum_transfer_along_surjection_preimage U0 K' T ψ hsurj hiff (fun x => h (p x))
    (fun d => φ (F.j g * (d : UA L n))) (fun x => f (g * x)) lam haK hsupp hβ hφ'
  have hv : ∀ x (hx : TrivOutside {v} x), D.hval h (D.loc x) = h (p (ψ ⟨x, hx⟩)) := by
    intro x hx
    have e1 : D.loc x = (p (ψ ⟨x, hx⟩)).val := by rw [hloc, hp]; rfl
    rw [InertDatum.hval, dite_eq_left (e1 ▸ (p (ψ ⟨x, hx⟩)).2)]
    congr 1
    exact Subtype.ext e1

  have hL : GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) K' (fun x => h (p x)) φ (F.j g) =
      ∑ᶠ d : locU n w ⧸ K', h (p d.out) * φ (F.j g * (d.out : UA L n)) := by
    unfold GlobalTheory.LFun.heckeVec
    have hfin' : (Function.support fun c : locU n w ⧸ K' =>
        (fun x => h (p x)) c.out • ((RU L n).comp (locU n w).subtype) c.out φ).Finite :=
      hsupp.subset fun c hc h0 => hc (by simp only [h0, zero_smul])
    change (Pi.evalAddMonoidHom (fun _ : UA L n => ℂ) (F.j g))
      (∑ᶠ c : locU n w ⧸ K', (fun x => h (p x)) c.out • ((RU L n).comp (locU n w).subtype) c.out φ) = _
    rw [AddMonoidHom.map_finsum _ hfin']
    rfl
  rw [hL, key]
  congr 1
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  split_ifs with h1 h2 h2
  · rw [hv h2.choose h2.choose_spec.2]
    rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

end GlobalTheory.InertTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (D : InertDatum L n v w) (U0 : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU D.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ y, D.loc y = b⁻¹ * cLoc w (F.j y) * b) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU D.σw n), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U0, NG.rt L n κ f = f) → ∀ (lam : W →ₗ[ℂ] ℂ) (φ : UA L n → ℂ), (∀ g, φ (F.j g) = lam (f g)) → ∀ g, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU D.σw n).comap p) (fun x => h (p x)) φ (F.j g) = lam (heckeFunI L n U0 D h f g) := by
  first | exact @GlobalTheory.InertTransfer.heckeVec_frame_eval | exact GlobalTheory.InertTransfer.heckeVec_frame_eval | (intros; apply GlobalTheory.InertTransfer.heckeVec_frame_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeTransformInvariantUnderFieldAutomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeTransformInvariantUnderFieldAutomorphism
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInvAuto

open Formalism.UG GlobalTheory.SatInd

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

def diagExp (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

theorem tMat_eq_diag (x : K) (n m : ℕ) (a : Fin m → ℤ) :
    tMat x n m a = Matrix.diagonal fun i => x ^ diagExp n m a i := by
  unfold tMat diagExp
  congr 1
  funext i
  split_ifs <;> simp

theorem diagExp_rev {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (i : Fin n) :
    diagExp n m a i.rev = -diagExp n m a i := by
  have hi := i.isLt
  have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
  unfold diagExp
  by_cases h1 : (i : ℕ) < m
  · have h2 : ¬ (i.rev : ℕ) < m := by omega
    have h3 : n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m := by omega
    rw [dite_eq_right h2, dite_eq_left h3, dite_eq_left h1]
    rw [show (⟨n - 1 - (i.rev : ℕ), h3.2⟩ : Fin m) = ⟨i, h1⟩ from
      Fin.ext (show n - 1 - (i.rev : ℕ) = (i : ℕ) by omega)]
  · by_cases h4 : n - m ≤ (i : ℕ) ∧ n - 1 - (i : ℕ) < m
    · have h2 : (i.rev : ℕ) < m := by omega
      rw [dite_eq_left h2, dite_eq_right h1, dite_eq_left h4, neg_neg]
      rw [show (⟨(i.rev : ℕ), h2⟩ : Fin m) = ⟨n - 1 - i, h4.2⟩ from Fin.ext hr]
    · have h2 : ¬ (i.rev : ℕ) < m := by omega
      have h3 : ¬ (n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m) := by omega
      rw [dite_eq_right h2, dite_eq_right h3, dite_eq_right h1, dite_eq_right h4, neg_zero]

theorem div_mem_intL {ϖ x : K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hx : x ∈ intL K) (hx' : x⁻¹ ∉ intL K) : x / ϖ ∈ intL K := by
  unfold intL at *
  rw [Valuation.mem_integer_iff] at *
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hx'
    simp
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx (fun h => hx' (by rw [map_inv₀, h, inv_one]))
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [map_div₀, hϖ, ← WithZero.exp_log hv0, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem map_mul_mat (g : K ≃+* K) {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    (A * B).map g = A.map g * B.map g := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum]

end Local

section Cell

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cell_guMap (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ : K} {q n m : ℕ} (hU : IsUnramInv ϖ σ q)
    (hm : 2 * m ≤ n) (a : Fin m → ℤ) (y : GU σ n)
    (hy : ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u, hu, k, hk, hyuk⟩ := hy
  obtain ⟨-, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖint : ϖ ∈ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖinv : ϖ⁻¹ ∉ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, map_inv₀, hϖ', ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp]; norm_num
  set c : K := g ϖ / ϖ with hc
  have hgϖ : g ϖ = ϖ * c := by rw [hc]; field_simp
  have hc0 : c ≠ 0 := div_ne_zero ((map_ne_zero g).2 h0) h0
  have hcint : c ∈ intL K := div_mem_intL hϖ' ((hint ϖ).1 hϖint)
    (by rw [← map_inv₀]; exact fun h => hϖinv ((hint _).2 h))
  have hcinv : c⁻¹ ∈ intL K := by
    have h1 : g.symm ϖ / ϖ ∈ intL K := div_mem_intL hϖ' (by rw [hint]; simpa using hϖint)
      (by rw [← map_inv₀, hint]; simpa using hϖinv)
    have h2 := (hint _).1 h1
    rw [map_div₀, RingEquiv.apply_symm_apply] at h2
    rw [hc, inv_div]; exact h2
  have hcv : Valued.v c = 1 := by
    unfold intL at hcint hcinv
    rw [Valuation.mem_integer_iff] at hcint hcinv
    refine le_antisymm hcint ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c * c⁻¹) := by rw [mul_inv_cancel₀ hc0, map_one]
      _ = Valued.v c * Valued.v c⁻¹ := map_mul _ _ _
      _ ≤ Valued.v c * 1 := mul_le_mul' le_rfl hcinv
      _ = Valued.v c := mul_one _
  have hσc : σ c = c := by rw [hc, map_div₀, hσϖ, ← hg, hσϖ]
  set e : Fin n → K := fun i => c ^ diagExp n m a i with he
  have he0 : ∀ i, e i ≠ 0 := fun i => zpow_ne_zero _ hc0
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) e (fun i => by
    simp only [he]; rw [map_zpow₀, hσc, diagExp_rev hm, ← zpow_add₀ hc0, add_neg_cancel, zpow_zero])
  have hdK : d ∈ KU σ n := by
    have hI : Formalism.UG.P.fIwasawaInt (((d : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      intro i j
      rw [hd]
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, he]; simp only; rw [map_zpow₀, hcv, one_zpow]
      · rw [Matrix.diagonal_apply_ne _ hij, map_zero]; exact zero_le'
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ d) hI
    have e' : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ d) = d := Subtype.ext (Units.ext rfl)
    rwa [e'] at this
  have hk1 : guMap g hg n k ∈ KU σ n := (mem_KU_iff_guMap g hg hint k).1 hk
  refine ⟨d * guMap g hg n u * d⁻¹, ?_, d * guMap g hg n k, (KU σ n).mul_mem hdK hk1, ?_⟩
  · refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.1 i j hij, map_zero, mul_zero, zero_mul]
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.2 i, map_one, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [guMap_val, hyuk, map_mul_mat, map_mul_mat]
    simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val]
    rw [tMat_eq_diag, Matrix.diagonal_map (map_zero _)]
    have hD : (Matrix.diagonal fun i => g (ϖ ^ diagExp n m a i)) =
        Matrix.diagonal (fun i => ϖ ^ diagExp n m a i) * Matrix.diagonal e := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [map_zpow₀, hgϖ, mul_zpow]
    have hinv : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (he0 i)
    rw [hD]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun i => (e i)⁻¹) (Matrix.diagonal e), hinv, Matrix.one_mul]

end Cell

theorem satU_guMap_self : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (ϖ : K) (q n m : ℕ), Formalism.UG.IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h : Formalism.UG.GU σ n → ℂ, Formalism.UG.IsBiInv (Formalism.UG.KU σ n) h → ∀ α : Fin m → ℂ, Formalism.UG.SatU ϖ q (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) α = Formalism.UG.SatU ϖ q h α := by
  intro K _ _ g σ hg hint ϖ q n m hU hm1 _ h hbi α
  have hg' : ∀ x, g.symm (σ x) = σ (g.symm x) := by
    intro x; apply g.injective; rw [hg]; simp
  have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := by
    intro x; rw [hint (g.symm x)]; simp
  refine satU_guMap g hg hint ϖ ϖ q n m h hbi
    (fun a y => ⟨cell_guMap g hg hint hU hm1 a y, fun hy => ?_⟩) α
  have := cell_guMap g.symm hg' hint' hU hm1 a (guMap g hg n y) hy
  rwa [guMap_symm_comp g hg hg' y] at this

end GlobalTheory.SatInvAuto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeTransformInvariantUnderFieldAutomorphismStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeTransform_invariant_under_field_automorphism : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (ϖ : K) (q n m : ℕ), Formalism.UG.IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h : Formalism.UG.GU σ n → ℂ, Formalism.UG.IsBiInv (Formalism.UG.KU σ n) h → ∀ α : Fin m → ℂ, Formalism.UG.SatU ϖ q (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) α = Formalism.UG.SatU ϖ q h α := by
  first | exact @GlobalTheory.SatInvAuto.satU_guMap_self | exact GlobalTheory.SatInvAuto.satU_guMap_self | (intros; apply GlobalTheory.SatInvAuto.satU_guMap_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHecke
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInd

theorem guMap_comp_mem_hecke : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (n : ℕ) (h : Formalism.UG.GU σ' n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ' n) → (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) := by
  intro K _ _ g σ σ' hg hint n h hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : Formalism.UG.GU σ n ≃* Formalism.UG.GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have hK : ∀ y, y ∈ Formalism.UG.KU σ' n ↔ e.symm y ∈ Formalism.UG.KU σ n := by
    intro y
    rw [mem_KU_iff_guMap g hg hint (e.symm y)]
    change y ∈ Formalism.UG.KU σ' n ↔ e (e.symm y) ∈ Formalism.UG.KU σ' n
    rw [MulEquiv.apply_symm_apply]
  have := GlobalTheory.LFun.EigLoc.comp_symm_mem_hecke e.symm hK hh
  exact this

end GlobalTheory.SatInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHeckeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antidiagTransport_comp_mem_sphericalHecke : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (n : ℕ) (h : Formalism.UG.GU σ' n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ' n) → (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) := by
  first | exact @GlobalTheory.SatInd.guMap_comp_mem_hecke | exact GlobalTheory.SatInd.guMap_comp_mem_hecke | (intros; apply GlobalTheory.SatInd.guMap_comp_mem_hecke <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.UnramDict

theorem fixed_of_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  intro L _ _ _ n F U hU v w hw U0 hU0 σ b hb p hp φ hφU hfix x hK
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  have hK1 : (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf.1 hK).2
  have hK2 : cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have h : cLoc w x.val = b * (p x).val * b⁻¹ := by rw [hp]; group
    rw [h]
    exact mul_mem (mul_mem hb hK1) (inv_mem hb)
  have hx := x.2
  obtain ⟨y, hy⟩ := F.onto x.val (Subgroup.mem_inf.1 hx).1
  have hyU : y ∈ Umax L n := fun i j => mem_ALint F _ fun u => by
    rw [← F.loc, hy]
    exact cLoc_entry_mem hx hK2 u i j
  have hk (a : L) (z : AFplus L) :
      F.κ.toRingHom (a ⊗ₜ[maximalRealSubfield L] z) =
        algebraMap L _ a * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
    have h1 (z : AFplus L) : F.κ (1 ⊗ₜ z) =
        GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
      refine FiniteAdeleRing.ext _ fun q => ?_
      obtain ⟨i, hi, hia⟩ := F.right q (q.under (𝓞 (maximalRealSubfield L))) rfl
      rw [hia]
      change i (z (q.under (𝓞 (maximalRealSubfield L)))) = GlobalTheory.LFun.complMap rfl (z (q.under (𝓞 (maximalRealSubfield L))))
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
        (q.under (𝓞 (maximalRealSubfield L)))).equalizer hi
        (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k => ?_)) _
      change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
      rw [GlobalTheory.LFun.complMap_algebraMap]
      have he : (algebraMap (maximalRealSubfield L) (AFplus L) k) (q.under (𝓞 (maximalRealSubfield L))) =
          algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (q.under (𝓞 (maximalRealSubfield L)))) k := rfl
      rw [← he, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
      rfl
    rw [← h1, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hc (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L)
      (hz : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 (maximalRealSubfield L)) = v → F.κ z u = 0) :
      compAt L v z = 0 :=
    (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) hk v z).2 hz
  have hyt : TrivOutside {w.under (𝓞 (maximalRealSubfield L))} y := by
    intro v hv
    refine Matrix.ext fun i j => ?_
    have h0 := hc v (y.1.val i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) fun u hu => by
      have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
        (fun e => hv (hu.symm.trans e)))
      have h1 := F.loc y u i j
      rw [hy, h] at h1
      rw [map_sub]
      change F.κ _ u - F.κ _ u = 0
      rw [← h1]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> simp <;> rfl
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hy0 : y ∈ U0 := (hU0 y hyt).2 hyU
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hU.aut _ (U.sub_mem (hU.stable _ _ hφU) hφU)) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  change φ (F.j g * x.val) - φ (F.j g) = 0
  rw [← hy, ← map_mul, sub_eq_zero]
  exact hfix g y hy0

end GlobalTheory.UnramDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  first | exact @GlobalTheory.UnramDict.fixed_of_mem_KU | exact GlobalTheory.UnramDict.fixed_of_mem_KU | (intros; apply GlobalTheory.UnramDict.fixed_of_mem_KU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftSatakeVectorLocalHeckeEigen
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

theorem GlobalTheory.InertHeckeTransfer.exists_lift_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n F π U hD v w hw Dv α hα hs b hbK hbJ p hp
  obtain ⟨f, hfS, hf0, U0, hfixU0, hU0, heig⟩ := hα
  obtain ⟨g0, hg0⟩ : ∃ g0, f g0 ≠ 0 := Function.ne_iff.1 hf0
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (f g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  have hmem : (fun x => lam (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hD.2]
    exact Submodule.subset_span ⟨f, hfS, lam, rfl⟩
  obtain ⟨φ, hφU, hφ⟩ := hmem
  have hφ' : ∀ g, φ (F.j g) = lam (f g) := fun g => congrFun hφ g
  have hfU : ∀ g, ∀ κ ∈ U0, f (g * κ) = f g := fun g κ hκ => congrFun (hfixU0 κ hκ) g
  refine ⟨φ, hφU, fun h => hlam ?_, GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed L n F U hD.1 v w hw U0 hU0 Dv.σw b hbK p hp φ hφU
    (fun g κ hκ => by rw [hφ', hφ', hfU g κ hκ]), fun h hh => ?_⟩
  · rw [← hφ', h]; rfl
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv L n F v w hw Dv hs
  have hbP : b ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := hbK
  let D0 : InertDatum L n v w := ⟨e, Dv.σw, Dv.ϖ, b, he1, Dv.unram, he2, hbP, hbJ⟩
  have hloc : ∀ y, D0.loc y = b⁻¹ * cLoc w (F.j y) * b := by
    intro y
    show b⁻¹ * _ * b = _
    congr 2
    refine Units.ext (Matrix.ext fun s t => ?_)
    rw [F.loc]
    exact he3 _
  have hbi := hh.1
  have hh' := GlobalTheory.T.antidiagTransport_comp_mem_sphericalHecke (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) n h hh
  have heig0 : heckeFunI L n U0 D0 h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
    rw [GlobalTheory.SatInd.heckeFunI_indepDatum L n v w Dv D0 U0 π.W h hbi f, heig _ hh',
      GlobalTheory.T.satakeTransform_invariant_under_field_automorphism (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) Dv.ϖ _ n (n / 2)
        Dv.unram (by omega) (by omega) h hbi α]
  have htr := GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints L n F v w hw D0 U0 hU0 b hbK p hp hloc h hh π.W f hfixU0 lam φ hφ'
  have hvecU : GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ ∈ U := by
    unfold GlobalTheory.LFun.heckeVec
    by_cases hfin : (Function.support fun c : (locU n w) ⧸ ((Formalism.UG.KU Dv.σw n).comap p) =>
        h (p c.out) • ((RU L n).comp (locU n w).subtype) c.out φ).Finite
    · rw [finsum_eq_sum _ hfin]
      exact U.sum_mem fun c _ => U.smul_mem _ (hD.1.stable _ _ hφU)
    · rw [finsum_of_infinite_support hfin]
      exact U.zero_mem
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hD.1.aut _ (U.sub_mem hvecU (U.smul_mem _ hφU))) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  rw [Pi.sub_apply, Pi.smul_apply, htr g, heig0, hφ', Pi.smul_apply, map_smul, smul_eq_mul, sub_self]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftSatakeVectorLocalHeckeEigenStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_satake_vector_local_hecke_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  first | exact @GlobalTheory.InertHeckeTransfer.exists_lift_eigen | exact GlobalTheory.InertHeckeTransfer.exists_lift_eigen | (intros; apply GlobalTheory.InertHeckeTransfer.exists_lift_eigen <;> assumption)
end

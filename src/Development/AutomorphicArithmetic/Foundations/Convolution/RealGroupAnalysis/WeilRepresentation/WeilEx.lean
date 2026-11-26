module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OpsRel
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormRationalEmbed
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.IdxEta
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierConstMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousQuaternaryFormLeft
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

noncomputable section

private theorem continuous_form {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a c b d e : R) :
    Continuous fun y : Fin 4 → R => 2 * (y 2 * a - c * (y 3 * b)) - y 1 * d - y 0 * e := by
  fun_prop

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_psi : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp (continuous_adelicChar (K := F))

private theorem norm_psi (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

private theorem continuous_quaternaryForm_left (δ : F) (v : V4 F) : Continuous fun y : V4 F => B4 δ y v := by
  exact continuous_form (v 2) (rt δ) (v 3) (v 0) (v 1)

private theorem integrable_ft (δ : F) {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    Integrable (fun y => φ y * ψ (B4 δ y v)) (adeleMeasurePi F) := by
  refine (integrable_of_mem_schwartzBruhatPi hφ).mul_bdd (c := 1) ?_ ?_
  · exact (continuous_psi.comp (continuous_quaternaryForm_left δ v)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => (norm_psi _).le

private theorem quaternaryFourier_add (δ : F) {φ φ' : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (hφ' : φ' ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    ft4 δ (φ + φ') v = ft4 δ φ v + ft4 δ φ' v := by
  unfold ft4
  rw [← integral_add (integrable_ft δ hφ v) (integrable_ft δ hφ' v)]
  congr 1
  funext y
  simp [add_mul]

private theorem quaternaryFourier_smul (δ : F) (c : ℂ) (φ : V4 F → ℂ) (v : V4 F) :
    ft4 δ (c • φ) v = c * ft4 δ φ v := by
  unfold ft4
  rw [← integral_const_mul]
  congr 1
  funext y
  simp [mul_assoc]

private def opN (δ : F) (b : A F) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ψ (b * q4 δ v) * φ.1 v, by
    have h := chirpQ F δ b 0 φ.1 φ.2
    have e : (fun v => ψ (b * q4 δ v + B4 δ v 0) * φ.1 v) = fun v => ψ (b * q4 δ v) * φ.1 v := by
      funext v
      simp [B4]
    rwa [e] at h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def scal (a : (A F)ˣ) : GL (Fin 4) (A F) :=
  ⟨(a : A F) • 1, ((a⁻¹ : (A F)ˣ) : A F) • 1, by simp [smul_smul], by simp [smul_smul]⟩

private def opM (η : (A F)ˣ →* ℂˣ) (a : (A F)ˣ) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i, by
    have h := D.sClos F (Fin 4) (scal a) φ.1 φ.2
    have e : (fun v => φ.1 ((scal a).val *ᵥ v)) = fun v => φ.1 fun i => (a : A F) * v i := by
      funext v
      have e' : (scal a).val *ᵥ v = fun i => (a : A F) * v i := by
        funext i
        simp [scal, Matrix.smul_mulVec]
      rw [e']
    rw [e] at h
    exact Submodule.smul_mem _ (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def opW (δ : F) (hδ : δ ≠ 0) : Module.End ℂ (S4 F) where
  toFun φ := ⟨ft4 δ φ.1, (ftBasic F δ hδ φ.1 φ.2).1⟩
  map_add' φ φ' := by
    ext v
    exact quaternaryFourier_add δ φ.2 φ'.2 v
  map_smul' c φ := by
    ext v
    exact quaternaryFourier_smul δ c φ.1 v

end UpperTheory.ConvolutionTheory.R2.C

end

theorem UpperTheory.ConvolutionTheory.R2.C.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ), δ ≠ 0 → Nonempty (Ops δ η) := by
  intro F _ _ δ η hδ
  exact ⟨{ N := opN δ, M := opM η, W := opW δ hδ
           N_apply := fun _ _ _ => rfl
           M_apply := fun _ _ _ => rfl
           W_apply := fun _ _ => rfl }⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaEx
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NormForm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.normForm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (a : (A F)ˣ), (∃ s t : A F, (a : A F) = s ^ 2 - rt D.δ * t ^ 2) ↔ ∃ z : (A E)ˣ, ideleNorm F E z = a := by
  intro F E _ _ _ _ _ D a
  constructor
  · rintro ⟨s, t, h⟩
    have hm : D.mkE s t * D.bar (D.mkE s t) = am E (a : A F) := by rw [D.mkE_mul_bar, h]
    have hu : IsUnit (D.mkE s t * D.bar (D.mkE s t)) := by
      rw [hm]
      exact a.isUnit.map (am (F := F) E)
    obtain ⟨z, hz⟩ := isUnit_of_mul_isUnit_left hu
    refine ⟨z, Units.ext ?_⟩
    rw [D.coe_ideleNorm, hz, D.co_mkE, h]
    simp
  · rintro ⟨z, rfl⟩
    exact ⟨D.co z 0, D.co z 1, D.coe_ideleNorm z⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaQuad
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.QuadraticHeckeCharacter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem normV_abs {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem normV_eq_pow (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  rw [normV_abs, normV_abs, ← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 F)).asIdeal, map_pow]

private theorem one_lt_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    1 < normV v := by
  rw [normV_abs]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

private theorem under_of_mem {v : HeightOneSpectrum (𝓞 F)} (u : SemiLocal.PlacesOver E v) : u.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext u.2.over.symm

private theorem inertiaDeg_pos (w : HeightOneSpectrum (𝓞 E)) : 0 < w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal]
  exact Ideal.inertiaDeg'_pos _ _

private theorem finite_bad :
    {w : HeightOneSpectrum (𝓞 E) | ¬ Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F))}.Finite := by
  refine (Set.Finite.preimage' (f := fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F))
    (finite_setOf_exists_ramificationIdx_ne_one F E) fun v _ => ?_).subset fun w hw => ?_
  · exact (Set.finite_range fun u : SemiLocal.PlacesOver E v => u.1).subset fun w hw =>
      ⟨⟨w, ⟨by rw [← (Set.mem_singleton_iff.1 hw)]; rfl⟩⟩, rfl⟩
  · obtain ⟨u, hu, he⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧
        u.asIdeal.ramificationIdx (𝓞 F) ≠ 1 := by
      have hw' : ¬ Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) := hw
      simpa only [GlobalTheory.LFun.isUnram_iff, not_forall, exists_prop, ne_eq] using hw'
    exact ⟨u, ⟨by change (w.under (𝓞 F)).asIdeal = _; rw [← hu]; rfl⟩, he⟩

private theorem isSplit_iff_normV (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E))
    (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F))) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 F)) ↔ normV w = normV (w.under (𝓞 F)) := by
  have hsum := SemiLocal.sum_ramificationIdx_mul_inertiaDeg E (w.under (𝓞 F))
  rw [h2] at hsum
  have hterm : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)),
      u.1.asIdeal.ramificationIdx (𝓞 F) * u.1.asIdeal.inertiaDeg (𝓞 F) = u.1.asIdeal.inertiaDeg (𝓞 F) :=
    fun u => by rw [GlobalTheory.LFun.isUnram_iff.1 hu u.1 (under_of_mem u), one_mul]
  simp only [hterm] at hsum
  let w₀ : SemiLocal.PlacesOver E (w.under (𝓞 F)) := ⟨w, ⟨rfl⟩⟩
  have h1 : 1 < normV (w.under (𝓞 F)) := one_lt_normV _
  constructor
  · intro hs
    obtain ⟨P, Q, hPQ, hP, hQ⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    obtain ⟨u, hu', hne⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧ u ≠ w := by
      by_cases h : P = w
      · exact ⟨Q, hQ, fun e => hPQ (h.trans e.symm)⟩
      · exact ⟨P, hP, h⟩
    let u₀ : SemiLocal.PlacesOver E (w.under (𝓞 F)) := ⟨u, ⟨by rw [← hu']; rfl⟩⟩
    have hne' : w₀ ≠ u₀ := fun e => hne (congrArg Subtype.val e).symm
    have hle := Finset.add_le_sum (f := fun u : SemiLocal.PlacesOver E (w.under (𝓞 F)) => u.1.asIdeal.inertiaDeg (𝓞 F))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w₀) (Finset.mem_univ u₀) hne'
    rw [hsum] at hle
    have p1 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := inertiaDeg_pos w
    have p2 : 0 < u.asIdeal.inertiaDeg (𝓞 F) := inertiaDeg_pos u
    have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
      change w.asIdeal.inertiaDeg (𝓞 F) + u.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle
      omega
    rw [normV_eq_pow (F := F) w, hf, pow_one]
  · intro hn
    by_contra hs
    have hall : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)), u = w₀ := fun u =>
      Subtype.ext (GlobalTheory.LFun.eq_of_not_isSplit hs (under_of_mem u) rfl)
    rw [Finset.sum_eq_single w₀ (fun b _ hb => absurd (hall b) hb) (by simp)] at hsum
    change w.asIdeal.inertiaDeg (𝓞 F) = 2 at hsum
    rw [normV_eq_pow (F := F) w, hsum] at hn
    nlinarith

end UpperTheory.ConvolutionTheory.R2.C.QuadraticHeckeCharacter

theorem UpperTheory.ConvolutionTheory.R2.C.etaQuad :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E], ∃ η : HChar F, IsQuadCharOf E η ∧
    ∀ a, ((η.1 a : ℂˣ) : ℂ) = (((GlobalTheory.IdeleNormChar.normSign E a : ℤˣ) : ℤ) : ℂ) := by
  intro F E _ _ _ _ _ _
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨η, hη, -⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E h2
  have hη' : GlobalTheory.LFun.IsEta F E η := hη
  have he := hη'.eq_normSign
  refine ⟨GlobalTheory.LFun.toHChar η hη'.isHeckeF, ?_, fun a => ?_⟩
  · have hfin := QuadraticHeckeCharacter.finite_bad (F := F) (E := E)
    filter_upwards [hfin.compl_mem_cofinite] with w hw v hv
    have hw' : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) := by simpa using hw
    obtain rfl : w.under (𝓞 F) = v := GlobalTheory.LFun.comap_eq_iff.1 hv.symm
    refine ⟨(hη'.unrAt_iff h2).2 hw', ?_⟩
    rw [hη'.val_eq h2 hw']
    unfold GlobalTheory.LFun.etaU
    have hi := QuadraticHeckeCharacter.isSplit_iff_normV h2 w hw'
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 F))
    · rw [if_pos hs, if_pos (hi.1 hs)]
    · rw [if_neg hs, if_neg (mt hi.2 hs)]
  · have h3 : ((GlobalTheory.LFun.toHChar η hη'.isHeckeF).1 a : ℂ) = ((η a : Circle) : ℂ) := rfl
    rw [h3, he, MonoidHom.comp_apply]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;>
      simp [e, GlobalTheory.IdeleNormChar.signToCircle]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.etaEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ η : HChar F, IsQuadCharOf E η ∧ (∀ a, η.1 a ^ 2 = 1) ∧ (∀ z : (A E)ˣ, η.1 (ideleNorm F E z) = 1) ∧
    ∀ a, η.1 a = 1 → ∃ (t : F) (z : (A E)ˣ), t ≠ 0 ∧ (a : A F) = rt t * (ideleNorm F E z : (A F)ˣ) := by
  intro F E _ _ _ _ _ D
  haveI : Algebra.IsQuadraticExtension F E :=
    ⟨by rw [Module.finrank_eq_card_basis D.b]; simp⟩
  have h0 : D.b 0 = 1 := D.b0
  have h1 : D.b 1 * D.b 1 = algebraMap F E D.δ := by
    rw [D.b1, ← pow_two, D.sq]
  obtain ⟨η, hq, hη⟩ := UpperTheory.ConvolutionTheory.R2.C.etaQuad F E
  have hone : ∀ a, GlobalTheory.IdeleNormChar.normSign E a = 1 → η.1 a = 1 := by
    intro a ha
    refine Units.ext ?_
    rw [hη a, ha]
    simp
  have hsign : ∀ a, η.1 a = 1 → GlobalTheory.IdeleNormChar.normSign E a = 1 := by
    intro a ha
    have h := hη a
    rw [ha] at h
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e
    · exact e
    · rw [e] at h
      norm_num at h
  have hmem : ∀ z : (A E)ˣ, ideleNorm F E z ∈ GlobalTheory.QuadSymbol.normGroup F E (A F) := by
    intro z
    obtain ⟨s, t, hst⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D (ideleNorm F E z)).2 ⟨z, rfl⟩
    exact (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).2 ⟨s, t, hst⟩
  refine ⟨η, hq, ?_, ?_, ?_⟩
  · intro a
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hη a]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;> rw [e] <;> simp
  · intro z
    exact hone _ (GlobalTheory.IdeleNormChar.normSign_of_mem E (hmem z))
  · intro a ha
    obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 (hsign a ha)
    obtain ⟨s, u, hsu⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).1 ht
    obtain ⟨z, hz⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D _).1 ⟨s, u, hsu⟩
    refine ⟨(t : F), z, t.ne_zero, ?_⟩
    rw [hz]
    have : a = GlobalTheory.QuadSymbol.toUnits F (A F) t * (a / GlobalTheory.QuadSymbol.toUnits F (A F) t) := by
      rw [mul_div_cancel]
    exact congrArg Units.val this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GenRel
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GrpRel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 hiding mD_val wW_val
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

section
variable {F : Type} [Field F] [NumberField F]

private lemma nU_val (b : A F) : (nU b).1 = !![1, b; 0, 1] := rfl
private lemma mD_val (a : (A F)ˣ) : (mD a).1 = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl
private lemma wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

private lemma sl_ext {g h : G1 F} (e : g.1 = h.1) : g = h := Subtype.ext e

private lemma sl_of {g h : G1 F} {p q r s : A F} (e : h.1 = !![p, q; r, s])
    (h00 : g.1 0 0 = p) (h01 : g.1 0 1 = q) (h10 : g.1 1 0 = r) (h11 : g.1 1 1 = s) : g = h := by
  apply sl_ext
  rw [e, Matrix.eta_fin_two g.1, h00, h01, h10, h11]

private lemma det_eq (g : G1 F) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma nm_val (b : A F) (a : (A F)ˣ) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, mD_val, Matrix.mul_fin_two]
  simp

private lemma cell_val (b b' : A F) (a : (A F)ˣ) :
    (nU b * mD a * wW F * nU b').1 =
      !![-(b * ((a⁻¹ : (A F)ˣ) : A F)), (a : A F) - b * ((a⁻¹ : (A F)ˣ) : A F) * b';
        -((a⁻¹ : (A F)ˣ) : A F), -(((a⁻¹ : (A F)ˣ) : A F) * b')] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, nm_val, wW_val, nU_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  simp
  ring_nf

private lemma rel_part : Rel (nU (F := F)) mD (wW F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Group.isUnit _⟩
  · apply sl_ext
    simp [nU_val, Matrix.one_fin_two]
  · intro b c
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, nU_val, nU_val, Matrix.mul_fin_two]
    simp [add_comm]
  · apply sl_ext
    simp [mD_val, Matrix.one_fin_two]
  · intro a a'
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, mD_val, mD_val, mD_val, Matrix.mul_fin_two]
    simp [mul_comm]
  · intro a b
    apply sl_ext
    have he : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
    rw [Matrix.SpecialLinearGroup.coe_mul, nm_val, mD_val, nU_val, Matrix.mul_fin_two]
    have hq : (a : A F) ^ 2 * b * ((a⁻¹ : (A F)ˣ) : A F) = (a : A F) * b := by
      linear_combination ((a : A F) * b) * he
    simp [hq]
  · intro a
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, mD_val, mD_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp

private lemma gauss_part : Gauss (nU (F := F)) mD (wW F) := by
  intro t
  apply sl_ext
  have he : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := t.mul_inv
  rw [cell_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, nU_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [he]

private lemma tri_part (g : G1 F) : g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a := by
  constructor
  · intro h
    have h' : g.1 1 0 = 0 := h
    have hd := det_eq g
    rw [h', mul_zero, sub_zero] at hd
    have hd' : g.1 1 1 * g.1 0 0 = 1 := by rw [mul_comm]; exact hd
    refine ⟨g.1 0 1 * g.1 0 0, ⟨g.1 0 0, g.1 1 1, hd, hd'⟩, ?_⟩
    refine sl_of (nm_val _ _) rfl ?_ h' rfl
    show g.1 0 1 = g.1 0 1 * g.1 0 0 * g.1 1 1
    linear_combination (-g.1 0 1) * hd
  · rintro ⟨b, a, rfl⟩
    show (nU b * mD a).1 1 0 = 0
    rw [nm_val]
    simp

private lemma tri_uniq (b b' : A F) (a a' : (A F)ˣ) (e : nU b * mD a = nU b' * mD a') : b = b' ∧ a = a' := by
  have h := congrArg Subtype.val e
  rw [nm_val, nm_val] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  have ha : a = a' := Units.ext h00
  subst ha
  exact ⟨(Units.mul_left_inj _).1 h01, rfl⟩

private lemma cell_part (g : G1 F) : IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  constructor
  · rintro ⟨c, hc⟩
    have hc' : g.1 1 0 = (c : A F) := hc.symm
    have he : (c : A F) * ((c⁻¹ : (A F)ˣ) : A F) = 1 := c.mul_inv
    have hd := det_eq g
    rw [hc'] at hd
    refine ⟨g.1 0 0 * ((c⁻¹ : (A F)ˣ) : A F), -c⁻¹, g.1 1 1 * ((c⁻¹ : (A F)ˣ) : A F), ?_⟩
    refine sl_of (cell_val _ _ _) ?_ ?_ ?_ ?_
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 0 0) * he
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) ^ 2)) * hd +
        (-((c⁻¹ : (A F)ˣ) : A F) - g.1 0 1 * ((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) + 1)) * he
    · simp only [inv_neg, inv_inv, Units.val_neg, neg_neg]
      exact hc'
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 1 1) * he
  · rintro ⟨b, a, b', rfl⟩
    show IsUnit ((nU b * mD a * wW F * nU b').1 1 0)
    rw [cell_val]
    simp
end

theorem UpperTheory.ConvolutionTheory.R2.C.grpRel :
    ∀ (F : Type) [Field F] [NumberField F], Rel (nU (F := F)) mD (wW F) ∧ Gauss (nU (F := F)) mD (wW F) ∧
    (∀ g : G1 F, g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a) ∧ (∀ (b b' : A F) a a', nU b * mD a = nU b' * mD a' → b = b' ∧ a = a') ∧
    ∀ g : G1 F, IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  intro F _ _
  exact ⟨rel_part, gauss_part, tri_part, tri_uniq, cell_part⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private def upperP (F : Type) [Field F] [NumberField F] : Subgroup (G1 F) where
  carrier := {g | g 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    have hg' : g.1 1 0 = 0 := hg
    have hh' : h.1 1 0 = 0 := hh
    show (g * h).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg', hh']
    simp
  one_mem' := by
    show (1 : G1 _).1 1 0 = 0
    simp
  inv_mem' := by
    intro g hg
    have hg' : g.1 1 0 = 0 := hg
    show (g⁻¹).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hg']

private theorem bor {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (b b' : A F) (a a' : (A F)ˣ) :
    (N b * M a) * (N b' * M a') = N (b + (a : A F) ^ 2 * b') * M (a * a') := by
  rw [hR.N_add, hR.M_mul]
  calc N b * M a * (N b' * M a') = N b * (M a * N b') * M a' := by simp only [mul_assoc]
    _ = _ := by rw [hR.MN]; simp only [mul_assoc]

private theorem gen_rel {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (hG : Gauss N M W) (t a : (A F)ˣ) :
    W * (N (t : A F) * M a) * W =
      (N (-((t⁻¹ : (A F)ˣ) : A F)) * M (-t⁻¹)) * W * (N (-((t⁻¹ : (A F)ˣ) : A F)) * M a⁻¹) := by
  have h1 : M a * W = W * M a⁻¹ := by
    have := hR.WM a⁻¹
    rw [inv_inv] at this
    exact this.symm
  calc W * (N (t : A F) * M a) * W = W * N (t : A F) * (M a * W) := by simp only [mul_assoc]
    _ = W * N (t : A F) * W * M a⁻¹ := by rw [h1]; simp only [mul_assoc]
    _ = _ := by rw [hG t]; simp only [mul_assoc]

private theorem w_small {F : Type} [Field F] [NumberField F] {b c : A F} {a d : (A F)ˣ}
    (h : wW F * (nU b * mD a) = nU c * mD d * wW F) : b = 0 ∧ c = 0 ∧ d = a⁻¹ := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] :=
    congrArg Subtype.val h
  have e11 := congrFun (congrFun h' 1) 1
  have e01 := congrFun (congrFun h' 0) 1
  have e00 := congrFun (congrFun h' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11 e01 e00
  exact ⟨e11, e00, (Units.ext e01).symm⟩

private theorem w_big {F : Type} [Field F] [NumberField F] {b c c' : A F} {a d d' : (A F)ˣ}
    (h : wW F * (nU b * mD a) * wW F = nU c * mD d * wW F * (nU c' * mD d')) : IsUnit b := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) * !![(0 : A F), 1; -1, 0] =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] *
        (!![1, c'; 0, 1] * !![(d' : A F), 0; 0, ((d'⁻¹ : (A F)ˣ) : A F)]) :=
    congrArg Subtype.val h
  have e := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  have hu : IsUnit (b * ((a⁻¹ : (A F)ˣ) : A F)) := by
    rw [e, ← Units.val_mul]
    exact (d⁻¹ * d').isUnit.neg
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.ConvolutionTheory.R2.C.chunk :
    ∀ (F : Type) [Field F] [NumberField F] (H : Type) [Monoid H] (N : A F → H) (M : (A F)ˣ → H) (W : H), Rel N M W → Gauss N M W →
    (∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0)) →
    ∃ Φ : G1 F →* H, (∀ b, Φ (nU b) = N b) ∧ (∀ a, Φ (mD a) = M a) ∧ Φ (wW F) = W := by
  intro F _ _ H _ N M W hR hG hgen
  obtain ⟨gR, gG, gP, gU, gC⟩ := grpRel F
  obtain ⟨N', hN'⟩ : ∃ N' : A F → Hˣ, ∀ b, (N' b : H) = N b :=
    ⟨fun b => ⟨N b, N (-b), by rw [← hR.N_add]; simp [hR.N_zero],
      by rw [← hR.N_add]; simp [hR.N_zero]⟩, fun _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : (A F)ˣ → Hˣ, ∀ a, (M' a : H) = M a :=
    ⟨fun a => ⟨M a, M a⁻¹, by rw [← hR.M_mul]; simp [hR.M_one],
      by rw [← hR.M_mul]; simp [hR.M_one]⟩, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W' : Hˣ, (W' : H) = W := hR.W_unit
  have memP : ∀ b a, nU b * mD a ∈ upperP F := fun b a => (gP _).2 ⟨b, a, rfl⟩
  have memN : ∀ b, nU b ∈ upperP F := fun b => (gP _).2 ⟨b, 1, by rw [gR.M_one, mul_one]⟩
  have memM : ∀ a, mD a ∈ upperP F := fun a => (gP _).2 ⟨0, a, by rw [gR.N_zero, one_mul]⟩
  have hex : ∀ p : upperP F, ∃ b a, (p : G1 F) = nU b * mD a := fun p => (gP p).1 p.2
  choose bb aa hba using hex
  have huniq : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → bb p = b ∧ aa p = a :=
    fun p b a h => gU _ _ _ _ ((hba p).symm.trans h)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : upperP F →* Hˣ, ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a →
      ρ p = N' b * M' a := by
    refine ⟨MonoidHom.mk' (fun p => N' (bb p) * M' (aa p)) ?_, ?_⟩
    · intro p q
      obtain ⟨e1, e2⟩ := huniq (p * q) (bb p + (aa p : A F) ^ 2 * bb q) (aa p * aa q) (by
        rw [Subgroup.coe_mul, hba p, hba q, bor gR])
      rw [e1, e2]
      apply Units.ext
      simp only [Units.val_mul, hN', hM']
      exact (bor hR _ _ _ _).symm
    · intro p b a h
      obtain ⟨e1, e2⟩ := huniq p b a h
      simp [e1, e2]
  have ρv : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → ((ρ p : Hˣ) : H) = N b * M a := by
    intro p b a h
    rw [hρ p b a h, Units.val_mul, hN', hM']
  have c1 : ∀ p q : upperP F, wW F * p = q * wW F → W' * ρ p = ρ q * W' := by
    intro p q h
    rw [hba p, hba q] at h
    obtain ⟨hb, hc, hd⟩ := w_small h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ρv p _ _ (hba p), ρv q _ _ (hba q), hb, hc, hd, hW', hR.N_zero,
      one_mul, one_mul]
    exact hR.WM _
  have c2 : ∀ p : upperP F, (∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂) →
      ∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂ ∧ W' * ρ p * W' = ρ p₁ * W' * ρ p₂ := by
    rintro p ⟨p₁, p₂, h⟩
    rw [hba p, hba p₁, hba p₂] at h
    obtain ⟨t, ht⟩ := w_big h
    refine ⟨⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩, ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩, ?_, ?_⟩
    · rw [hba p, ← ht]
      exact gen_rel gR gG t (aa p)
    · apply Units.ext
      simp only [Units.val_mul]
      rw [ρv p _ _ (hba p), ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩ _ _ rfl,
        ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩ _ _ rfl, hW', ← ht]
      exact gen_rel hR hG t (aa p)
  have c3 : ∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, ∃ p₁ p₂ : upperP F, g * u = p₁ * wW F * p₂ := by
    intro s
    obtain ⟨u, hu⟩ := hgen s
    refine ⟨u, fun g hg => ?_⟩
    obtain ⟨b, a, b', e⟩ := (gC _).1 (hu g hg)
    exact ⟨⟨_, memP b a⟩, ⟨_, memN b'⟩, e⟩
  obtain ⟨Φ, h1, h2⟩ := GlobalTheory.bigCell_hom (G1 F) Hˣ (upperP F) (wW F) ρ W' c1 c2 c3
  refine ⟨(Units.coeHom H).comp Φ, fun b => ?_, fun a => ?_, ?_⟩
  · have := h1 ⟨_, memN b⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (nU b) = ρ ⟨_, memN b⟩ from this,
      ρv ⟨_, memN b⟩ b 1 (by rw [gR.M_one, mul_one]), hR.M_one, mul_one]
  · have := h1 ⟨_, memM a⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (mD a) = ρ ⟨_, memM a⟩ from this,
      ρv ⟨_, memM a⟩ 0 a (by rw [gR.N_zero, one_mul]), hR.N_zero, one_mul]
  · simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [h2, hW']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousFiniteAdeleEmbed
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma exists_cube {ι Y : Type} [Finite ι] [TopologicalSpace Y] {y₀ : Y} {W : Set (ι → Y)}
    (hW : W ∈ 𝓝 (fun _ => y₀ : ι → Y)) :
    ∃ U ∈ 𝓝 y₀, ∀ y : ι → Y, (∀ i, y i ∈ U) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun y hy => hsub fun i _ => Set.mem_iInter.1 (hy i) i⟩

private noncomputable def fin0 {F : Type} [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F) : A F := (0, x)

private lemma continuous_finiteAdeleEmbed {F : Type} [Field F] [NumberField F] :
    Continuous (fin0 (F := F)) :=
  show Continuous fun x : FiniteAdeleRing (𝓞 F) F => ((0, x) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from
    continuous_const.prodMk continuous_id

private noncomputable def oneAdd {F : Type} [Field F] [NumberField F]
    (X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (A F) :=
  fun i j => (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + fin0 (X (i, j))

private lemma continuous_oneAdd {F : Type} [Field F] [NumberField F] :
    Continuous (oneAdd (F := F)) := by
  refine continuous_matrix fun i j => ?_
  exact continuous_const.add (continuous_finiteAdeleEmbed.comp (continuous_apply _))

private lemma oneAdd_zero {F : Type} [Field F] [NumberField F] :
    oneAdd (F := F) (fun _ => 0) = 1 := by
  ext i j : 2
  change (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + 0 = _
  exact add_zero _

theorem UpperTheory.ConvolutionTheory.R2.C.unrOf :
    ∀ (F : Type) [Field F] [NumberField F] (P : G1 F → Prop), (∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → P g) → ∀ᶠ v in cofinite, ∀ g, At v g → IntAt v g → P g := by
  intro F _ _ P h
  have hind : IsInducing (fun g : G1 F => (g : Matrix (Fin 2) (Fin 2) (A F))) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing
  rw [Filter.Eventually, hind.nhds_eq_comap, Filter.mem_comap] at h
  obtain ⟨S, hS, hSP⟩ := h
  have h1 : S ∈ 𝓝 (oneAdd (F := F) fun _ => 0) := by
    rw [oneAdd_zero]; simpa using hS
  have h2 := continuous_oneAdd.continuousAt.preimage_mem_nhds h1
  obtain ⟨U, hU, hUS⟩ := exists_cube h2
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hU
  have hfin : ((idealSupport J : Finset _) : Set (HeightOneSpectrum (𝓞 F))).Finite :=
    Finset.finite_toSet _
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  by_contra hvJ
  apply hv
  intro g hg hint
  have hone : ∀ i j, ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, hij]
    · simp only [Matrix.one_apply, hij, if_false, Prod.snd_zero]
      change (0 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      exact zero_mem _
  set X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F :=
    fun p => (g p.1 p.2).2 - ((1 : Matrix (Fin 2) (Fin 2) (A F)) p.1 p.2).2 with hX
  have hXm : ∀ p, X p ∈ U := by
    intro p
    apply hJ
    rw [SetLike.mem_coe, mem_idealFiniteAdeles]
    intro w
    by_cases hw : w = v
    · subst hw
      rw [count_eq_zero_of_not_mem_idealSupport J (by simpa using hvJ)]
      simp only [neg_zero, WithZero.exp_zero]
      exact sub_mem (hint p.1 p.2) (hone p.1 p.2)
    · have : X p w = 0 := by
        have := hg.2 w hw p.1 p.2
        simp only [hX]
        exact sub_eq_zero.2 this
      rw [this, map_zero]
      exact zero_le
  have hgX : (g : Matrix (Fin 2) (Fin 2) (A F)) = oneAdd X := by
    ext i j : 2
    apply Prod.ext
    · have : (oneAdd X i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 + 0 := rfl
      rw [this, add_zero]
      exact hg.1 i j
    · have : (oneAdd X i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 + X (i, j) := rfl
      rw [this, hX]
      simp
  apply hSP
  · show (g : Matrix (Fin 2) (Fin 2) (A F)) ∈ S
    rw [hgX]
    exact hUS X hXm
  · exact hg.1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.AbMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

private theorem exHom {G V : Type} [Group G] (S : Submodule ℂ (V → ℂ)) (c : G → ℂ) (a : G → V → V)
    (c1 : c 1 = 1) (cm : ∀ g h, c (g * h) = c g * c h) (a1 : ∀ v, a 1 v = v)
    (am : ∀ g h v, a (g * h)⁻¹ v = a h⁻¹ (a g⁻¹ v))
    (hm : ∀ g, ∀ f ∈ S, (fun v => f (a g⁻¹ v)) ∈ S) :
    ∃ L : G →* Module.End ℂ S, ∀ g f v, (L g f).1 v = c g * f.1 (a g⁻¹ v) := by
  have hmem : ∀ (g : G) (f : S), (fun v => c g * f.1 (a g⁻¹ v)) ∈ S := fun g f =>
    S.smul_mem (c g) (hm g f.1 f.2)
  let T : G → Module.End ℂ S := fun g =>
    { toFun := fun f => ⟨_, hmem g f⟩
      map_add' := by
        intro f f'
        apply Subtype.ext
        funext v
        simp [mul_add]
      map_smul' := by
        intro k f
        apply Subtype.ext
        funext v
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨{ toFun := T, map_one' := ?_, map_mul' := ?_ }, fun g f v => rfl⟩
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext v
    show c 1 * f.1 (a 1⁻¹ v) = f.1 v
    rw [c1, one_mul, inv_one, a1]
  · intro g h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext v
    show c (g * h) * f.1 (a (g * h)⁻¹ v) = c g * (c h * f.1 (a h⁻¹ (a g⁻¹ v)))
    rw [cm, am, mul_assoc]

private theorem abMul {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : ab (s * t) = ab s * ab t := by
  simp only [ab, map_mul]
  rfl

private theorem abOne {F : Type} [Field F] [NumberField F] : ab (1 : (A F)ˣ) = 1 := by
  simp only [ab, map_one]
  rfl

private theorem nuMul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (g h : GL (Fin 2) (A E)) : nu F (g * h) = nu F g * nu F h := by
  simp only [nu, map_mul]

private theorem nuOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    nu F (1 : GL (Fin 2) (A E)) = 1 := by
  simp only [nu, map_one]

theorem UpperTheory.ConvolutionTheory.R2.D.lEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ L : GL (Fin 2) (A E) →* Module.End ℂ (S4 F),
    ∀ h φ v, (L h φ).1 v = (((ab (nu F h))⁻¹ : ℝ) : ℂ) * φ.1 (D.act h⁻¹ v) := by
  intro F E _ _ _ _ _ D
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  refine exHom (schwartzBruhatPi (K := F) (ι := Fin 4)) (fun h => (((ab (nu F h))⁻¹ : ℝ) : ℂ)) D.act ?_ ?_ ?_ ?_ ?_
  · show (((ab (nu F (1 : GL (Fin 2) (A E))))⁻¹ : ℝ) : ℂ) = 1
    rw [nuOne, abOne]
    simp
  · intro g h
    show (((ab (nu F (g * h)))⁻¹ : ℝ) : ℂ) = (((ab (nu F g))⁻¹ : ℝ) : ℂ) * (((ab (nu F h))⁻¹ : ℝ) : ℂ)
    rw [nuMul, abMul, mul_inv]
    push_cast
    rfl
  · intro v
    rw [hρ, map_one]
    exact Matrix.one_mulVec v
  · intro g h v
    rw [hρ, hρ, hρ, _root_.mul_inv_rev, map_mul]
    exact (Matrix.mulVec_mulVec v _ _).symm
  · intro g f hf
    have h1 := UpperTheory.ConvolutionTheory.R2.D.sClos F (Fin 4) (ρ g⁻¹) f hf
    have h2 : (fun v => f (D.act g⁻¹ v)) = fun v => f ((ρ g⁻¹).val *ᵥ v) := by
      funext v
      rw [hρ]
    rw [h2]
    exact h1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActRat
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem mkE_rt (D : Dat F E) (u t : F) :
    D.mkE (rt u) (rt t) = rt (algebraMap F E u + algebraMap F E t * D.θ) := by
  simp only [Dat.mkE, rt, AdeleBaseChange.adeleMap_algebraMap, map_add (f := _), map_mul]

private theorem bar_rt (D : Dat F E) (z : E) : D.bar (rt z) = rt (D.σ z) :=
  AdeleBaseChange.smul_algebraMap D.σ z

private theorem co_rt (D : Dat F E) (z : E) (i : Fin 2) : D.co (rt z) i = rt (D.b.repr z i) :=
  AdeleBaseChange.adeleBasis_repr_algebraMap D.b z i

private theorem herm_rt (D : Dat F E) (ξ : Fin 4 → F) :
    D.herm (fun i => rt (ξ i)) =
      (!![algebraMap F E (ξ 1) + algebraMap F E 0 * D.θ, algebraMap F E (ξ 2) + algebraMap F E (ξ 3) * D.θ;
        algebraMap F E (ξ 2) + algebraMap F E (-ξ 3) * D.θ, algebraMap F E (ξ 0) + algebraMap F E 0 * D.θ]).map
        (algebraMap E (A E)) := by
  have e0 : ∀ u : F, D.mkE (rt u) 0 = rt (algebraMap F E u + algebraMap F E 0 * D.θ) := fun u => by
    rw [← mkE_rt, show (rt (0 : F) : A F) = 0 from map_zero _]
  have e3 : D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (algebraMap F E (ξ 2) + algebraMap F E (-ξ 3) * D.θ) := by
    rw [← mkE_rt, show (rt (-ξ 3) : A F) = -rt (ξ 3) from map_neg _ _]
  ext i j
  fin_cases i <;> fin_cases j
  · exact e0 _
  · exact mkE_rt D _ _
  · exact e3
  · exact e0 _

variable [_root_.NumberField.IsTotallyComplex E]

private theorem ab_nu (γ : GL (Fin 2) E) : ab (nu F (ratGL E 2 γ)) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (ratGL E 2 γ) =
      IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) := Units.ext (by
    change (ratGL E 2 γ).val.det = algebraMap E (A E) γ.val.det
    rw [RingHom.map_det]
    rfl)
  rw [nu, hd, ideleNorm_diagonal, ab, IdeleGroup.ideleModule_diagonal]
  rfl

private theorem act_rat (D : Dat F E) (γ : GL (Fin 2) E) (ξ : Fin 4 → F) :
    ∃ ξ' : Fin 4 → F, D.act (ratGL E 2 γ) (fun i => rt (ξ i)) = fun i => rt (ξ' i) := by
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) E, D.herm (fun i => rt (ξ i)) = X.map (algebraMap E (A E)) := ⟨_, herm_rt D ξ⟩
  have hh : (ratGL E 2 γ).val = γ.val.map (algebraMap E (A E)) := rfl
  have hb : (ratGL E 2 γ).val.map D.bar = (γ.val.map D.σ).map (algebraMap E (A E)) := by
    ext i j
    exact bar_rt D (γ.val i j)
  set P : Matrix (Fin 2) (Fin 2) E := γ.val * X * (γ.val.map D.σ)ᵀ with hP
  have hm : (ratGL E 2 γ).val * D.herm (fun i => rt (ξ i)) * ((ratGL E 2 γ).val.map D.bar)ᵀ =
      P.map (algebraMap E (A E)) := by
    rw [hX, hb, hh, hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  refine ⟨![D.b.repr (P 1 1) 0, D.b.repr (P 0 0) 0, D.b.repr (P 0 1) 0, D.b.repr (P 0 1) 1], ?_⟩
  rw [Dat.act, hm]
  funext i
  fin_cases i
  · exact co_rt D _ _
  · exact co_rt D _ _
  · exact co_rt D _ _
  · exact co_rt D _ _

end

end UpperTheory.ConvolutionTheory.R2.D

theorem UpperTheory.ConvolutionTheory.R2.D.thL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (γ : GL (Fin 2) E) (φ : V4 F → ℂ),
    Th (fun v => (((ab (nu F (ratGL E 2 γ)))⁻¹ : ℝ) : ℂ) * φ (D.act (ratGL E 2 γ)⁻¹ v)) = Th φ := by
  intro F E _ _ _ _ _ _ D γ φ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hmul : ∀ h h' v, D.act (h * h') v = D.act h (D.act h' v) := by
    intro h h' v
    rw [hρ, hρ, hρ, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ v, D.act 1 v = v := by
    intro v
    rw [hρ, map_one, Units.val_one, Matrix.one_mulVec]
  have hinj : Function.Injective (fun (ξ : Fin 4 → F) (i : Fin 4) => (rt (ξ i) : A F)) := by
    intro a b hab
    funext i
    exact AdeleRing.algebraMap_injective (𝓞 F) F (congrFun hab i)
  choose f hf using fun (g : GL (Fin 2) E) (ξ : Fin 4 → F) => UpperTheory.ConvolutionTheory.R2.D.act_rat D g ξ
  have hinv : ∀ (g : GL (Fin 2) E) ξ, f g⁻¹ (f g ξ) = ξ := by
    intro g ξ
    apply hinj
    change (fun i => (rt (f g⁻¹ (f g ξ) i) : A F)) = fun i => rt (ξ i)
    rw [← hf g⁻¹ (f g ξ), ← hf g ξ, ← hmul, ← map_mul, inv_mul_cancel, map_one, hone]
  let e : (Fin 4 → F) ≃ (Fin 4 → F) :=
    ⟨f γ⁻¹, f γ, fun ξ => by simpa using hinv γ⁻¹ ξ, hinv γ⟩
  simp only [Th, UpperTheory.ConvolutionTheory.R2.D.ab_nu, inv_one, Complex.ofReal_one, one_mul, ← map_inv, hf]
  exact e.tsum_eq fun ξ => φ fun i => rt (ξ i)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.weilEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), St.WeilEx D := by
  intro F E _ _ _ _ _ _ _ D
  have hδ : D.δ ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    intro h
    have := D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨η, hq, hsq, hn, hk⟩ := etaEx F E D
  obtain ⟨O⟩ := opsEx F D.δ η.1 hδ
  obtain ⟨Om, h1, h2, h3⟩ := chunk F _ O.N O.M O.W (opsRel F D.δ η.1 O hδ hsq)
    (opsGauss F D.δ η.1 O hδ hsq (idxEta F E D η.1 hsq hk)) (generic F)
  have hO : IsOm D.δ η.1 Om :=
    ⟨fun b φ v => h1 b ▸ O.N_apply b φ v, fun a φ v => h2 a ▸ O.M_apply a φ v, fun φ v => h3 ▸ O.W_apply φ v⟩
  obtain ⟨L, hL⟩ := UpperTheory.ConvolutionTheory.R2.D.lEx F E D
  exact ⟨{
    η := η, Om := Om, L := L, quad := hq, η_sq := hsq, η_norm := hn, Om_n := hO.n, Om_m := hO.m, Om_w := hO.w, L_apply := hL
    comm := UpperTheory.ConvolutionTheory.R2.D.comm F E D η.1 Om L hn hO.n hO.m hO.w hL
    th_Om := thOm F D.δ η.1 Om hδ hO
    th_L := fun γ φ => by
      rw [← UpperTheory.ConvolutionTheory.R2.D.thL F E D γ φ.1]
      exact congrArg Th (funext (hL _ φ))
    level := level F D.δ η.1 Om hO
    unr := fun φ => unrOf F _ (level F D.δ η.1 Om hO φ)
    cont := cont F D.δ η.1 Om η.2.1 hO }⟩

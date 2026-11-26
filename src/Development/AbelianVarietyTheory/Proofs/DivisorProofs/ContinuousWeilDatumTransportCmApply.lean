module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWeilDatumTransportCmApply
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWeilDatumTransportCmApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.WeilContF

open Formalism.IndefR.DatumF

theorem continuous_transportF_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ z : κ → AF F, Continuous fun p => om p Φ z := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
    Φ hΦ z
  have hstd := hω.std
  have hψ := hstd.1

  have hth : ∀ w, Continuous fun p => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w := by
    intro w
    have hex : ∀ p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB),
        ∃ (g : GAF σ JS) (h : GAF σ JT),
          mtF σ JT h = p.1.1.1 ∧ mtF σ JS g = (p.2⁻¹).1.1ᵀ := fun p =>
      GlobalTheory.T.exists_unitaryPair_partner_cmExtension F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB p.1 p.2
    choose g h hh hg using hex
    have hθ : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
      ⟨GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        GlobalTheory.T.continuous_thetaTransform_schwartz_cm F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        GlobalTheory.T.contDiff_thetaTransform_archimedean_cm F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ⟩
    have hhU : ∀ p, matHomF σ JT (h p) = p.1.1 := fun p => Units.ext (hh p)
    have hgU : ∀ p, (matHomF σ JS (g p))⁻¹.1 = p.2.1.1ᵀ := by
      intro p
      apply Units.inv_eq_of_mul_eq_one_right
      change mtF σ JS (g p) * _ = 1
      rw [hg p, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
    have hcH' : Continuous fun p => matHomF σ JT (h p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JT (h p)) = fun p => p.1.1.1 := funext fun p => hh p
        rw [e]
        exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
      · have e : (fun p => (matHomF σ JT (h p))⁻¹.1) = fun p => (p.1.1)⁻¹.1 := funext fun p => by rw [hhU p]
        rw [e]
        exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
    have hcG' : Continuous fun p => matHomF σ JS (g p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JS (g p)) = fun p => ((p.2.1)⁻¹).1ᵀ := funext fun p => hg p
        rw [e]
        exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
      · have e : (fun p => (matHomF σ JS (g p))⁻¹.1) = fun p => p.2.1.1ᵀ := funext hgU
        rw [e]
        exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
    have hcH : Continuous h := continuous_induced_rng.2 hcH'
    have hcG : Continuous g := continuous_induced_rng.2 hcG'
    have heq : ∀ p, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w =
        ω (g p, h p) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) w := fun p =>
      congrFun (htr p.1 p.2 (g p) (h p) (hh p) (hg p) Φ hΦ).2 w
    exact ((hω.om_cont _ hθ w).comp (hcG.prodMk hcH)).congr fun p => (heq p).symm
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    GlobalTheory.T.exists_local_finiteDimensional_finite_parts_weil_transport F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, pureA F (f p i) (g i) := fun p hp => by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      GlobalTheory.T.weilDatumTransport_archimedeanSlice_schwartz_bounds F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
        Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.SchwartzMajorant.exists_summable_majorant F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → F) → AddChar (κ → AF F) ℂ := fun a =>
    B.ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = B.ψ ((fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
      B.ψ (⅟(2 : AF F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
    intro p y'
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.2.2.2
    refine ⟨Pi.single i (algebraMap F (AF F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF F, B.ψ (-t) * B.ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul B.ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, B.ψ (-(⅟(2 : AF F) * (z ⬝ᵥ y'))) *
          GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := GlobalTheory.continuousAt_charSeries_coef_zero e (fun a y => hψ.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL

end GlobalTheory.WeilContF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWeilDatumTransportCmApplyStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_weilDatum_transport_cm_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ z : κ → AF F, Continuous fun p => om p Φ z := by
  first | exact @GlobalTheory.WeilContF.continuous_transportF_apply | exact GlobalTheory.WeilContF.continuous_transportF_apply | (intros; apply GlobalTheory.WeilContF.continuous_transportF_apply <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlace
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblSplitForm

section Abstract

variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}

theorem exists_ext_form (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) (l0 : M →ₗ[ℂ] ℂ) (gen : Set M)
    (hinv : ∀ u ∈ Y, ∀ p ∈ gen, l0 (ρ u p) = l0 p) :
    ∃ ℓ : M →ₗ[ℂ] ℂ, (∀ u ∈ Y, ∀ g ∈ Θ, ℓ (ρ u g) = ℓ g) ∧ ∀ p ∈ gen, ℓ p = l0 p := by
  classical
  let P : Submodule ℂ M := Submodule.span ℂ gen
  let K : Submodule ℂ M := Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g}
  have hl0P : ∀ u ∈ Y, ∀ p ∈ P, l0 (ρ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf => exact hinv u hu f hf
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, -⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero hadd h0 hsm hmK
    have h1 : l0 (∑ j ∈ s, ρ (y j) m) = (s.card : ℂ) * l0 m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc
  let fP : M →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : M →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : M) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : M) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu g hg => ?_, fun p hp => ?_⟩
  · have hk : ρ u g - g ∈ K := Submodule.subset_span ⟨u, hu, g, hg, rfl⟩
    have hz : ρ u g - g ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (ρ u g - g) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp' : p ∈ P := Submodule.subset_span hp
    have hz : p ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp'
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp'⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 p + 0 = _
    rw [add_zero]

end Abstract

def conjForm {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun g := conj (ℓ (fun y => conj (g y)))
  map_add' a b := by
    have : (fun y => conj ((a + b) y)) = (fun y => conj (a y)) + fun y => conj (b y) := by
      funext y; simp
    rw [this, map_add (f := _), map_add (f := _)]
  map_smul' c a := by
    have : (fun y => conj ((c • a) y)) = conj c • fun y => conj (a y) := by
      funext y; simp
    rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]

theorem conjForm_mul {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (b : X → ℂ) :
    conjForm ℓ (fun y => c * conj (b y)) = c * conj (ℓ b) := by
  have : (fun y => conj (c * conj (b y))) = conj c • b := by
    funext y; simp
  show conj (ℓ (fun y => conj (c * conj (b y)))) = _
  rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]

open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def joinR (x₁ x₂ : WOF F E nS nT) : WOF F E nS (nT + nT) := (Matrix.fromRows x₁ x₂).submatrix finSumFinEquiv.symm id

theorem topR_joinR (x₁ x₂ : WOF F E nS nT) : topR (joinR x₁ x₂) = x₁ := by
  ext i j
  simp [joinR, topR, Matrix.submatrix_apply]

theorem botR_joinR (x₁ x₂ : WOF F E nS nT) : botR (joinR x₁ x₂) = x₂ := by
  ext i j
  show Matrix.fromRows x₁ x₂ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) j = x₂ i j
  rw [Equiv.symm_apply_apply]; rfl

def dblForm (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ :=
  ℓ ∘ₗ LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y))

theorem dblForm_deltaT (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) (a b : WOF F E nS nT → ℂ) :
    dblForm ℓ (deltaT a b) = ℓ a * conj (ℓ b) := by
  have h : (LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y)))
      (deltaT a b) = conj (ℓ b) • a := by
    funext x₁
    have e : (LinearMap.funLeft ℂ ℂ (fun y : WOF F E nS nT => joinR x₁ (-y))) (deltaT a b) =
        fun y => a x₁ * conj (b y) := by
      funext y
      simp [LinearMap.funLeft_apply, deltaT_apply, topR_joinR, botR_joinR]
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, e, conjForm_mul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dblForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DblSplitForm

namespace GlobalTheory.DblSplitForm
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

theorem exists_invForm_dbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
  obtain ⟨f₀, hf₀, hf₀0⟩ : ∃ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 :=
    GlobalTheory.T.exists_nonzero_thetaFun_oriented_model_cm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ₁, hℓ₁, f, hf, hℓf⟩ := GlobalTheory.T.exists_splitPlace_conjHeisenberg_invariantForm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  have hheis := GlobalTheory.DblHeis.heisOF_dblG_deltaT F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ, h1, h2⟩ := exists_ext_form (Y := GlobalTheory.SplitInvFormF.conjHalf σ e nS (nT + nT))
    (ρ := GlobalTheory.SplitInvFormF.heisL σ JS (dblG JT) ξ₀ B.ψ)
    (Θ := {g | IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g})
    (fun x hx x' hx' g => by
      show heisOF σ JS (dblG JT) ξ₀ B.ψ x (heisOF σ JS (dblG JT) ξ₀ B.ψ x' g) = heisOF σ JS (dblG JT) ξ₀ B.ψ (x + x') g
      rw [GlobalTheory.SplitInvFormF.heisOF_heisOF, GlobalTheory.SplitInvFormF.symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun g => GlobalTheory.SplitInvFormF.heisOF_zero g)
    (fun u hu g hg => GlobalTheory.SplitInvFormF.exists_nsmul_fix he hu hg)
    (dblForm ℓ₁) {p | ∃ a b, IsThetaFunOF σ JS JT ξ₀ B.ψ a ∧ IsThetaFunOF σ JS JT ξ₀ B.ψ b ∧ p = deltaT a b}
    (fun u hu p hp => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hp
      have hu' : ∀ i j, cAF σ e * u i j = u i j := hu
      have ht : ∀ i j, cAF σ e * topR u i j = topR u i j := fun i j => hu' _ _
      have hb' : ∀ i j, cAF σ e * (-botR u) i j = (-botR u) i j := fun i j => by
        show cAF σ e * -(u _ j) = -(u _ j)
        rw [mul_neg, hu']
      show dblForm ℓ₁ (heisOF σ JS (dblG JT) ξ₀ B.ψ u (deltaT a b)) = dblForm ℓ₁ (deltaT a b)
      rw [hheis, dblForm_deltaT, dblForm_deltaT, hℓ₁ _ ht a ha, hℓ₁ _ hb' b hb])
  refine ⟨ℓ, fun u hu g hg => h1 u hu g hg, f, f, hf, hf, ?_⟩
  rw [h2 _ ⟨f, f, hf, hf, rfl⟩, dblForm_deltaT]
  exact mul_ne_zero hℓf ((map_ne_zero _).2 hℓf)

end GlobalTheory.DblSplitForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlaceStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_invariant_form_doubled_space_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  first | exact @GlobalTheory.DblSplitForm.exists_invForm_dbl | exact GlobalTheory.DblSplitForm.exists_invForm_dbl | (intros; apply GlobalTheory.DblSplitForm.exists_invForm_dbl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameAtSmallPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicIrreducibleOfNotDvdDiscr
namespace GlobalTheory

open Polynomial NumberField

theorem cyclotomic_irreducible_of_not_dvd_discr :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ NumberField.discr E →
      Irreducible (Polynomial.cyclotomic l E) := by
  intro E _ _ l hl hd
  refine ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt hl fun P hP hlP => ?_
  exact (not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.1 hl)).1 hd P hP
    (by simpa using hlP)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoOrderLOfCyclotomicIrreducible
namespace GlobalTheory

open Polynomial in
theorem no_order_l_of_cyclotomic_irreducible :
    ∀ (E : Type) [Field E] [CharZero E] (l N : ℕ) (g : Matrix (Fin N) (Fin N) E),
      l.Prime → Irreducible (Polynomial.cyclotomic l E) → N + 1 < l → g ^ l = 1 → g = 1 := by
  intro E _ _ l N g hl hirr hN hg
  haveI : Fact l.Prime := ⟨hl⟩
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hdeg : g.charpoly.natDegree = N := by
    simpa using Matrix.charpoly_natDegree_eq_dim g
  have hndvd : ¬ cyclotomic l E ∣ g.charpoly := by
    intro h
    have h1 := Polynomial.natDegree_le_of_dvd h hmon.ne_zero
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl, hdeg] at h1
    omega
  obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 hndvd
  have hev := congrArg (aeval g) hab
  simp only [map_add (f := _), map_mul, map_one, Matrix.aeval_self_charpoly, mul_zero, add_zero] at hev
  have hcyc : aeval g (cyclotomic l E) * (g - 1) = 0 := by
    have := congrArg (aeval g) (Polynomial.cyclotomic_prime_mul_X_sub_one E l)
    simp only [map_mul, map_sub, aeval_X, map_one, map_pow] at this
    rw [this, hg, sub_self]
  have : g - 1 = 0 := by
    calc g - 1 = (aeval g a * aeval g (cyclotomic l E)) * (g - 1) := by rw [hev, one_mul]
      _ = aeval g a * (aeval g (cyclotomic l E) * (g - 1)) := by rw [mul_assoc]
      _ = 0 := by rw [hcyc, mul_zero]
  exact sub_eq_zero.1 this

end GlobalTheory
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.TameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Groups

variable {G Γ : Type} [Group G] [Group Γ]

def conjIn (H J : Subgroup G) (g : G) : Subgroup G where
  carrier := {x | x ∈ H ∧ g⁻¹ * x * g ∈ J}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have := J.mul_mem ha' hb'
    convert this using 1
    group
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have := J.inv_mem ha'
    convert this using 1
    group

def conjInEquiv (H J : Subgroup G) (g : G) : {γ : H // g⁻¹ * (γ : G) * g ∈ J} ≃ conjIn H J g where
  toFun γ := ⟨γ.1.1, γ.1.2, γ.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_conj (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G) (hrep : Bridge.IsReps ι J y)
    (hfin : ∀ i, Finite (Bridge.stab ι J (y i))) (g : G) : Finite {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := by
  obtain ⟨c, ⟨γ₀, k, hg⟩, -⟩ := hrep g
  haveI := hfin c
  let f : Bridge.stab ι J (y c) → {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := fun s =>
    ⟨⟨ι (γ₀ * s * γ₀⁻¹), γ₀ * s * γ₀⁻¹, rfl⟩, by
      have hs : (y c)⁻¹ * ι s * (y c) ∈ J := by
        have := s.2
        simpa [Bridge.stab, Subgroup.mem_comap, MulAut.conj_apply] using this
      have := J.mul_mem (J.mul_mem (J.inv_mem k.2) hs) k.2
      convert this using 1
      rw [hg]
      simp only [map_mul, map_inv]
      group⟩
  refine Finite.of_surjective f ?_
  rintro ⟨⟨_, a, rfl⟩, ha⟩
  refine ⟨⟨γ₀⁻¹ * a * γ₀, ?_⟩, ?_⟩
  · have := J.mul_mem (J.mul_mem k.2 ha) (J.inv_mem k.2)
    simp only [Bridge.stab, Subgroup.mem_comap, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
    convert this using 1
    rw [hg]
    simp only [map_mul, map_inv]
    group
  · apply Subtype.ext
    apply Subtype.ext
    show ι (γ₀ * (γ₀⁻¹ * a * γ₀) * γ₀⁻¹) = ι a
    congr 1
    group

end Groups


set_option maxHeartbeats 1600000 in
theorem rat_eq_one {D : D7} (V : TH.HSp D) (l : ℕ) (hl : l.Prime) (hN : V.rank + 1 < l)
    (hirr : Irreducible (Polynomial.cyclotomic l D.host.E)) (x : Bridge.Gf V) (hx : x ∈ (Bridge.ratF V).range)
    (hxl : x ^ l = 1) : x = 1 := by
  obtain ⟨q, rfl⟩ := hx
  have hq := q.2
  simp only [Formalism.L2.Theta.GQ, GlobalTheoryTheory.GenusMassVolumes.HFinIn, Subgroup.mem_subgroupOf, GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map] at hq
  obtain ⟨u, -, hu⟩ := hq
  let φ : D.host.E →+* GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F))
  have key : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val = u.val.map φ := by
    have hu' : (q.1 : Formalism.L2.Theta.GA D V).1 =
        Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) u := hu.symm
    have h1 : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
        Formalism.UG.bc (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
          (q.1 : Formalism.L2.Theta.GA D V).1 := rfl
    rw [h1, hu']
    ext i j
    rfl
  rcases subsingleton_or_nontrivial (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) with hs | hs
  · apply Subtype.ext
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _
  · have hφ : Function.Injective φ := φ.injective
    have h2 := congrArg (fun z : Bridge.Gf V => (z : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val) hxl
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one] at h2
    rw [key] at h2
    have h3 : φ.mapMatrix (u.val ^ l) = φ.mapMatrix 1 := by
      rw [map_pow, map_one, RingHom.mapMatrix_apply]
      exact h2
    have hu1 : u.val ^ l = 1 := Matrix.map_injective hφ h3
    have hu2 : u.val = 1 :=
      GlobalTheory.no_order_l_of_cyclotomic_irreducible D.host.E l V.rank _ hl hirr hN hu1
    apply Subtype.ext
    apply Units.ext
    rw [key, hu2]
    have h4 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ = 1 := Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)
    rw [h4]
    rfl

theorem tameAt_of_smallAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m)
    (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hNr : P.Nr = (Vc D j).rank) (hS : SmallAt p j P w) :
    TameAt p j w := by
  obtain ⟨hl, hN, hd, -, -⟩ := hS
  intro g
  have hfin : Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} :=
    finite_conj (Bridge.ratF (Vc D j)) (levJ p j (p.R.mu w)) (p.R.B.L j (p.R.mu w)).pres.y (p.R.B.L j (p.R.mu w)).pres.reps
      (fun c => Finite.of_equiv _ ((p.R.B.L j (p.R.mu w)).pres.stabI c).toEquiv) g
  refine ⟨hfin, ?_⟩
  intro hdvd
  haveI : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hl⟩
  rw [Nat.card_congr (conjInEquiv _ _ g)] at hdvd
  haveI : Finite (conjIn (Bridge.ratF (Vc D j)).range (levJ p j (p.R.mu w)) g) := Finite.of_equiv _ (conjInEquiv _ _ g)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Formalism.EigenvalueLevelCeiling.plc w) hdvd
  have hirr := GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr D.host.E (Formalism.EigenvalueLevelCeiling.plc w) hl hd
  have hxl : (x : Bridge.Gf (Vc D j)) ^ (Formalism.EigenvalueLevelCeiling.plc w) = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]
    rfl
  have h1 := rat_eq_one (Vc D j) (Formalism.EigenvalueLevelCeiling.plc w) hl (hNr ▸ hN) hirr x x.2.1 hxl
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  exact hl.one_lt.ne hx

end GlobalTheory.TameStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutationAtSmallPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perm_of_isDC {G : Type} [Group G] (J : Subgroup G) (x : G) (A : Finset G) (h : Bridge.IsDC J x A) (κ : G)
    (hκ : κ ∈ J) : ∃ σ : Equiv.Perm A, ∀ s : A, ((σ s : A) : G)⁻¹ * κ * s ∈ J := by
  classical
  have hex : ∀ s : A, ∃ a : A, (a : G)⁻¹ * (κ * s) ∈ J := by
    intro s
    obtain ⟨k₁, k₂, hs⟩ := h.1 s s.2
    obtain ⟨a, ⟨ha, haJ⟩, -⟩ := h.2 (κ * s) ⟨⟨κ, hκ⟩ * k₁, k₂, by rw [hs]; simp [mul_assoc]⟩
    exact ⟨⟨a, ha⟩, haJ⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [hss] at h1
    have h3 : (s : G)⁻¹ * s' ∈ J := by
      have := J.mul_mem (J.inv_mem h1) h2
      simpa [mul_assoc] using this
    obtain ⟨k₁, k₂, hs'⟩ := h.1 s' s'.2
    have hu := (h.2 s' ⟨k₁, k₂, hs'⟩).unique ⟨s.2, h3⟩ ⟨s'.2, by simp [J.one_mem]⟩
    exact Subtype.ext hu
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun s => ?_⟩
  simpa [mul_assoc] using hf s

theorem map_ev_eq_one_of_loc : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  obtain ⟨e, α, he, -, hs, hxα⟩ := hx
  obtain ⟨v, ε, ⟨a, rfl, -, ha⟩, hf, hv⟩ := GlobalTheory.VacLat.place_of_primeIdem (Or.inl ⟨he, rfl⟩)
  have h0 : ev (a ⊗ₜ[D.host.F] 1) = 0 := by
    refine hev.2.2.1 a fun v' hv' => ha v' ?_
    rintro rfl
    apply hl
    rw [← hv] at hv'
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((l : ℕ) : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hv'
    rwa [map_natCast] at h1
  have h2 := GlobalTheory.SplitHeckeAdj.map_eq_one_of_supp (ev.comp (Formalism.L2.Theta.finPart D)) (e + Formalism.L2.Theta.cA D e)
    (by rw [hf]; exact h0) (Formalism.L2.Theta.mt V α) hs
  rw [hxα]
  exact h2

theorem chi_move {G : Type} [Group G] (J Lc : Subgroup G) (χ : J →* ℂˣ)
    (l2 : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l)
    (l3 : ∀ k : J, (k : G) ∈ Lc → χ k = 1) (κ κ' : J) (a s : G) (ha : a ∈ Lc) (hs : s ∈ Lc)
    (h : (κ' : G) = a⁻¹ * κ * s) : χ κ' = χ κ := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := l2 κ κ.2
  have e1 : κ = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : ((κ' * (⟨k₂, h₂⟩ : J)⁻¹ : J) : G) = a⁻¹ * k₁ * s := by
    show (κ' : G) * k₂⁻¹ = _
    rw [h, hk, mul_assoc a⁻¹, mul_assoc k₁, (hc s hs).eq]; group
  have e3 := l3 (κ' * (⟨k₂, h₂⟩ : J)⁻¹) (e2 ▸ Lc.mul_mem (Lc.mul_mem (Lc.inv_mem ha) hL) hs)
  rw [map_mul, map_inv, mul_inv_eq_one] at e3
  rw [e3, e1, map_mul, l3 ⟨k₁, h₁⟩ hL, one_mul]


set_option maxHeartbeats 1600000 in
theorem levChi_eq_of_loc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ∀ (κ κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i → s ∈ hkA p j t i → (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → levChi p j t κ' = levChi p j t κ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i h1 h2 κ κ' a s ha hs h
  have hb := p.charW.base
  have ha' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i a := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ a ha
  have hs' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i s := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ s hs
  refine hb.fam.tie.elim fun _ x => x.elim fun _ x => x.elim fun _ tie => ?_
  refine (hb.lev.βV j).elim fun c hc => ?_
  rw [one_pow] at hc
  refine ha'.elim fun e x => x.elim fun _ x => ?_
  have he := x.1
  have hsp := (tie.ok t _).1 (show (p.P.A3.A.ok t) × ℕ from i).1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc _ e he
    fun PP hP => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr)
  refine hl.elim fun Lc l => ?_
  have hA : a ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ ha' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  have hS : s ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ hs' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  exact chi_move _ Lc _ l.2.1 l.2.2.1 κ κ' a s hA hS h

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem chi_cancel {K R : Type} [Field K] [CommRing R] (io : K ≃+* ℂ) (emb : R →+* K) (hinj : Function.Injective emb)
    (u u' : Rˣ) (X X' : K) (hXX : X' = X) (hX : X ≠ 0) (c c' : ℂ) (hcc : c' = c) (hc : c ≠ 0)
    (e1 : io (emb u' * X') * c' = 1) (e2 : io (emb u * X) * c = 1) : u' = u := by
  subst hXX hcc
  have e4 := io.injective (mul_right_cancel₀ hc (e1.trans e2.symm))
  exact Units.ext (hinj (mul_right_cancel₀ hX e4))

theorem perm_core (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ)
    (hR : 1 ≤ i.2 ∧ i.2 ≤ (Vc D j).rank) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i), ∀ s : hkA p j t i, ((σ s : hkA p j t i) : Bridge.Gf (Vc D j))⁻¹ * κ * s ∈ levJ p j t := by
  have h : Bridge.IsDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) := (p.R.B.L j t).hecke.hDC i hR
  exact perm_of_isDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) h κ κ.2

theorem perm_gen (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (io : PadicAlgCl l ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ)
    (hev : ∀ τ, EvOk (incOf D e0 b τ) (ev τ)) (hkap : KapEq p j t ev bs rk kap) (hchi : ChiEq p j t io sh kap chi)
    (i : Ix p j t l N) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i.1), ∀ s : hkA p j t i.1, ∃ κ' : levJ p j t,
      (κ : Bridge.Gf (Vc D j)) * (s : Bridge.Gf (Vc D j)) = (σ s : Bridge.Gf (Vc D j)) * κ' ∧ kap κ' = kap κ ∧
        chi κ' = chi κ := by
  have hN : N = (Vc D j).rank := Fin.equiv_iff_eq.mp ⟨rk.toEquiv⟩
  have hR : 1 ≤ i.1.2 ∧ i.1.2 ≤ (Vc D j).rank := ⟨i.2.1, by rw [← hN]; exact i.2.2.1⟩
  have hp := perm_core p j t i.1 hR κ
  refine hp.elim fun σ hσ => ?_
  have hinj : Function.Injective (intEmb Lf) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have loc : ∀ y ∈ hkA p j t i.1, ∀ τ,
      ((y : GL (Fin (Vc D j).rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) = 1 := by
    intro y hy τ
    have hy' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y := (p.R.B.L j t).hecke.hA_loc i.1 hR y hy
    exact map_ev_eq_one_of_loc (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y _ (ev τ) (hev τ) i.2.2.2 hy'
  have key : ∀ (κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i.1 → s ∈ hkA p j t i.1 →
      (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → kap κ' = kap κ ∧ chi κ' = chi κ := by
    intro κ' a s ha hs he
    have hmap : ∀ τ, (((κ' : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) =
        (((κ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) := by
      intro τ
      have ha1 := loc a ha τ
      have hs1 := loc s hs τ
      have ha' : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
        have h0 : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) *
            (((a : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
          rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.map_one _ (ev τ).map_zero (ev τ).map_one]
        rwa [ha1, mul_one] at h0
      rw [he]
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha', hs1, one_mul, mul_one]
    have hmat : ∀ τ, kapMat p j t ev bs rk κ' τ = kapMat p j t ev bs rk κ τ := by
      intro τ
      unfold kapMat matOf
      rw [hmap τ]
    have hK : kap κ' = kap κ := by
      funext τ
      apply Units.ext
      apply Matrix.ext
      intro a c
      apply hinj
      have h1 := (hkap κ' τ).trans ((hmat τ).trans (hkap κ τ).symm)
      exact congrFun (congrFun h1 a) c
    refine ⟨hK, ?_⟩
    have hL := levChi_eq_of_loc p j t i.1 hR.1 hR.2 κ κ' a s ha hs he
    have hX : (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ?_
      exact ((Matrix.GeneralLinearGroup.det (kap κ τ)).isUnit.map (intEmb Lf)).ne_zero
    have hXX : (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) = ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ :=
      congrArg (fun f : D.what₂.Tau → GL (Fin N) (intR Lf) => ∏ τ, intEmb Lf (f τ).val.det ^ sh τ) hK
    have hcc : ((levChi p j t κ' : ℂˣ) : ℂ) = ((levChi p j t κ : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hL
    have e1 : io (intEmb Lf (chi κ') * ∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) * ((levChi p j t κ' : ℂˣ) : ℂ) = 1 :=
      hchi κ'
    have e2 : io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1 :=
      hchi κ
    exact chi_cancel io (intEmb Lf) hinj (chi κ) (chi κ') (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ)
      (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) hXX hX ((levChi p j t κ : ℂˣ) : ℂ) ((levChi p j t κ' : ℂˣ) : ℂ) hcc
      (levChi p j t κ).ne_zero e1 e2
  refine ⟨σ, fun s => ⟨⟨((σ s : hkA p j t i.1) : Bridge.Gf (Vc D j))⁻¹ * κ * s, hσ s⟩, ?_, ?_, ?_⟩⟩
  · show (κ : Bridge.Gf (Vc D j)) * s = (σ s : Bridge.Gf (Vc D j)) * ((σ s : Bridge.Gf (Vc D j))⁻¹ * κ * s)
    group
  · exact (key _ _ _ (σ s).2 s.2 rfl).1
  · exact (key _ _ _ (σ s).2 s.2 rfl).2


set_option maxHeartbeats 800000 in
open Classical in
theorem permAt (p : PtAt ex Csz) (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    PermAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hC
  obtain ⟨-, -, -, hev, hkap, hchi⟩ := hC
  dsimp only [GlobalTheory.FrameOf.frameOf]
  intro i κ
  exact perm_gen p j (p.R.mu w) e0 b io ev bs rk sh Lf kap chi hev hkap hchi i κ

end Point

end GlobalTheory.FramePerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTop
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem pcTrace_eq_zero {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem span_harm2_sup_coinv_eq_univ : ∀ (P Q R S : ℕ) (x : ℂ),
    Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  intro P Q R S x
  refine eq_top_iff.2 fun f _ => ?_
  have hpr : ∀ Z : Mat P Q, IsPC Z → ∀ g, (coinv P Q R S x).mkQ (fockAct1 P Q R S Z g) = 0 := by
    intro Z hZ g
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨Z, g, ?_⟩
    rw [pcTrace_eq_zero hZ, mul_zero, zero_smul, sub_zero]
  obtain ⟨h, hh, he⟩ := GlobalTheory.FockAlg.HarmLift.exists_harm2_rep P Q R S _ (coinv P Q R S x).mkQ hpr f
  have hd : f - h ∈ coinv P Q R S x := by
    rw [← Submodule.Quotient.eq]; exact he.symm
  have : f = h + (f - h) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.subset_span hh) hd

end GlobalTheory.HoweR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTopStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top : ∀ (P Q R S : ℕ) (x : ℂ), Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  first | exact @GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | exact GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | (intros; apply GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem coinv_stab_snd (P Q R S : ℕ) (x : ℂ) : Stab (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro Z y hy
  have hcomm := (GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S).2.2.2.2
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Z f, ?_⟩
    rw [map_sub, map_smul, hcomm]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem degW_le_of_abs_le {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) (B : ℚ) (hμ : ∀ a, |μ a| ≤ B) :
    degW c μ ≤ ((p + q : ℕ) : ℚ) * (B + |c|) := by
  unfold degW
  have h : ∀ a, |shiftNu c μ a| ≤ B + |c| := by
    intro a
    rcases a with i | j
    · simp only [shiftNu]; exact (abs_sub _ _).trans (add_le_add (hμ _) le_rfl)
    · simp only [shiftNu]; exact (abs_add_le _ _).trans (add_le_add (hμ _) le_rfl)
  calc ∑ a, |shiftNu c μ a| ≤ ∑ _a : Ix p q, (B + |c|) := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp [Finset.card_univ, Fintype.card_sum]; ring

theorem fockCoinvariantKernel_highestWeight_admissible (P Q R S : ℕ) (x : ℂ) : AdmMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro B
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ ⌊((R + S : ℕ) : ℚ) * (B + |cPair P Q|)⌋₊, inferInstance, ?_⟩
  intro μ hμ v hv
  obtain ⟨-, hL2, -, hw2, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  have hgood : Good (fockAct2 P Q R S) := ⟨hL2, hw2, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩
  obtain ⟨hspan, -, hK2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inl rfl))
  have hKc : KStable (fockAct2 P Q R S) (coinv P Q R S x) := fun X _ w hw => coinv_stab_snd P Q R S x X w hw
  have hv' : v ∈ (Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x) ⊓ hwSub (fockAct2 P Q R S) μ :=
    ⟨by rw [GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top]; exact Submodule.mem_top, hv⟩
  have hsplit := GlobalTheory.T.howeHighestWeight_sup_stable_le R S _ (fockAct2 P Q R S) hgood _ _ hK2 hKc μ hv'
  obtain ⟨h, hh, c, hc, rfl⟩ := Submodule.mem_sup.1 hsplit
  refine Submodule.add_mem_sup ?_ hc.1
  rw [mem_restrictTotalDegree]
  have hh2 : h ∈ harm2 P Q R S := by rw [← hspan]; exact hh.1
  exact (GlobalTheory.DegKeep.deg_le_of_harm hh2 hh.2).trans (Nat.floor_mono (degW_le_of_abs_le _ μ B hμ))

theorem coinv_stab_adm : ∀ (P Q R S : ℕ) (x : ℂ),
    Stab (fockAct2 P Q R S) (coinv P Q R S x) ∧ AdmMod (fockAct2 P Q R S) (coinv P Q R S x) :=
  fun P Q R S x => ⟨coinv_stab_snd P Q R S x, fockCoinvariantKernel_highestWeight_admissible P Q R S x⟩

end GlobalTheory.HoweR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissibleStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoinvariantKernel_stable_and_admissible : ∀ (P Q R S : ℕ) (x : ℂ), Stab (fockAct2 P Q R S) (coinv P Q R S x) ∧ AdmMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.coinv_stab_adm | exact GlobalTheory.HoweR.coinv_stab_adm | (intros; apply GlobalTheory.HoweR.coinv_stab_adm <;> assumption)
end
end

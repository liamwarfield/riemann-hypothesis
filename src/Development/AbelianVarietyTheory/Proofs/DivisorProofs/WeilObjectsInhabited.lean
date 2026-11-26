module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem invariant_comp_mulVec [Fintype κ] [DecidableEq κ] (m : ((κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ SB (κ → F), ∀ a, m (fun x => φ (x + a)) = m φ) (g : GL κ F) {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F))
    (hφ' : (fun x => φ (g.val.mulVec x)) ∈ SB (κ → F)) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * m (fun x => φ (g.val.mulVec x)) = m φ := by
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  have := nonarch_pi F κ
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → F) (Measure.pi fun _ => (Measure.addHaar : Measure F)) m hm
  rw [hc _ hφ, hc _ hφ', mul_left_comm, integral_comp_mulVec]

theorem diag_mem_SB [Fintype κ] {φ : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) :
    (fun x : κ → F => φ (Sum.elim x x)) ∈ SB (κ → F) := by
  have := SplitWeil.t2Space F
  have hc : Continuous fun x : κ → F => (Sum.elim x x : κ ⊕ κ → F) :=
    continuous_pi (by rintro (k | k) <;> exact continuous_apply k)
  have hc' : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  refine ⟨hφ.1.comp_continuous hc, HasCompactSupport.intro (hφ.2.image hc') fun x hx => ?_⟩
  by_contra h
  exact hx ⟨Sum.elim x x, subset_tsupport _ h, rfl⟩

theorem diag_invariant_comp [Invertible (2 : F)] [Fintype κ] [DecidableEq κ] (ψ : AddChar F ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (g : GL κ F) {φ φ' : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) (hφ' : φ' ∈ SB (κ ⊕ κ → F))
    (h : ∀ x, φ' (Sum.elim x x) = φ (Sum.elim (g.val.mulVec x) (g.val.mulVec x))) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * l φ' = l φ := by
  classical
  have := SplitWeil.t2Space F
  have := nonarch_field F
  have hlc := isLocallyConstant_addChar ψ hψ

  have hz : ∀ φ ∈ SB (κ ⊕ κ → F), (∀ x, φ (Sum.elim x x) = 0) → l φ = 0 := by
    intro φ hφ h0
    refine eq_zero_of_mul_invariant l (Set.range fun y : κ → F => fun u => ψ (u ⬝ᵥ Sum.elim y (-y))) ?_ ?_ hφ ?_
    · rintro _ ⟨y, rfl⟩
      exact hlc.comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, rfl⟩ φ hφ
      rw [← hl 0 y φ hφ]
      congr 1
      funext u
      simp [schr]
    · intro u hu
      obtain ⟨k, hk⟩ : ∃ k, u (Sum.inl k) - u (Sum.inr k) ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hu
        rw [← h0 (u ∘ Sum.inl)]
        congr 1
        ext (k | k)
        · rfl
        · exact (sub_eq_zero.mp (hne k)).symm
      obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ1
      refine ⟨_, ⟨Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))), rfl⟩, ?_⟩
      have : u ⬝ᵥ Sum.elim (Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))))
          (-Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k)))) = a := by
        conv_lhs => rw [← Sum.elim_comp_inl_inr u]
        rw [sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_single, dotProduct_single, ← sub_eq_add_neg,
          ← sub_mul]
        exact mul_div_cancel₀ _ hk
      show ψ _ ≠ 1
      rwa [this]

  let K : Set (κ → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => SplitWeil.isCompact_int F
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int F⟩
  let e : (κ → F) → ℂ := K.indicator 1
  have he : IsLocallyConstant e := (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant
  have he0 : e 0 = 1 := Set.indicator_of_mem (show (0 : κ → F) ∈ K from fun _ _ => zero_mem _) _
  let ext : ((κ → F) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → F) → ℂ) :=
    { toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)
      map_add' := fun f f' => by funext u; simp [add_mul]
      map_smul' := fun a f => by funext u; simp [mul_assoc] }
  have hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) := fun _ _ => rfl
  have c1 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  have c2 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inr := continuous_pi fun k => continuous_apply _
  have hSB : ∀ f ∈ SB (κ → F), ext f ∈ SB (κ ⊕ κ → F) := by
    intro f hf
    have c3 : Continuous fun p : (κ → F) × (κ → F) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → F) :=
      continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)
    refine ⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)),
      HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩
    by_contra h
    rw [hext] at h
    refine hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩
    simp
  have hres : ∀ φ ∈ SB (κ ⊕ κ → F), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x) := by
    intro φ hφ
    rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub]
    refine hz _ (sub_mem hφ (hSB _ (diag_mem_SB hφ))) fun x => ?_
    simp [hext, he0]
  have hinv : ∀ f ∈ SB (κ → F), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f := by
    intro f hf a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]
    congr 1
    funext u
    have e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a := rfl
    have e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a := rfl
    simp [schr, hext, e1, e2]
  have h' := diag_mem_SB hφ'
  rw [hres φ hφ, hres φ' hφ']
  simp only [h] at h' ⊢
  exact invariant_comp_mulVec _ hinv g (diag_mem_SB hφ) h'

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]

section Pair

variable {R : Type} [CommRing R]



end Pair

end GlobalTheory.WeilM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginNoeth

def baseHom (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : R →+* D :=
  (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R))

def closure (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Subring D :=
  letI := (baseHom A R D).toAlgebra
  (integralClosure R D).toSubring

def closureAlg (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Algebra R (closure A R D) :=
  ((baseHom A R D).codRestrict (closure A R D) (fun r => by
    letI := (baseHom A R D).toAlgebra
    exact isIntegral_algebraMap (R := R) (A := D) (x := r))).toAlgebra

def ClosureFiniteEtale (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Prop :=
  letI := closureAlg A R D
  Module.Finite R (closure A R D) ∧ Algebra.Etale R (closure A R D) ∧ Nontrivial (closure A R D)

def Good (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) : Prop :=
  letI := closureAlg A R D
  (∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] closure A R D)) ∧
    ∃ s : closure A R D →+* FractionRing A,
      s.comp (algebraMap R (closure A R D)) = (algebraMap A (FractionRing A)).comp ρ

end GlobalTheory.KeyOriginNoeth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
open ValuativeRel
open scoped Matrix Topology

noncomputable section
namespace GlobalTheory.CondRescale

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one_of_pow_near (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1) : ‖z‖ ≤ 1 := by
  by_contra hz
  push_neg at hz
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hz
  have h1 := h n
  have h2 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖z ^ n‖ = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_pow, norm_one] at h2
  linarith

theorem exists_ball_trivial (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ0 t = 1 := by
  have hc : Continuous fun t : k => ‖ψ0 t - 1‖ := (hψ.sub continuous_const).norm
  have h0 : ‖ψ0 0 - 1‖ < 1 := by simp
  have hU : {t : k | ‖ψ0 t - 1‖ < 1} ∈ nhds (0 : k) :=
    (isOpen_lt hc continuous_const).mem_nhds h0
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hU
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have hp : ∀ s : k, valuation k s < γ → ∀ n : ℕ, ‖ψ0 s ^ n - 1‖ < 1 := by
    intro s hs n
    have h1 : n • s ∈ {t : k | ‖ψ0 t - 1‖ < 1} :=
      hsub (lt_of_le_of_lt (GlobalTheory.CharDualMat.valuation_nsmul_le s n) hs)
    rw [Set.mem_setOf_eq, AddChar.map_nsmul_eq_pow] at h1
    exact h1
  have hneg : valuation k (-t) < γ := by rwa [Valuation.map_neg]
  have a1 := norm_le_one_of_pow_near _ (hp t ht)
  have a2 := norm_le_one_of_pow_near _ (hp (-t) hneg)
  have hm : ψ0 (-t) * ψ0 t = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 t‖ = 1 := by
    have := congrArg norm hm
    rw [norm_mul, norm_one] at this
    nlinarith [norm_nonneg (ψ0 t), norm_nonneg (ψ0 (-t))]
  exact GlobalTheory.IrredSB.eq_one_of_forall_pow hn (hp t ht)

theorem exists_rescale_conductor_integers [CharZero k]
    (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (hne : ψ0 ≠ 1) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (c * (x * y)) = 1) ↔ x ∈ 𝒪[k] := by
  classical
  let P : k → Prop := fun a => ∀ y ∈ 𝒪[k], ψ0 (a * y) = 1
  obtain ⟨t, ht⟩ : ∃ t : k, ψ0 t ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hne (AddChar.ext _ _ fun s => by simpa using hall s)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one _)
  have hbd : ∀ a, P a → a ≠ 0 → valuation k a < valuation k t := by
    intro a ha ha0
    by_contra hle
    push_neg at hle
    apply ht
    have hmem : t / a ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    have := ha _ hmem
    rwa [mul_div_cancel₀ _ ha0] at this
  obtain ⟨γ, hγ, hball⟩ := exists_ball_trivial ψ0 hψ
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  have hPr : P (r ^ m) := by
    intro y hy
    apply hball
    rw [map_mul, map_pow]
    calc valuation k r ^ m * valuation k y ≤ valuation k r ^ m * 1 :=
          mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 hy)
      _ < γ := by simpa using hm
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hex : ∀ a : k, a ≠ 0 → ∃ n : ℤ, e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro a ha
    have h1 : e (valuation k a) ≠ 0 := by
      intro h
      apply ha
      have : valuation k a = 0 := by
        have h2 : e (valuation k a) = e 0 := by rw [h, map_zero]
        exact e.injective h2
      simpa using this
    obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h1
    exact ⟨Multiplicative.toAdd u, by simpa using hu.symm⟩
  let Q : ℤ → Prop := fun n => ∃ a, P a ∧ a ≠ 0 ∧
    e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨N, hN⟩ := hex t ht0
  have hr0' : r ^ m ≠ 0 := pow_ne_zero _ hr0
  obtain ⟨n1, hn1⟩ := hex _ hr0'
  obtain ⟨n0, ⟨a0, ha0P, ha0, hn0⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := Q)
    ⟨N, fun n ⟨a, ha, ha0, hn⟩ => by
      have h1 : e (valuation k a) < e (valuation k t) := e.strictMono (hbd a ha ha0)
      rw [hn, hN, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt] at h1
      exact h1.le⟩ ⟨n1, r ^ m, hPr, hr0', hn1⟩
  have hdown : ∀ b, P b → b ≠ 0 → valuation k b ≤ valuation k a0 := by
    intro b hb hb0
    obtain ⟨n, hn⟩ := hex b hb0
    have h1 := hmax n ⟨b, hb, hb0, hn⟩
    have h2 : e (valuation k b) ≤ e (valuation k a0) := by
      rw [hn, hn0, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
      exact h1
    exact (map_le_map_iff e).1 h2
  have hv0 : valuation k a0 ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  refine ⟨a0, ha0, fun x => ⟨fun hx => ?_, fun hx y hy => ha0P _ (mul_mem hx hy)⟩⟩
  by_cases hx0 : x = 0
  · rw [hx0]
    exact zero_mem _
  have hP : P (a0 * x) := fun y hy => by
    rw [mul_assoc]
    exact hx y hy
  have h1 := hdown _ hP (mul_ne_zero ha0 hx0)
  rw [Valuation.mem_integer_iff]
  have h2 : valuation k x = valuation k (a0 * x) / valuation k a0 := by
    rw [map_mul, mul_div_cancel_left₀ _ hv0]
  rw [h2]
  exact (div_le_one₀ (zero_lt_iff.2 hv0)).2 h1

end GlobalTheory.CondRescale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (f g : ℤ_[p] →+* O) : f = g := by
  ext x
  rw [← sub_eq_zero]
  apply IsHausdorff.haus (I := Ideal.span {(p : O)}) ‹_›
  intro n
  rw [SModEq.zero]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[p]) + y * (p : ℤ_[p]) ^ n := by rw [hy]; ring
  have hfx : f x - g x = (f y - g y) * (p : O) ^ n := by
    rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  rw [hfx, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton'.mpr ⟨f y - g y, rfl⟩

theorem padicToO_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (g : ℤ_[p] →+* O), g = padicToO p O := by
  intro p _ O _ _ _ g
  exact padicInt_ringHom_ext p O g (padicToO p O)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv


open Matrix TensorProduct in
theorem _root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
      (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 ∧
        _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ ε hζ
  have hε : ε ≠ 1 := by
    rintro rfl
    have h1 : _root_.GlobalTheory.Sandwich.root (1 : PreTilt O p) = 1 := by
      unfold _root_.GlobalTheory.Sandwich.root
      exact map_one _
    have h2 : PreTilt.untilt (1 : PreTilt O p) = 1 := by simp
    rw [h1, h2] at hζ
    have hp : p ∣ 1 := (hζ.pow_eq_one_iff_dvd 1).mp (pow_one 1)
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hp)
  have hc : (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 := by
    unfold _root_.GlobalTheory.Sandwich.mu
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    exact sub_ne_zero.mpr hε
  have hmu : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    intro h
    apply hc
    rw [h]
    exact WittVector.zero_coeff _ _ _
  refine ⟨hc, hmu, fun h => hmu ?_⟩
  rw [← _root_.GlobalTheory.Sandwich.xi_mul_nu, h, mul_zero]

end GlobalTheory.DetInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latOf_discrete [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) :
    DiscreteTopology (latOf N) := GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage F N

theorem latOf_isZLattice [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] : IsZLattice ℝ (latOf N) := GlobalTheory.T.isZLattice_fractionalIdealRealLatticeImage F N hN

theorem covolume_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)] :
    ZLattice.covolume (latOf N) = covol N := GlobalTheory.T.covolume_fractionalIdealRealLatticeImage F N hN

theorem dual_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual F N hN

theorem fourier_lipschitzOneVariableKernel (k : ℕ) (hk : 2 ≤ k) (he : Even k) (w : ℂ) (hw : w.im ≠ 0) (x : ℝ) :
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) :=
  GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq k hk he w hw x

theorem Phi_cont_decay (k : ℕ) (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧
      ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel F k hk z hz

theorem summable_lhsTerm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) (hM : M ≠ 0) (k : ℕ)
    (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Summable (fun a : (M : Set F) => lhsTerm k z a) := GlobalTheory.T.summable_lipschitzLatticeNormPowSummand F M hM k hk z hz

theorem fourier_prod_coord (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

theorem remb_injective [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

theorem Phi_remb (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) :
    Phi k z (remb F ν) =
      if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 := by
  unfold Phi
  by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
  · rw [if_pos hc, Finset.prod_congr rfl fun τ _ => by rw [remb_apply, phi1, if_pos (hc τ)],
      Finset.prod_mul_distrib, ← Complex.exp_sum, rhsTerm, Finset.abs_prod, ← Finset.prod_pow, Complex.ofReal_prod]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨τ, hτ⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [remb_apply, phi1, if_neg (not_lt.2 hτ)])

theorem fourier_Phi (k : ℕ) (hk : 2 ≤ k) (he : Even k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0)
    (a : F) : 𝓕 (Phi k z) (remb F a) =
      (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ) *
        lhsTerm k z (-a) := by
  rw [show Phi k z = fun ξ : RSp F => ∏ τ, phi1 k (z τ) (ξ τ) from rfl, fourier_prod_coord]
  simp only [remb_apply]
  have h := fun τ : F →+* ℝ => fourier_lipschitzOneVariableKernel k hk he (z τ) (hz τ) (τ a)
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, lhsTerm, Finset.prod_zpow]
  simp [map_neg, sub_eq_add_neg]

theorem lipschitz : Lipschitz := by
  intro F _ _ _ M hM k hk he z hz
  haveI : DiscreteTopology (latOf M) := latOf_discrete M
  haveI : IsZLattice ℝ (latOf M) := latOf_isZLattice M hM
  set L := Formalism.H.dual (latOf M) with hL
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) (latOf M)
  haveI : DiscreteTopology L := h1
  haveI : IsZLattice ℝ L := h2
  have hdd : Formalism.H.dual L = latOf M := Formalism.H.dualDual (RSp F) (latOf M)
  have hcov : ZLattice.covolume L = (covol M)⁻¹ := by
    rw [Formalism.H.covolumeDual (RSp F) (latOf M), covolume_latOf M hM]
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ FractionalIdeal.dual ℤ ℚ M, remb F ν = x := by
    intro x; rw [hL, dual_latOf M hM]; exact mem_latOf _ x
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ M, remb F a = x := by
    intro x; rw [hdd]; exact mem_latOf _ x
  obtain ⟨hcont, hdec⟩ := Phi_cont_decay k hk z hz
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L (Phi k z) hcont
    ((Module.finrank ℝ (RSp F) : ℝ) + 1) (by linarith) (hdec _)
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 (Phi k z) μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L (Phi k z) hint D hD μ μ.2

  let eM : (M : Set F) ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hDmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  let eD : (FractionalIdeal.dual ℤ ℚ M : Set F) ≃ L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hLmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  set cst : ℂ := (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ)
  have hsL := summable_lhsTerm M hM k hk z hz
  let eN : (M : Set F) ≃ (M : Set F) :=
    ⟨fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => by simp, fun a => by simp⟩
  have hsLn : Summable (fun a : (M : Set F) => lhsTerm k z (-(a : F))) :=
    (eN.summable_iff (f := fun a : (M : Set F) => lhsTerm k z a)).2 hsL
  have hFM : ∀ a : (M : Set F), 𝓕 (Phi k z) (eM a) = cst * lhsTerm k z (-(a : F)) :=
    fun a => fourier_Phi k hk he z hz a
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact (hsLn.mul_left cst).congr fun a => (hFM a).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Phi k z ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have H4' : HasSum (fun a : (M : Set F) => (covol M : ℂ) * cst * lhsTerm k z (-(a : F)))
      (∑' l : L, Phi k z (l : RSp F)) := by
    refine H4.congr_fun fun a => ?_
    simp only [Function.comp_apply, hFM, hcov, Complex.ofReal_inv, inv_inv]
    ring
  have hs0 : Summable (fun l : L => Phi k z (l : RSp F)) := by
    simpa using hsumx 0
  set g : F → ℂ := fun ν =>
    if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 with hg
  have hind : (FractionalIdeal.dual ℤ ℚ M : Set F).indicator g = (dualCone M z).indicator (rhsTerm k z) := by
    funext ν
    by_cases hν : ν ∈ (FractionalIdeal.dual ℤ ℚ M : Set F)
    · have hν' : ν ∈ traceDual M := (mem_traceDual_iff hM ν).2 hν
      by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
      · rw [Set.indicator_of_mem hν, Set.indicator_of_mem (show ν ∈ dualCone M z from ⟨hν', hc⟩), hg]
        simp [hc]
      · rw [Set.indicator_of_mem hν, Set.indicator_of_notMem (show ν ∉ dualCone M z from fun h => hc h.2), hg]
        simp [hc]
    · have hν' : ν ∉ dualCone M z := fun h => hν ((mem_traceDual_iff hM ν).1 h.1)
      rw [Set.indicator_of_notMem hν, Set.indicator_of_notMem hν']
  have hPg : ∀ ν : (FractionalIdeal.dual ℤ ℚ M : Set F), Phi k z (eD ν) = g ν := fun ν => Phi_remb k z ν
  have hsD : Summable (fun ν : (FractionalIdeal.dual ℤ ℚ M : Set F) => g ν) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hPg ν
  have hsR : Summable (fun ν : dualCone M z => rhsTerm k z ν) := by
    have h3 := (summable_subtype_iff_indicator (s := (FractionalIdeal.dual ℤ ℚ M : Set F)) (f := g)).1 hsD
    rw [hind] at h3
    exact (summable_subtype_iff_indicator (s := dualCone M z) (f := rhsTerm k z)).2 h3
  have hR : ∑' l : L, Phi k z (l : RSp F) = ∑' ν : dualCone M z, rhsTerm k z ν := by
    rw [← eD.tsum_eq, tsum_subtype (dualCone M z) (rhsTerm k z), ← hind, ← tsum_subtype]
    exact tsum_congr fun ν => hPg ν
  have hLn : ∑' a : (M : Set F), lhsTerm k z (-(a : F)) = ∑' a : (M : Set F), lhsTerm k z a :=
    eN.tsum_eq (fun a : (M : Set F) => lhsTerm k z a)
  have hmain := H4'.tsum_eq
  rw [tsum_mul_left, hLn, hR] at hmain
  refine ⟨hsL, hsR, ?_⟩
  rw [← hmain]
  have hc0 : (covol M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (covol_pos hM).ne'
  have hf0 : ((k - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [lipConst, cst, card_realEmb, div_pow, pow_mul]
  field_simp

end GlobalTheory.LipschitzTR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoissonStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_formula_totally_real_poisson : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz := by
  first | exact @GlobalTheory.LipschitzTR.lipschitz | exact GlobalTheory.LipschitzTR.lipschitz | (intros; apply GlobalTheory.LipschitzTR.lipschitz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

def genFibMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E] [Algebra T O]
    (ψ : E →ₐ[T] O) : GenFib T E →+* GenFib T O :=
  IsLocalization.map (M := Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (T := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (GenFib T O) ψ.toRingHom (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (ψ.commutes t).symm⟩)

theorem genFibMap_algebraMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) :
    genFibMap ψ (algebraMap E (GenFib T E) e) = algebraMap O (GenFib T O) (ψ e) := by
  simp [genFibMap, IsLocalization.map_eq]

theorem genFib_ringHom_ext {T E C : Type} [CommRing T] [CommRing E] [CommRing C] [Algebra T E]
    {f g : GenFib T E →+* C} (h : ∀ e : E, f (algebraMap E _ e) = g (algebraMap E _ e)) : f = g :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (RingHom.ext h)

end GlobalTheory.LocAcyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickening
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecGlue

theorem preimage_eq_of_comp_eq_of_sqZero : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T),
    Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens,
      u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  intro S T _ _ q hq hsq Y u w huw V
  have hsurj : Function.Surjective (spMap q).base := by
    intro p
    have hker : RingHom.ker q ≤ p.asIdeal := by
      intro x hx
      have hx2 : x * x ∈ RingHom.ker q ^ 2 := by
        rw [sq]; exact Ideal.mul_mem_mul hx hx
      rw [hsq, Ideal.mem_bot] at hx2
      exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
    haveI := p.isPrime
    haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
    refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
    intro x hx
    exact hker (by simpa [RingHom.mem_ker] using hx)
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, huw]

end GlobalTheory.SecGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickeningStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_eq_of_square_zero_thickening : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens, u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  first | exact @GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | exact GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | (intros; apply GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChange
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem isZModTorsor_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D]
    [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  intro B B' D _ _ _ _ _ q hq act hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  haveI : NeZero q := ⟨hq.ne'⟩
  let act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)) :=
    { toFun := fun g => Algebra.TensorProduct.congr (AlgEquiv.refl : B' ≃ₐ[B'] B') (act g)
      map_one' := by
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      map_mul' := by
        intro g h
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply, AlgEquiv.mul_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy] }
  have hact : ∀ (g : Multiplicative (ZMod q)) (b : B') (x : D),
      act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x := by
    intro g b x
    simp [act', Algebra.TensorProduct.congr_apply]
  refine ⟨act', hact, inferInstance, inferInstance, inferInstance, ?_⟩
  let Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))
  let e := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B'
  let dBC := TensorProduct.AlgebraTensorModule.distribBaseChange B B' D D
  let pR := TensorProduct.piRight B B' B' (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, (Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      (dBC z) = pR (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [dBC, pR, e, Φ, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, hact, Algebra.TensorProduct.tmul_mul_tmul,
          LinearEquiv.ofBijective_apply]
        rfl
      | add s t hs ht => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
  have hfun : ⇑(Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      = fun w => pR (e (dBC.symm w)) := by
    funext w
    rw [← key, dBC.apply_symm_apply]
  rw [hfun]
  exact pR.bijective.comp (e.bijective.comp dBC.symm.bijective)

end GlobalTheory.LocAcyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChangeStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isZModTorsorFiniteProjective_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D] [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  first | (exact @GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (exact GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (intros; apply GlobalTheory.LocAcyc.isZModTorsor_baseChange  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
open scoped SchwartzMap NNReal ContDiff
open GlobalTheory.Published.Metaplectic

namespace GlobalTheory.SchwartzTranslateLip

theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K N k n : ℕ) (hk : k ≤ K) (hn : n ≤ N) (a : V) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K *
        ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) := by
  set B := 2 ^ K * ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) = (fun z => f (z + a)) - ⇑f := by
    funext z; simp
  have eit : iteratedFDeriv ℝ n ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) x
      = iteratedFDeriv ℝ n f (x + a) - iteratedFDeriv ℝ n f x := by
    rw [efun, iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    c0.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
      (‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => x + s • a) a s := by
      simpa using ((hasDerivAt_id s).smul_const a).const_add x
    exact ((hd (x + s • a)).hasFDerivAt.comp_hasDerivAt s hl).const_smul (‖x‖ ^ k)
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a‖ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by
    intro s hs
    set y := x + s • a with hy
    have hsa : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    have hx : ‖x‖ ≤ ‖y‖ + ‖a‖ := by
      have h4 := norm_sub_le y (s • a)
      rw [show y - s • a = x by simp [hy]] at h4
      linarith
    have hx2 : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg a, norm_nonneg y, mul_nonneg (norm_nonneg a) (norm_nonneg y)]
    have ha1 : 1 ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    have hxk : ‖x‖ ^ k ≤ (1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k := by
      calc ‖x‖ ^ k ≤ ((1 + ‖a‖) * (1 + ‖y‖)) ^ k := pow_le_pow_left₀ (norm_nonneg _) hx2 k
        _ = (1 + ‖a‖) ^ k * (1 + ‖y‖) ^ k := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have hop : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖ := by
      rw [← norm_fderiv_iteratedFDeriv]; exact (fderiv ℝ (iteratedFDeriv ℝ n f) y).le_opNorm a
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, N + 1)) (k := k)
      (n := n + 1) hk (by simp; omega) f y
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖x‖ ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖
        ≤ ((1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k) * (‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖) := by gcongr
      _ = ‖a‖ * (1 + ‖a‖) ^ K * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f y‖) := by ring
      _ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by gcongr
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := 1) (fun s _ => (hderiv s).hasDerivWithinAt) hbound (by simp) (by simp)
  simp only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one] at key
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key

theorem translate_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
      p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set K := s.sup Prod.fst
  set N := s.sup Prod.snd
  refine ⟨(C * 2 ^ K) • (Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2,
    K, ?_, fun a f => ?_⟩
  · have h : Continuous ⇑((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) :=
      Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
    rw [Seminorm.coe_smul]
    exact h.const_smul _
  set S := ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have h1 : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S) := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    exact seminorm_translate_sub_le K N i.1 i.2 (Finset.le_sup (f := Prod.fst) hi)
      (Finset.le_sup (f := Prod.snd) hi) a f
  have h2 := hC (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  push_cast
  calc p (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f) := h2
    _ ≤ (C : ℝ) * (‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S)) := by gcongr
    _ = _ := by ring

end GlobalTheory.SchwartzTranslateLip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

def TraceOpen (R : Type) [CommRing R] [TopologicalSpace R] (a b : R) : Prop :=
  ∀ g : ℍ[R, a, b], nrm g = 1 → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g →
    ∃ O : Set R, IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t

def SqOpen (K : Type) [Monoid K] [TopologicalSpace K] : Prop :=
  ∀ V ∈ 𝓝 (1 : K), ∃ U ∈ 𝓝 (1 : K), ∀ r ∈ U, ∃ μ ∈ V, μ ^ 2 = r

end GlobalTheory.QSA
end
end

module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MapMulInvEqOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem quadraticForm_add_expand (δ : F) (x y : V4 F) : q4 δ (x + y) = q4 δ x + B4 δ x y + q4 δ y := by
  simp only [q4, B4, Pi.add_apply]
  ring

private theorem quaternaryForm_unit_scaling (δ : F) (b : A F) (x y : V4 F) : B4 δ x (fun i => b * y i) = b * B4 δ x y := by
  simp only [B4]
  ring

private theorem quaternaryForm_zero_right (δ : F) (x : V4 F) : B4 δ x 0 = 0 := by
  simp [B4]

private theorem pc_eq (δ : F) (b : A F) (φ : V4 F → ℂ) (y : V4 F) :
    Pc δ b φ y = ψ (b * q4 δ y) * ft4 δ (fun x => ψ (b * q4 δ x) * φ x) fun i => b * y i := by
  simp only [Pc, ft4]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [quaternaryForm_unit_scaling, quadraticForm_add_expand, mul_add, mul_add, psi_add, psi_add]
  ring

private theorem chirp_mem (δ : F) (b : A F) (φ : V4 F → ℂ) (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun v => ψ (b * q4 δ v) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  have h := chirpQ F δ b 0 φ hφ
  simpa only [quaternaryForm_zero_right, add_zero] using h

private theorem scale_mem (b : (A F)ˣ) (φ : V4 F → ℂ) (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun v : V4 F => φ fun i => (b : A F) * v i) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  have h := UpperTheory.ConvolutionTheory.R2.D.sClos F (Fin 4) (Units.map (Matrix.scalar (Fin 4)).toMonoidHom b) φ hφ
  convert h using 3 with v
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal_apply]

theorem UpperTheory.ConvolutionTheory.R2.C.pcMem :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), (∀ b φ y, Pc δ b φ y = ψ (b * q4 δ y) * ft4 δ (fun x => ψ (b * q4 δ x) * φ x) fun i => b * y i) ∧
    (δ ≠ 0 → ∀ b : (A F)ˣ, ∀ φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4), Pc δ (b : A F) φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) := by
  intro F _ _ δ
  refine ⟨pc_eq δ, fun hδ b φ hφ => ?_⟩
  have e : Pc δ (b : A F) φ = fun y => ψ ((b : A F) * q4 δ y) *
      ft4 δ (fun x => ψ ((b : A F) * q4 δ x) * φ x) fun i => (b : A F) * y i :=
    funext (pc_eq δ b φ)
  rw [e]
  exact chirp_mem δ b _ (scale_mem b _ (ftBasic F δ hδ _ (chirp_mem δ b φ hφ)).1)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormShiftExpand
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_add' {F : Type} [Field F] [NumberField F] (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private lemma psi_neg_mul {F : Type} [Field F] [NumberField F] (a : A F) : ψ (-a) * ψ a = 1 := by
  rw [← psi_add', neg_add_cancel]
  simp [ψ]

private lemma quadraticForm_shift_expand {F : Type} [Field F] [NumberField F] (δ : F) (b c : A F) (hbc : b * c = 1) (x y v : V4 F) :
    b * q4 δ (x + (y + fun i => c * v i)) = b * q4 δ (x + y) + B4 δ x v + B4 δ y v + c * q4 δ v := by
  simp only [q4, B4, Pi.add_apply]
  linear_combination (2 * ((x 2 + y 2) * v 2 - rt δ * ((x 3 + y 3) * v 3)) - (x 1 + y 1) * v 0 - (x 0 + y 0) * v 1
    + c * (v 2 ^ 2 - rt δ * v 3 ^ 2 - v 1 * v 0)) * hbc

private lemma quaternaryForm_neg_right {F : Type} [Field F] [NumberField F] (δ : F) (x v : V4 F) : B4 δ x (-v) = -B4 δ x v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.idxFt :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    ft4 δ (Pc δ (b : A F) φ.1) v = c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ft4 δ φ.1 (-v) := by
  intro F _ _ δ b c h φ v
  have hbc : (b : A F) * ((b⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv b
  let φ' : S4 F := ⟨fun x => ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x, chirpQ F δ 0 (-v) φ.1 φ.2⟩
  have hφ' : ∀ x, φ'.1 x = ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x := fun _ => rfl
  have hr : ∫ x, φ'.1 x ∂(adeleMeasurePi F) = ft4 δ φ.1 (-v) := by
    unfold ft4
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add]
    exact mul_comm _ _
  have hl : ft4 δ (Pc δ (b : A F) φ.1) v =
      ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * Lam4 δ (b : A F) φ'.1 := by
    unfold ft4 Pc Lam4 abelian₂
    rw [← integral_add_right_eq_self
      (fun y => ∫ x, φ'.1 x * ψ ((b : A F) * q4 δ (x + y)) ∂(adeleMeasurePi F))
      (fun i => ((b⁻¹ : (A F)ˣ) : A F) * v i), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add, quaternaryForm_neg_right]
    rw [quadraticForm_shift_expand δ _ _ hbc x y v, psi_add', psi_add', psi_add']
    have e1 := psi_neg_mul (B4 δ x v)
    have e2 := psi_neg_mul (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)
    linear_combination (-(φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v))
      * (ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ψ (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v))) * e1
      - (φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v)) * e2
  rw [hl, h φ', hr]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Generic
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GenLoc
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.genLoc :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : Finset (R × R)), (∀ p ∈ s, IsUnit p.1 ∨ IsUnit p.2) →
    (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField R) → ∃ t : R, ∀ p ∈ s, IsUnit (p.1 + p.2 * t) := by
  intro R _ _ s hs hcard
  let f : R × R → IsLocalRing.ResidueField R := fun p =>
    -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2)
  have hex : ∃ u : IsLocalRing.ResidueField R, u ∉ s.image f := by
    by_contra hall
    have hall' : ∀ u : IsLocalRing.ResidueField R, u ∈ s.image f := by
      intro u
      by_contra hu
      exact hall ⟨u, hu⟩
    have hsub : (Set.univ : Set (IsLocalRing.ResidueField R)) ⊆ ((s.image f : Finset _) : Set _) :=
      fun u _ => by simpa using hall' u
    have h1 : ENat.card (IsLocalRing.ResidueField R) ≤ ((s.image f).card : ℕ∞) := by
      have h2 := Set.encard_le_encard hsub
      rwa [Set.encard_univ, Set.encard_coe_eq_coe_finsetCard] at h2
    have h3 : ((s.image f).card : ℕ∞) ≤ (s.card : ℕ∞) := by
      exact_mod_cast Finset.card_image_le
    exact absurd (lt_of_le_of_lt (h1.trans h3) hcard) (lt_irrefl _)
  obtain ⟨u, hu⟩ := hex
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective u
  refine ⟨t, fun p hp => ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add (f := _), map_mul]
  intro h0
  by_cases hb : IsLocalRing.residue R p.2 = 0
  · rw [hb, zero_mul, add_zero] at h0
    rcases hs p hp with h | h
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h h0
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h hb
  · apply hu
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    show -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2) = _
    rw [div_eq_iff hb]
    linear_combination -h0
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ResBig
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma natCast_ne_zero_res {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : v.valuation F (m : F) = 1) :
    ((m : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 0 := by
  have hval : Valued.v (((m : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    have hc : (((m : v.adicCompletionIntegers F)) : v.adicCompletion F)
        = algebraMap F (v.adicCompletion F) (m : F) := by
      rw [map_natCast]; exact map_natCast (v.adicCompletionIntegers F).subtype m
    rw [hc]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (m : F)).trans hm
  have hu : IsUnit (m : v.adicCompletionIntegers F) :=
    (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.2 hval
  intro h0
  have h1 : IsLocalRing.residue (v.adicCompletionIntegers F) (m : v.adicCompletionIntegers F) = 0 := by
    simpa using h0
  rw [IsLocalRing.residue_eq_zero_iff] at h1
  exact (IsLocalRing.notMem_maximalIdeal.2 hu) h1

private lemma lt_card_of_inj {k : Type*} (n : ℕ) (f : Fin (n + 1) → k) (hf : Function.Injective f) :
    (n : ℕ∞) < ENat.card k := by
  rcases finite_or_infinite k with h | h
  · have := Nat.card_le_card_of_injective f hf
    rw [ENat.card_eq_coe_natCard]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact_mod_cast this
  · rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top n

theorem UpperTheory.ConvolutionTheory.R2.C.resBig :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (n : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  intro F _ _ n
  have hne : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [Filter.eventually_cofinite]
  refine (GlobalTheory.QNorm.finite_valuation_ne_one F (Units.mk0 _ hne)).subset ?_
  intro v hv h1
  apply hv
  have h1' : v.valuation F ((n.factorial : ℕ) : F) = 1 := by simpa using h1
  have hfac := natCast_ne_zero_res v _ h1'
  refine lt_card_of_inj n (fun i => ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F))) ?_
  have key : ∀ i j : ℕ, i < j → j ≤ n →
      ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ (j : ℕ) := by
    intro i j hij hj heq
    have hd : ((j - i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = 0 := by
      rw [Nat.cast_sub hij.le, heq, sub_self]
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj)
    apply hfac
    rw [hc, Nat.cast_mul, hd, zero_mul]
  intro a b hab
  rcases lt_trichotomy (a : ℕ) b with h | h | h
  · exact absurd hab (key _ _ h (Nat.lt_succ_iff.1 b.2))
  · exact Fin.ext h
  · exact absurd hab.symm (key _ _ h (Nat.lt_succ_iff.1 a.2))
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma fieldCase (K : Type) [Field K] [CharZero K] {ι : Type} (s : Finset ι) (c d : ι → K)
    (h : ∀ i ∈ s, c i ≠ 0 ∨ d i ≠ 0) : ∃ t : K, ∀ i ∈ s, c i + d i * t ≠ 0 := by
  have hinf : Infinite (IsLocalRing.ResidueField K) :=
    Infinite.of_injective _ (IsLocalRing.residue K).injective
  have hc : ((s.image fun i => (c i, d i)).card : ℕ∞) < ENat.card (IsLocalRing.ResidueField K) := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top _
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc K (s.image fun i => (c i, d i)) (by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    simpa [isUnit_iff_ne_zero] using h i hi) hc
  exact ⟨t, fun i hi => (ht _ (Finset.mem_image_of_mem _ hi)).ne_zero⟩

private lemma rowUnit {R : Type} [CommRing R] [IsLocalRing R] {a b c d : R}
    (h : a * d - b * c = 1) : IsUnit c ∨ IsUnit d := by
  by_contra hn
  push_neg at hn
  have hc : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal c).2 hn.1
  have hd : d ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal d).2 hn.2
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← h]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hd) (Ideal.mul_mem_left _ _ hc)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)

private lemma row {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma valUnit {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletionIntegers F) (h : IsUnit x) : Valued.v (x : v.adicCompletion F) = 1 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (u : v.adicCompletionIntegers F).2
  have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have h3 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
    rw [← map_mul]
    have h4 : (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
        (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      exact_mod_cast congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) u.mul_inv
    rw [h4, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

private lemma goodPlace {F : Type} [Field F] [NumberField F] (s : Finset (G1 F))
    (v : HeightOneSpectrum (𝓞 F))
    (hint : ∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F)
    (hbig : (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    ∃ t : v.adicCompletion F, t ∈ v.adicCompletionIntegers F ∧
      ∀ g ∈ s, Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1 := by
  let toO : v.adicCompletion F → v.adicCompletionIntegers F :=
    fun x => if h : x ∈ v.adicCompletionIntegers F then ⟨x, h⟩ else 0
  have hto : ∀ x (h : x ∈ v.adicCompletionIntegers F), (toO x : v.adicCompletion F) = x := by
    intro x h
    simp only [toO, dif_pos h]
  let pr : G1 F → v.adicCompletionIntegers F × v.adicCompletionIntegers F :=
    fun g => (toO ((g 1 0).2 v), toO ((g 1 1).2 v))
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc (v.adicCompletionIntegers F) (s.image pr) (by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hp
    have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
      congrArg (fun x : A F => x.2 v) (row g)
    refine rowUnit (a := toO ((g 0 0).2 v)) (b := toO ((g 0 1).2 v)) (Subtype.ext ?_)
    push_cast
    rw [hto _ (hint g hg 0 0), hto _ (hint g hg 0 1), hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)]
    exact hdet) (lt_of_le_of_lt (by exact_mod_cast Finset.card_image_le) hbig)
  refine ⟨t, t.2, fun g hg => ?_⟩
  have h := valUnit v _ (ht _ (Finset.mem_image_of_mem pr hg))
  simp only [pr] at h
  push_cast at h
  rwa [hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)] at h

theorem UpperTheory.ConvolutionTheory.R2.C.generic :
    ∀ (F : Type) [Field F] [NumberField F] (s : Finset (G1 F)), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0) := by
  intro F _ _ s
  have hI : ∀ w : InfinitePlace F, ∃ t : w.Completion, ∀ g ∈ s, (g 1 0).1 w + (g 1 1).1 w * t ≠ 0 := by
    intro w
    haveI : CharZero w.Completion :=
      charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
    refine fieldCase w.Completion s (fun g => (g 1 0).1 w) (fun g => (g 1 1).1 w) fun g _ => ?_
    have hdet : (g 0 0).1 w * (g 1 1).1 w - (g 0 1).1 w * (g 1 0).1 w = 1 :=
      congrArg (fun x : A F => x.1 w) (row g)
    by_contra hn
    push_neg at hn
    simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  let G : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    (∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F) ∧
      (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  have hG : ∀ᶠ v in cofinite, G v := by
    refine Filter.Eventually.and ?_ (UpperTheory.ConvolutionTheory.R2.C.resBig F s.card)
    refine (Filter.eventually_all_finset s).2 fun g _ => ?_
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    exact (g i j).2.2
  have hF : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F,
      (G v → t ∈ v.adicCompletionIntegers F) ∧
      ∀ g ∈ s, (g 1 0).2 v + (g 1 1).2 v * t ≠ 0 ∧
        (G v → Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1) := by
    intro v
    by_cases hv : G v
    · obtain ⟨t, ht, hu⟩ := goodPlace s v hv.1 hv.2
      refine ⟨t, fun _ => ht, fun g hg => ⟨fun h0 => ?_, fun _ => hu g hg⟩⟩
      have := hu g hg
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · obtain ⟨t, ht⟩ := fieldCase (v.adicCompletion F) s (fun g => (g 1 0).2 v)
        (fun g => (g 1 1).2 v) (fun g _ => by
          have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
            congrArg (fun x : A F => x.2 v) (row g)
          by_contra hn
          push_neg at hn
          simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
          exact zero_ne_one hdet)
      exact ⟨t, fun h => absurd h hv, fun g hg => ⟨ht g hg, fun h => absurd h hv⟩⟩
  choose tI htI using hI
  choose tF htF using hF
  let tf : FiniteAdeleRing (𝓞 F) F := ⟨tF, hG.mono fun v hv => (htF v).1 hv⟩
  let t : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F := (tI, tf)
  let t' : A F := t
  let u : G1 F := ⟨!![1, 0; t', 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨u, fun g hg => ?_⟩
  have hu : (g * u) 1 0 = g 1 0 + g 1 1 * t' := by
    show (g.1 * !![1, 0; t', 1]) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp
  rw [hu]
  refine (UpperTheory.ConvolutionTheory.R2.C.unitA F _).2 ⟨fun w => htI w g hg, fun v => ((htF v).2 g hg).1, ?_⟩
  exact hG.mono fun v hv => ((htF v).2 g hg).2 hv
end

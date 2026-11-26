module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section Loc

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    Subalgebra F (FractionRing (MRing ι F ⧸ P)) :=
  Algebra.adjoin F {x | ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
    g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}

theorem div_mem_degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F)))
    {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) (hgP : g ∉ P)
    (hg𝒲 : ∀ W ∈ 𝒲, g ∉ W) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ degZeroLoc P 𝒲 :=
  Algebra.subset_adjoin ⟨b, f, g, hf, hg, hgP, hg𝒲, rfl⟩

end Loc

section Fibre

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

def fibrePrimes (P' : Ideal (MRing ι' F)) (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Set (Ideal (MRing ι' F)) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ contractPrime j W' = W}

theorem map_degZeroLoc_le (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    (degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P') ≤
      degZeroLoc P' (fibrePrimes j P' W) := by
  unfold degZeroLoc
  rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_, ?_⟩
  · rintro W' ⟨-, -, hc⟩ hgW'
    apply hgW W (Set.mem_singleton W)
    rw [← hc]
    exact hgW'
  · rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]

def degZeroLocContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    degZeroLoc (contractPrime j P') {W} →ₐ[F] degZeroLoc P' (fibrePrimes j P' W) :=
  ((contractFracMap j P').comp (degZeroLoc (contractPrime j P') {W}).val).codRestrict _
    (fun x => map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩))

instance degZeroLoc.algebraContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Algebra (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) :=
  (degZeroLocContract j P' W).toRingHom.toAlgebra

theorem degZeroLoc.algebraMap_contract_coe (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (x : degZeroLoc (contractPrime j P') {W}) :
    ((algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) x :
      degZeroLoc P' (fibrePrimes j P' W)) : FractionRing (MRing ι' F ⧸ P')) =
      contractFracMap j P' x :=
  rfl

end Fibre

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DivPushForward.proof (hC : ContractRelDimLe.Statement.{u})
    (hL : DivPushForwardLocal.Statement.{u}) : DivPushForward.Statement.{u} := by
  classical
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hdim hdimP c a ha haP N' N h1 h2
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  have hsup' := DivCycleSupport.proof F K' ι' P' hP' n hdim _ (rename (blockIncl j ι') a)
    (isMultiHomog_rename j ι' ha) haP
  have hsup := DivCycleSupport.proof F K _ _ hP n hdimP c a ha haP
  set D' := divCycle P' (rename (blockIncl j ι') a) with hD'
  set D := divCycle (contractPrime j P') a with hD
  have hfin : (Function.support D').Finite := by
    refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
      (P' ⊔ Ideal.span {rename (blockIncl j ι') a})).subset fun W' hW' => ?_
    by_contra h
    exact hW' (by rw [hD', divCycle, dite_eq_right (fun h' => h h'.1)])

  let rd : Ideal (MRing ι' F) → ℤ := fun W' =>
    if h : W'.IsPrime then haveI := h; (relDeg j W' : ℤ) else 0
  let M : Ideal (MRing (fun k => ι' (j k)) F) → Ideal (MRing ι' F) → ℤ := fun W W' =>
    if contractPrime j W' = W ∧ relDim W = (n : ℕ) then rd W' else 0
  have hM0 : ∀ W W', ¬ (contractPrime j W' = W ∧ relDim W = (n : ℕ)) → M W W' = 0 :=
    fun _ _ h => if_neg h
  have hM1 : ∀ (W : Ideal (MRing (fun k => ι' (j k)) F)) (W' : Ideal (MRing ι' F)) [hW' : W'.IsPrime], contractPrime j W' = W → relDim W = (n : ℕ) →
      M W W' = (relDeg j W' : ℤ) :=
    fun _ _ hW' hc hd => (if_pos ⟨hc, hd⟩).trans (dif_pos hW')

  have step1 : ∀ W', D' W' * N' W' = ∑ᶠ W, D' W' * M W W' * N W := by
    intro W'
    by_cases h0 : D' W' = 0
    · simp [h0]
    obtain ⟨hW', hdW'⟩ := hsup' W' h0
    rw [finsum_eq_single _ (contractPrime j W') (fun W hW => by
      rw [hM0 W W' (fun h => hW h.1.symm), mul_zero, zero_mul])]
    have hle := hC F K K' j ι' W' hW'
    rw [hdW'] at hle
    rcases hle.lt_or_eq with hlt | heq
    · rw [h2 W' hW' hdW' hlt]
      rw [hM0 _ W' (fun h => (ne_of_lt hlt) h.2), mul_zero, zero_mul]
    · rw [h1 W' hW' hdW' heq]
      rw [@hM1 _ W' hW'.isPrime rfl heq]
      ring

  have step2 : ∀ W, ∑ᶠ W', D' W' * M W W' = relDeg j P' * D W := by
    intro W
    by_cases hW : IsMultiProjPrime W ∧ relDim W = (n : ℕ)
    · exact hL F K K' j ι' P' hP' n hdim hdimP c a ha haP W hW.1 hW.2 (M W)
        (fun W' hW' hc => @hM1 W W' hW'.isPrime hc hW.2)
        (fun W' hc => hM0 W W' (fun h => hc h.1))
    · have hDW : D W = 0 := by
        by_contra h
        exact hW (hsup W h)
      rw [hDW, mul_zero]
      refine (finsum_congr fun W' => ?_).trans finsum_zero
      by_cases h0 : D' W' = 0
      · rw [h0, zero_mul]
      by_cases hc : contractPrime j W' = W ∧ relDim W = (n : ℕ)
      · exact absurd ⟨hc.1 ▸ isMultiProjPrime_contractPrime j ι' (hsup' W' h0).1, hc.2⟩ hW
      · rw [hM0 W W' hc, mul_zero]

  set s := hfin.toFinset
  set t := s.image (contractPrime j)
  have hsub : ∀ W', D' W' ≠ 0 → W' ∈ s := fun W' h => hfin.mem_toFinset.2 h
  have hzero : ∀ W' W, W' ∉ s ∨ W ∉ t → D' W' * M W W' * N W = 0 := by
    rintro W' W (h | h)
    · rw [show D' W' = 0 by by_contra h'; exact h (hsub W' h'), zero_mul, zero_mul]
    · by_cases h0 : D' W' = 0
      · rw [h0, zero_mul, zero_mul]
      have hc : ¬ (contractPrime j W' = W ∧ relDim W = (n : ℕ)) := fun hc =>
        h (Finset.mem_image.2 ⟨W', hsub W' h0, hc.1⟩)
      rw [hM0 W W' hc, mul_zero, zero_mul]
  have swap : ∑ᶠ W', ∑ᶠ W, D' W' * M W W' * N W = ∑ᶠ W, ∑ᶠ W', D' W' * M W W' * N W := by
    rw [finsum_congr fun W' => finsum_eq_sum_of_support_subset _ (s := t) fun W hW => by
        by_contra h; exact hW (hzero W' W (Or.inr h)),
      finsum_congr fun W => finsum_eq_sum_of_support_subset _ (s := s) fun W' hW' => by
        by_contra h; exact hW' (hzero W' W (Or.inl h)),
      finsum_eq_sum_of_support_subset _ (s := s) fun W' hW' => by
        by_contra h; exact hW' (Finset.sum_eq_zero fun W _ => hzero W' W (Or.inl h)),
      finsum_eq_sum_of_support_subset _ (s := t) fun W hW => by
        by_contra h; exact hW (Finset.sum_eq_zero fun W' _ => hzero W' W (Or.inr h)),
      Finset.sum_comm]
  calc cycEval N' D' = ∑ᶠ W', D' W' * N' W' := rfl
    _ = ∑ᶠ W', ∑ᶠ W, D' W' * M W W' * N W := finsum_congr step1
    _ = ∑ᶠ W, ∑ᶠ W', D' W' * M W W' * N W := swap
    _ = ∑ᶠ W, (∑ᶠ W', D' W' * M W W') * N W := finsum_congr fun W => (finsum_mul _ _).symm
    _ = ∑ᶠ W, (relDeg j P' : ℤ) * (D W * N W) := finsum_congr fun W => by rw [step2]; ring
    _ = relDeg j P' * cycEval N D := (mul_finsum _ _).symm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.BlockInclInjectiveOfEmbedding
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem PFContracted.natCast_lt_withBotWithTop {a b : ℕ} (h : a < b) :
    ((a : ℕ) : WithBot (WithTop ℤ)) < ((b : ℕ) : WithBot (WithTop ℤ)) := by
  show (((a : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((b : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by exact_mod_cast h))

theorem PFContracted.blockIncl_injective_of_embedding {K K' : Type} (j : K ↪ K') (ι' : K' → Type) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨k₁, x₁⟩ ⟨k₂, x₂⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  cases j.injective h1
  cases eq_of_heq h2
  rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

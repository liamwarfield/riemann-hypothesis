module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdentityCosetEntryProportionalColumnDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionsAgreeRationalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymChainPatternIffPlaceConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymChainPatternIffPlaceConditions
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.PatResidue

theorem zPos_lt {κ τ l j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rcases a with (i | i) | ⟨s, u⟩
  · have := i.isLt
    simp only [zPos]
    omega
  · have := i.isLt
    simp only [zPos]
    omega
  · have hs := s.isLt
    have hu := u.isLt
    have h2 : ((s : ℕ) + 1) * τ ≤ j * τ := Nat.mul_le_mul_right _ hs
    rw [Nat.add_mul, one_mul] at h2
    simp only [zPos]
    omega

theorem zPos_injective {κ τ l j : ℕ} {a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j} (h : zPos a = zPos b) : a = b := by
  rcases a with (i | i) | ⟨s, u⟩ <;> rcases b with (i' | i') | ⟨s', u'⟩ <;> simp only [zPos] at h
  · obtain rfl := Fin.ext h
    rfl
  · have := i.isLt
    omega
  · have := i.isLt
    omega
  · have := i'.isLt
    omega
  · obtain rfl := Fin.ext (Nat.add_left_cancel h)
    rfl
  · have := i.isLt
    omega
  · have := i'.isLt
    omega
  · have := i'.isLt
    omega
  · have e1 := PatPlaces.block_div (r := κ + l) (i := (s : ℕ)) u.isLt
    have e2 := PatPlaces.block_div (r := κ + l) (i := (s' : ℕ)) u'.isLt
    rw [h, e2] at e1
    obtain rfl : s = s' := Fin.ext e1.symm
    obtain rfl : u = u' := Fin.ext (Nat.add_left_cancel h)
    rfl

theorem places_to_pattern (F : Type) [Zero F] [One F] (κ ρ l τ j : ℕ) (R : ℕ → ℕ → F) :
    ((∀ p', p' < κ + l → R p' p' = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' →
        (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ →
        (p' - (κ + l)) / τ < (p - (κ + l)) / τ → R p p' = 0)) →
    (∀ (a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) := by
  rintro ⟨hA, hB⟩ a b hab
  by_cases he : a = b
  · subst he
    rw [if_pos rfl]
    rcases a with (i | i) | ⟨s, u⟩
    · exact (hA _ (by have := i.isLt; simp only [zPos]; omega)).1
    · exact (hA _ (by have := i.isLt; simp only [zPos]; omega)).1
    · exact absurd (by simp [FreeIx]) hab
  · rw [if_neg he]
    have hne : zPos a ≠ zPos b := fun h => he (zPos_injective h)
    have hs1 := PatPlaces.symIdx_cases κ ρ (zPos a)
    have hs2 := PatPlaces.symIdx_cases κ ρ (zPos b)
    rcases b with (j' | j') | ⟨s', u'⟩
    · refine (hA _ (by have := j'.isLt; simp only [zPos]; omega)).2 _ (zPos_lt a) hne ?_
      rcases a with (i | i) | ⟨s, u⟩
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · left
        simp only [zPos]
        omega
    · refine (hA _ (by have := j'.isLt; simp only [zPos]; omega)).2 _ (zPos_lt a) hne ?_
      rcases a with (i | i) | ⟨s, u⟩
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · left
        simp only [zPos]
        omega
    · rcases a with (i | i) | ⟨s, u⟩
      · exact absurd (by simp [FreeIx]) hab
      · exact absurd (by simp [FreeIx]) hab
      · have hlt : (s' : ℕ) < s := by
          simp only [FreeIx, not_le, Fin.lt_iff_val_lt_val] at hab
          exact hab
        refine hB _ _ (by simp only [zPos]; omega) (zPos_lt _) (zPos_lt _) ?_
        simp only [zPos]
        rw [PatPlaces.block_div u'.isLt, PatPlaces.block_div u.isLt]
        exact hlt

theorem pattern_to_places (F : Type) [Zero F] [One F] (κ ρ l τ j : ℕ) (R : ℕ → ℕ → F) :
    (∀ (a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) →
    ((∀ p', p' < κ + l → R p' p' = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' →
        (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ →
        (p' - (κ + l)) / τ < (p - (κ + l)) / τ → R p p' = 0)) := by
  intro hpat
  refine ⟨fun p' hp' => ?_, fun p p' h1 h2 h3 h4 => ?_⟩
  · obtain ⟨a, rfl⟩ := PatPlaces.zPos_surj (show p' < κ + l + j * τ by omega)
    refine ⟨?_, fun p hp hne hcond => ?_⟩
    · have h0 := hpat a a (by
        rcases a with (i | i) | ⟨s, u⟩
        · simp [FreeIx, FreeTop]
        · simp [FreeIx, FreeTop]
        · simp only [zPos] at hp'
          omega)
      rwa [if_pos rfl] at h0
    · obtain ⟨c, rfl⟩ := PatPlaces.zPos_surj hp
      have hca : c ≠ a := fun h => hne (h ▸ rfl)
      rw [hpat c a ?_, if_neg hca]
      have hs1 := PatPlaces.symIdx_cases κ ρ (zPos c)
      have hs2 := PatPlaces.symIdx_cases κ ρ (zPos a)
      rcases a with (i | i) | ⟨s', u'⟩
      · rcases c with (i' | i') | ⟨s, u⟩
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · simp [FreeIx]
      · rcases c with (i' | i') | ⟨s, u⟩
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · simp [FreeIx]
      · simp only [zPos] at hp'
        omega
  · obtain ⟨a, rfl⟩ := PatPlaces.zPos_surj h2
    obtain ⟨c, rfl⟩ := PatPlaces.zPos_surj h3
    rcases a with (i | i) | ⟨s', u'⟩
    · have := i.isLt
      simp only [zPos] at h1
      omega
    · have := i.isLt
      simp only [zPos] at h1
      omega
    · rcases c with (i | i) | ⟨s, u⟩
      · have h0 : zPos (Sum.inl (Sum.inl i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) - (κ + l) = 0 := by
          have := i.isLt
          simp only [zPos]
          omega
        rw [h0, Nat.zero_div] at h4
        exact absurd h4 (Nat.not_lt_zero _)
      · have h0 : zPos (Sum.inl (Sum.inr i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) - (κ + l) = 0 := by
          have := i.isLt
          simp only [zPos]
          omega
        rw [h0, Nat.zero_div] at h4
        exact absurd h4 (Nat.not_lt_zero _)
      · simp only [zPos] at h4
        rw [PatPlaces.block_div u'.isLt, PatPlaces.block_div u.isLt] at h4
        rw [hpat _ _ ?_, if_neg ?_]
        · intro h
          cases h
          exact lt_irrefl _ h4
        · simp only [FreeIx, Fin.le_iff_val_le_val]
          omega

section Entry
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem entry_iff {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {m : E} (hm : IntAt P m) (c : Prop) [Decidable c] :
    valuation k (ι m - (if c then 1 else 0)) < 1 ↔ redP P m = if c then 1 else 0 := by
  have hI := (GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU).2.1
  by_cases hc : c
  · simp only [if_pos hc]
    have h0 : ι m - 1 = ι (m + algebraMap (𝓞 E) E (-1)) := by
      simp [sub_eq_add_neg]
    rw [h0, hI _ (hm.add (IntAt.coe P _)), reduction_add hm (IntAt.coe P _), reduction_coe]
    simp [add_neg_eq_zero]
  · simp only [if_neg hc, sub_zero]
    exact hI m hm

end Entry

theorem pattern_iff_places : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l ρ τ j : ℕ) (M : ℕ → ℕ → E), (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) → ((∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔ ((∀ p', p' < κ + l → redP P (M p' p') = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' → (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → redP P (M p p') = 0) ∧ (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ → (p' - (κ + l)) / τ < (p - (κ + l)) / τ → redP P (M p p') = 0))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l ρ τ j M hM
  have h : (∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b →
      valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔
      (∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → redP P (M (zPos a) (zPos b)) = if a = b then 1 else 0) := by
    refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_
    rw [Matrix.one_apply]
    exact entry_iff hC hU (hM _ _ (zPos_lt a) (zPos_lt b)) (a = b)
  rw [h]
  exact ⟨pattern_to_places _ κ ρ l τ j fun p p' => redP P (M p p'),
    places_to_pattern _ κ ρ l τ j fun p p' => redP P (M p p')⟩

end GlobalTheory.PatResidue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymChainPatternIffPlaceConditionsStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symChainPattern_iff_place_conditions : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l ρ τ j : ℕ) (M : ℕ → ℕ → E), (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) → ((∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔ ((∀ p', p' < κ + l → redP P (M p' p') = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' → (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → redP P (M p p') = 0) ∧ (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ → (p' - (κ + l)) / τ < (p - (κ + l)) / τ → redP P (M p p') = 0))) := by
  first | exact @GlobalTheory.PatResidue.pattern_iff_places | exact GlobalTheory.PatResidue.pattern_iff_places | (intros; apply GlobalTheory.PatResidue.pattern_iff_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPoint
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem GlobalTheory.symLevel_lam_residue_elim : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  exact GlobalTheory.symLevel_lam_residue E K k P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPointStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevel_character_at_rational_point : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  first | exact @GlobalTheory.symLevel_lam_residue_elim | exact GlobalTheory.symLevel_lam_residue_elim | (intros; apply GlobalTheory.symLevel_lam_residue_elim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZPosIxSuccInl
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree

def zEquiv (κ l τ j : ℕ) : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem zEquiv_val {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : (zEquiv κ l τ j a).val = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]; ring

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}


open Classical in
def phiM (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ rS r t j N : ℕ)
    (M : ℕ → ℕ → E) : K :=
  if (∀ p p', p < N → p' < r + j * t → IntAt P (M p p')) ∧
      (∀ p p', r + j * t ≤ p → p < N → p' < r + j * t → IntAt P (M p p' / (q : E))) ∧
      (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < r + j * t → p ≠ p' →
        (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
      (∀ p p', r ≤ p' → p' < r + j * t → p < r + j * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)
  then LocE.lamGvS ψ₀ χ k₀ r t j M *
    (LocE.unitV (χ j) (Matrix.det (Matrix.of fun s s' : Fin (r + j * t) => M s.1 s'.1)))⁻¹ else 0

theorem PhiGS_eq (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    LocE.PhiGS q ψ₀ χ k₀ rS r t (j + 1) c' n' c n x =
      phiM q ψ₀ χ k₀ rS r t j (n + c) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) := by
  rfl

variable {k : Type} [Field k]

theorem zPos_ixSucc_inl {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inl a)) = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩ <;> rfl

theorem zPos_ixSucc_inr {κ l τ j : ℕ} (u : Fin τ) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inr u)) = κ + l + j * τ + u := rfl

theorem zPos_lt {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rw [← zEquiv_val]; exact (zEquiv κ l τ j a).isLt

theorem det_of_places (ι : E →+* k) {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} (f : X ≃ Fin n) (pos : X → ℕ)
    (off : ℕ) (h : ∀ x, pos x = off + (f x).val) (M : ℕ → ℕ → E) :
    Matrix.det (Matrix.of fun x y => ι (M (pos x) (pos y))) =
      ι (Matrix.det (Matrix.of fun s s' : Fin n => M (off + s.1) (off + s'.1))) := by
  rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self f]
  congr 1
  ext x y
  simp [h]

end GlobalTheory.SymBridge.TopAgree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionsAgreeRationalPoints
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree
variable {E K k : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdOrd_top {κ τ s : ℕ} (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 1)) :
    ∃ b', stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl b = Sum.inl b' ∧ xPos b' = zPos b := by
  rcases b with (i | i) | p
  · exact ⟨_, stdOrd_eps _ _ _ _ _ i, rfl⟩
  · have h := stdOrd_f (Fin κ) (Fin τ) (s + 1) 0 rfl i
    have e : (⟨0 + i.val, by omega⟩ : Fin (s + 1)) = i := Fin.ext (by simp)
    rw [e] at h
    exact ⟨_, h, rfl⟩
  · exact ⟨_, stdOrd_d _ _ _ _ _ p, rfl⟩

theorem top_entries (q : ℕ) (ι : E →+* k) {s κ : ℕ} (S : SymData k s κ) (τ n' n : ℕ)
    (e' : XIx (Fin κ) (Fin τ) (s + 1) ⊕ Fin 0 ≃ Fin (n' + 0)) (e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (n + 0))
    (he' : IsOrd (yPos xPos n') e') (he : IsOrd zPos e) (x : (Fin (n' + 0) → E) →ₗ[E] (Fin (n + 0) → E)) :
    (S.T (Fin τ)).PhiTop (toLoc ι e e' x) = S.P.iterPhi (Fin τ) S.μ S.tame (s + 1)
      (Matrix.of fun a b => ι (LocE.entB q κ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b))) := by
  simp only [SymData.T, typeChain, Chain.ofType, LatFrame.transport, LatFrame.coords]
  congr 1
  have hb : (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl)).bas.val = 1 := by
    ext (u | u) (v | v)
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact v.elim0
    · exact u.elim0
    · exact u.elim0
  ext a b
  obtain ⟨b', hb1, hb2⟩ := stdOrd_top (κ := κ) (τ := τ) (s := s) b
  have ha : zPos a < n := by have := (e a).isLt; rw [he a] at this; omega
  have hb' : zPos b < n' := by
    have := (e' (Sum.inl b')).isLt; rw [he' (Sum.inl b')] at this; simp [yPos] at this; omega
  have h1 : ∀ p N, (if p < κ then p else if p < κ + 0 then N + (p - κ) else p - 0) = p := by
    intro p N; split_ifs <;> omega
  rw [hb]
  simp only [LatFrame.refl, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_apply, id,
    Equiv.refl_apply, Matrix.of_apply, typeFrame, hb1, toLoc, LocE.entB, LocE.fIdx, LocE.scE, h1, if_pos ha, if_pos hb',
    sub_self, zpow_zero, mul_one, Loc.atN, dif_pos (show zPos a < n + 0 from ha)]
  have hv : (Pi.single (e' (Sum.inl b')) 1 : Fin (n' + 0) → E) = Loc.eN E (n' + 0) (zPos b) := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff, he' (Sum.inl b'), yPos, Sum.elim_inl, hb2]
  rw [hv, show e a = ⟨zPos a, by omega⟩ from Fin.ext (he a)]

theorem bottom_iff {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (κ l τ j : ℕ) (M : ℕ → ℕ → E) :
    MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
        Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k).submatrix
          (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j) id).toRows₂ ↔
      ∀ p p', κ + l + j * τ ≤ p → p < κ + l + (j + 1) * τ → p' < κ + l + j * τ → IntAt P (M p p' / (q : E)) := by
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  constructor
  · intro h p p' hp hp' hp''
    have := h ⟨p - (κ + l + j * τ), by rw [Nat.add_mul] at hp'; omega⟩ ((zEquiv κ l τ j).symm ⟨p', hp''⟩)
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr] at this
    rw [← zEquiv_val, Equiv.apply_symm_apply] at this
    rw [← (res.1 _)]
    convert this using 4
    omega
  · intro h u b
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr]
    rw [res.1]
    exact h _ _ (by omega) (by rw [Nat.add_mul]; omega) (zPos_lt b)

theorem unit_char {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {σ₀ : K →+* ℂ} {ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K}
    {χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {s κ : ℕ} {S : SymData k s κ} (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (i : ℕ) (d : E) (u : kˣ)
    (hd : IntAt P d) (hu : valuation k (u : k) = 1) (e : (u : k) = ι d) :
    (S.μ (i + 1) u : ℂ) = σ₀ (LocE.unitV (χ i) d) := by
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι S.ϖ hT.compl S.unif
  exact hT.chi i d u hd ((res.2.2.1 d hd).1 (e ▸ hu)) e

theorem intAt_div {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {a : E} (h : IntAt P (a / (q : E))) (hq : (q : E) ≠ 0) :
    IntAt P a := by
  have := h.mul (IntAt.coe P (q : 𝓞 E))
  simpa [div_mul_cancel₀ _ hq] using this

theorem core (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s κ : ℕ} (S : SymData k s κ) (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (τ j N : ℕ)
    (hN : N = κ + s + 1 + (j + 1) * τ) (M : ℕ → ℕ → E) :
    S.P.iterPhi (Fin τ) S.μ S.tame j (Matrix.of fun a b => ι (M (zPos a) (zPos b))) =
      σ₀ (phiM q ψ₀ χ κ S.ρ (κ + s + 1) τ j N M) := by
  subst hN
  have hC := hT.compl
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι S.ϖ hC S.unif
  have hq : (q : E) ≠ 0 := res.2.2.2.1
  have hpat := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S (Fin τ) j
  set T : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b)) with hTdef
  have hTop : ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₁ = T := by
    ext a b; simp [Matrix.toRows₁, hTdef, zPos_ixSucc_inl]
  have hB := bottom_iff hC S.unif κ (s + 1) τ j M

  have hpatM := GlobalTheory.T.symChainPattern_iff_place_conditions E k P q ι S.ϖ hC S.unif κ (s + 1) S.ρ τ j M
  have hKO := GlobalTheory.T.mem_integralGL_iff_isUnit_det_at_prime E k P q ι S.ϖ hC S.unif κ (s + 1) τ j M
  simp only [TypeDatum.iterPhi, TypeDatum.Phi, hTop]
  unfold phiM
  by_cases hb : MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₂
  swap
  · rw [if_neg hb, if_neg, map_zero]
    rintro ⟨-, h2, -⟩
    exact hb (hB.2 fun p p' h1 h1' h1'' => h2 p p' h1 (by rw [Nat.add_mul] at h1' ⊢; omega) h1'')
  rw [if_pos hb]
  have h2 := hB.1 hb
  have hzT : ∀ a b, T a b = ι (M (zPos a) (zPos b)) := fun a b => rfl
  have hdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g.val = T →
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) =
        ι (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hTdef,
      det_of_places ι (zEquiv κ (s + 1) τ j) zPos 0 (fun x => by simp [zEquiv_val]) M]
    simp only [zero_add]
    rfl
  have hintdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g ∈ KO k _ → g.val = T →
      IntAt P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg hgT
    rw [← hC.int, ← hdet g hgT, Valuation.mem_integer_iff, valuation_det_of_mem_KO hg]
  by_cases hJ : ∃ g ∈ (S.P.iter (Fin τ) S.μ S.tame j).J, g.val = T
  · obtain ⟨g, hgJ, hgT⟩ := hJ
    obtain ⟨hgKO, hgpat⟩ := (hpat g).1 hgJ
    obtain ⟨hint, -⟩ := hKO.1 ⟨g, hgKO, hgT⟩
    have hpat' : ∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j),
        ¬FreeIx S.ρ a b → (valuation k) (ι (M (zPos a) (zPos b)) -
          (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k) a b) < 1 := by
      intro a b hf; have := hgpat a b hf; rwa [hgT] at this
    obtain ⟨h3, h4⟩ := (hpatM hint).1 hpat'
    have hcond : (∀ p p', p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ → IntAt P (M p p')) ∧
        (∀ p p', κ + s + 1 + j * τ ≤ p → p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ →
          IntAt P (M p p' / (q : E))) ∧
        (∀ p', p' < κ + s + 1 → redP P (M p' p') = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
          (κ + s + 1 ≤ p ∨ symIdx κ S.ρ p' < symIdx κ S.ρ p ∨ (p' = κ + S.ρ ∧ p < κ)) → redP P (M p p') = 0) ∧
        (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
          (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → redP P (M p p') = 0) := by
      refine ⟨fun p p' hp hp' => ?_, fun p p' hp hp' hp'' => h2 p p' hp hp' hp'', h3, h4⟩
      by_cases hpa : p < κ + s + 1 + j * τ
      · exact hint p p' hpa hp'
      · exact intAt_div (h2 p p' (by omega) hp hp') hq
    rw [if_pos hcond, ← hgT, extZ_coe _ _ ⟨g, hgJ⟩, TypeDatum.rho_apply]
    obtain ⟨g₀, D, hg₀, hD, hlam⟩ := GlobalTheory.T.iteratedDepthOneLevel_character_closed_form k _ (Fin τ) S.P S.μ S.tame j ⟨g, hgJ⟩
    rw [hlam]
    simp only [Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, LocE.lamGvS, map_mul, map_prod, map_inv₀]
    congr 2
    · refine GlobalTheory.T.symmetricLevel_character_at_rational_point E K k P q ι σ₀ ψ₀ χ s κ S hT M (fun p p' hp hp' => hint p p' (by omega) (by omega)) g₀ ?_
      rw [hg₀, hgT]
      ext (x | x) (y | y) <;> rfl
    · rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hdi : ((Matrix.GeneralLinearGroup.det (D i) : kˣ) : k) =
          ι (Matrix.det (Matrix.of fun u v : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + v.val))) := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, (hD i).2, Ix.diagonalBlockOfMatrix, hgT]
        exact det_of_places ι (Equiv.refl _) (fun u : Fin τ => κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ)
          (fun _ => rfl) M
      refine unit_char hT i _ _ ?_ (valuation_det_of_mem_KO (hD i).1) hdi
      rw [← hC.int, ← hdi, Valuation.mem_integer_iff, valuation_det_of_mem_KO (hD i).1]
    · exact unit_char hT j _ _ (hintdet g hgKO hgT) (valuation_det_of_mem_KO hgKO) (hdet g hgT)
  · rw [extZ_of_not _ _ hJ]
    split_ifs with hc
    · have hnu : ¬ IsUnit (redP P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1))) := by
        intro hu
        have hint : ∀ p p', p < κ + (s + 1) + j * τ → p' < κ + (s + 1) + j * τ → IntAt P (M p p') :=
          fun p p' hp hp' => hc.1 p p' (by rw [Nat.add_mul]; omega) hp'
        obtain ⟨g, hgKO, hgT⟩ := hKO.2 ⟨hint, hu⟩
        refine hJ ⟨g, (hpat g).2 ⟨hgKO, fun a b hf => ?_⟩, hgT⟩
        rw [hgT]
        exact (hpatM hint).2 ⟨hc.2.2.1, hc.2.2.2⟩ a b hf
      rw [LocE.unitV, dite_eq_right hnu, _root_.inv_zero, mul_zero, map_zero]
    · rw [map_zero]

end GlobalTheory.SymBridge.TopAgree


open GlobalTheory.SymBridge.TopAgree in
theorem GlobalTheory.SymBridge.phiTopAgree_of_tie : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k)
    (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ),
    Comparison₂ P q ι σ₀ ψ₀ χ S → PhiTopAgree P q ι σ₀ ψ₀ χ S := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ n' c' n hn' hc' hn e' e he' he x
  subst hc'
  rw [top_entries q ι S τ n' n e' e he' he x,
    core P q ι σ₀ ψ₀ χ S hT τ (s + 1) (n + 0) (by omega)]
  exact congrArg σ₀ (PhiGS_eq q ψ₀ χ κ S.ρ (κ + s + 1) τ (s + 1) 0 n' 0 n x).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionsAgreeRationalPointsStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_testFunctions_agree_rationalPoints : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → PhiTopAgree P q ι σ₀ ψ₀ χ S := by
  first | exact @GlobalTheory.SymBridge.phiTopAgree_of_tie | exact GlobalTheory.SymBridge.phiTopAgree_of_tie | (intros; apply GlobalTheory.SymBridge.phiTopAgree_of_tie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunction
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.LastStepProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_of_not [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

theorem topAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → TopAgree Ch sel mu cst σ₀ P ι S ν := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν hA e' e he' he
  refine ⟨1, one_ne_zero, fun y y' hy' => ?_⟩
  have hm : R.m = s + 2 := hA.steps
  have hT := hA.tie
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hT.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega

  have hq : (qOf P.1 : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hB : hat S.ψ ν (-1) (cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk fun a => ι (y' (e' a))))
      ((toLoc ι e e' y) (Sum.inr ())) = σ₀ (ftY sel mu cst P η' y') := by
    rw [hrow, ftY, if_pos hA.mem]
    by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 (η' (Pi.single i 1))
    · rw [if_pos hη, GlobalTheory.StepData.Model.hat_coset S.cond hν (neg_mem (one_mem _)) _
        (fun a => (hint _).2 (hη _)), hdot]
      have hi : IntAt P.1 ((qOf P.1 : X.E) * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        have : (qOf P.1 : X.E) * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -∑ i, ((qOf P.1 : X.E) * y' i) * η' (Pi.single i 1) := by
          simp only [epsSg, Int.cast_neg, Int.cast_one, Finset.mul_sum]; ring_nf; simp [Finset.sum_neg_distrib]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [this, map_neg, map_sum]
        exact neg_mem (sum_mem fun i _ => by rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i)))
      have h1 := hT.psi _ hi
      have h2 := hA.psi0 _ hi
      rw [mul_div_cancel_left₀ _ hq] at h1 h2
      rw [h2, ← h1]
      simp [epsSg]
    · rw [if_neg hη, map_zero]
      exact LastStepProof.hat_coset_of_not S.cond hν (by simp) _
        fun h => hη fun i => by simpa using (hint _).1 (h (e'.symm i))

  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  have hρ : R.rS = S.ρ := by have := S.odd; unfold Ranks.rS; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; omega
  have hN : R.N R.m - 1 = R.k + s + 1 + (s + 2) * R.t := by
    unfold Ranks.N; rw [hm]
    have : (s + 2) * (R.t + 1) = (s + 2) * R.t + (s + 2) := by ring
    omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) := fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrd (yPos xPos (R.N (s + 1))) E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hPT := GlobalTheory.T.lastStep_testFunctions_agree_rationalPoints X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hT R.t (R.N (s + 1))
    (cOf R (s + 1)) (R.N R.m - 1) rfl hc hN E1' E1 hE1' hE1
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  have hkey : ∀ c' n' c n : ℕ, LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t R.m c' n' c n =
      LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k S.ρ (R.k + s + 1) R.t (s + 2) c' n' c n := by
    intro c' n' c n; rw [hρ, hr, hm]
  have hA' : (S.T (Fin R.t)).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
      σ₀ (PhiTop Ch mu cst.sharp s P.1
        (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
    rw [hmat, hPT, PhiTop, if_pos hA.mem, hA.sharp, if_pos rfl, hkey]
  simp only [Chain.xiTop]
  rw [one_mul, map_mul, hA', hB]

end GlobalTheory.SymBridge.LastStepProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunctionStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDatum_completion_eq_columnTestFunction : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → TopAgree Ch sel mu cst σ₀ P ι S ν := by
  first | exact @GlobalTheory.SymBridge.LastStepProof.topAgree | exact GlobalTheory.SymBridge.LastStepProof.topAgree | (intros; apply GlobalTheory.SymBridge.LastStepProof.topAgree <;> assumption)
end
end

namespace GlobalTheory.SymBridge

theorem matchAtType : MatchAtType := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν h
  exact ⟨GlobalTheory.T.identityCoset_entry_proportional_columnDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    GlobalTheory.T.psiDatum_agree_columnDatum_at_typePrime X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    GlobalTheory.T.stepDatum_completion_eq_columnTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h⟩

end GlobalTheory.SymBridge

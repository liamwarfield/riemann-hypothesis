module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
noncomputable section

open scoped Matrix

namespace GlobalTheory.Sl2Ad

variable {K : Type*} [Field K]

def coord (X : Matrix (Fin 2) (Fin 2) K) : Fin 3 → K := ![X 0 1, X 1 0, X 0 0]

def ofCoord (v : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K := !![v 2, v 0; v 1, -v 2]

def ad (A : GL (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i

def form : LinearMap.BilinForm K (Fin 3 → K) := Matrix.toBilin' !![0, 1, 0; 1, 0, 0; 0, 0, 2]

theorem trace_ofCoord (v : Fin 3 → K) : (ofCoord v).trace = 0 := by
  simp [ofCoord, Matrix.trace_fin_two]

theorem ofCoord_coord {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) : ofCoord (coord X) = X := by
  rw [Matrix.trace_fin_two] at hX
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord, coord] <;> linear_combination -hX

theorem coord_ofCoord (v : Fin 3 → K) : coord (ofCoord v) = v := by
  ext i; fin_cases i <;> simp [ofCoord, coord]

theorem coord_add (X Y : Matrix (Fin 2) (Fin 2) K) : coord (X + Y) = coord X + coord Y := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_smul (c : K) (X : Matrix (Fin 2) (Fin 2) K) : coord (c • X) = c • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem ofCoord_eq_sum (v : Fin 3 → K) : ofCoord v = ∑ j, v j • ofCoord (Pi.single j 1) := by
  ext i k; fin_cases i <;> fin_cases k <;> simp [ofCoord, Fin.sum_univ_three]

theorem coord_conj_ofCoord (A : GL (Fin 2) K) (v : Fin 3 → K) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ v := by
  conv_lhs => rw [ofCoord_eq_sum]
  ext i
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mulVec, dotProduct, ad, Matrix.of_apply]
  rw [show ∀ (s : Finset (Fin 3)) (f : Fin 3 → Matrix (Fin 2) (Fin 2) K), coord (∑ j ∈ s, f j) i = ∑ j ∈ s, coord (f j) i from by
    intro s f; induction s using Finset.induction_on with
    | empty => simp [coord]; fin_cases i <;> rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add, Pi.add_apply, ih]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coord_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem trace_conj (A : GL (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem coord_conj (A : GL (Fin 2) K) {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ coord X := by
  conv_lhs => rw [← ofCoord_coord hX]
  exact coord_conj_ofCoord A _

theorem ad_mul (A B : GL (Fin 2) K) : ad (A * B) = ad A * ad B := by
  ext i j
  have h1 := coord_conj_ofCoord (A * B) (Pi.single j 1)
  have h2 := coord_conj_ofCoord B (Pi.single j 1)
  have h3 := coord_conj A (X := (B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (by rw [trace_conj, trace_ofCoord])
  rw [h2] at h3
  have : ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * (((A * B)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (A : Matrix (Fin 2) (Fin 2) K) * ((B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [this, h3, Matrix.mulVec_mulVec] at h1
  have := congrFun h1 i
  simpa [Matrix.mulVec_single, Matrix.mul_apply] using this.symm

theorem ad_one : ad (1 : GL (Fin 2) K) = 1 := by
  ext i j
  simp only [ad, Matrix.of_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, coord_ofCoord]
  fin_cases i <;> fin_cases j <;> rfl

def adHom : GL (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := ad
  map_one' := ad_one
  map_mul' := ad_mul

theorem form_apply (v w : Fin 3 → K) : form v w = v 0 * w 1 + v 1 * w 0 + 2 * (v 2 * w 2) := by
  simp [form, Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem form_coord {X Y : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) (hY : Y.trace = 0) :
    form (coord X) (coord Y) = (X * Y).trace := by
  rw [Matrix.trace_fin_two] at hX hY
  rw [form_apply]
  simp [coord, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (X 0 0) * hY - (Y 1 1) * hX

end GlobalTheory.Sl2Ad

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducible
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory.Sl2Ad

theorem form_ne_zero_of_isIrr : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ →
    ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  intro K _ _ Γ _ ρ hirr y hy hstab hform
  have hq : y 0 * y 1 + y 2 * y 2 = 0 := by
    rw [form_apply] at hform
    have h2 : (2 : K) * (y 0 * y 1 + y 2 * y 2) = 0 := by linear_combination hform
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hconj : ∀ g, ∃ c : K, ofCoord y * (ρ g : Matrix (Fin 2) (Fin 2) K) = (ρ g : Matrix (Fin 2) (Fin 2) K) * (c • ofCoord y) := by
    intro g
    obtain ⟨c, hc⟩ := hstab g⁻¹
    refine ⟨c, ?_⟩
    have h1 := coord_conj_ofCoord (ρ g⁻¹) y
    rw [hc] at h1
    have htr : ((ρ g⁻¹ : Matrix (Fin 2) (Fin 2) K) * ofCoord y * (((ρ g⁻¹)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = 0 := by
      rw [trace_conj, trace_ofCoord]
    have h2 := ofCoord_coord htr
    rw [h1] at h2
    have h3 : ofCoord (c • y) = c • ofCoord y := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord]
    rw [h3, map_inv, inv_inv] at h2
    have hu : (ρ g : Matrix (Fin 2) (Fin 2) K) * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  let Wk : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.mulVecLin (ofCoord y))
  have hmem : ∀ x, x ∈ Wk ↔ ofCoord y *ᵥ x = 0 := fun x => by
    simp [Wk, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hinv : IsInv ρ Wk := by
    intro g x hx
    rw [hmem] at hx ⊢
    obtain ⟨c, hc⟩ := hconj g
    have hs : (c • ofCoord y) *ᵥ x = c • (ofCoord y *ᵥ x) := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hs, hx, smul_zero, Matrix.mulVec_zero]
  have hy0 : ∀ a b c : K, a = 0 → b = 0 → c = 0 → y 0 = a → y 1 = b → y 2 = c → False := by
    intro a b c ha hb hc h0 h1 h2
    apply hy
    ext i; fin_cases i
    · simpa [ha] using h0
    · simpa [hb] using h1
    · simpa [hc] using h2
  rcases hirr.2.2 Wk le_top hinv with h | h
  · have hv1 : (![y 0, -y 2] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    have hv2 : (![y 2, y 1] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    rw [h, Submodule.mem_bot] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b1 := congrFun hv2 1
    simp at a0 a1 b1
    exact hy0 0 0 0 rfl rfl rfl a0 b1 a1
  · have hv1 : (Pi.single 0 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    have hv2 : (Pi.single 1 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    rw [hmem] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b0 := congrFun hv2 0
    simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1 b0
    exact hy0 0 0 0 rfl rfl rfl b0 a1 a0

end GlobalTheory.Sl2Ad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducibleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_ne_zero_of_stable_line_irreducible : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  first | exact @GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr | exact GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr | (intros; apply GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducible
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory

theorem ad_invariant_eq_zero_of_isIrr {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ]
    (ρ : Γ →* GL (Fin 2) K) (hρ : IsIrr ρ) (v : Fin 3 → K) (hv : ∀ g, ad (ρ g) *ᵥ v = v) : v = 0 := by
  set Y : Matrix (Fin 2) (Fin 2) K := ofCoord v with hY

  have hcomm : ∀ g, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
    intro g
    have h1 : coord ((ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = coord Y := by
      rw [coord_conj_ofCoord, hv g, coord_ofCoord]
    have h2 : (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y := by
      have := congrArg ofCoord h1
      rwa [ofCoord_coord (by rw [trace_conj, trace_ofCoord]), ofCoord_coord (trace_ofCoord v)] at this
    calc (ρ g : Matrix (Fin 2) (Fin 2) K) * Y
        = (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc _ _ (ρ g : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hW
  have hWne : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
  have hWinv : IsInv ρ W := by
    intro g x hx
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have hWtop : W = ⊤ := by
    rcases hρ.2.2 W le_top hWinv with h | h
    · exact absurd h hWne
    · exact h
  have hYμ : Y = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    have hx : (Pi.single j 1 : Fin 2 → K) ∈ W := by rw [hWtop]; trivial
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_single_one] at hx
    have := congrFun hx i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  have htr : (2 : K) * μ = 0 := by
    have := trace_ofCoord v
    rw [← hY, hYμ, Matrix.trace_smul, Matrix.trace_one] at this
    simpa [mul_comm] using this
  have hμ0 : μ = 0 := by
    rcases mul_eq_zero.mp htr with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hY0 : Y = 0 := by rw [hYμ, hμ0, zero_smul]
  rw [← coord_ofCoord v, ← hY, hY0]
  ext i; fin_cases i <;> simp [coord]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducibleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ v : Fin 3 → K, (∀ g, ad (ρ g) *ᵥ v = v) → v = 0 := by
  first | exact @GlobalTheory.ad_invariant_eq_zero_of_isIrr | exact GlobalTheory.ad_invariant_eq_zero_of_isIrr | (intros; apply GlobalTheory.ad_invariant_eq_zero_of_isIrr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThree
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducible
open scoped Matrix

namespace GlobalTheory.AugSpan

theorem exists_mem_span_sub_one_eq_id_on :
    ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ}
      (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)),
      (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) →
      (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) →
      (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) →
      ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  intro K _ _ Γ _ m S P hst hirrP hnt
  classical
  set J := Submodule.span K (Set.range fun g => S g - 1) with hJ
  obtain ⟨g₀, v₀, hv₀, hne⟩ := hnt
  have hP : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hv₀
    apply hne
    rw [hv₀, Matrix.mulVec_zero]
  have hinv : ∀ g, ∀ v ∈ P, (Matrix.toLin' (S g)) v ∈ P :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact hst g v hv
  let r : Representation K Γ P :=
    { toFun := fun g => (Matrix.toLin' (S g)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : P), ((r g v : P) : Fin m → K) = S g *ᵥ (v : Fin m → K) :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => hP ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule K P) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : P) ∈ (⊥ : Submodule K P) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map P.subtype ≤ P := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : ∀ g, ∀ v ∈ W.toSubmodule.map P.subtype, S g *ᵥ v ∈ W.toSubmodule.map P.subtype := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases hirrP _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule K P)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  have hJl : ∀ g, ∀ T ∈ J, S g * T ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : S g * (S h - 1) = (S (g * h) - 1) - (S g - 1) := by
        rw [map_mul, mul_sub, mul_one]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hx
  have hJr : ∀ g, ∀ T ∈ J, T * S g ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : (S h - 1) * S g = (S (h * g) - 1) - (S g - 1) := by
        rw [map_mul, sub_mul, one_mul]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hx
  let J' : Submodule K (Module.End K P) :=
    { carrier := {f | ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w}
      add_mem' := by
        rintro f f' ⟨T, hT, hTf⟩ ⟨T', hT', hTf'⟩
        exact ⟨T + T', J.add_mem hT hT', fun w => by
          rw [Matrix.add_mulVec, hTf, hTf']; simp⟩
      zero_mem' := ⟨0, J.zero_mem, fun w => by simp⟩
      smul_mem' := by
        rintro c f ⟨T, hT, hTf⟩
        exact ⟨c • T, J.smul_mem c hT, fun w => by
          rw [Matrix.smul_mulVec, hTf]; simp⟩ }
  have hmem : ∀ f, f ∈ J' ↔ ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w := fun f => Iff.rfl
  have hl : ∀ a : Module.End K P, ∀ f ∈ J', a * f ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨S g * T, hJl g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, hTf, Module.End.mul_apply, hr]
    | zero => rw [zero_mul]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact J'.smul_mem c hx
  have hrt : ∀ a : Module.End K P, ∀ f ∈ J', f * a ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨T * S g, hJr g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, ← hr, hTf, Module.End.mul_apply]
    | zero => rw [mul_zero]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact J'.smul_mem c hx
  set f₀ : Module.End K P := r g₀ - 1 with hf₀def
  have hf₀ : f₀ ∈ J' := (hmem _).2 ⟨S g₀ - 1, Submodule.subset_span ⟨g₀, rfl⟩, fun w => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr]; rfl⟩
  set w₀ : P := ⟨v₀, hv₀⟩ with hw₀
  have hfw : f₀ w₀ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    rw [hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr, Submodule.coe_zero, sub_eq_zero] at h'
    exact h'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K P, ψ (f₀ w₀) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hfw ((Module.forall_dual_apply_eq_zero_iff K _).1 hc)
  let b := Module.finBasis K P
  have hid : (1 : Module.End K P) ∈ J' := by
    have heq : (1 : Module.End K P) = ∑ i, ((ψ (f₀ w₀))⁻¹ • ψ.smulRight (b i)) * f₀ *
        ((b.coord i).smulRight w₀) := by
      ext1 w
      rw [LinearMap.sum_apply, Module.End.one_apply]
      conv_lhs => rw [← b.sum_repr w]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        smul_eq_mul, smul_smul, Module.Basis.coord_apply]
      congr 1
      field_simp
    rw [heq]
    exact J'.sum_mem fun i _ => hrt _ _ (hl _ _ hf₀)
  obtain ⟨T, hT, hTid⟩ := (hmem _).1 hid
  exact ⟨T, hT, fun v hv => hTid ⟨v, hv⟩⟩

end GlobalTheory.AugSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducibleStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible : ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ} (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)), (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) → (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) → (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) → ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  first | exact @GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | exact GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | (intros; apply GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThree
open scoped Matrix

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {m : ℕ}

abbrev augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) : Submodule K (Matrix (Fin m) (Fin m) K) :=
  Submodule.span K (Set.range fun g => S g - 1)

def Stable (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P

theorem mul_mem_augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) {A C : Matrix (Fin m) (Fin m) K}
    (hA : A ∈ augSpan S) (hC : C ∈ augSpan S) : A * C ∈ augSpan S := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hC using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      have e : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
        rw [map_mul]; noncomm_ring
      rw [e]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ a hx

theorem augSpan_preserves (S : Γ →* Matrix (Fin m) (Fin m) K) {P : Submodule K (Fin m → K)}
    (hP : Stable S P) {T : Matrix (Fin m) (Fin m) K} (hT : T ∈ augSpan S) :
    ∀ v ∈ P, T *ᵥ v ∈ P := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact P.sub_mem (hP g v hv) hv
  | zero => intro v _; rw [Matrix.zero_mulVec]; exact P.zero_mem
  | add x y _ _ hx hy => intro v hv; rw [Matrix.add_mulVec]; exact P.add_mem (hx v hv) (hy v hv)
  | smul a x _ hx => intro v hv; rw [Matrix.smul_mulVec]; exact P.smul_mem a (hx v hv)

def Good (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∃ T ∈ augSpan S, ∀ v ∈ P, T *ᵥ v = v

theorem good_sup (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) (gL : Good S L) (gP : Good S P) : Good S (L ⊔ P) := by
  obtain ⟨T₁, h₁, e₁⟩ := gL
  obtain ⟨T₂, h₂, e₂⟩ := gP
  refine ⟨T₁ + T₂ - T₁ * T₂, Submodule.sub_mem _ (Submodule.add_mem _ h₁ h₂)
    (mul_mem_augSpan S h₁ h₂), ?_⟩
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hTa : T₂ *ᵥ a ∈ L := augSpan_preserves S hL h₂ a ha
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
    e₁ a ha, e₂ b hb, e₁ _ hTa]
  abel

theorem good_bot (S : Γ →* Matrix (Fin m) (Fin m) K) : Good S ⊥ :=
  ⟨0, Submodule.zero_mem _, fun v hv => by
    rw [(Submodule.mem_bot K).mp hv, Matrix.mulVec_zero]⟩

theorem stable_inf (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) : Stable S (L ⊓ P) :=
  fun g v hv => ⟨hL g v hv.1, hP g v hv.2⟩

theorem stable_orthogonal (S : Γ →* Matrix (Fin m) (Fin m) K)
    (B : LinearMap.BilinForm K (Fin m → K))
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) {Q : Submodule K (Fin m → K)}
    (hQ : Stable S Q) : Stable S (B.orthogonal Q) := by
  intro g v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro n hn
  have e : S g *ᵥ (S g⁻¹ *ᵥ n) = n := by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have := hv _ (hQ g⁻¹ n hn)
  rw [← e, hinv]
  exact this

end GlobalTheory.AugCore

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

theorem inf_orthogonal_eq_bot (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊓ B.orthogonal Q = ⊥ := by
  set Z := Q ⊓ B.orthogonal Q with hZ
  have hZs : Stable S Z := stable_inf S hQ hQo
  have hZle : Z ≤ B.orthogonal Z := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz.2) n hn.1
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hfo : Module.finrank K (B.orthogonal Z) = 3 - Module.finrank K Z := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, h3]
  have hmono := Submodule.finrank_mono hZle
  by_contra hne
  obtain ⟨y, hyZ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsp : (K ∙ y) ≤ Z := (Submodule.span_singleton_le_iff_mem y Z).mpr hyZ
  have h1 : Module.finrank K (K ∙ y) = 1 := finrank_span_singleton hy0
  have hspm := Submodule.finrank_mono hsp
  have hZ1 : Module.finrank K Z = 1 := by omega
  have heq : (K ∙ y) = Z := Submodule.eq_of_le_of_finrank_eq hsp (by rw [h1, hZ1])
  apply hiso y hy0
  · intro g
    have : S g *ᵥ y ∈ (K ∙ y) := by rw [heq]; exact hZs g y hyZ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hyZ.2) y hyZ.1

theorem sup_orthogonal_eq_top (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊔ B.orthogonal Q = ⊤ := by
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have key := Submodule.finrank_sup_add_finrank_inf_eq Q (B.orthogonal Q)
  rw [inf_orthogonal_eq_bot S B hB hiso hQ hQo, finrank_bot,
    LinearMap.BilinForm.finrank_orthogonal hB, h3] at key
  have hle := Submodule.finrank_le Q
  rw [h3] at hle
  apply Submodule.eq_top_of_finrank_eq
  rw [h3]; omega

theorem good_of_stable (S : Γ →* Matrix (Fin 3) (Fin 3) K) [IsAlgClosed K]
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w)
    (hfix : ∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) :
    ∀ n, ∀ P : Submodule K (Fin 3 → K), Stable S P → Module.finrank K P = n → Good S P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP hn
  by_cases hirr : ∀ Q : Submodule K (Fin 3 → K), Q ≤ P → Stable S Q → Q = ⊥ ∨ Q = P
  · by_cases hbot : P = ⊥
    · rw [hbot]; exact good_bot S
    · have hnt : ∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v := by
        by_contra hc
        push_neg at hc
        apply hbot
        rw [Submodule.eq_bot_iff]
        intro v hv
        exact hfix v (fun g => hc g v hv)
      exact GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible S P hP hirr hnt
  · push_neg at hirr
    obtain ⟨Q, hQP, hQs, hQ0, hQne⟩ := hirr
    have hQo : Stable S (B.orthogonal Q) := stable_orthogonal S B hinv hQs
    set R := P ⊓ B.orthogonal Q with hR
    have hRs : Stable S R := stable_inf S hP hQo
    have htop := sup_orthogonal_eq_top S B hB hiso hQs hQo
    have hinf := inf_orthogonal_eq_bot S B hB hiso hQs hQo
    have hQR : Q ⊔ R = P := by
      apply le_antisymm (sup_le hQP inf_le_left)
      intro v hv
      have hvt : v ∈ Q ⊔ B.orthogonal Q := by rw [htop]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvt
      have hbP : b ∈ P := by
        have := P.sub_mem hv (hQP ha)
        simpa using this
      exact Submodule.mem_sup.mpr ⟨a, ha, b, ⟨hbP, hb⟩, rfl⟩
    have hQlt : Module.finrank K Q < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hQP hQne)
    have hRne : R ≠ P := by
      intro hRP
      apply hQ0
      rw [eq_bot_iff, ← hinf]
      intro x hx
      have : x ∈ R := by rw [hRP]; exact hQP hx
      exact ⟨hx, this.2⟩
    have hRlt : Module.finrank K R < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hRne)
    have g := good_sup S hQs hRs (ih _ hQlt Q hQs rfl) (ih _ hRlt R hRs rfl)
    rwa [hQR] at g

end GlobalTheory.AugCore

theorem GlobalTheory.augSpan_one_mem_of_orthogonal_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  intro K _ _ _ Γ _ S B hB _ hinv hfix hiso
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.AugCore.good_of_stable S B hB hinv hfix hiso _ ⊤
    (fun _ _ _ => trivial) rfl
  have e : T = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    exact hTv v trivial
  exact (congrArg (· ∈ Submodule.span K (Set.range fun g => S g - 1)) e).mp hT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThreeStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  first | exact @GlobalTheory.augSpan_one_mem_of_orthogonal_three | exact GlobalTheory.augSpan_one_mem_of_orthogonal_three | (intros; apply GlobalTheory.augSpan_one_mem_of_orthogonal_three <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZero
open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem det_affine_eval {K : Type} [Field K] {m : ℕ} (U V : Matrix (Fin m) (Fin m) K) (t : K) :
    ((X : K[X]) • V.map C + U.map C).det.eval t = (U + t • V).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [add_comm]
  ring

theorem exists_nat_det_ne_zero_affine {K : Type} [Field K] [CharZero K] {m : ℕ}
    (U V : Matrix (Fin m) (Fin m) K) (t : K) (h : (U + t • V).det ≠ 0) :
    ∃ k : ℕ, (U + (k : K) • V).det ≠ 0 := by
  classical
  set p : K[X] := ((X : K[X]) • V.map C + U.map C).det
  have hp : p ≠ 0 := by
    intro h0
    apply h
    rw [← det_affine_eval]
    simp [p, h0]
  by_contra hall
  push_neg at hall
  have hsub : Set.range (fun k : ℕ => (k : K)) ⊆ (p.roots.toFinset : Set K) := by
    rintro _ ⟨k, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot, det_affine_eval]
    exact hall k
  have hinf : (Set.range (fun k : ℕ => (k : K))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  exact hinf ((p.roots.toFinset.finite_toSet).subset hsub)

theorem exists_nat_coeffs_on_finset_det_sum_ne_zero {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (s : Finset (Fin n)) :
    ∀ b : Fin n → K, (∑ i, b i • T i).det ≠ 0 →
      ∃ b' : Fin n → K, (∑ i, b' i • T i).det ≠ 0 ∧ ∀ i ∈ s, ∃ k : ℕ, b' i = k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro b hb; exact ⟨b, hb, by simp⟩
  | insert j s hj ih =>
    intro b hb
    obtain ⟨b₁, hb₁, hs⟩ := ih b hb
    have key : ∀ t : K, ∑ i, Function.update b₁ j t i • T i
        = (∑ i, Function.update b₁ j 0 i • T i) + t • T j := by
      intro t
      have h1 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j t i • T i) (Finset.mem_univ j)
      have h2 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j 0 i • T i) (Finset.mem_univ j)
      have h3 : ∑ i ∈ Finset.univ.erase j, Function.update b₁ j t i • T i
          = ∑ i ∈ Finset.univ.erase j, Function.update b₁ j 0 i • T i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
          Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [← h1, ← h2, h3]
      simp
    have hb₁' : ((∑ i, Function.update b₁ j 0 i • T i) + b₁ j • T j).det ≠ 0 := by
      rw [← key, Function.update_eq_self]; exact hb₁
    obtain ⟨k, hk⟩ := exists_nat_det_ne_zero_affine _ _ _ hb₁'
    refine ⟨Function.update b₁ j (k : K), by rw [key]; exact hk, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨k, by simp⟩
    · obtain ⟨k', hk'⟩ := hs i hi'
      refine ⟨k', ?_⟩
      rw [Function.update_of_ne (by rintro rfl; exact hj hi')]
      exact hk'

theorem exists_nat_coeffs_det_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K),
    (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  intro K _ _ m n T b hb
  obtain ⟨b', hb', hs⟩ := exists_nat_coeffs_on_finset_det_sum_ne_zero T Finset.univ b hb
  choose a ha using fun i => hs i (Finset.mem_univ i)
  refine ⟨a, ?_⟩
  simp_rw [← ha]; exact hb'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZeroStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_coeffs_det_sum_smul_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ} (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K), (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  first | exact @GlobalTheory.exists_nat_coeffs_det_ne_zero | exact GlobalTheory.exists_nat_coeffs_det_ne_zero | (intros; apply GlobalTheory.exists_nat_coeffs_det_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZero
open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem one_mem_of_mulClosed_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)),
    (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  intro F K _ _ _ _ m S hS T hT hdet
  classical
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet)
  have hint : IsIntegral F T := by
    have hK : IsIntegral K T := Algebra.IsIntegral.isIntegral T
    exact isIntegral_trans T hK
  have hpow : ∀ n : ℕ, T ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ]; exact hS _ ih _ hT
  have hmul : ∀ q : F[X], T * aeval T q ∈ S := by
    intro q
    rw [aeval_eq_sum_range, Finset.mul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']
    exact S.smul_mem _ (hpow i)
  set p := minpoly F T with hpdef
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hkey : T * aeval T p.divX + algebraMap F _ (p.coeff 0) = 0 := by
    have h0 : aeval T p = 0 := minpoly.aeval F T
    have e : aeval T p = T * aeval T p.divX + algebraMap F _ (p.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add p, mul_comm p.divX X]
      simp only [map_add (f := _), map_mul, aeval_X, aeval_C]
    rw [← e, h0]
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero, add_zero] at hkey
    have hq : aeval T p.divX = 0 := by
      exact hTu.mul_right_eq_zero.1 hkey
    have hne : p.divX ≠ 0 := by
      intro h
      rw [divX_eq_zero_iff, hc, map_zero] at h
      exact hp0 h
    have hle := minpoly.degree_le_of_ne_zero F T hne hq
    exact absurd (degree_divX_lt hp0) (not_lt.2 hle)
  have hone : (1 : Matrix (Fin m) (Fin m) K) = (-(p.coeff 0)⁻¹) • (T * aeval T p.divX) := by
    rw [eq_neg_of_add_eq_zero_left hkey, smul_neg, neg_smul, neg_neg, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hc, map_one]
  rw [hone]
  exact S.smul_mem _ (hmul _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZeroStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)), (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | exact GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | (intros; apply GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrredu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Sl2Ad

theorem form_isSymm {K : Type} [Field K] : (form (K := K)).IsSymm := by
  first
  | exact ⟨fun v w => by simp only [RingHom.id_apply, form_apply]; ring⟩
  | exact fun v w => by simp only [RingHom.id_apply, form_apply]; ring
  | (intro v w; simp only [RingHom.id_apply, form_apply]; ring)

theorem form_ad {K : Type} [Field K] (A : GL (Fin 2) K) (v w : Fin 3 → K) :
    form (ad A *ᵥ v) (ad A *ᵥ w) = form v w := by
  rw [← coord_conj_ofCoord, ← coord_conj_ofCoord,
    form_coord (by rw [trace_conj, trace_ofCoord]) (by rw [trace_conj, trace_ofCoord])]
  conv_rhs => rw [← coord_ofCoord v, ← coord_ofCoord w, form_coord (trace_ofCoord v) (trace_ofCoord w)]
  have : ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord w * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = (A : Matrix (Fin 2) (Fin 2) K) * (ofCoord v * ofCoord w) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), h, Matrix.one_mul]
  rw [this, trace_conj]

theorem form_nondegenerate {K : Type} [Field K] [CharZero K] : (form (K := K)).Nondegenerate := by
  rw [form, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  simp [Matrix.det_fin_three]

theorem coord_smul_scalar {F K : Type} [Field F] [Field K] [Algebra F K] (a : F) (X : Matrix (Fin 2) (Fin 2) K) :
    coord (a • X) = a • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_sum {K : Type} [Field K] {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) K) :
    coord (∑ i ∈ s, f i) = ∑ i ∈ s, coord (f i) := by
  ext j; fin_cases j <;> simp [coord, Matrix.sum_apply]

end GlobalTheory.Sl2Ad


open GlobalTheory.Sl2Ad in
theorem GlobalTheory.Sl2Ad.augmentation_contains_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  intro l _ c Γ _ r _ hirr
  set S : Γ →* Matrix (Fin 3) (Fin 3) (Qbar l) := adHom.comp r with hS
  have hSg : ∀ g, S g = ad (r g) := fun g => rfl
  have h1 := GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three S form form_nondegenerate form_isSymm (fun g v w => form_ad _ v w)
    (fun v hv => GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr r hirr v (fun g => by rw [← hSg]; exact hv g))
    (fun y hy hy' => GlobalTheory.T.traceForm_ne_zero_of_stable_line_irreducible r hirr y hy (fun g => by rw [← hSg]; exact hy' g))
  obtain ⟨n, b, g, hg⟩ := Submodule.mem_span_set'.mp h1
  choose γ hγ using fun i => (g i).2
  have hdet : (∑ i, b i • (S (γ i) - 1)).det ≠ 0 := by
    have : ∑ i, b i • (S (γ i) - 1) = 1 :=
      (Finset.sum_congr rfl fun i _ => by rw [← hγ i]).trans hg
    rw [this, Matrix.det_one]; exact one_ne_zero
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_nat_coeffs_det_sum_smul_ne_zero (fun i => S (γ i) - 1) b hdet
  set J : Submodule ℚ_[l] (Matrix (Fin 3) (Fin 3) (Qbar l)) := Submodule.span ℚ_[l] (Set.range fun g => S g - 1) with hJ
  have hmul : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        have : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
          rw [map_mul]; noncomm_ring
        rw [this]
        exact J.sub_mem (J.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
      | zero => rw [mul_zero]; exact J.zero_mem
      | add y z _ _ hy hz => rw [mul_add]; exact J.add_mem hy hz
      | smul t y _ hy => rw [mul_smul_comm]; exact J.smul_mem t hy
    | zero => rw [zero_mul]; exact J.zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact J.add_mem hx hz
    | smul t x _ hx => rw [smul_mul_assoc]; exact J.smul_mem t hx
  have hT : (∑ i, (a i : Qbar l) • (S (γ i) - 1)) ∈ J := by
    refine J.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact J.nsmul_mem (Submodule.subset_span ⟨_, rfl⟩) _
  have hone := GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero J hmul _ hT ha
  obtain ⟨n', a', g', hg'⟩ := Submodule.mem_span_set'.mp hone
  choose γ' hγ' using fun i => (g' i).2
  refine ⟨n', γ', a', fun X hX => ?_⟩
  have htr : (∑ i, a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) - X)).trace = 0 := by
    rw [Matrix.trace_sum]; refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_sub, trace_conj, hX, sub_zero, smul_zero]
  refine ((ofCoord_coord hX).symm.trans ?_).trans (ofCoord_coord htr)
  congr 1
  rw [coord_sum]
  have : ∀ i, coord (a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X))
      = (a' i • (S (γ' i) - 1)) *ᵥ coord X := by
    intro i
    rw [coord_smul_scalar, show ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X)
      = (r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) + (-1 : Qbar l) • X by
        rw [neg_one_smul, ← sub_eq_add_neg], coord_add, coord_conj _ hX, coord_smul, hSg, Matrix.smul_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, neg_one_smul, ← sub_eq_add_neg]
  simp_rw [this, ← Matrix.sum_mulVec]
  have e : ∑ i, a' i • (S (γ' i) - 1) = 1 :=
    (Finset.sum_congr rfl fun i _ => by rw [← hγ' i]).trans hg'
  rw [e, Matrix.one_mulVec]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrreduStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_augmentation_combination_eq_id_traceless_irreducible : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  first | exact @GlobalTheory.Sl2Ad.augmentation_contains_one | exact GlobalTheory.Sl2Ad.augmentation_contains_one | (intros; apply GlobalTheory.Sl2Ad.augmentation_contains_one <;> assumption)
end

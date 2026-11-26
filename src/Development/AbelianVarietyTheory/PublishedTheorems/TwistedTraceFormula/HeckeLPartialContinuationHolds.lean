module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Host (HChar)
open GlobalTheory.LFun GlobalTheory.HeckeOne
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

namespace GlobalTheory.Published

def HeckeLPartialContinuation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite →
    (∀ χ : HChar K, χ.IsUnitary → (¬ ∃ t : ℝ, IsNormPow χ t) →
      ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ s : ℂ, 1 < s.re → Λ s = heckeL T χ s) ∧ ∀ s : ℂ, 1 ≤ s.re → Λ s ≠ 0) ∧
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * zetaOff T s) ∧
      ∀ s : ℂ, 1 ≤ s.re → Z s ≠ 0

end GlobalTheory.Published

namespace GlobalTheory.HeckePartial

variable {K : Type} [Field K] [NumberField K]

def removed (T : Finset (HeightOneSpectrum (𝓞 K))) (χ : HChar K) (s : ℂ) : ℂ :=
  ∏ w ∈ T, eulerPoly (heckeFam χ w) (npow w (-s))

theorem differentiable_removed (T : Finset (HeightOneSpectrum (𝓞 K))) (χ : HChar K) :
    Differentiable ℂ (removed T χ) :=
  Differentiable.fun_finsetProd fun _ _ => differentiable_eulerPoly _ _

theorem eulerPoly_heckeFam_ne_zero {χ : HChar K} (hu : χ.IsUnitary) (w : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) : eulerPoly (heckeFam χ w) (npow w (-s)) ≠ 0 :=
  eulerPoly_ne_zero fun _ hb => ((bounded_heckeFam ∅ hu).norm_le le_rfl (Set.notMem_empty w) hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

theorem removed_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (hu : χ.IsUnitary) {s : ℂ}
    (hs : 0 < s.re) : removed T χ s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => eulerPoly_heckeFam_ne_zero hu w hs

theorem heckeL_eq_mul_removed (T : Finset (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (hu : χ.IsUnitary) {s a : ℂ}
    (hs : 1 < s.re) (ha : HasProd (eulerFactor χ s) a) : heckeL (T : Set _) χ s = a * removed T χ s := by
  have h1 := (converges_heckeFam (T : Set _) hu hs).hasProd
  have h2 : HasProd (fun w => locL (heckeFam χ) w s) _ :=
    HasProd.mul_compl (s := (T : Set _)) (Finset.hasProd T fun w => locL (heckeFam χ) w s) h1
  have h3 : a = (∏ w ∈ T, locL (heckeFam χ) w s) * heckeL (T : Set _) χ s := by
    refine ha.unique ?_
    exact (funext (fun w => locL_heckeFam χ w s) : (fun w => locL (heckeFam χ) w s) = eulerFactor χ s) ▸ h2
  have h4 : (∏ w ∈ T, locL (heckeFam χ) w s) = (removed T χ s)⁻¹ := by
    rw [removed, ← Finset.prod_inv_distrib]; rfl
  have h5 := removed_ne_zero T hu (s := s) (by linarith)
  rw [h3, h4]
  field_simp

theorem eq_one_add_of_re {s : ℂ} (hs : s.re = 1) : s = 1 + (s.im : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im s, hs]
  simp

theorem IsHeckeL.ne_zero_of_one_le {χ : HChar K} (hu : χ.IsUnitary) (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) {Λ : ℂ → ℂ}
    (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 ≤ s.re) : Λ s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · rw [(hΛ.2 s hs).unique (hasProd_exp hu hs)]
    exact Complex.exp_ne_zero _
  · set t := s.im
    have hχ' : ¬ ∃ u : ℝ, IsNormPow (χ * normChar K t) u := fun ⟨u, h⟩ => hχ ⟨u + -t, by
      rw [isNormPow_iff] at h ⊢
      rw [normChar_add, ← h, mul_assoc, ← normChar_add, add_neg_cancel, normChar_zero, mul_one]⟩
    obtain ⟨Λ', h1, h2⟩ := exists_entire_ne_zero GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds
      (hu.mul (isUnitary_normChar t)) hχ'
    have h3 : IsHeckeL (χ * normChar K t) fun z => Λ (z + (t : ℂ) * Complex.I) :=
      ⟨hΛ.1.comp (by fun_prop), fun z hz => by
        rw [eulerFactor_mul_normChar]
        exact hΛ.2 _ (by simpa using hz)⟩
    have h4 := (isContAtOne_of_isHeckeL h3).apply_one_eq (isContAtOne_of_isHeckeL h1)
    rw [eq_one_add_of_re hs.symm]
    exact fun h => h2 (h4.symm.trans h)

theorem _root_.GlobalTheory.Published.HeckeLPartialContinuation_holds : GlobalTheory.Published.HeckeLPartialContinuation := by
  intro K _ _ T hT
  obtain ⟨T, rfl⟩ : ∃ T' : Finset _, (T' : Set _) = T := ⟨hT.toFinset, hT.coe_toFinset⟩
  refine ⟨fun χ hu hχ => ?_, ?_⟩
  · obtain ⟨Λ, hΛ⟩ := entire_of_not_normPow hu hχ
    exact ⟨fun s => Λ s * removed T χ s, hΛ.1.mul (differentiable_removed T χ),
      fun s hs => (heckeL_eq_mul_removed T hu hs (hΛ.2 s hs)).symm,
      fun s hs => mul_ne_zero (IsHeckeL.ne_zero_of_one_le hu hχ hΛ hs) (removed_ne_zero T hu (by linarith))⟩
  · obtain ⟨Z, hZd, hZ1, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero K
    have hu : (1 : HChar K).IsUnitary := fun _ => by simp
    have hc : ∀ P : HeightOneSpectrum (𝓞 K), cf (1 : HChar K) P = 1 := fun P => if_pos fun _ _ => rfl
    refine ⟨fun s => Z s * removed T 1 s, hZd.mul (differentiable_removed T 1), fun s hs => ?_,
      fun s hs => mul_ne_zero ?_ (removed_ne_zero T hu (by linarith))⟩
    · have h := hasProd_exp hu hs
      simp only [hc] at h
      beta_reduce
      rw [← heckeL_one, heckeL_eq_mul_removed T hu hs h, hZ s hs, mul_assoc]
    · rcases hs.lt_or_eq with hs | hs
      · rw [hZ s hs]
        exact mul_ne_zero (sub_ne_zero.2 fun h => by rw [h] at hs; simp at hs) (Complex.exp_ne_zero _)
      · rw [eq_one_add_of_re hs.symm]
        by_cases ht : s.im = 0
        · simpa [ht] using hZ1
        · exact GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ _ ht

end GlobalTheory.HeckePartial

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
noncomputable section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta

namespace GlobalTheory.HolDS

variable {n : ℕ}

def IsHolChamber (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  ∀ a b, ε a = true → ε b = false → lam b < lam a

def pPlus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ a b, ¬ (ε a = true ∧ ε b = false) → Z a b = 0}

def pMinus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ b a, ¬ (ε b = false ∧ ε a = true) → Z b a = 0}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def raisingSpan (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  Submodule.span ℂ {w | ∃ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) ∧
    ∃ v ∈ S, w = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v}

def IsLowestWeightOver (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧
      μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
  (∀ v, IsKFin ε σ v → SmoothVec {X | inG ε X} σ v) ∧
  (∀ Z ∈ pMinus ε, ∀ v ∈ lowKSub ε lam σ, GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = 0) ∧
  ∀ v, IsKFin ε σ v ↔ v ∈ raisingSpan ε σ (lowKSub ε lam σ)

end GlobalTheory.HolDS

namespace GlobalTheory.Published

open GlobalTheory.HolDS

def HolomorphicDiscreteSeries : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ → IsLowestWeightOver ε lam σ

end GlobalTheory.Published

namespace GlobalTheory.HolDS

open Formalism.L2.NTheta

variable {n : ℕ}

theorem single_mem_pPlus {ε : Fin n → Bool} {a b : Fin n} (ha : ε a = true) (hb : ε b = false) (z : ℂ) :
    Matrix.single a b z ∈ pPlus ε := by
  intro c d h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨ha, hb⟩

theorem IsHolChamber.lt {ε : Fin n → Bool} {lam : Fin n → ℝ} (h : IsHolChamber ε lam) (hl : StrictAnti lam)
    {a b : Fin n} (ha : ε a = true) (hb : ε b = false) : a < b :=
  hl.lt_iff_gt.1 (h a b ha hb)

variable {p q : ℕ} {κ : Fin p ⊕ Fin q → ℤ}

theorem strictAnti_holEnt (h : HolOK p q κ) :
    StrictAnti fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c) := by
  intro c d hcd
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective c
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective d
  simp only [Equiv.symm_apply_apply]
  rw [Fin.lt_def] at hcd
  rcases x with i | i <;> rcases y with j | j <;> simp at hcd
  · have h1 : ((κ (Sum.inl j) : ℤ) : ℚ) ≤ κ (Sum.inl i) := by exact_mod_cast h.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inl]
    linarith
  · exact h.2.2 i j
  · omega
  · have h1 : ((κ (Sum.inr j) : ℤ) : ℚ) ≤ κ (Sum.inr i) := by exact_mod_cast h.2.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inr]
    linarith

theorem enum_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lam (Fin.cast hn (finSumFinEquiv x)) = holEnt p q κ x ∧
      ε (Fin.cast hn (finSumFinEquiv x)) = Sum.elim (fun _ => true) (fun _ => false) x := by
  obtain ⟨hl, r, hr, hS⟩ := he
  have hra : StrictAnti r := fun a b hab => by
    have := hl hab
    rw [hr, hr] at this
    exact_mod_cast this
  have hs := strictAnti_holEnt h
  have hinj : Function.Injective (holEnt p q κ) := fun x y hxy =>
    finSumFinEquiv.injective (hs.injective (by simpa using hxy))
  have hn : p + q = n := by
    have := congrArg Finset.card hS
    unfold holPar at this
    rw [Finset.card_image_of_injective _ fun x y hxy => hinj (congrArg Prod.fst hxy),
      Finset.card_image_of_injective _ fun x y hxy => hra.injective (congrArg Prod.fst hxy)] at this
    simpa using this
  subst hn
  have hm : ∀ z, (∃ x, (holEnt p q κ x, Sum.elim (fun _ => true) (fun _ => false) x) = z) ↔
      ∃ a, (r a, ε a) = z := fun z => by
    simpa [holPar] using Finset.ext_iff.1 hS z
  have hrr : (fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c)) = r := by
    rw [← hs.range_inj hra]
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := (hm _).1 ⟨finSumFinEquiv.symm c, rfl⟩
      exact ⟨a, congrArg Prod.fst ha⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := (hm _).2 ⟨a, rfl⟩
      exact ⟨finSumFinEquiv x, by simpa using congrArg Prod.fst hx⟩
  refine ⟨rfl, fun x => ?_⟩
  have h1 : r (finSumFinEquiv x) = holEnt p q κ x := by rw [← hrr]; simp
  refine ⟨by rw [Fin.cast_eq_self, hr, h1], ?_⟩
  obtain ⟨y, hy⟩ := (hm _).2 ⟨finSumFinEquiv x, rfl⟩
  obtain rfl : y = x := hinj ((congrArg Prod.fst hy).trans h1)
  exact (congrArg Prod.snd hy).symm

theorem lowK_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lowK ε lam (Fin.cast hn (finSumFinEquiv x)) = κ x := by
  obtain ⟨rfl, hx⟩ := enum_holPar h he
  simp only [Fin.cast_eq_self] at hx
  refine ⟨rfl, fun x => ?_⟩
  have hc : ∀ P : Fin (p + q) → Prop, ∀ _ : DecidablePred P, (univ.filter P).card =
      (univ.filter fun i : Fin p => P (finSumFinEquiv (Sum.inl i))).card +
        (univ.filter fun j : Fin q => P (finSumFinEquiv (Sum.inr j))).card := by
    intro P _
    simp only [Finset.card_filter]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Fin.cast_eq_self, lowK, Pi.add_apply, Pi.sub_apply, rhoN, rhoC]
  rw [hc, hc, hc, hc, (hx x).1]
  simp only [(hx _).2]
  rcases x with i | i
  · have h1 : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd p j := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin q, ¬ Fin.natAdd p j < Fin.castAdd q i := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin p, Fin.castAdd q j < Fin.castAdd q j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((p - 1 - i : ℕ)) : ℝ) = p - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring
  · have h1 : ∀ j : Fin p, Fin.castAdd q j < Fin.natAdd p i := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin p, ¬ Fin.natAdd p i < Fin.castAdd q j := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin q, Fin.natAdd p j < Fin.natAdd p j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((q - 1 - i : ℕ)) : ℝ) = q - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring

end GlobalTheory.HolDS

namespace GlobalTheory.Published

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
noncomputable section

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec Matrix

namespace GlobalTheory.RealBessel

variable {n m r : ℕ}

structure IsFrame (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Prop where
  herm : Jᴴ = J
  unit : IsUnit J
  unit₀ : IsUnit J₀
  codim : m + 2 * r + 1 = n
  gram : Fᴴ * J * F = J₀
  e_indep : LinearIndependent ℂ eᵀ
  e_iso : eᴴ * J * e = 0
  e_perp : Fᴴ * J * e = 0
  z_perpF : (Fᴴ * J) *ᵥ z = 0
  z_perpE : (eᴴ * J) *ᵥ z = 0
  z_ne : Formalism.QuantumDeterminants.herm J z z ≠ 0

def unipRad (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {u | u ∈ UH J ∧
    (∀ i : Fin r, ∃ a : Fin r → ℂ, (∀ j, i ≤ j → a j = 0) ∧ (u - 1) *ᵥ (fun k => e k i) = e *ᵥ a) ∧
    ∀ x : Fin n → ℂ, (eᴴ * J) *ᵥ x = 0 → ∃ a : Fin r → ℂ, (u - 1) *ᵥ x = e *ᵥ a}

def flagVec (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Fin (r + 1) → Fin n → ℂ :=
  Fin.snoc (α := fun _ => Fin n → ℂ) (fun i k => e k i) z

def IsCharWith (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) (c : Fin r → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ u ∈ unipRad J e, ∀ a : Fin r → Fin r → ℂ, (∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j) →
    χ u = Complex.exp (Complex.I * ((∑ j, c j * a j j).re : ℂ))

def IsGeneric (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ c : Fin r → ℂ, (∀ j, c j ≠ 0) ∧ IsCharWith J e z c χ

def IsEmb (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin m) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  g * F = F * h ∧ ∀ x : Fin n → ℂ, (Fᴴ * J) *ᵥ x = 0 → g *ᵥ x = x

section Forms

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W : Type} [AddCommGroup W] [Module ℂ W]

def IsContIrred (G : Set (Matrix (Fin m) (Fin m) ℂ)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W) : Prop :=
  IsRepOn G π₀ ∧ (∀ (w : W) (l : Module.Dual ℂ W), ContinuousOn (fun h => l (π₀ h w)) G) ∧
    ∀ U : Submodule ℂ W, (∀ h ∈ G, ∀ w ∈ U, π₀ h w ∈ U) → U = ⊥ ∨ U = ⊤

structure IsBesselForm (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) (β : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  cont : ∀ w : W, ∃ l : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG J) σ l ∧ ∀ x : V, l x = β w x
  inv : ∀ h ∈ UH J₀, ∀ g ∈ UH J, IsEmb J F g h → ∀ (w : W) (x y : V), (y : H) = σ g x → β (π₀ h w) y = β w x
  equiv : ∀ u ∈ unipRad J e, ∀ (w : W) (x y : V), (y : H) = σ u x → β w y = χ u * β w x

def besselForms (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) : Submodule ℂ (W →ₗ[ℂ] V →ₗ[ℂ] ℂ) where
  carrier := {β | IsBesselForm J J₀ F e χ σ π₀ V β}
  zero_mem' := ⟨fun _ => ⟨0, ⟨[], 0, by simp, by simp⟩, fun _ => rfl⟩, fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => by simp⟩
  add_mem' := fun {β β'} hβ hβ' =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      obtain ⟨l', h1', h2'⟩ := hβ'.cont w
      exact ⟨l + l', GlobalTheory.MultMem.sobCont_add h1 h1', fun x => by simp [h2, h2']⟩,
    fun h hh g hg hE w x y hy => by
      simp only [LinearMap.add_apply, hβ.inv h hh g hg hE w x y hy, hβ'.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.add_apply, hβ.equiv u hu w x y hy, hβ'.equiv u hu w x y hy, mul_add]⟩
  smul_mem' := fun c β hβ =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      exact ⟨c • l, GlobalTheory.MultMem.sobCont_smul c h1, fun x => by simp [h2]⟩,
    fun h hh g hg hE w x y hy => by simp only [LinearMap.smul_apply, hβ.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.smul_apply, hβ.equiv u hu w x y hy, smul_eq_mul, mul_left_comm]⟩

end Forms

variable {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ}
  {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ}

theorem IsFrame.exists_coords (hf : IsFrame J J₀ F e z) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad J e) :
    ∃ a : Fin r → Fin r → ℂ, ∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j := by
  have : ∀ i : Fin (r + 1), ∃ a, (u - 1) *ᵥ flagVec e z i = e *ᵥ a := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [flagVec] using hu.2.2 z hf.z_perpE
    · obtain ⟨a, -, ha⟩ := hu.2.1 j
      exact ⟨a, by simpa [flagVec] using ha⟩
  exact ⟨fun j => (this j.succ).choose, fun j => (this j.succ).choose_spec⟩

end GlobalTheory.RealBessel

namespace GlobalTheory.Published

open GlobalTheory.RealBessel

def BesselUniquenessReal : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ → IsIrredOn (UH J) σ →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1


end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (absFin absBar finEmb FvBar compFin compInf htFin htInf normFin)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt finHt finNorm finCoord)

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {ι : Type} [Fintype ι]
  (b : Module.Basis ι F E)

theorem absFin_le_coord (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) {K c : ℝ≥0}
    (hK : ∀ k, absFin F v ((1 : Fv F v) ⊗ₜ[F] b k) ≤ K)
    (hc : ∀ k, ‖(Algebra.TensorProduct.basis (Fv F v) b).repr y k‖₊ ≤ c) : absFin F v y ≤ K * c := by
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
  refine GlobalTheory.AdelicU.absFin_sum_le F v _ _ fun k _ => ?_
  have e : ∀ a : Fv F v, a • (Algebra.TensorProduct.basis (Fv F v) b) k =
      ((1 : Fv F v) ⊗ₜ[F] b k) * (a ⊗ₜ[F] (1 : E)) := fun a => by
    simp [TensorProduct.smul_tmul']
  rw [e]
  refine (GlobalTheory.AdelicU.absFin_mul_le F v _ _).trans (mul_le_mul' (hK k) ?_)
  rw [GlobalTheory.AdelicU.absFin_tmul_one]
  exact hc k

theorem exists_trace_eq_repr : ∃ b' : ι → E, ∀ x k, Algebra.trace F E (b' k * x) = b.repr x k := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨fun k => ((Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)).symm (b.coord k), fun x k => ?_⟩
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate F E) (b.coord k) x

theorem coord_le_absFin {b' : ι → E} (hb : ∀ x k, Algebra.trace F E (b' k * x) = b.repr x k)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (k : ι) :
    ‖(Algebra.TensorProduct.basis (Fv F v) b).repr y k‖₊ ≤ absFin F v ((1 : Fv F v) ⊗ₜ[F] b' k) * absFin F v y := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b).repr y k) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ (((1 : Fv F v) ⊗ₜ[F] b' k) * y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
    | tmul a x =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.AdelicU.finEmb_tmul, ← Finset.mul_sum]
      rw [← trace_eq_sum_embeddings (FvBar F v), hb, Algebra.TensorProduct.basis_repr_tmul,
        IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), ← map_mul]
      simp
  rw [← GlobalTheory.AdelicU.absBar_algebraMap, e]
  refine Valuation.map_sum_le (GlobalTheory.AdelicU.valBar F v) fun τ _ => ?_
  exact (GlobalTheory.AdelicU.le_absFin F v τ _).trans (GlobalTheory.AdelicU.absFin_mul_le F v _ _)

theorem exists_absFin_bound (x : ι → E) : ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧
    ∀ v, 1 ≤ K v ∧ ∀ k, absFin F v ((1 : Fv F v) ⊗ₜ[F] x k) ≤ K v := by
  refine ⟨fun v => max 1 (Finset.univ.sup fun k => absFin F v ((1 : Fv F v) ⊗ₜ[F] x k)), ?_, fun v =>
    ⟨le_max_left _ _, fun k => le_max_of_le_right
      (Finset.le_sup (f := fun k => absFin F v ((1 : Fv F v) ⊗ₜ[F] x k)) (Finset.mem_univ k))⟩⟩
  have h := eventually_all.2 fun k => GlobalTheory.AdelicU.eventually_absFin_le_one F ((1 : AF F) ⊗ₜ[F] x k)
  refine (eventually_cofinite.1 h).subset fun v hv hv' => hv (max_eq_left (Finset.sup_le fun k _ => ?_))
  simpa [compFin] using hv' k

theorem evalV_repr (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) (k : ι) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((Algebra.TensorProduct.basis (Af F) b).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k) =
      (Algebra.TensorProduct.basis (Fv F v) b).repr (compFin F E v z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a x => simp [compFin, GlobalTheory.AdelicU.evFin, Algebra.TensorProduct.basis_repr_tmul]

end Local

theorem finprod_le_mul {α : Type} {f g K : α → ℝ≥0} (hf : (Function.mulSupport f).Finite)
    (hg : (Function.mulSupport g).Finite) (hK : (Function.mulSupport K).Finite) (h : ∀ a, f a ≤ K a * g a) :
    ∏ᶠ a, f a ≤ (∏ᶠ a, K a) * ∏ᶠ a, g a := by
  rw [← finprod_mul_distrib hK hg]
  exact finprod_le_finprod' hf ((hK.union hg).subset (Function.mulSupport_mul _ _)) h

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem evalV_finCoord (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (i j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g i j) k) =
      (Algebra.TensorProduct.basis (Fv D.host.F v) (Module.finBasis D.host.F D.host.E)).repr
        (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) k :=
  evalV_repr (Module.finBasis D.host.F D.host.E) v ((Formalism.L2.Theta.matHom V g).1 i j) k

theorem finNorm_le_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D V} {c : ℝ≥0} : finNorm V v g ≤ c ↔
    ∀ i j k, ‖(Algebra.TensorProduct.basis (Fv D.host.F v) (Module.finBasis D.host.F D.host.E)).repr
      (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) k‖₊ ≤ c := by
  simp only [finNorm, Finset.sup_le_iff, Finset.mem_univ, true_imp_iff, Prod.forall, evalV_finCoord]

theorem exists_finNorm_comparison : ∃ K : HeightOneSpectrum (𝓞 D.host.F) → ℝ≥0, (Function.mulSupport K).Finite ∧
    ∀ v, 1 ≤ K v ∧ ∀ g : GA D V,
      finNorm V v g ≤ K v * normFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 ∧
      normFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 ≤ K v * finNorm V v g := by
  obtain ⟨b', hb⟩ := exists_trace_eq_repr (Module.finBasis D.host.F D.host.E)
  obtain ⟨K, hK, h⟩ := exists_absFin_bound (F := D.host.F) (Sum.elim (Module.finBasis D.host.F D.host.E) b')
  refine ⟨K, hK, fun v => ⟨(h v).1, fun g => ⟨(finNorm_le_iff V).2 fun i j k => ?_,
    (GlobalTheory.AdelicU.normFin_le_iff _ v).2 fun i j => ?_⟩⟩⟩
  · exact (coord_le_absFin _ hb v _ _).trans (mul_le_mul' ((h v).2 (.inr _))
      (GlobalTheory.AdelicU.absFin_le_normFin _ v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 i j))
  · exact absFin_le_coord (Module.finBasis D.host.F D.host.E) v
      (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) (fun k => (h v).2 (.inl k))
      ((finNorm_le_iff V).1 le_rfl i j)

theorem height_comparison (hθ : IsInfFam θ) : ∃ C : ℝ, 0 < C ∧ ∀ g : GA D V,
    (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ≤ C * height V g ∧ height V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  obtain ⟨K, hK, h⟩ := exists_finNorm_comparison V
  have key : ∀ {k a a' c c' : ℝ≥0}, 1 ≤ k → a ≤ k * c → a' ≤ k * c' → max 1 (max a a') ≤ k * max 1 (max c c') :=
    fun hk h1 h2 => max_le (one_le_mul_of_one_le_of_one_le hk (le_max_left _ _)) (max_le
      (h1.trans (mul_le_mul_right (le_max_of_le_right (le_max_left _ _)) _))
      (h2.trans (mul_le_mul_right (le_max_of_le_right (le_max_right _ _)) _)))
  have h1 : (1 : ℝ≥0) ≤ ∏ᶠ v, K v := one_le_finprod' fun v => (h v).1
  refine ⟨(∏ᶠ v, K v : ℝ≥0), by exact_mod_cast zero_lt_one.trans_le h1, fun g => ?_⟩
  have e : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) = ∏ τ, infHt θ V τ g :=
    (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
      (Finset.prod_congr rfl fun τ _ => htInf_eq_infHt V hθ τ g)
  have hi := fun v => (h v).2 g⁻¹
  simp only [map_inv] at hi
  have f1 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g
  have f2 := GlobalTheory.AdelicU.finite_mulSupport_htFin D.host.F (Formalism.L2.Theta.matHom V g)
  have a1 := finprod_le_mul f1 f2 hK fun v => key (h v).1 ((h v).2 g).1 (hi v).1
  have a2 := finprod_le_mul f2 f1 hK fun v => key (h v).1 ((h v).2 g).2 (hi v).2
  unfold height GlobalTheory.AdelicU.heightGL GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  rw [e]
  constructor
  · exact_mod_cast (mul_le_mul_right a1 _).trans_eq (mul_left_comm _ _ _)
  · exact_mod_cast (mul_le_mul_right a2 _).trans_eq (mul_left_comm _ _ _)

end GlobalTheory.Grow

end
end

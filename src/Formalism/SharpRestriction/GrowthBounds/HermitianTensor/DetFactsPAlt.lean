module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def genY (A : Type) [CommRing A] (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) :=
  Matrix.of fun i j => X (i, j)

def TauP : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [CharZero O] [Field K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (r N e : ℕ) (α : Fin r → ℕ), 1 ≤ r → Antitone α → (∀ i, α i ≤ N) → (∀ i, e ≤ α i) → (∃ i, α i = e) →
    ∃ τ : MvPolynomial (Fin r × Fin r) K →ₗ[K] MvPolynomial (Fin r × Fin r) K,
      (∀ f' ∈ dualWeyl K r r (fun i => N - α i.rev), τ f' ∈ dualWeyl K r r (fun i => α i - e)) ∧
      (∀ f' ∈ intO O r (fun i => N - α i.rev), τ f' ∈ intO O r (fun i => α i - e)) ∧
      (∀ g ∈ intO O r (fun i => α i - e), ∃ f' ∈ intO O r (fun i => N - α i.rev), τ f' = g) ∧
      (∀ l : Matrix (Fin r) (Fin r) K, IsUnit l.det → ∀ f' ∈ dualWeyl K r r (fun i => N - α i.rev),
        rowAct K l.transpose (τ (rowAct K l f')) = l.det ^ (N - e) • τ f')

def SmithP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] R.Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
        B (rowAct R.Kf g P) Q = B P (rowAct R.Kf g.transpose Q)) ∧
      (∀ P ∈ intO R.O (m + 1) ν, ∀ Q ∈ intO R.O (m + 1) ν, B P Q ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (x x' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim (m + 1) (fun j => (ν j : ℤ)) ∧ (∀ b, ka b ≤ N0 (m + 1) * deF p (m + 1) (ν 0)) ∧
        (∀ b, x b ∈ intO R.O (m + 1) ν) ∧ (∀ a', x' a' ∈ intO R.O (m + 1) ν) ∧
        ∀ a' b, B (x b) (x' a') = if a' = b then (p : R.Kf) ^ ka b else 0

def BilinP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ)
    (B : MvPolynomial (Fin r × Fin r) K →ₗ[K] MvPolynomial (Fin r × Fin r) K →ₗ[K] K),
    ∃ L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K,
      ∀ f f', L (blockEmb K true f * blockEmb K false f') = B f f'

def DetFactsP : Prop :=
  ∀ (A : Type) [CommRing A] (r e : ℕ),
    detY A r ^ e ∈ dualWeyl A r r (fun _ => e) ∧
    ∀ l : Matrix (Fin r) (Fin r) A, rowAct A l (detY A r) = C l.det * detY A r

def NumP : Prop :=
  ∀ (p a c r ell : ℕ), 2 ≤ p → 1 ≤ r → ell ≤ c → c ≤ 8 * a → N0 r * deF p r ell ≤ ⌈kappaOneExponent p a (r + 1)⌉₊

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem intCapP : IntCapP := by
  intro O K _ _ _ hinj k ν F hF hco
  obtain ⟨G, hG⟩ : F ∈ Set.range (map (algebraMap O K) : MvPolynomial (Fin k × Fin k) O →+* _) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨u, hu, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact hco u
  subst hG
  have hcomm : ∀ (l j : Fin k) (p : MvPolynomial (Fin k × Fin k) O),
      map (algebraMap O K) (colAddGen O l j p) = colAddGen K l j (map (algebraMap O K) p) := by
    intro l j p
    induction p using MvPolynomial.induction_on
    next a => simp [colAddGen]
    next p q hp hq => simp only [map_add (f := _), hp, hq]
    next p x hp =>
      simp only [map_mul, hp, map_X]
      congr 1
      simp only [colAddGen, aeval_X]
      split_ifs <;> simp
  refine Submodule.mem_map.mpr ⟨G, ?_, ?_⟩
  · simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero, AlgHom.toLinearMap_apply, mem_weightedHomogeneousSubmodule] at hF ⊢
    obtain ⟨h1, h2⟩ := hF
    refine ⟨?_, ?_⟩
    · intro d hd
      exact h1 (by rw [coeff_map]; exact fun h0 => hd ((map_eq_zero_iff _ hinj).mp h0))
    · intro l j hlj
      apply MvPolynomial.map_injective _ hinj
      rw [hcomm, map_rename, h2 l j hlj]
  · first
      | rfl
      | simp [MvPolynomial.mapAlgHom]

theorem qa_nuNext_add {n : ℕ} (ν ν' : Fin n → ℕ) (s : Fin n) : nuNext (ν + ν') s = nuNext ν s + nuNext ν' s := by
  unfold nuNext
  split_ifs <;> simp

theorem qa_nuNext_le {n : ℕ} (ν : Fin n → ℕ) (h : Antitone ν) (s : Fin n) : nuNext ν s ≤ ν s := by
  unfold nuNext
  split_ifs with hs
  · exact h (Fin.le_def.2 (Nat.le_succ _))
  · exact Nat.zero_le _

theorem hwMulP : HwMulP := by
  intro A _ k ν ν' hν hν'
  refine ⟨?_, ?_⟩
  · simp only [hw, ← Finset.prod_mul_distrib, ← pow_add]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    congr 1
    rw [qa_nuNext_add, Pi.add_apply]
    have h1 := qa_nuNext_le ν hν s
    have h2 := qa_nuNext_le ν' hν' s
    omega
  · have key : ∀ (m : ℕ) (h1 : m ≤ k) (h2 : m ≤ k), eval (idPoint A k k) (lpMinor A m h1 h2) = 1 := by
      intro m h1 h2
      rw [lpMinor, RingHom.map_det]
      convert (Matrix.det_one : (1 : Matrix (Fin m) (Fin m) A).det = 1)
      ext p q
      simp [idPoint, Matrix.one_apply, Fin.ext_iff]
    simp only [hw, map_prod, map_pow, key, one_pow, Finset.prod_const_one]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def dPsi (K : Type) [Field K] (m : ℕ) : PolXY K (m + 1) →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (deltaB K m).toLinearMap ∘ₗ (PsiXY K m).toLinearMap

theorem dPsi_apply (K : Type) [Field K] (m : ℕ) (f : PolXY K (m + 1)) : dPsi K m f = deltaB K m (PsiXY K m f) := rfl

theorem tie5b (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) R.Kf)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) = g⁻¹) (a b : ℕ)
    (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) :
    y ∈ H0 R.O m (wtPQ m a b) (colSpan R.O g) ↔
      ∃ f ∈ PolAB R.Kf (m + 1) a b, f ∈ latOf g' (GaussLat R.Ov.toSubring) ∧ deltaB R.Kf m (PsiXY R.Kf m f) = y := by
  have := R.std.1.frac_O
  have hΛ : IsLattice R.O (colSpan R.O g) := ⟨g, hg, rfl⟩
  rw [mem_invariant_sections_two_weight_iff hCO m a b hm _ hΛ y]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (h2 R.Kf m hm a b x).1 (twoLat_le_twoSp m a b _ hΛ x hx)
    exact ⟨f, hf, (h5 p n' R m hm g hg g' hg' a b f hf).1 hx, rfl⟩
  · rintro ⟨f, hf, hl, rfl⟩
    exact ⟨_, (h5 p n' R m hm g hg g' hg' a b f hf).2 hl, rfl⟩

theorem tie3 (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) :
    (PolAB R.Kf (m + 1) a b).map (dPsi R.Kf m) = dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact delta_twoSp R.Kf m a b hm _ ((h2 R.Kf m hm a b _).2 ⟨f, hf, rfl⟩)
  · have h1 : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf).det := by rw [Matrix.det_one]; exact isUnit_one
    obtain ⟨B, -, hB1, -, hB2⟩ := la_basis hinj m (wtPQ m a b) 1 h1
    rw [← hB2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : B i ∈ H0 R.O m (wtPQ m a b) (colSpan R.O (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf)) := by
      rw [H0_eq_twisted_nabla (la_indep hinj) m _ (wtPQ_anti m a b hm) 1 h1, ← hB1]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨f, hf, -, hfe⟩ := (tie5b h2 h5 hCO R m hm 1 h1 1 (by simp) a b (B i)).1 hi
    exact ⟨f, hf, hfe⟩

theorem nuOf_wtPQ_cast (m a b : ℕ) (i : Fin (m + 2)) :
    ((nuOf (wtPQ (m + 1) a b) i : ℕ) : ℤ) = hwt m a b i + b := by
  have h0 : (0 : Fin (m + 1 + 1)) ≠ Fin.last (m + 1) := (last_ne_zero' m).symm
  rw [hwt_apply]
  by_cases hi : i = 0
  · subst hi
    simp [nuOf, wtPQ, h0.symm]
    omega
  · by_cases hl : i = Fin.last (m + 1)
    · simp [nuOf, wtPQ, hl, h0.symm]
    · simp [nuOf, wtPQ, hi, hl, h0.symm]

theorem weylDim_shift (n : ℕ) (lam : Fin n → ℤ) (c : ℤ) : weylDim n (fun i => lam i + c) = weylDim n lam := by
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [add_sub_add_right_eq_sub]

theorem finrank_wtPQ (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (K : Type) [Field K] [CharZero K] (m a b : ℕ) :
    Module.finrank K (dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))) = dimHar (m + 1) a b := by
  have hanti : Antitone (nuOf (wtPQ (m + 1) a b)) := by
    intro i j hij
    have := wtPQ_anti (m + 1) a b (by omega) hij
    unfold nuOf
    omega
  have hq : (Module.finrank K (dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b))) : ℚ) =
      (dimHar (m + 1) a b : ℚ) := by
    rw [finrank_weyl D h3 K _ _ hanti, ← weylDim_hwt_eq, ← weylDim_shift (m + 2) (hwt m a b) b]
    congr 1
    funext i
    exact nuOf_wtPQ_cast m a b i
  exact_mod_cast hq

theorem tie4 (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ}
    (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) :
    ∀ f ∈ PolAB R.Kf (m + 1) a b, deltaB R.Kf m (PsiXY R.Kf m f) = 0 →
      ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), f = hXY R.Kf (m + 1) * G := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have : CharZero R.Kf := R.charZero
  have hfin : Module.Finite R.Kf (PolAB R.Kf (m + 1 + 1) a b) := Har2.finite_polAB (m + 1) a b
  set T := (dPsi R.Kf (m + 1)).domRestrict (PolAB R.Kf (m + 1 + 1) a b) with hT
  have hrange : LinearMap.range T = dualWeyl R.Kf (m + 1 + 1) (m + 1 + 1) (nuOf (wtPQ (m + 1) a b)) := by
    rw [hT, LinearMap.range_domRestrict]
    exact tie3 h2 h5 hCO R (m + 1) hm a b
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hrange, finrank_wtPQ D h3 R.Kf m a b, Har2.finrank_polAB] at hrn
  intro f hf hf0
  have hfk : (⟨f, hf⟩ : PolAB R.Kf (m + 1 + 1) a b) ∈ LinearMap.ker T := hf0
  by_cases hab : a = 0 ∨ b = 0
  · have hk0 : Module.finrank R.Kf (LinearMap.ker T) = 0 := by
      unfold dimHar dimPol at hrn
      rw [if_pos hab] at hrn
      omega
    have hbot : LinearMap.ker T = ⊥ := Submodule.finrank_eq_zero.1 hk0
    rw [hbot, Submodule.mem_bot] at hfk
    have hf00 : f = 0 := congrArg Subtype.val hfk
    exact ⟨0, Submodule.zero_mem _, by rw [hf00, mul_zero]⟩
  · rw [not_or] at hab
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    let μ : PolAB R.Kf (m + 1 + 1) a b →ₗ[R.Kf] PolAB R.Kf (m + 1 + 1) (a + 1) (b + 1) :=
      LinearMap.codRestrict _ ((LinearMap.mulLeft R.Kf (hXY R.Kf (m + 1 + 1))) ∘ₗ (PolAB R.Kf (m + 1 + 1) a b).subtype)
        (fun G => Har2.h_mul_mem G.2)
    have hμinj : Function.Injective μ := by
      intro G G' h
      have h' : hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)) = hXY R.Kf (m + 1 + 1) * G' :=
        congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel₀ (hXY_ne_zero R.Kf (m + 1)) h')
    have hle : LinearMap.range μ ≤ LinearMap.ker T := by
      rintro _ ⟨G, rfl⟩
      show deltaB R.Kf (m + 1) (PsiXY R.Kf (m + 1) (hXY R.Kf (m + 1 + 1) * (G : PolXY R.Kf (m + 1 + 1)))) = 0
      rw [map_mul, map_mul, delta_Psi_h R.Kf (m + 1) hm, zero_mul]
    have hr : Module.finrank R.Kf (LinearMap.range μ) = (a + (m + 1)).choose (m + 1) * (b + (m + 1)).choose (m + 1) := by
      rw [LinearMap.finrank_range_of_inj hμinj, Har2.finrank_polAB]
    have hle2 := Submodule.finrank_mono hle
    have heq : LinearMap.range μ = LinearMap.ker T := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      unfold dimHar dimPol at hrn
      rw [if_neg (by omega)] at hrn
      simp only [Nat.add_sub_cancel] at hrn
      have hkle : Module.finrank R.Kf (LinearMap.ker T) ≤
          (a + 1 + (m + 1)).choose (m + 1) * (b + 1 + (m + 1)).choose (m + 1) := by omega
      omega
    rw [← heq] at hfk
    obtain ⟨G, hG⟩ := hfk
    exact ⟨G, G.2, (congrArg Subtype.val hG).symm⟩

theorem tiePsi_of (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto)
    (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) : TiePsi := by
  intro p n' R m hm
  have hm1 : 1 ≤ m := by omega
  refine ⟨h1 R.Kf m hm1, h2 R.Kf m hm1, ?_, tie4 D h3 h2 h5 hCO R m hm1, ?_⟩
  · intro a b y
    rw [← tie3 h2 h5 hCO R m hm1 a b]
    exact Submodule.mem_map
  · rintro Λ ⟨g, hg, rfl⟩
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨Matrix.GeneralLinearGroup.mk'' g⁻¹ hgi, ?_, ?_⟩
    · intro P Q f hf
      exact h5 p n' R m hm1 g hg _ rfl P Q f hf
    · intro a b y
      exact tie5b h2 h5 hCO R m hm1 g hg _ rfl a b y

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section Basic

variable {A : Type} [CommRing A] {r : ℕ}

theorem qa_subY_X_some (v : Fin (r + 1 + 1) × Fin (r + 1 + 1)) (j : Fin r) (h : midOf v.2 = some j) :
    subY A r (X v) = ∑ i : Fin r, C (X (i, j)) * X (v.1, midI r i) := by
  unfold subY
  rw [aeval_X]
  simp only [h]

theorem qa_subY_X_none (v : Fin (r + 1 + 1) × Fin (r + 1 + 1)) (h : midOf v.2 = none) :
    subY A r (X v) = X v := by
  unfold subY
  rw [aeval_X]
  simp only [h]

theorem qa_subY_C (a : A) : subY A r (C a) = C (C a) := by
  unfold subY
  exact aeval_C _ a

end Basic

theorem qa_rowAct_X {R : Type} [CommRing R] {k n : ℕ} (g : Matrix (Fin k) (Fin k) R) (x : Fin k × Fin n) :
    rowAct R g (X x) = ∑ b : Fin k, C (g x.1 b) * X (b, x.2) := by
  unfold rowAct
  exact aeval_X _ x

theorem qa_rowAct_C {R : Type} [CommRing R] {k n : ℕ} (g : Matrix (Fin k) (Fin k) R) (c : R) :
    rowAct R (n := n) g (C c) = C c := by
  unfold rowAct
  exact aeval_C _ c

theorem subMapP : SubMapP := by
  intro A B _ _ φ r v
  have h : ((subY B r).toRingHom.comp (map φ)) = ((map (map φ)).comp (subY A r).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show subY B r (map φ (C a)) = map (map φ) (subY A r (C a))
      rw [map_C, qa_subY_C, qa_subY_C, map_C, map_C]
    · intro w
      show subY B r (map φ (X w)) = map (map φ) (subY A r (X w))
      rw [map_X]
      cases hm : midOf w.2 with
      | none => rw [qa_subY_X_none w hm, qa_subY_X_none w hm, map_X]
      | some j =>
        set_option synthInstance.maxHeartbeats 100000 in
          rw [qa_subY_X_some w j hm, qa_subY_X_some w j hm, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_C, map_X, map_X]
  exact RingHom.congr_fun h v

def rowInd {k n : ℕ} (a : Fin k) : Fin k × Fin n → ℕ := fun v => if v.1 = a then 1 else 0

theorem qa_weight_rowInd {k n : ℕ} (a : Fin k) (u : Fin k × Fin n →₀ ℕ) :
    Finsupp.weight (rowInd a) u = rowDeg u a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, rowDeg]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [rowInd]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [rowInd, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem qa_iwh_pow {σ R M : Type} [CommSemiring R] [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ R} {n : M}
    (h : IsWeightedHomogeneous w φ n) (k : ℕ) : IsWeightedHomogeneous w (φ ^ k) (k • n) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul]
    exact isWeightedHomogeneous_one R w
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul h

theorem subRowP : SubRowP := by
  classical
  intro A _ r a d v hv
  have hX : ∀ x, IsWeightedHomogeneous (rowInd a) (subY A r (X x)) (rowInd a x) := by
    intro x
    cases hm : midOf x.2 with
    | none =>
      rw [qa_subY_X_none x hm]
      exact isWeightedHomogeneous_X _ _ _
    | some j =>
      rw [qa_subY_X_some x j hm]
      refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
      have h := (isWeightedHomogeneous_C (rowInd a) (X (i, j) : MvPolynomial (Fin r × Fin r) A)).mul
        (isWeightedHomogeneous_X (MvPolynomial (Fin r × Fin r) A) (rowInd a) (x.1, midI r i))
      rw [zero_add] at h
      exact h
  have hmain : IsWeightedHomogeneous (rowInd a) (subY A r v) d := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← support_sum_monomial_coeff v, map_sum]
    refine IsWeightedHomogeneous.sum _ _ _ fun u hu => ?_
    have hd : rowDeg u a = d := hv u (mem_support_iff.1 hu)
    have e : (monomial u (AddMonoidAlgebra.coeff v u) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) =
        C (AddMonoidAlgebra.coeff v u) * ∏ x ∈ u.support, X x ^ u x := monomial_eq
    rw [e, map_mul (subY A r), qa_subY_C, map_prod]
    have h1 : IsWeightedHomogeneous (rowInd a) (∏ x ∈ u.support, subY A r (X x ^ u x))
        (∑ x ∈ u.support, u x • rowInd a x) :=
      IsWeightedHomogeneous.prod _ _ _ fun x _ => by
        rw [map_pow]
        exact qa_iwh_pow (hX x) (u x)
    have h2 : ∑ x ∈ u.support, u x • rowInd a x = d := by
      have h0 := qa_weight_rowInd a u
      rw [Finsupp.weight_apply] at h0
      exact h0.trans hd
    have h3 := (isWeightedHomogeneous_C (rowInd a) (C (AddMonoidAlgebra.coeff v u) : MvPolynomial (Fin r × Fin r) A)).mul h1
    rw [zero_add, h2] at h3
    exact h3
  intro u hu
  rw [← qa_weight_rowInd a u]
  exact hmain hu

theorem qa_subY_rowAct {A : Type} [CommRing A] {r : ℕ} (g : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) A)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    subY A r (rowAct A g v) = rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C) (subY A r v) := by
  have h : (subY A r).toRingHom.comp (rowAct A g).toRingHom =
      (rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C)).toRingHom.comp (subY A r).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show subY A r (rowAct A g (C a)) = rowAct _ (g.map C) (subY A r (C a))
      rw [qa_rowAct_C, qa_subY_C, qa_rowAct_C]
    · intro x
      show subY A r (rowAct A g (X x)) = rowAct _ (g.map C) (subY A r (X x))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [qa_rowAct_X, map_sum]
      cases hm : midOf x.2 with
      | none =>
        rw [qa_subY_X_none x hm, qa_rowAct_X]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul (subY A r), qa_subY_C, qa_subY_X_none (b, x.2) hm]
        try rfl
      | some j =>
        set_option synthInstance.maxHeartbeats 100000 in
          rw [qa_subY_X_some x j hm, map_sum]
        have e1 : ∀ b, subY A r (C (g x.1 b) * X (b, x.2)) =
            ∑ i, C (C (g x.1 b)) * (C (X (i, j)) * X (b, midI r i)) := by
          intro b
          rw [map_mul (subY A r), qa_subY_C, qa_subY_X_some (b, x.2) j hm, Finset.mul_sum]
        have e2 : ∀ i, rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C) (C (X (i, j)) * X (x.1, midI r i)) =
            ∑ b, C (X (i, j)) * (C (C (g x.1 b)) * X (b, midI r i)) := by
          intro i
          rw [map_mul (rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C)), qa_rowAct_C, qa_rowAct_X, Finset.mul_sum]
          try rfl
        simp only [e1, e2]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
        ring
  exact RingHom.congr_fun h v

end Formalism.MainNotions.flipOneThree.Pf

end
end

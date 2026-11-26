module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellLeviTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleDeterminantTwist
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleDeterminantTwist
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.JacBridge

open GlobalTheory.SmGL Matrix
open scoped Kronecker
open GroundTheory.Automorphic.Parabolic (levi jacquetRep JacquetModule sqrtModular invSqrtModular leviIncl unipotentRadical
  jacquetRep_mk mem_unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper mem_blockUpper)
open GroundTheory.Automorphic.Measures (adLie parabolicCoord ParabolicIndex coe_adLie coe_parabolicCoord_symm_single
  mul_single_mul_apply modularCharacter_blockUpper)

theorem prod_le_pairs {α G : Type} [Fintype α] [LinearOrder α] [CommGroup G] (f : α → G) (n : α → ℕ) :
    ∏ a, ∏ c, (if a ≤ c then f a ^ n c * (f c)⁻¹ ^ n a else 1) =
      ∏ a, f a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
  have h1 : ∀ a c : α, (if a ≤ c then f a ^ n c * (f c)⁻¹ ^ n a else 1) =
      (if a < c then f a ^ n c else 1) * (if a < c then (f c)⁻¹ ^ n a else 1) := by
    intro a c
    rcases lt_trichotomy a c with h | rfl | h
    · simp [h.le, h]
    · simp
    · simp [not_le.mpr h, not_lt.mpr h.le]
  have hA : ∀ a : α, ∏ c, (if a < c then f a ^ n c else 1) = f a ^ (∑ b with a < b, n b) := by
    intro a
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum]
  have hB : ∀ c : α, ∏ a, (if a < c then (f c)⁻¹ ^ n a else 1) =
      (f c ^ (∑ b with b < c, n b))⁻¹ := by
    intro c
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, inv_pow]
  calc ∏ a, ∏ c, (if a ≤ c then f a ^ n c * (f c)⁻¹ ^ n a else 1)
      = ∏ a, ∏ c, ((if a < c then f a ^ n c else 1) * (if a < c then (f c)⁻¹ ^ n a else 1)) :=
        Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun c _ => h1 a c
    _ = (∏ a, ∏ c, (if a < c then f a ^ n c else 1)) *
          ∏ a, ∏ c, (if a < c then (f c)⁻¹ ^ n a else 1) := by
        simp only [Finset.prod_mul_distrib]
    _ = (∏ a, ∏ c, (if a < c then f a ^ n c else 1)) *
          ∏ c, ∏ a, (if a < c then (f c)⁻¹ ^ n a else 1) := by
        congr 1
        exact Finset.prod_comm
    _ = (∏ a, f a ^ (∑ b with a < b, n b)) * ∏ a, (f a ^ (∑ b with b < a, n b))⁻¹ := by
        rw [Finset.prod_congr rfl fun a _ => hA a, Finset.prod_congr rfl fun c _ => hB c]
    _ = ∏ a, f a ^ (∑ b with a < b, n b) * (f a ^ (∑ b with b < a, n b))⁻¹ := by
        rw [Finset.prod_mul_distrib]
    _ = ∏ a, f a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [_root_.zpow_sub, ← Nat.cast_sum, ← Nat.cast_sum, zpow_natCast, zpow_natCast]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)]
  [∀ j, DecidableEq (m' j)] {N : ℕ}

theorem label_eq_iff {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (x y : Fin N) :
    γ x = γ y ↔ blk e' x = blk e' y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have a1 : ¬ blk e' x < blk e' y := fun hl => by
      have := (hγ x y).mpr hl
      rw [h] at this
      exact lt_irrefl _ this
    have a2 : ¬ blk e' y < blk e' x := fun hl => by
      have := (hγ y x).mpr hl
      rw [h] at this
      exact lt_irrefl _ this
    exact le_antisymm (not_lt.mp a2) (not_lt.mp a1)
  · have a1 : ¬ γ x < γ y := fun hl => by
      have := (hγ x y).mp hl
      rw [h] at this
      exact lt_irrefl _ this
    have a2 : ¬ γ y < γ x := fun hl => by
      have := (hγ y x).mp hl
      rw [h] at this
      exact lt_irrefl _ this
    exact le_antisymm (not_lt.mp a2) (not_lt.mp a1)

theorem unipRad_eq {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) :
    unipRad k e' = unipotentRadical k N γ := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GlobalTheory.SmGL.mem_parab, mem_unipotentRadical, mem_blockUpper]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => h1 i j ((hγ j i).mp hij), fun i j hij => ?_⟩
    have hb := (label_eq_iff hγ i j).mp hij
    obtain ⟨⟨a, u⟩, rfl⟩ := e'.surjective i
    obtain ⟨⟨b, v⟩, rfl⟩ := e'.surjective j
    rw [blk_apply, blk_apply] at hb
    subst hb
    rw [h2 a u v]
    simp [Matrix.one_apply]
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => h1 ((hγ j i).mpr hij), fun a u v => ?_⟩
    rw [h2 _ _ ((label_eq_iff hγ _ _).mpr (by rw [blk_apply, blk_apply]))]
    simp [Matrix.one_apply]

def adCoord {γ : Fin N → ℕ} (p : blockUpper k N γ) :
    (ParabolicIndex N γ → k) →ₗ[k] (ParabolicIndex N γ → k) :=
  (((parabolicCoord k N γ).symm.trans ((adLie k N γ p).trans (parabolicCoord k N γ))) :
    (ParabolicIndex N γ → k) →ₗ[k] (ParabolicIndex N γ → k))

theorem det_adLie_eq {γ : Fin N → ℕ} (p : blockUpper k N γ) :
    (LinearEquiv.det (adLie k N γ p) : k) = (LinearMap.toMatrix' (adCoord p)).det := by
  rw [LinearMap.det_toMatrix', adCoord, ← LinearEquiv.coe_det]
  exact congrArg Units.val (LinearEquiv.det_conj (adLie k N γ p) (parabolicCoord k N γ)).symm

theorem adCoord_apply {γ : Fin N → ℕ} (p : blockUpper k N γ) (s t : ParabolicIndex N γ) :
    LinearMap.toMatrix' (adCoord p) s t =
      ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) s.1.1 t.1.1 *
        (((p : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) t.1.2 s.1.2 := by
  rw [LinearMap.toMatrix'_apply]
  show ((adLie k N γ p ((parabolicCoord k N γ).symm (Pi.single t 1)) : Matrix (Fin N) (Fin N) k)) s.1.1 s.1.2 = _
  rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]

theorem leviEmb_apply_ne' (e' : (Σ j, m' j) ≃ Fin N) (g : Levi k m') {x y : Fin N}
    (h : blk e' x ≠ blk e' y) : (leviEmb k e' g : Matrix (Fin N) (Fin N) k) x y = 0 := by
  simp only [leviEmb, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
  exact dif_neg h

def parabolicBlockPair (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ) (s : ParabolicIndex N γ) : Lex (β' × β') :=
  toLex (blk e' s.1.1, blk e' s.1.2)

section DetAd

variable {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
  (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (g : Levi k m') (p : blockUpper k N γ)
  (hp : (p : GL (Fin N) k) = leviEmb k e' g)

include hp in
theorem adCoord_apply_levi (s t : ParabolicIndex N γ) :
    LinearMap.toMatrix' (adCoord p) s t =
      (leviEmb k e' g : Matrix (Fin N) (Fin N) k) s.1.1 t.1.1 *
        (leviEmb k e' g⁻¹ : Matrix (Fin N) (Fin N) k) t.1.2 s.1.2 := by
  rw [adCoord_apply, hp, ← map_inv]

include hp in
theorem adCoord_blockTriangular :
    (LinearMap.toMatrix' (adCoord p)).BlockTriangular (parabolicBlockPair e' γ) := by
  intro s t hst
  rw [adCoord_apply_levi g p hp s t]
  by_cases h1 : blk e' s.1.1 = blk e' t.1.1
  · by_cases h2 : blk e' t.1.2 = blk e' s.1.2
    · have heq : parabolicBlockPair e' γ t = parabolicBlockPair e' γ s := by
        simp only [parabolicBlockPair, h1, h2]
      rw [heq] at hst
      exact absurd hst (lt_irrefl _)
    · rw [leviEmb_apply_ne' e' g⁻¹ h2, mul_zero]
  · rw [leviEmb_apply_ne' e' g h1, zero_mul]

include hγ hp in
theorem block_det_of_le {a c : β'} (hac : a ≤ c) :
    ((LinearMap.toMatrix' (adCoord p)).toSquareBlock (parabolicBlockPair e' γ) (toLex (a, c))).det =
      (g a : Matrix (m' a) (m' a) k).det ^ Fintype.card (m' c) *
        ((g c)⁻¹ : GL (m' c) k).val.det ^ Fintype.card (m' a) := by
  have hmem : ∀ (u : m' a) (v : m' c), ¬ γ (e' ⟨c, v⟩) < γ (e' ⟨a, u⟩) := by
    intro u v h
    have h' := (hγ _ _).mp h
    simp only [blk, Equiv.symm_apply_apply] at h'
    exact absurd hac (not_le.mpr h')
  let F : m' a × m' c → {s : ParabolicIndex N γ // parabolicBlockPair e' γ s = toLex (a, c)} :=
    fun uv => ⟨⟨(e' ⟨a, uv.1⟩, e' ⟨c, uv.2⟩), hmem uv.1 uv.2⟩, by simp [parabolicBlockPair, blk]⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ h
      have h1 : e' ⟨a, u⟩ = e' ⟨a, u'⟩ := congrArg (fun s => s.1.1.1) h
      have h2 : e' ⟨c, v⟩ = e' ⟨c, v'⟩ := congrArg (fun s => s.1.1.2) h
      simp only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1 h2
      rw [h1, h2]
    · rintro ⟨⟨⟨i, j⟩, hij⟩, hs⟩
      simp only [parabolicBlockPair, toLex_inj, Prod.mk.injEq] at hs
      obtain ⟨hi, hj⟩ := hs
      obtain ⟨⟨ai, u⟩, rfl⟩ := e'.surjective i
      obtain ⟨⟨cj, v⟩, rfl⟩ := e'.surjective j
      simp only [blk, Equiv.symm_apply_apply] at hi hj
      subst hi hj
      exact ⟨(u, v), rfl⟩
  have hL : ∀ (g' : Levi k m') (b : β') (x y : m' b),
      (leviEmb k e' g' : Matrix (Fin N) (Fin N) k) (e' ⟨b, x⟩) (e' ⟨b, y⟩) =
        (g' b : Matrix (m' b) (m' b) k) x y := by
    intro g' b x y
    simp only [leviEmb, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]
  let E := Equiv.ofBijective F hF
  have hM : ((LinearMap.toMatrix' (adCoord p)).toSquareBlock (parabolicBlockPair e' γ) (toLex (a, c))).submatrix E E =
      (g a : Matrix (m' a) (m' a) k) ⊗ₖ (((g c)⁻¹ : GL (m' c) k) : Matrix (m' c) (m' c) k)ᵀ := by
    ext ⟨u, v⟩ ⟨u', v'⟩
    show LinearMap.toMatrix' (adCoord p) (F (u, v)).1 (F (u', v')).1 =
      (g a : Matrix (m' a) (m' a) k) u u' * (((g c)⁻¹ : GL (m' c) k) : Matrix (m' c) (m' c) k) v' v
    rw [adCoord_apply_levi g p hp]
    show (leviEmb k e' g : Matrix (Fin N) (Fin N) k) (e' ⟨a, u⟩) (e' ⟨a, u'⟩) *
      (leviEmb k e' g⁻¹ : Matrix (Fin N) (Fin N) k) (e' ⟨c, v'⟩) (e' ⟨c, v⟩) = _
    rw [hL g a u u', hL g⁻¹ c v' v]
    rfl
  rw [← Matrix.det_submatrix_equiv_self E, hM, Matrix.det_kronecker, Matrix.det_transpose]

include hγ in
theorem block_det_of_not_le {a c : β'} (hac : ¬ a ≤ c) :
    ((LinearMap.toMatrix' (adCoord p)).toSquareBlock (parabolicBlockPair e' γ) (toLex (a, c))).det = 1 := by
  haveI : IsEmpty {s : ParabolicIndex N γ // parabolicBlockPair e' γ s = toLex (a, c)} := ⟨fun s => by
    have hs := s.2
    simp only [parabolicBlockPair, toLex_inj, Prod.mk.injEq] at hs
    apply s.1.2
    rw [hγ, hs.1, hs.2]
    exact not_le.mp hac⟩
  exact Matrix.det_isEmpty


include hγ hp in
theorem det_adLie_levi :
    (LinearEquiv.det (adLie k N γ p) : kˣ) =
      ∏ a, GeneralLinearGroup.det (g a) ^ modExp m' a := by
  have key := prod_le_pairs (fun a => GeneralLinearGroup.det (g a)) (fun a => Fintype.card (m' a))
  apply Units.ext
  rw [det_adLie_eq, (adCoord_blockTriangular g p hp).det,
    Finset.prod_subset (Finset.subset_univ _) (fun x _ hx => ?hz)]
  case hz =>
    haveI : IsEmpty {s : ParabolicIndex N γ // parabolicBlockPair e' γ s = x} :=
      ⟨fun s => hx (Finset.mem_image.mpr ⟨s.1, Finset.mem_univ _, s.2⟩)⟩
    exact Matrix.det_isEmpty
  rw [← Equiv.prod_comp toLex, Fintype.prod_prod_type]
  change _ = ((∏ a, GeneralLinearGroup.det (g a) ^ ((∑ b with a < b, (Fintype.card (m' b) : ℤ)) -
    ∑ b with b < a, (Fintype.card (m' b) : ℤ)) : kˣ) : k)
  rw [← key, Units.coe_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  by_cases hac : a ≤ c
  · rw [if_pos hac, block_det_of_le hγ g p hp hac, ← Matrix.GeneralLinearGroup.val_det_apply,
      ← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
  · rw [if_neg hac, block_det_of_not_le hγ p hac, Units.val_one]

end DetAd

section Main

theorem modularCharacter_levi {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (g : Levi k m') (p : blockUpper k N γ)
    (hp : (p : GL (Fin N) k) = leviEmb k e' g) :
    ((MeasureTheory.Measure.modularCharacter p : NNReal) : ℝ) = modulus k m' g := by
  rw [modularCharacter_blockUpper, det_adLie_levi hγ g p hp, map_prod, NNReal.coe_prod, modulus]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_zpow, NNReal.coe_zpow]
  rfl

theorem invSqrtModular_levi {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (g : Levi k m') (p : blockUpper k N γ)
    (hp : (p : GL (Fin N) k) = leviEmb k e' g) :
    invSqrtModular k N γ p = (((deltaHalf k m' g)⁻¹ : ℂˣ) : ℂ) := by
  have hpos : ∀ a, 0 ≤ GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det (g a)) := fun a => NNReal.coe_nonneg _
  have h1 : ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : NNReal) : ℝ) =
      ∏ a, GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det (g a)) ^ ((modExp m' a : ℝ) / 2) := by
    rw [Real.coe_sqrt, modularCharacter_levi hγ g p hp, modulus, Real.sqrt_eq_rpow,
      ← Real.finsetProd_rpow _ _ (fun a _ => zpow_nonneg (hpos a) _)]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul (hpos a)]
    ring_nf
  simp only [invSqrtModular, sqrtModular, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h1, Units.val_inv_eq_inv_val]
  congr 1
  rw [deltaHalf, MonoidHom.finsetProd_apply, Units.coe_prod, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Complex.ofReal_cpow (hpos a)]
  simp only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar, absPow, MonoidHom.coe_toHomUnits,
    MonoidHom.coe_mk, OneHom.coe_mk]
  push_cast
  rfl

theorem twKer_eq_ker {e' : (Σ j, m' j) ≃ Fin N} {γ : Fin N → ℕ}
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    GlobalTheory.PRep.twKer π (unipRad k e') 1 =
      Representation.Coinvariants.ker (π.comp (unipotentRadical k N γ).subtype) := by
  rw [unipRad_eq hγ]
  unfold GlobalTheory.PRep.twKer Representation.Coinvariants.ker
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_range, MonoidHom.one_apply, Units.val_one, one_smul, Prod.exists,
    MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply]
  constructor <;> rintro ⟨n, v, h⟩ <;> exact ⟨n, v, h.symm⟩

theorem jac_equiv_jacquetRep (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type}
    [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {N : ℕ} (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ)
    (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y) (φ' : Levi k m' ≃* levi k N γ)
    (hφ : ∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    Nonempty ((GlobalTheory.SmGL.jac e' π).Equiv ((jacquetRep k N γ π).comp φ'.toMonoidHom)) := by
  let L : GlobalTheory.PRep.Jacquet π (unipRad k e') ≃ₗ[ℂ] JacquetModule k N γ π :=
    Submodule.quotEquivOfEq _ _ (twKer_eq_ker hγ π)
  have hL : ∀ v : V, L (Submodule.Quotient.mk v) =
      Representation.Coinvariants.mk (π.comp (unipotentRadical k N γ).subtype) v := fun v => rfl
  have hI : ∀ (g : Levi k m') (x : GlobalTheory.PRep.Jacquet π (unipRad k e')),
      L (GlobalTheory.SmGL.jac e' π g x) = ((jacquetRep k N γ π).comp φ'.toMonoidHom) g (L x) := by
    intro g x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer π (unipRad k e') 1) x
    have hp : ((leviIncl (φ' g) : blockUpper k N γ) : GL (Fin N) k) = leviEmb k e' g := hφ g
    have h1 : GlobalTheory.SmGL.jac e' π g (Submodule.Quotient.mk v) =
        (((deltaHalf k m' g)⁻¹ : ℂˣ) : ℂ) •
          (Submodule.Quotient.mk (π (leviEmb k e' g) v) : GlobalTheory.PRep.Jacquet π (unipRad k e')) := rfl
    rw [h1, map_smul, hL, hL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, jacquetRep_mk,
      invSqrtModular_levi hγ g _ hp, hφ g]
  exact ⟨Representation.Equiv.mk' ⟨L.toLinearMap, fun g => LinearMap.ext fun x => hI g x⟩
    L.symm L.left_inv L.right_inv⟩

end Main

end GlobalTheory.CompanionTheory.JacBridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleDeterminantTwistStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jac_equiv_jacquetRep_comp_levi_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {N : ℕ} (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (φ' : Levi k m' ≃* levi k N γ), (∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g) → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Nonempty ((GlobalTheory.SmGL.jac e' π).Equiv ((jacquetRep k N γ π).comp φ'.toMonoidHom)) := by
  first | exact @GlobalTheory.CompanionTheory.JacBridge.jac_equiv_jacquetRep | exact GlobalTheory.CompanionTheory.JacBridge.jac_equiv_jacquetRep | (intros; apply GlobalTheory.CompanionTheory.JacBridge.jac_equiv_jacquetRep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuous
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmoothBridge

theorem isSmooth_comp {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G) (hψ : Continuous ψ) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (hρ : GlobalTheory.PRep.IsSmooth ρ) : GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  intro v
  have h := (hρ v).preimage hψ
  exact h

end GlobalTheory.CompanionTheory.SmoothBridge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuousStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmooth_comp_continuous : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G), Continuous ψ → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp | exact GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp | (intros; apply GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquiv
set_option maxSynthPendingDepth 1

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.CompanionTheory.SmGLBridge

namespace GlobalTheory.CompanionTheory.ParIndReindex

section Generic

variable {G G' V V' W : Type} [Group G] [Group G']
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]

theorem twKer_map (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    (twKer π N 1).map (L : V →ₗ[ℂ] V') = twKer π' N' 1 := by
  delta GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨⟨r n, (hN n).1 n.2⟩, L v, by simp [hL]⟩
  · rintro ⟨n', v', rfl⟩
    refine ⟨_, ⟨⟨r.symm n', (hN _).2 (by simpa using n'.2)⟩, L.symm v', rfl⟩, ?_⟩
    simp [hL]

def jacquetEquiv (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    Jacquet π N ≃ₗ[ℂ] Jacquet π' N' :=
  Submodule.Quotient.equiv _ _ L (twKer_map r L hL hN)

def pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') : indSpace H σ :=
  ⟨fun x => f.1 (r x), fun h g => by
    show f.1 (r (h * g)) = σ h (f.1 (r g))
    rw [map_mul, ← hσ h]
    exact f.2 ⟨r h, hH h⟩ (r g)⟩

theorem ind_pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') (g : G) :
    ind H σ g (pullFun r hH hσ f) = pullFun r hH hσ (ind H' σ' (r g) f) := by
  apply Subtype.ext
  funext x
  show f.1 (r (x * g)) = f.1 (r x * r g)
  rw [map_mul]

theorem pullFun_eq_iff (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f f' : indSpace H' σ') :
    pullFun r hH hσ f = pullFun r hH hσ f' ↔ f = f' := by
  constructor
  · intro h
    apply Subtype.ext
    funext y
    have h1 : f.1 (r (r.symm y)) = f'.1 (r (r.symm y)) :=
      congrArg (fun p : indSpace H σ => p.1 (r.symm y)) h
    simpa using h1
  · rintro rfl
    rfl

variable [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']

def pull (r : G ≃* G') (hr : Continuous r) {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) :
    smoothPart (ind H' σ') →ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := ⟨pullFun r hH hσ f.1, by
    have hset : {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1} =
        r ⁻¹' {g' : G' | ind H' σ' g' f.1 = f.1} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ind_pullFun, pullFun_eq_iff]
    show IsOpen {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1}
    rw [hset]
    exact IsOpen.preimage hr f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def indEquiv (r : G ≃* G') (hr : Continuous r) (hs : Continuous r.symm) {H : Subgroup G}
    {H' : Subgroup G'} (hH : ∀ g, g ∈ H ↔ r g ∈ H') {σ : Representation ℂ H W}
    {σ' : Representation ℂ H' W} (hσ : ∀ h : H, σ' ⟨r h, (hH h).1 h.2⟩ = σ h) :
    smoothPart (ind H σ) ≃ₗ[ℂ] smoothPart (ind H' σ') :=
  LinearEquiv.ofLinear
    (pull r.symm hs (fun h' => (hH _).2 (by simp)) (fun h' => by
      rw [← hσ ⟨r.symm h', (hH _).2 (by simp)⟩]
      congr 1
      exact Subtype.ext (by simp)))
    (pull r hr (fun h => (hH h).1 h.2) hσ)
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r (r.symm x)) = _
      simp)))
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r.symm (r x)) = _
      simp)))

end Generic

section Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {N : ℕ}

theorem glReindex_apply (ι : n ≃ Fin N) (g : GL n k) (i j : n) :
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι i) (ι j) =
      (g : Matrix n n k) i j := by
  show (Matrix.reindexAlgEquiv k k ι (g : Matrix n n k)) (ι i) (ι j) = (g : Matrix n n k) i j
  simp [Matrix.coe_reindexAlgEquiv]

theorem mem_parab_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ parab k e ↔ glReindex ι g ∈ parab k (e.trans ι) := by
  show (g : Matrix n n k).BlockTriangular (blk e) ↔
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (e.trans ι))
  constructor
  · intro h i j hij
    have h2 := @h (ι.symm i) (ι.symm j) (by simpa [blk] using hij)
    have e1 := glReindex_apply ι g (ι.symm i) (ι.symm j)
    simp only [Equiv.apply_symm_apply] at e1
    rw [e1]
    exact h2
  · intro h i j hij
    have h2 := @h (ι i) (ι j) (by simpa [blk] using hij)
    rw [glReindex_apply] at h2
    exact h2

private theorem leviProj_glReindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k)
    (h : g ∈ parab k e) (h' : glReindex ι g ∈ parab k (e.trans ι)) :
    leviProj k (e.trans ι) ⟨glReindex ι g, h'⟩ = leviProj k e ⟨g, h⟩ := by
  funext a
  apply Units.ext
  ext i j
  show ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι (e ⟨a, i⟩)) (ι (e ⟨a, j⟩)) =
    (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩)
  exact glReindex_apply ι g _ _

theorem mem_unipRad_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ unipRad k e ↔ glReindex ι g ∈ unipRad k (e.trans ι) := by
  show g ∈ Subgroup.map (parab k e).subtype (leviProj k e).ker ↔
    glReindex ι g ∈ Subgroup.map (parab k (e.trans ι)).subtype (leviProj k (e.trans ι)).ker
  simp only [Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨⟨p, hp'⟩, hp, rfl⟩
    refine ⟨⟨glReindex ι p, (mem_parab_reindex e ι p).1 hp'⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι p hp']
    exact hp
  · rintro ⟨⟨p, hp'⟩, hp, hpg⟩
    simp only [Subgroup.coe_subtype] at hpg
    subst hpg
    have hg : g ∈ parab k e := (mem_parab_reindex e ι g).2 hp'
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι g hg hp'] at hp
    exact hp

theorem leviProj_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (p : parab k e) :
    leviProj k (e.trans ι) ⟨glReindex ι p, (mem_parab_reindex (k := k) e ι p.1).1 p.2⟩ = leviProj k e p := by
  exact leviProj_glReindex e ι p.1 p.2 _

theorem leviEmb_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : Levi k m) :
    glReindex ι (leviEmb k e g) = leviEmb k (e.trans ι) g := by
  apply Units.ext
  ext i j
  have h1 := glReindex_apply (k := k) ι (leviEmb k e g) (ι.symm i) (ι.symm j)
  simp only [Equiv.apply_symm_apply] at h1
  rw [h1]
  rfl

theorem continuous_glReindex_symm (ι : n ≃ Fin N) :
    Continuous (glReindex (k := k) ι).symm := by
  have h1 : ⇑(glReindex (k := k) ι).symm = ⇑(glReindex (k := k) ι.symm) :=
    funext (glReindex_symm ι)
  rw [h1]
  exact continuous_glReindex ι.symm

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def parIndEquiv (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W) :
    IndSp e ρ ≃ₗ[ℂ] IndSp (e.trans ι) ρ :=
  indEquiv (glReindex ι) (continuous_glReindex ι) (continuous_glReindex_symm ι)
    (mem_parab_reindex e ι) (fun h => by
      show (GlobalTheory.SmGL.twist ρ (deltaHalf k m)) (leviProj k (e.trans ι) _) = (GlobalTheory.SmGL.twist ρ (deltaHalf k m)) (leviProj k e h)
      rw [leviProj_reindex])

theorem parIndEquiv_apply (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W)
    (g : GL n k) (f : IndSp e ρ) :
    parIndEquiv e ι ρ (parInd e ρ g f) = parInd (e.trans ι) ρ (glReindex ι g) (parIndEquiv e ι ρ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  show f.1.1 ((glReindex ι).symm y * g) = f.1.1 ((glReindex ι).symm (y * glReindex ι g))
  rw [map_mul, MulEquiv.symm_apply_apply]

end Reindex

theorem jac_parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((GlobalTheory.SmGL.jac e' (parInd e ρ)).Equiv (GlobalTheory.SmGL.jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  intro k _ _ _ _ α β' n _ _ _ _ _ _ m _ _ m' _ _ e e' N ι W _ _ ρ
  refine ⟨Representation.Equiv.mk
    (jacquetEquiv (glReindex (k := k) ι) (parIndEquiv e ι ρ) (parIndEquiv_apply e ι ρ)
      (mem_unipRad_reindex e' ι)) (fun l => ?_)⟩
  apply LinearMap.ext
  intro y
  obtain ⟨v, rfl⟩ := Quot.exists_rep y
  have h1 := parIndEquiv_apply e ι ρ (leviEmb k e' l) v
  rw [leviEmb_reindex] at h1
  have h2 : parIndEquiv e ι ρ ((((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) • parInd e ρ (leviEmb k e' l) v) =
      (((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) •
        parInd (e.trans ι) ρ (leviEmb k (e'.trans ι) l) (parIndEquiv e ι ρ v) := by
    rw [LinearEquiv.map_smul, h1]
  exact congrArg (Quot.mk _) h2

end GlobalTheory.CompanionTheory.ParIndReindex
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquivStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((GlobalTheory.SmGL.jac e' (parInd e ρ)).Equiv (GlobalTheory.SmGL.jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  first | exact @GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex | exact GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex | (intros; apply GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetBlockMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetBlockMatrix
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoCell

open GroundTheory.Automorphic.Parabolic

theorem eq_iff_of_lt_iff {C A B : Type} [LinearOrder A] [LinearOrder B] (f : C → A) (g : C → B)
    (h : ∀ x y, f x < f y ↔ g x < g y) (x y : C) : f x = f y ↔ g x = g y := by
  constructor
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this

theorem card_cell_of_card_corner {n : ℕ} {β γ : Fin n → ℕ} {w w' : Equiv.Perm (Fin n)}
    (h : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card) (a b : ℕ) :
    (Finset.univ.filter fun j => γ j = b ∧ β (w j) = a).card =
      (Finset.univ.filter fun j => γ j = b ∧ β (w' j) = a).card := by
  classical
  have h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card := by
    intro a b
    cases b with
    | zero => simpa using h a 0
    | succ b =>
      have key : ∀ u : Equiv.Perm (Fin n),
          (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card =
            (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card +
              (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card := by
        intro u
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          omega
        · rw [Finset.disjoint_filter]
          intro j _ h1 h2
          omega
      have := h a (b + 1)
      rw [key w, key w', h a b] at this
      omega
  have key : ∀ u : Equiv.Perm (Fin n),
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card =
        (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card +
          (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card := by
    intro u
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      omega
  have := h1 a b
  rw [key w, key w', h1 (a + 1) b] at this
  omega

theorem permGL_mem_doubleCoset_iff_card : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  intro k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ e' γ hγ w w'
  classical
  have hβe := eq_iff_of_lt_iff β (blk e) hβ
  have hγe := eq_iff_of_lt_iff γ (blk e') hγ
  have reidx : ∀ (u : Equiv.Perm (Fin N)) (i : α) (j : β'),
      (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (u.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j).card := by
    intro u i j
    apply Finset.card_equiv u.symm
    intro x
    simp
  constructor
  · intro hmem i j
    have hc : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
        (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card := by
      intro a b
      rw [← cellRank_permGL (F := k), ← cellRank_permGL (F := k)]
      exact (cellRank_of_mem_doubleCoset hmem a b).symm
    rw [reidx, reidx]
    by_cases hi : ∃ x0, blk e x0 = i
    · by_cases hj : ∃ y0, blk e' y0 = j
      · obtain ⟨x0, rfl⟩ := hi
        obtain ⟨y0, rfl⟩ := hj
        have conv : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = blk e x0 ∧ blk e' y = blk e' y0) =
              Finset.univ.filter fun y => γ y = γ y0 ∧ β (u y) = β x0 := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβe, hγe]
          tauto
        rw [conv, conv]
        exact card_cell_of_card_corner hc _ _
      · have hz : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => hj ⟨y, h.2⟩
        rw [hz, hz]
    · have hz : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hi ⟨u y, h.1⟩
      rw [hz, hz]
  · intro h
    have hcard : ∀ c : α × β', Fintype.card {y : Fin N // (blk e (w y), blk e' y) = c} =
        Fintype.card {y : Fin N // (blk e (w' y), blk e' y) = c} := by
      intro c
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have conv : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => (blk e (u y), blk e' y) = c) =
            Finset.univ.filter fun y => blk e (u y) = c.1 ∧ blk e' y = c.2 := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      rw [conv, conv, ← reidx, ← reidx]
      exact h c.1 c.2
    let v : Fin N ≃ Fin N := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)
    have hv : ∀ j, (blk e (w' (v j)), blk e' (v j)) = (blk e (w j), blk e' j) := fun j =>
      Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j
    have hvβ : ∀ j, β (w' (v j)) = β (w j) := fun j => (hβe _ _).2 (Prod.ext_iff.1 (hv j)).1
    have hvγ : ∀ j, γ (v j) = γ j := fun j => (hγe _ _).2 (Prod.ext_iff.1 (hv j)).2
    let u : Equiv.Perm (Fin N) := w' * v * w⁻¹
    have hu : ∀ x, β (u x) = β x := by
      intro x
      simp only [u, Equiv.Perm.mul_apply]
      rw [hvβ]
      simp
    have hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin N)) x) = γ x := by
      intro x
      have := hvγ ((v⁻¹ : Equiv.Perm (Fin N)) x)
      have h' : v ((v⁻¹ : Equiv.Perm (Fin N)) x) = x := Equiv.apply_symm_apply v x
      rw [h'] at this
      exact this.symm
    refine DoubleCoset.mem_doubleCoset.2 ⟨permGL k u, permGL_mem_blockUpper hu, permGL k v⁻¹,
      permGL_mem_blockUpper hv', ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [u]
    group

end GlobalTheory.CompanionTheory.GeoCell
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetBlockMatrixStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_block_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  first | exact @GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card | exact GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card | (intros; apply GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltration
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoAssembly

def equivComp {G H V V' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') (ψ : H →* G) : Representation.Equiv (ρ.comp ψ) (ρ'.comp ψ) :=
  Representation.Equiv.mk' ⟨e.toLinearEquiv.toLinearMap, fun h => by
      ext x; exact LinearMap.congr_fun (e.isIntertwining' (ψ h)) x⟩ e.invFun
    e.left_inv e.right_inv


set_option maxHeartbeats 1000000 in
theorem jacquetOfInducedFiltration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  intro k _ _ _ _ α β n _ _ _ _ _ _ m _ _ m' _ _ e e'
  let N := Fintype.card n
  let ι : n ≃ Fin N := Fintype.equivFin n
  let E := e.trans ι
  let E' := e'.trans ι
  obtain ⟨βF, hβ⟩ := GlobalTheory.T.exists_strict_block_order m E
  obtain ⟨γF, hγ⟩ := GlobalTheory.T.exists_strict_block_order m' E'
  obtain ⟨φ, hφ, -, hφsc⟩ := GlobalTheory.T.levi_block_homeomorph k E βF hβ
  obtain ⟨φ', hφ', -, -⟩ := GlobalTheory.T.levi_block_homeomorph k E' γF hγ
  obtain ⟨K, w, hcov, hfilt⟩ := GlobalTheory.T.bernstein_zelevinsky_geometric_lemma k N βF γF
  let sz : Equiv.Perm (Fin N) → α → β → ℕ := fun v i j =>
    (Finset.univ.filter fun x : Fin N => blk E x = i ∧ blk E' (v.symm x) = j).card
  let toSM : Fin K → SizeMatrix m m' := fun t => ⟨sz (w t), GlobalTheory.T.permutation_block_counts E E' (w t)⟩
  have hsz : ∀ v v' : Equiv.Perm (Fin N), permGL k v' ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) ↔ sz v = sz v' := by
    intro v v'
    rw [GlobalTheory.T.double_coset_block_matrix k E βF hβ E' γF hγ v v']
    exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => congrFun (congrFun h i) j⟩
  have hself : ∀ v : Equiv.Perm (Fin N), permGL k v ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) := fun v =>
    (hsz v v).2 rfl
  have inj : Function.Injective toSM := by
    intro t t' h
    have h1 : sz (w t) = sz (w t') := congrArg Subtype.val h
    obtain ⟨j, -, huniq⟩ := hcov (permGL k (w t'))
    exact (huniq t ((hsz _ _).2 h1)).trans (huniq t' (hself _)).symm
  have surj : Function.Surjective toSM := by
    intro B
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_perm_block_matrix E E' B
    obtain ⟨t, ht, -⟩ := hcov (permGL k v)
    refine ⟨t, Subtype.ext ?_⟩
    show sz (w t) = B.1
    rw [(hsz _ _).1 ht]
    exact funext fun i => funext fun j => hv i j
  refine ⟨K, Equiv.ofBijective toSM ⟨inj, surj⟩, ?_⟩
  intro W _ _ ρ hρ
  let σ := ρ.comp φ.symm.toMonoidHom
  have hσ : GroundTheory.Automorphic.IsSmooth σ := GlobalTheory.T.isSmooth_comp_continuous φ.symm.toMonoidHom hφsc ρ hρ
  have hF := hfilt W σ hσ
  obtain ⟨V, hF⟩ := hF
  obtain ⟨hV0, hF⟩ := hF
  obtain ⟨hVK, hF⟩ := hF
  obtain ⟨hVmono, hV, hΨ⟩ := hF
  have e1' := GlobalTheory.T.induction_reindex_equiv k e e' ι ρ
  obtain ⟨e1⟩ := e1'
  have e2' := GlobalTheory.T.jac_equiv_jacquetRep_comp_levi_equiv k E' γF hγ φ' hφ' (V := IndSp E ρ) (parInd E ρ)
  obtain ⟨e2⟩ := e2'
  have e3' := GlobalTheory.T.parabolicInd_equiv_levi_transport k E βF hβ φ hφ ρ
  obtain ⟨e3⟩ := e3'
  have e4' := GlobalTheory.T.jacquet_module_equiv k N γF (V := IndSp E ρ) (parInd E ρ) _ e3
  obtain ⟨e4⟩ := e4'
  have e12 := e1.trans e2
  have e45 := equivComp e4 φ'.toMonoidHom
  have e5 := e12.trans e45
  have hT := GlobalTheory.T.filtration_transport_equiv φ'.toMonoidHom _ _ e5 K _
    (fun j => indRep (cellLeviSub k βF γF (w j)) (normInducing σ γF (w j))) V hV0 hVK hVmono hV hΨ
  obtain ⟨S, hT⟩ := hT
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hT
  refine ⟨S, hS1, hS2, hS3, fun t f g => ?_⟩
  have q1' := hS4 t
  obtain ⟨q1⟩ := q1'
  have c' := GlobalTheory.T.levi_intersection_conjugate k E βF hβ φ hφ E' γF hγ φ' hφ' ρ (w t)
  obtain ⟨f0, g0, c'⟩ := c'
  obtain ⟨q2⟩ := c'
  have q3' := GlobalTheory.T.cell_levi_tensor_decomposition (fun i j => by rw [Fintype.card_fin, Fintype.card_fin]; rfl) f0 g0 f g ρ
  obtain ⟨q3⟩ := q3'
  exact ⟨q1.trans (q2.trans q3)⟩

end GlobalTheory.CompanionTheory.GeoAssembly
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltrationStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_of_induced_filtration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  first | exact @GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration | exact GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration | (intros; apply GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration <;> assumption)
end

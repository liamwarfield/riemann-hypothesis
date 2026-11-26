module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachLatticeMatricesGammaPhi
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachLatticeMatricesGammaPhi
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

noncomputable section

namespace GlobalTheory.HWL.Mat

section Abstract

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : Submodule A M} {r : ℕ}

theorem coeff_ext (nb : Module.Basis (Fin r) A ↥N) {a b : Fin r → A}
    (h : ∑ i, a i • (nb i : M) = ∑ i, b i • (nb i : M)) (i : Fin r) : a i = b i := by
  have hli : LinearIndependent A (fun i => (nb i : M)) :=
    nb.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  exact Fintype.linearIndependent_iffₛ.1 hli a b h i

theorem eq_sum (nb : Module.Basis (Fin r) A ↥N) {x : M} (hx : x ∈ N) :
    x = ∑ i, nb.repr ⟨x, hx⟩ i • (nb i : M) := by
  have h := congrArg N.subtype (nb.sum_repr ⟨x, hx⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simpa using h.symm

theorem semi_sum {f : M →+ M} {σ : A → A} (hf : ∀ a x, f (a • x) = σ a • f x) (a : Fin r → A)
    (x : Fin r → M) : f (∑ i, a i • x i) = ∑ i, σ (a i) • f (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hf _ _

theorem sum_sum (P C : Matrix (Fin r) (Fin r) A) (e : Fin r → M) (j : Fin r) :
    ∑ k, C k j • ∑ i, P i k • e i = ∑ i, (P * C) i j • e i := by
  simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem common_exp (S : Submodule A M) (Q : A) (x : Fin r → M) (h : ∀ j, ∃ k : ℕ, Q ^ k • x j ∈ S) :
    ∃ m : ℕ, ∀ j, Q ^ m • x j ∈ S := by
  choose k hk using h
  refine ⟨∑ j, k j, fun j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [hc, add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk j)

theorem exists_matrices {Γ : Type} [Mul Γ] (nb : Module.Basis (Fin r) A ↥N) (Q π : A)
    (φ : M →+ M) (σ : A → A) (hφ : ∀ a x, φ (a • x) = σ a • φ x)
    (γ : Γ → M →+ M) (τ : Γ → A →+* A) (hγ : ∀ g a x, γ g (a • x) = τ g a • γ g x)
    (hmul : ∀ g h x, γ (g * h) x = γ g (γ h x)) (hcomm : ∀ g x, φ (γ g x) = γ g (φ x))
    (hNφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hNinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set M)))
    (hNΓ : ∀ g, ∀ x ∈ N, γ g x ∈ N) (hNπ : ∀ g, ∀ x ∈ N, ∃ y ∈ N, γ g x - x = π • y) :
    ∃ (m m' : ℕ) (Gm : Γ → Matrix (Fin r) (Fin r) A) (Pm Pm' : Matrix (Fin r) (Fin r) A),
      (∀ g h, Gm (g * h) = Gm g * (Gm h).map (τ g)) ∧
      (∀ g i j, ∃ c, Gm g i j = (if i = j then 1 else 0) + π * c) ∧
      Pm * Pm' = (Q ^ m') • (1 : Matrix (Fin r) (Fin r) A) ∧
      (∀ g, (τ g Q ^ m) • (Pm * (Gm g).map σ) = (Q ^ m) • (Gm g * Pm.map (τ g))) ∧
      (∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M)) ∧
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) := by
  classical
  obtain ⟨m, hm⟩ := common_exp N Q (fun j => φ (nb j : M)) fun j => hNφ _ (nb j).2
  obtain ⟨k, hk⟩ := common_exp _ Q (fun j => (nb j : M)) fun j => hNinv _ (nb j).2
  have hspan : Submodule.span A (φ '' (N : Set M)) ≤
      Submodule.span A (Set.range fun i => φ (nb i : M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [eq_sum nb hx, semi_sum hφ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun A).1 (hspan (hk j))
  obtain ⟨Gm, hG⟩ : ∃ Gm : Γ → Matrix (Fin r) (Fin r) A,
      ∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M) :=
    ⟨fun g i j => nb.repr ⟨_, hNΓ g _ (nb j).2⟩ i, fun g j => eq_sum nb _⟩
  obtain ⟨Pm, hP⟩ : ∃ Pm : Matrix (Fin r) (Fin r) A,
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) :=
    ⟨fun i j => nb.repr ⟨_, hm j⟩ i, fun j => eq_sum nb _⟩
  have hone : ∀ (a : A) (j : Fin r),
      ∑ i, (a * if i = j then 1 else 0) • (nb i : M) = a • (nb j : M) := by
    intro a j
    rw [Finset.sum_eq_single j] <;> simp +contextual
  refine ⟨m, m + k, Gm, Pm, Matrix.of fun i j => c j i, ?_, ?_, ?_, ?_, hG, hP⟩
  · intro g h
    ext i j
    refine coeff_ext nb (a := fun i => Gm (g * h) i j)
      (b := fun i => (Gm g * (Gm h).map (τ g)) i j) ?_ i
    rw [← hG, hmul, hG h, semi_sum (hγ g), ← sum_sum]
    simp only [hG, Matrix.map_apply]
  · intro g i j
    obtain ⟨y, hy, e⟩ := hNπ g _ (nb j).2
    refine ⟨nb.repr ⟨y, hy⟩ i, ?_⟩
    refine coeff_ext nb (a := fun i => Gm g i j)
      (b := fun i => (if i = j then 1 else 0) + π * nb.repr ⟨y, hy⟩ i) ?_ i
    have h1 := hone 1 j
    simp only [one_mul, one_smul] at h1
    simp only [add_smul, Finset.sum_add_distrib, mul_smul]
    rw [← hG, h1, ← Finset.smul_sum, ← eq_sum nb hy, ← e]
    abel
  · ext i j
    refine coeff_ext nb (a := fun i => (Pm * Matrix.of fun i j => c j i) i j)
      (b := fun i => ((Q ^ (m + k)) • (1 : Matrix (Fin r) (Fin r) A)) i j) ?_ i
    rw [← sum_sum]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hone, ← hP, Matrix.of_apply]
    rw [pow_add, mul_smul, ← hc j, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  · intro g
    ext i j
    refine coeff_ext nb (a := fun i => ((τ g Q ^ m) • (Pm * (Gm g).map σ)) i j)
      (b := fun i => ((Q ^ m) • (Gm g * Pm.map (τ g))) i j) ?_ i
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← sum_sum, ← sum_sum]
    have h1 : ∑ k, (Gm g).map σ k j • ∑ i, Pm i k • (nb i : M) = Q ^ m • γ g (φ (nb j : M)) := by
      rw [← hcomm, hG, semi_sum hφ, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← hP, smul_comm, Matrix.map_apply]
    have h2 : ∑ k, Pm.map (τ g) k j • ∑ i, Gm g i k • (nb i : M) =
        τ g Q ^ m • γ g (φ (nb j : M)) := by
      rw [← map_pow, ← hγ, hP, semi_sum (hγ g)]
      exact Finset.sum_congr rfl fun l _ => by rw [← hG, Matrix.map_apply]
    rw [h1, h2, smul_comm]

end Abstract

theorem wach_matrices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n} (Mo : WN E zl) (T : LocLat G Qp LL O) (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)), ∃ (m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) ∧ (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) ∧ Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) ∧ (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) ∧ (∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)) ∧ ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n s Γ R Zl Ai _ _ _ _
    RW _ _ inclR φR gR πA I E zl Mo T r nb
  have hφ : ∀ (a : LetA O n) (x : E.DD T), E.φD T (a • x) = letφ R.φ₀ a • E.φD T x := by
    intro a x
    rw [← algebraMap_smul R.EE a x, E.φD_smul, R.φE_ext, algebraMap_smul]
  have hγ : ∀ g (a : LetA O n) (x : E.DD T),
      E.γD T g (a • x) = letγ (R.γ₀ g) a • E.γD T g x := by
    intro g a x
    rw [← algebraMap_smul R.EE a x, E.γD_smul, R.γE_ext, algebraMap_smul]
  obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ :=
    exists_matrices nb R.Q letπ (E.φD T).toAddMonoidHom (letφ R.φ₀) hφ
      (fun g => (E.γD T g).toAddMonoidHom) (fun g => (letγ (n := n) (R.γ₀ g)).toRingHom) hγ
      (E.γD_mul T) (E.φγ_comm T) (Mo.N_φ T) (Mo.N_φinv T) (Mo.N_Γ T) (Mo.N_π T)
  refine ⟨m, m', Gm, Pm, Pm', h1, ?_, h3, h4, h5, h6⟩
  intro g i j k
  obtain ⟨c, hc⟩ := h2 g i j
  rw [hc]
  split_ifs <;> simp [letπ]

end GlobalTheory.HWL.Mat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachLatticeMatricesGammaPhiStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachLattice_matrices_gamma_phi : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n} (Mo : WN E zl) (T : LocLat G Qp LL O) (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)), ∃ (m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) ∧ (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) ∧ Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) ∧ (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) ∧ (∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)) ∧ ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T) := by
  first | exact @GlobalTheory.HWL.Mat.wach_matrices | exact GlobalTheory.HWL.Mat.wach_matrices | (intros; apply GlobalTheory.HWL.Mat.wach_matrices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesTransport
noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Matrix

section Cz

variable {L : Type} [Field L]

theorem cz_neg (f : PowerSeries L) {k : ℤ} (hk : k < 0) : cz f k = 0 := by
  simp [cz, not_le.mpr hk]

theorem cz_nat (f : PowerSeries L) (k : ℕ) : cz f (k : ℤ) = PowerSeries.coeff k f := by
  simp [cz]

theorem cz_add (f g : PowerSeries L) (k : ℤ) : cz (f + g) k = cz f k + cz g k := by
  unfold cz; split_ifs <;> simp

theorem cz_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries L) (k : ℤ) :
    cz (∑ i ∈ s, f i) k = ∑ i ∈ s, cz (f i) k := by
  unfold cz; split_ifs <;> simp

theorem cz_C_mul (c : L) (f : PowerSeries L) (k : ℤ) : cz (PowerSeries.C c * f) k = c * cz f k := by
  unfold cz; split_ifs <;> simp

theorem cz_rescale (c : L) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.rescale c f) k = c ^ k * cz f k := by
  rcases lt_or_ge k 0 with h | h
  · simp [cz_neg _ h]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [cz_nat, PowerSeries.coeff_rescale]

theorem cz_X_pow_mul (w : ℕ) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.X ^ w * f) (k + (w : ℤ)) = cz f k := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    rcases lt_or_ge (k + (w : ℤ)) 0 with h' | h'
    · exact cz_neg _ h'
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h'
      rw [hm, cz_nat, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [← Nat.cast_add, cz_nat, cz_nat, PowerSeries.coeff_X_pow_mul]

theorem cz_mul (g f : PowerSeries L) (k : ℤ) (N : ℕ) (hN : k < (N : ℤ)) :
    cz (g * f) k = ∑ i ∈ Finset.range N, PowerSeries.coeff i g * cz f (k - (i : ℤ)) := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [cz_neg _ (by omega), mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [cz_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show m + 1 ≤ N by omega))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
      rw [← Nat.cast_sub this, cz_nat]
    · intro i _ hi
      have : m < i := by simpa using hi
      rw [cz_neg _ (by omega), mul_zero]

theorem series_transport {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
    {r r' : ℕ} (w w' : ℕ) (A : Fin r' → PowerSeries L) (Bs : Fin r → PowerSeries L) (κ : L) (hκ : κ ≠ 0)
    (g : PowerSeries L) (c : Fin r' → Fin r → L)
    (hA : ∀ j, (PowerSeries.C κ * PowerSeries.X) ^ w * A j =
      PowerSeries.X ^ w' * (g * ∑ p, PowerSeries.C (c j p) * PowerSeries.rescale κ (Bs p)))
    (h : M →ₗ[L] M') (D : Fin r → M) (D' : Fin r' → M') (hD : ∀ p, h (D p) = ∑ j, c j p • D' j) (k : ℤ) :
    ∑ j, cz (A j) (k + (w' : ℤ)) • D' j = ∑ᶠ i : ℕ, PowerSeries.coeff i g •
      (κ ^ (k - (i : ℤ)) • h (∑ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) • D p)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k + (w : ℤ) < (N : ℤ) := ⟨(k + (w : ℤ)).toNat + 1, by omega⟩
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
  · have key : ∀ j, cz (A j) (k + (w' : ℤ)) = ∑ i ∈ Finset.range N, ∑ p, PowerSeries.coeff i g *
        (κ ^ (k - (i : ℤ)) * (cz (Bs p) (k - (i : ℤ) + (w : ℤ)) * c j p)) := by
      intro j
      have h1 := congrArg (fun f => cz f (k + (w : ℤ) + (w' : ℤ))) (hA j)
      rw [cz_X_pow_mul, mul_pow, ← map_pow, mul_assoc, cz_C_mul, add_right_comm, cz_X_pow_mul,
        cz_mul _ _ _ N hN] at h1
      apply mul_left_cancel₀ (pow_ne_zero w hκ)
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cz_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cz_C_mul, cz_rescale, show k + (w : ℤ) - (i : ℤ) = k - (i : ℤ) + (w : ℤ) by ring, zpow_add₀ hκ,
        zpow_natCast]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [key, Finset.sum_smul, map_sum, map_smul, hD, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · intro i hi
    by_contra hc
    apply hi
    have : N ≤ i := by simpa using hc
    have hz : ∀ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) = 0 := fun p => cz_neg _ (by omega)
    simp [hz]

end Cz

theorem basis_transport {C S : Type} [CommRing C] [CommRing S] (J : C →+* S) (σ : C →+* C) (σS : S →+* S)
    (hJ : ∀ a, J (σ a) = σS (J a)) {M M' : Type} [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    (h : M →+ M') (hh : ∀ (a : S) m, h (a • m) = σS a • h m) (t q : C) (ht : IsUnit (J t)) (hq : IsUnit (J q))
    {r r' : ℕ} (w w' : ℕ) (bn d : Fin r → M) (bn' d' : Fin r' → M') (U : Fin r → Fin r → C)
    (U' : Fin r' → Fin r' → C) (H Cm : Fin r' → Fin r → C)
    (hd : ∀ j, J t ^ w • d j = ∑ i, J (U i j) • bn i) (hd' : ∀ j, J t ^ w' • d' j = ∑ i, J (U' i j) • bn' i)
    (hH : ∀ j, J q • h (bn j) = ∑ i, J (H i j) • bn' i)
    (hU : ∀ k p, t ^ w' * ∑ i, H k i * σ (U i p) = σ t ^ w * q * ∑ j, U' k j * Cm j p) (p : Fin r) :
    h (d p) = ∑ j, J (Cm j p) • d' j := by
  have hu : IsUnit (J t ^ w' * σS (J t) ^ w * J q) := ((ht.pow _).mul ((ht.map σS).pow _)).mul hq
  apply hu.smul_left_cancel.mp
  have e1 : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) =
      ∑ k, J (t ^ w' * ∑ i, H k i * σ (U i p)) • bn' k := by
    have : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) = J t ^ w' • J q • h (J t ^ w • d p) := by
      rw [hh, map_pow, smul_smul, smul_smul]
      congr 1
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, hd, map_sum, Finset.smul_sum, Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hh, smul_comm (J q), hH, Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have e2 : (J t ^ w' * σS (J t) ^ w * J q) • ∑ j, J (Cm j p) • d' j =
      ∑ k, J (σ t ^ w * q * ∑ j, U' k j * Cm j p) • bn' k := by
    have : ∀ j, (J t ^ w' * σS (J t) ^ w * J q) • J (Cm j p) • d' j =
        (σS (J t) ^ w * J q * J (Cm j p)) • J t ^ w' • d' j := by
      intro j
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [this, hd', Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  rw [e1, e2]
  simp only [hU]

theorem coord_transport {A : Type} [CommRing A] (σ : A →+* A) {r r' : ℕ} (U V : Matrix (Fin r) (Fin r) A)
    (U' V' : Matrix (Fin r') (Fin r') A) (H Cm : Matrix (Fin r') (Fin r) A) (q q' : A)
    (hq : ∀ a, q * a = 0 → a = 0) (hUV : U * V = 1) (hUV' : U' * V' = 1)
    (hU : H * U.map σ = q • (U' * Cm)) (c : Fin r → A) (c' : Fin r' → A)
    (hc : q • c' = q' • H *ᵥ (σ ∘ c)) : V' *ᵥ c' = q' • Cm *ᵥ (σ ∘ (V *ᵥ c)) := by
  have h1 : V' * H = q • (Cm * V.map σ) := by
    have h2 : U.map σ * V.map σ = 1 := by
      rw [← Matrix.map_mul, hUV, Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc V' * H = V' * (H * U.map σ) * V.map σ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = q • (Cm * V.map σ) := by
          rw [hU, Matrix.mul_smul, ← Matrix.mul_assoc, mul_eq_one_comm.mp hUV', Matrix.one_mul, Matrix.smul_mul]
  have h3 : σ ∘ (V *ᵥ c) = V.map σ *ᵥ (σ ∘ c) := by
    funext i
    exact RingHom.map_mulVec σ V c i
  have h4 : q • (V' *ᵥ c') = q • (q' • Cm *ᵥ (σ ∘ (V *ᵥ c))) := by
    rw [← Matrix.mulVec_smul, hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1, h3, Matrix.mulVec_mulVec,
      Matrix.smul_mulVec, smul_comm]
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.smul_apply, smul_eq_mul] at h5 ⊢
  exact sub_eq_zero.mp (hq _ (by rw [mul_sub, h5, sub_self]))

end GlobalTheory.HWL.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasis
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualTop

theorem eq_zero_of_forall_pow_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ c : O} (hϖ : Irreducible ϖ) (h : ∀ n : ℕ, ϖ ^ n ∣ c) : c = 0 := by
  by_contra hc
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  obtain ⟨d, hd⟩ := h (k + 1)
  have hk : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hu : (u : O) = ϖ * d := by
    apply mul_right_cancel₀ hk
    rw [hd]; ring
  exact hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro d hu.symm) u.isUnit)

section Lat

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem bT_smul_left (k : FractionRing O) (x : VT) (y : VT') :
    D.bT (k • x) y = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT
    (FractionRing O)).map_smul (D.bT.flip y) k x

theorem bT_smul_right (k : FractionRing O) (x : VT) (y : VT') :
    D.bT x (k • y) = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT'
    (FractionRing O)).map_smul (D.bT x) k y

theorem eq_zero_of_bT (hP : PerfectRight D.bT) {y : VT'} (h : ∀ x, D.bT x y = 0) : y = 0 :=
  (hP 0).unique h (fun x => by simp)

theorem dualLatticePairing_eq_zero_of_mem_lattice (hL : IsLatticeIn D.T) {y : VT'} (h : ∀ x ∈ D.T, D.bT x y = 0) (x : VT) :
    D.bT x y = 0 := by
  let ψ := (D.bT.flip y).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
  have hs : Submodule.span (FractionRing O) (D.T : Set VT) ≤ LinearMap.ker ψ :=
    Submodule.span_le.2 fun z hz => LinearMap.mem_ker.2 (h z hz)
  have hx : x ∈ Submodule.span (FractionRing O) (D.T : Set VT) := hL.2 ▸ Submodule.mem_top
  exact LinearMap.mem_ker.1 (hs hx)

theorem cont_bT (x : VT) : Continuous fun y : VT' => D.bT x y :=
  D.contbT.comp (continuous_const.prodMk continuous_id)

theorem isOpen_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsOpen ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
  have : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext t; simp [Submodule.mem_one]
  rw [this]; exact hemb.isOpen_range

theorem isClosed_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) :=
  AddSubgroup.isClosed_of_isOpen (1 : Submodule O (FractionRing O)).toAddSubgroup (isOpen_one hemb)

theorem isClosed_dualLattice_of_pairing (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed (D.T' : Set VT') := by
  have : (D.T' : Set VT') = ⋂ x ∈ D.T,
      (fun y => D.bT x y) ⁻¹' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext y
    exact ⟨fun h => Set.mem_iInter₂.2 fun x hx => h x hx, fun h x hx => Set.mem_iInter₂.1 h x hx⟩
  rw [this]
  exact isClosed_biInter fun x _ => (isClosed_one hemb).preimage (cont_bT D x)

end Lat

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem isCompact_dualLattice_of_pairing [CompactSpace O] (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) : IsCompact (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hL.1
  have hsK : Submodule.span (FractionRing O) (s : Set VT) = ⊤ := by
    rw [eq_top_iff, ← hL.2]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [← hs] at hx
    exact Submodule.span_subset_span O (FractionRing O) (s : Set VT) hx
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (FractionRing O) (s : Set VT)
  haveI : Fintype b := (s.finite_toSet.subset hbs).fintype
  obtain ⟨e, he⟩ : ∃ e : Module.Basis b (FractionRing O) VT, ∀ i, e i = (i : VT) :=
    ⟨Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hsK])),
      fun i => Module.Basis.mk_apply _ _ i⟩
  have hbT : ∀ i : b, (i : VT) ∈ D.T := fun i => hs ▸ Submodule.subset_span (hbs i.2)
  choose f hf using fun i : b => (hP (e.coord i)).exists
  let Φ : (b → O) → VT' := fun c => ∑ i, c i • f i
  have hΦ : Continuous Φ := continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hsub : (D.T' : Set VT') ⊆ Set.range Φ := by
    intro y hy
    have hy' : ∀ i : b, D.bT (i : VT) y ∈ (1 : Submodule O (FractionRing O)) := fun i => hy _ (hbT i)
    choose c hc using fun i => Submodule.mem_one.1 (hy' i)
    refine ⟨c, ?_⟩
    symm
    rw [← sub_eq_zero]
    apply eq_zero_of_bT D hP
    intro x
    have hx : D.bT x y = ∑ i, e.coord i x * algebraMap O (FractionRing O) (c i) := by
      conv_lhs => rw [← e.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bT_smul_left, he, ← hc i, Module.Basis.coord_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, hx, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hf, Algebra.smul_def, mul_comm]
  exact (isCompact_range hΦ).of_isClosed_subset (isClosed_dualLattice_of_pairing D hemb) hsub

end Lat2

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat3

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem isOpen_powSub (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
  obtain ⟨s, hs⟩ := hL.1
  set a : FractionRing O := algebraMap O (FractionRing O) ϖ ^ n with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ (fun h => hϖ.ne_zero
    (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero])))
  let W : Set ↥D.T' := ⋂ x ∈ s, (fun z : ↥D.T' => D.bT (a⁻¹ • x) (z : VT')) ⁻¹'
    ((1 : Submodule O (FractionRing O)) : Set (FractionRing O))
  have hW : IsOpen W := isOpen_biInter_finset fun x _ =>
    (isOpen_one hemb).preimage ((cont_bT D _).comp continuous_subtype_val)
  have h0 : (0 : ↥D.T') ∈ W := Set.mem_iInter₂.2 fun x _ => by
    simp only [Set.mem_preimage, ZeroMemClass.coe_zero, map_zero, SetLike.mem_coe]
    exact Submodule.zero_mem _
  have hWsub : W ⊆ ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
    intro z hz
    have hz' := Set.mem_iInter₂.1 hz
    have hyT : a⁻¹ • (z : VT') ∈ D.T' := by
      intro x hx
      have hle : Submodule.span O (s : Set VT) ≤
          (1 : Submodule O (FractionRing O)).comap (D.bT.flip (a⁻¹ • (z : VT'))) := by
        refine Submodule.span_le.2 fun x hx => ?_
        have := hz' x hx
        simp only [Set.mem_preimage, SetLike.mem_coe] at this
        show D.bT x (a⁻¹ • (z : VT')) ∈ (1 : Submodule O (FractionRing O))
        rwa [bT_smul_right, ← bT_smul_left]
      rw [hs] at hle
      exact hle hx
    refine mem_powSub.2 ⟨⟨a⁻¹ • (z : VT'), hyT⟩, Subtype.ext ?_⟩
    show ϖ ^ n • a⁻¹ • (z : VT') = z
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n), smul_smul, map_pow, ← ha, mul_inv_cancel₀ ha0,
      one_smul]
  exact AddSubgroup.isOpen_of_mem_nhds (powSub (M := ↥D.T') ϖ n).toAddSubgroup
    (Filter.mem_of_superset (hW.mem_nhds h0) hWsub)

theorem eq_zero_of_mem_powSub (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) {ϖ : O}
    (hϖ : Irreducible ϖ) {z : ↥D.T'} (hz : ∀ n, z ∈ powSub (M := ↥D.T') ϖ n) : z = 0 := by
  refine Subtype.ext (eq_zero_of_bT D hP (dualLatticePairing_eq_zero_of_mem_lattice D hL (fun x hx => ?_)))
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (z.2 x hx)
  have hdvd : ∀ n : ℕ, ϖ ^ n ∣ c := by
    intro n
    obtain ⟨w, hw⟩ := mem_powSub.1 (hz n)
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (w.2 x hx)
    refine ⟨d, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [hc, ← hw, map_mul, hd]
    show D.bT x (ϖ ^ n • (w : VT')) = _
    rw [map_smul, Algebra.smul_def]
  rw [← hc, eq_zero_of_forall_pow_dvd hϖ hdvd, map_zero]

end Lat3

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

theorem dualLat_compact_powSub_nhds : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), CompactSpace O → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → IsLatticeIn D.T → PerfectRight D.bT → T2Space VT' → ∀ ϖ : O, Irreducible ϖ → CompactSpace ↥D.T' ∧ (∀ n : ℕ, IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) ∧ ∀ U ∈ nhds (0 : ↥D.T'), ∃ n : ℕ, ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') ⊆ U := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D hO hemb hL hP hT2 ϖ hϖ
  have hK : IsCompact (D.T' : Set VT') := isCompact_dualLattice_of_pairing D hemb hL hP
  haveI : CompactSpace ↥D.T' := isCompact_iff_compactSpace.1 hK
  have hopen := isOpen_powSub D hemb hL hϖ
  refine ⟨inferInstance, hopen, fun U hU => ?_⟩
  obtain ⟨V, hVU, hV, h0V⟩ := mem_nhds_iff.1 hU
  obtain ⟨n, hn⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed
    (fun n : ℕ => ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T'))
    (fun n => AddSubgroup.isClosed_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n))
    (by
      rw [Set.disjoint_left]
      intro z hz hz'
      have : z = 0 := eq_zero_of_mem_powSub D hL hP hϖ fun n => Set.mem_iInter.1 hz' n
      exact hz (this ▸ h0V))
    (fun a b => ⟨max a b, fun x hx => powSub_anti ϖ (le_max_left a b) hx,
      fun x hx => powSub_anti ϖ (le_max_right a b) hx⟩)
  refine ⟨n, fun z hz => hVU ?_⟩
  by_contra hc
  exact Set.disjoint_left.1 hn hc hz

end GlobalTheory.LocDualTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasisStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), CompactSpace O → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → IsLatticeIn D.T → PerfectRight D.bT → T2Space VT' → ∀ ϖ : O, Irreducible ϖ → CompactSpace ↥D.T' ∧ (∀ n : ℕ, IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) ∧ ∀ U ∈ nhds (0 : ↥D.T'), ∃ n : ℕ, ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') ⊆ U := by
  first | exact @GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds | exact GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds | (intros; apply GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedLengthLatticeQuotientBaseChangeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedLengthLatticeQuotientBaseChangeEq
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

noncomputable section

namespace GlobalTheory.LatLenExt

open Formalism.L2.Col TensorProduct

section Int

variable {K : Type} [Field K] [NumberField K] {O : Type} [CommRing O] [IsDomain O]
  (e : K →+* FractionRing O) (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range)

def intMap : 𝓞 K →+* O :=
  (RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).symm.toRingHom.comp
    ((e.comp (algebraMap (𝓞 K) K)).codRestrict _ he)

theorem algebraMap_intMap (a : 𝓞 K) :
    algebraMap O (FractionRing O) (intMap e he a) = e (a : K) := by
  have h := (RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply
      ((e.comp (algebraMap (𝓞 K) K)).codRestrict _ he a)
  exact congrArg Subtype.val h

variable [IsDiscreteValuationRing O] (w : HeightOneSpectrum (𝓞 K))
  (hw : ∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) →
    (a ∈ w.asIdeal ↔ ¬ IsUnit z))

include hw in
theorem isUnit_intMap {a : 𝓞 K} (ha : a ∉ w.asIdeal) : IsUnit (intMap e he a) := by
  by_contra h
  exact ha ((hw a _ (algebraMap_intMap e he a)).2 h)

def owHom : Ow w →+* O :=
  IsLocalization.lift (M := w.asIdeal.primeCompl) (g := intMap e he)
    (fun s => isUnit_intMap e he w hw s.2)

theorem owHom_algebraMap (a : 𝓞 K) :
    owHom e he w hw (algebraMap (𝓞 K) (Ow w) a) = intMap e he a :=
  IsLocalization.lift_eq _ _

theorem algebraMap_owHom (x : Ow w) :
    algebraMap O (FractionRing O) (owHom e he w hw x) = e (algebraMap (Ow w) K x) := by
  have : (algebraMap O (FractionRing O)).comp (owHom e he w hw) = e.comp (algebraMap (Ow w) K) :=
    IsLocalization.ringHom_ext w.asIdeal.primeCompl (RingHom.ext fun a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        owHom_algebraMap, algebraMap_intMap, ← IsScalarTower.algebraMap_apply])
  exact RingHom.congr_fun this x

theorem owHom_injective : Function.Injective (owHom e he w hw) := by
  intro x y h
  have := congrArg (algebraMap O (FractionRing O)) h
  rw [algebraMap_owHom, algebraMap_owHom] at this
  exact algebraMap_ow_injective w (e.injective this)

theorem owHom_isLocalHom : IsLocalHom (owHom e he w hw) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl x
  rw [owHom, IsLocalization.lift_mk'] at hx
  have ha : IsUnit (intMap e he a) := (IsUnit.mul_iff.1 hx).1
  have : a ∉ w.asIdeal := fun h => ((hw a _ (algebraMap_intMap e he a)).1 h) ha
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (Ow w) w.asIdeal a s).2 this

end Int

theorem nonempty_quot_map_equiv {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (hf : Function.Injective f)
    (P Q : Submodule S M) (P' Q' : Submodule S N) (hP : P.map f = P') (hQ : Q.map f = Q') :
    Nonempty ((P ⧸ Q.submoduleOf P) ≃ₗ[S] (P' ⧸ Q'.comap P'.subtype)) := by
  subst hP hQ
  refine ⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf P) ?_⟩
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.submoduleOf, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := hy
    obtain rfl := hf hpq
    exact ⟨⟨p, hp⟩, hq, rfl⟩

end GlobalTheory.LatLenExt

namespace GlobalTheory.LatLenExt

open Formalism.L2.Col TensorProduct

theorem lenUnit_span_eq_lenUW : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  intro K _ _ O _ _ _ e V V' _ _ _ _ _ _ _ _ _ iV ι b hli he w l hl hlw hw A B _ _
  letI : Algebra (Ow w) O := (owHom e he w hw).toAlgebra
  letI : Algebra K (FractionRing O) := e.toAlgebra
  haveI : IsScalarTower (Ow w) K (FractionRing O) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Ow w) O (FractionRing O)]
    exact algebraMap_owHom e he w hw x
  haveI : FaithfulSMul (Ow w) O :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (owHom_injective e he w hw)
  haveI : IsLocalHom (algebraMap (Ow w) O) := owHom_isLocalHom e he w hw
  letI : Module K V' := Module.compHom V' e
  haveI : IsScalarTower K (FractionRing O) V' := ⟨fun c x y => by
    show (c • x) • y = e c • (x • y)
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let iVK : V →ₗ[K] V' :=
    { toFun := iV, map_add' := iV.map_add, map_smul' := fun c x => iV.map_smulₛₗ c x }
  let Φ : FractionRing O ⊗[K] V →ₗ[FractionRing O] V' := iVK.liftBaseChange (FractionRing O)
  have hΦ : ∀ v, Φ ((1 : FractionRing O) ⊗ₜ[K] v) = iV v := fun v => by
    simp [Φ, iVK]
  have hinj : Function.Injective Φ := by
    refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis (FractionRing O) b).span_eq ?_
    have hc : (Φ ∘ ⇑(Algebra.TensorProduct.basis (FractionRing O) b)) = fun a => iV (b a) :=
      funext fun i => by simp [hΦ]
    rw [hc]
    exact hli
  let Φs := Φ.restrictScalars O
  have key : ∀ A' : Submodule (𝓞 K) V,
      (GlobalTheory.spanBaseChange K O (FractionRing O) (atW w A')).map Φs =
        Submodule.span O (iV '' (A' : Set V)) := by
    intro A'
    rw [GlobalTheory.spanBaseChange, Submodule.map_span, Set.image_image]
    have h1 : (fun m => Φs ((1 : FractionRing O) ⊗ₜ[K] m)) = iV := funext fun m => hΦ m
    rw [h1]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hsx⟩ := mem_atW_iff.1 hx
      obtain ⟨u, hu⟩ := isUnit_intMap e he w hw hs
      have h2 : iV (s • x) = intMap e he s • iV x := by
        rw [← algebraMap_smul K s x, iV.map_smulₛₗ, ← algebraMap_smul (FractionRing O) (intMap e he s),
          algebraMap_intMap]
      have h3 : iV x = ((u⁻¹ : Oˣ) : O) • iV (s • x) := by
        rw [h2, ← hu, smul_smul, Units.inv_mul, one_smul]
      rw [SetLike.mem_coe, h3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsx, rfl⟩)
    · exact Submodule.span_mono (Set.image_mono fun x hx => Submodule.subset_span hx)
  obtain ⟨E2⟩ := nonempty_quot_map_equiv Φs hinj _ _ _ _ (key A) (key B)
  let E := GlobalTheory.spanBaseChangeSubquotEquiv K O (FractionRing O) (atW w A) (atW w B) ≪≫ₗ E2
  have hlen : Module.length O (↥(Submodule.span O (iV '' (A : Set V))) ⧸
      (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) =
      lenW w A B * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ) := by
    rw [← E.length_eq, GlobalTheory.length_baseChange_dvr]
    rfl
  have hden : Module.length O (O ⧸ Ideal.span {(l : O)}) =
      (eW w : ℕ∞) * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ) := by
    obtain rfl := eq_prW_of_mem w hl hlw
    rw [GlobalTheory.length_quotient_span_singleton_eq_addVal, ← map_natCast (algebraMap (Ow w) O),
      GlobalTheory.addVal_algebraMap, ← GlobalTheory.length_quotient_span_singleton_eq_addVal, length_ow_quot_prW]
  have hpos := GlobalTheory.ramificationIdx_maximalIdeal_pos (Ow w) O
  unfold lenUnit lenUW
  rw [hlen, hden]
  simp only [ENat.toNat_mul, ENat.toNat_coe]
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hpos.ne')

end GlobalTheory.LatLenExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedLengthLatticeQuotientBaseChangeEqStatement
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedLength_latticeQuotient_baseChange_eq : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  first | exact @GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | exact GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | (intros; apply GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW <;> assumption)
end
end

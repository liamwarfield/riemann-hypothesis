module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundSmallDepth
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsRingChange
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HLepolyTr

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoSumBoundOfMapsSplitting
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def BlockSplit : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (J : Type) [Fintype J] (n : ℕ) (z : O), z ≠ 0 →
    ∀ A : J → Matrix (Fin n) (Fin n) O, ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O) →
      ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O) (Q : Matrix (Fin n) (Fin (ν j)) O),
        P * A j * Q = z • (1 : Matrix (Fin (ν j)) (Fin (ν j)) O)

def RhoSumLatticeMaps : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (TT : Finset (Fin n')) (a : ℕ) (A B : TT → ℕ),
    (∀ s, A s + B s + 1 ≤ 8 * a) →
    ∃ (io : ∀ j : TT → ℕ, Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s)) →ₗ[R.Kf]
        VHH (m := m) R.Kf TT (ex A) (ex B))
      (pr : ∀ j : TT → ℕ, VHH (m := m) R.Kf TT (ex A) (ex B) →ₗ[R.Kf]
        Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s))),
      (∀ x, ∑ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)), io j (pr j x) = x) ∧
      ∀ (t c : ℕ) (e : Edge R.W R.Qq (m + 1)), IsEdge p n' 1 e →
        ∀ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)),
        (∀ x ∈ CCe p R.ι R.σ R.w TT (ex A) (ex B) t c e,
          ((p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊)) • pr j x ∈
            CCL R (flatW m (fun s => A s - j s) (fun s => B s - j s)) t c e) ∧
        (∀ Φ ∈ CCe' p R.ι R.σ R.w TT (ex A) (ex B) t c e,
          ((p : R.Kf) ^ (((2 * (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊) : ℕ) : ℤ) + AHH TT (ex A) (ex B) -
              Ar 1 (flatW m (fun s => A s - j s) (fun s => B s - j s)))) • (Φ ∘ₗ io j) ∈
            CCL' R (flatW m (fun s => A s - j s) (fun s => B s - j s)) t c e)

theorem vO_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {z : O} (hz : z ≠ 0) :
    vO p z = (((((IsDiscreteValuationRing.addVal O z).toNat : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  classical
  have hz' : algebraMap O (KK O) z ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hz
  simp only [vO, vK, ordW, if_neg hz']
  set ab := Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) with hab
  have hspec : algebraMap O (KK O) z * algebraMap O (KK O) (ab.2 : O) = algebraMap O (KK O) ab.1 :=
    Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  have h1 : z * (ab.2 : O) = ab.1 := IsFractionRing.injective O (KK O) (by rw [map_mul]; exact hspec)
  have hb0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.ne_zero ab.2.2
  have hv : IsDiscreteValuationRing.addVal O ab.1 =
      IsDiscreteValuationRing.addVal O z + IsDiscreteValuationRing.addVal O (ab.2 : O) := by
    rw [← h1, IsDiscreteValuationRing.addVal_mul]
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hbt : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [hv, ENat.toNat_add hzt hbt]
  simp only [WithTop.map_coe]
  congr 1
  push_cast
  ring

theorem vLEO_pow_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hp0 : (p : O) ≠ 0) (hpm : ¬ IsUnit (p : O)) {z : O} (hz : z ≠ 0) {D : ℝ} (k : ℕ) (h : vLEO p z D) :
    vLEO p ((p : O) ^ k * z) (D + k) := by
  obtain ⟨q, hq, hqD⟩ := h
  have hpz : (p : O) ^ k * z ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hz
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  set t := (IsDiscreteValuationRing.addVal O z).toNat with ht
  have hpa : IsDiscreteValuationRing.addVal O (p : O) = ((ramE p O : ℕ) : ℕ∞) := (ENat.coe_toNat hpt).symm
  have hza : IsDiscreteValuationRing.addVal O z = (t : ℕ∞) := (ENat.coe_toNat hzt).symm
  have hsum : IsDiscreteValuationRing.addVal O ((p : O) ^ k * z) = ((k * ramE p O + t : ℕ) : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hpa, hza]
    push_cast; ring
  have he : (ramE p O : ℚ) ≠ 0 := by
    have h0 : ramE p O ≠ 0 := by
      intro h0
      apply hpm
      rw [← IsDiscreteValuationRing.addVal_eq_zero_iff, hpa, h0]
      simp
    exact_mod_cast h0
  rw [vO_eq hz] at hq
  have hq' : ((t : ℤ) : ℚ) / (ramE p O : ℚ) = q := WithTop.coe_injective hq
  refine ⟨q + k, ?_, by push_cast; linarith⟩
  rw [vO_eq hpz, hsum, ENat.toNat_coe, ← hq']
  congr 1
  push_cast
  field_simp
  ring

theorem rho_sum_bound_of_maps_splitting (hM : RhoSumLatticeMaps) (hBS : BlockSplit) : RhoSumLowerBoundEdge := by
  classical
  intro p n' R m hm TT a A B hdeg t c D X e he hD hρ
  obtain ⟨io, pr, hsum, hST⟩ := hM p n' R m hm TT a A B hdeg
  obtain ⟨n, hXn, hfac⟩ := hρ
  set Jf := Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)) with hJf
  rcases hfac with h0 | ⟨x, y, hx, hy, z, Mat, hz, hvz, hG⟩
  · subst h0
    refine ⟨fun _ => 0, fun j _ => Or.inl rfl, ?_⟩
    simpa using hXn
  generalize hu : TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊ = u at hST
  have hp0 : (p : R.Kf) ≠ 0 := by
    rw [R.p_eq]; exact pow_ne_zero _ R.w_ne
  have hinj : Function.Injective (algebraMap R.O R.Kf) := by
    have := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  let lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ := fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)
  let xs : ∀ j : TT → ℕ, Fin n → Vsp R.Kf (lamj j) := fun j i => ((p : R.Kf) ^ u) • pr j (x i)
  let ys : ∀ j : TT → ℕ, Fin n → Module.Dual R.Kf (Vsp R.Kf (lamj j)) := fun j l =>
    ((p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j))) • (y l ∘ₗ io j)
  have hxs : ∀ j ∈ Jf, ∀ i, xs j i ∈ CCL R (lamj j) t c e := fun j hj i => (hST t c e he j hj).1 _ (hx i)
  have hys : ∀ j ∈ Jf, ∀ l, ys j l ∈ CCL' R (lamj j) t c e := fun j hj l => (hST t c e he j hj).2 _ (hy l)
  have hkey : ∀ j i l, be p 1 (lamj j) (xs j i) (ys j l) =
      (p : R.Kf) ^ (3 * u) * beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) := by
    intro j i l
    show (((p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j))) • (y l ∘ₗ io j))
      (((p : R.Kf) ^ Ar 1 (lamj j)) • (((p : R.Kf) ^ u) • pr j (x i))) =
      (p : R.Kf) ^ (3 * u) * (y l) (((p : R.Kf) ^ AHH TT (ex A) (ex B)) • io j (pr j (x i)))
    rw [LinearMap.smul_apply, map_smul, map_smul, map_smul, LinearMap.comp_apply]
    simp only [smul_eq_mul]
    have hc : (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) *
        ((p : R.Kf) ^ Ar 1 (lamj j) * (p : R.Kf) ^ u) = (p : R.Kf) ^ (3 * u) * (p : R.Kf) ^ AHH TT (ex A) (ex B) := by
      rw [← zpow_natCast (p : R.Kf) u, ← zpow_natCast (p : R.Kf) (3 * u), ← zpow_add₀ hp0, ← zpow_add₀ hp0,
        ← zpow_add₀ hp0]
      congr 1
      push_cast
      ring
    linear_combination (y l) (io j (pr j (x i))) * hc
  have hint : ∀ (j : Jf) (i l : Fin n), ∃ g : R.O, be p 1 (lamj j) (xs j i) (ys j l) = algebraMap R.O R.Kf g :=
    fun j i l => be_Re R (lamj j) e (hxs j j.2 i).1.2 (hys j j.2 l).1.2
  choose g hg using hint
  let Aj : Jf → Matrix (Fin n) (Fin n) R.O := fun j => (Matrix.of (g j)) * Mat
  have hz' : (p : R.O) ^ (3 * u) * z ≠ 0 := mul_ne_zero (pow_ne_zero _ R.p_ne) hz
  have hsumA : ∑ j, Aj j = ((p : R.O) ^ (3 * u) * z) • (1 : Matrix (Fin n) (Fin n) R.O) := by
    ext i k
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.sum_apply, map_sum]
    have e1 : ∀ j : Jf, algebraMap R.O R.Kf (Aj j i k) =
        ∑ l, (p : R.Kf) ^ (3 * u) * beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) *
          algebraMap R.O R.Kf (Mat l k) := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Aj, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, ← hg, hkey]
    simp only [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ l, ∑ j : Jf, (p : R.Kf) ^ (3 * u) * beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) *
          algebraMap R.O R.Kf (Mat l k) =
        (p : R.Kf) ^ (3 * u) * (beHH (m := m) p TT (ex A) (ex B) (x i) (y l) * algebraMap R.O R.Kf (Mat l k)) := by
      intro l
      have e3 : ∑ j : Jf, beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) =
          beHH (m := m) p TT (ex A) (ex B) (x i) (y l) := by
        rw [Finset.sum_coe_sort Jf (fun j => beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l))]
        unfold beHH
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, ← Finset.smul_sum, hsum]
      rw [← e3, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2]
    rw [← Finset.mul_sum, hG i k, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, map_mul, map_pow, map_natCast]
    · rw [mul_zero, mul_zero, map_zero]
  obtain ⟨ν, hν, hPQ⟩ := hBS R.O Jf n _ hz' Aj hsumA
  choose P Q hPQ' using hPQ
  refine ⟨fun j => if h : j ∈ Jf then ν ⟨j, h⟩ else 0, ?_, ?_⟩
  · intro j hj
    have hjm : j ∈ Jf := Fintype.mem_piFinset.2 fun s => Finset.mem_range.2 (Nat.lt_succ_of_le (hj s))
    have hnj : (if h : j ∈ Jf then ν ⟨j, h⟩ else 0) = ν ⟨j, hjm⟩ := dif_pos hjm
    beta_reduce
    rw [hnj]
    set jj : Jf := ⟨j, hjm⟩ with hjj
    right
    let x' : Fin (ν jj) → Vsp R.Kf (lamj j) := fun a' => ∑ i, algebraMap R.O R.Kf (P jj a' i) • xs j i
    let y' : Fin (ν jj) → Module.Dual R.Kf (Vsp R.Kf (lamj j)) := fun b' => ∑ l, (Mat * Q jj) l b' • ys j l
    have e4 : ∀ a' l', be p 1 (lamj j) (x' a') (y' l') = algebraMap R.O R.Kf ((P jj * Aj jj * Q jj) a' l') := by
      intro a' l'
      show be p 1 (lamj j) (∑ i, algebraMap R.O R.Kf (P jj a' i) • xs j i) (∑ l, (Mat * Q jj) l l' • ys j l) = _
      rw [be_sum_left, Matrix.mul_assoc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [be_sum, Matrix.mul_apply, map_sum, map_mul, Aj, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hgj : ∀ l, be p 1 (lamj j) (xs j i) (ys j l) = algebraMap R.O R.Kf (g jj i l) := fun l => hg jj i l
      simp only [hgj]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l1 _ => Finset.sum_congr rfl fun l2 _ => by ring
    refine ⟨x', y', ?_, ?_, (p : R.O) ^ (3 * u) * z, 1, hz', ?_, ?_⟩
    · intro a'
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (hxs j hjm i)
    · intro b'
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hys j hjm l)
    · have h1 := vLEO_pow_mul R.p_ne R.p_not_unit hz (3 * u) hvz
      refine vLEO_mono ?_ h1
      have : ((3 * u : ℕ) : ℝ) ≤ 4 * (TT.card : ℝ) * (⌈((m : ℝ) + 2) * lgA p a m⌉₊ : ℕ) := by
        rw [← hu]; push_cast
        have : (0 : ℝ) ≤ (TT.card : ℝ) * (⌈((m : ℝ) + 2) * lgA p a m⌉₊ : ℕ) := by positivity
        linarith
      linarith
    · intro a' b'
      show ∑ l', be p 1 (lamj j) (x' a') (y' l') * algebraMap R.O R.Kf ((1 : Matrix (Fin (ν jj)) (Fin (ν jj)) R.O) l' b') =
        if a' = b' then algebraMap R.O R.Kf ((p : R.O) ^ (3 * u) * z) else 0
      simp only [e4, hPQ']
      rw [Finset.sum_eq_single b' (fun l' _ hl' => by rw [Matrix.one_apply_ne hl', map_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)]
      rw [Matrix.one_apply_eq, map_one, mul_one, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
  · have h1 : (∑ j ∈ Jf, (((if h : j ∈ Jf then ν ⟨j, h⟩ else 0 : ℕ)) : ℝ)) = ((∑ j : Jf, ν j : ℕ) : ℝ) := by
      rw [← Finset.sum_coe_sort Jf (fun j => (((if h : j ∈ Jf then ν ⟨j, h⟩ else 0 : ℕ)) : ℝ))]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dif_pos j.2]
    rw [h1]
    exact le_trans hXn (by exact_mod_cast hν)

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorsLEOfIndex
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def othW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then 0 else lam0 s

def Pr {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
    [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [AddCommGroup V] [Module Kf V] [Module O V]
    (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) (M : Submodule O V₁) (N : Submodule O V₂) : Submodule O V :=
  Submodule.span O {x | ∃ F ∈ M, ∃ r ∈ N, x = μ F r}

def RestTensor : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∃ (μ : Vsp R.Kf (topW TT lam0) →ₗ[R.Kf] Vsp R.Kf (othW TT lam0) →ₗ[R.Kf] Vsp R.Kf lam0)
      (ν : Module.Dual R.Kf (Vsp R.Kf (topW TT lam0)) →ₗ[R.Kf] Module.Dual R.Kf (Vsp R.Kf (othW TT lam0)) →ₗ[R.Kf]
        Module.Dual R.Kf (Vsp R.Kf lam0)),
      (∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) ∧
      (∀ L : Submodule R.W (Fin (m + 1) → R.Qq), IsLattice R.W L →
        HL (O := R.O) R.ι R.σ lam0 L =
          Pr μ (HL (O := R.O) R.ι R.σ (topW TT lam0) L) (HL (O := R.O) R.ι R.σ (othW TT lam0) L)) ∧
      (∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
        HLe p R.ι R.σ R.w lam0 e =
          Pr μ (HLe p R.ι R.σ R.w (topW TT lam0) e) (HLe p R.ι R.σ R.w (othW TT lam0) e)) ∧
      dimV R.Kf lam0 = dimV R.Kf (topW TT lam0) * dimV R.Kf (othW TT lam0)

def RestOrdBound : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ), IsDominant lamO →
    (∀ s i, |lamO s i| ≤ c) → ∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
      Re p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ))) (HL R.ι R.σ lamO e.src) ∧
      Re' p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ)))
          (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (HL (O := R.O) R.ι R.σ lamO e.tgt))

section Formal

variable {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
  [IsScalarTower O Kf V₁] [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [IsScalarTower O Kf V₂] [AddCommGroup V]
  [Module Kf V] [Module O V] [IsScalarTower O Kf V]

theorem scale_mono (c : Kf) {M M' : Submodule O V} (h : M ≤ M') : scale c M ≤ scale c M' := Submodule.map_mono h

theorem scale_scale_mem {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale a (scale b M)) :
    x ∈ scale (a * b) M := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  refine Submodule.mem_map.mpr ⟨z, hz, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mem_scale_scale {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale (a * b) M) :
    x ∈ scale a (scale b M) := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp h
  refine Submodule.mem_map.mpr ⟨b • z, Submodule.mem_map.mpr ⟨z, hz, by simp⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂} {F : V₁} {r : V₂}
    (hF : F ∈ scale a M) (hr : r ∈ scale b N) : μ F r ∈ scale (a * b) (Pr μ M N) := by
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨r0, hr0, rfl⟩ := Submodule.mem_map.mp hr
  refine Submodule.mem_map.mpr ⟨μ F0 r0, Submodule.subset_span ⟨F0, hF0, r0, hr0, rfl⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem nu_dual (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M)
    (hρ : ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf N) : ν G ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, r, hr, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hG F hF
    obtain ⟨b, hb⟩ := hρ r hr
    exact ⟨a * b, by rw [hν, map_mul, ha, hb]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, ← algebraMap_smul Kf c x, map_smul, smul_eq_mul]⟩

theorem nu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ scale a (Formalism.GradedWeylDivisibility.dualLat O Kf M))
    (hρ : ρ ∈ scale b (Formalism.GradedWeylDivisibility.dualLat O Kf N)) :
    ν G ρ ∈ scale (a * b) (Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N)) := by
  obtain ⟨G0, hG0, rfl⟩ := Submodule.mem_map.mp hG
  obtain ⟨ρ0, hρ0, rfl⟩ := Submodule.mem_map.mp hρ
  refine Submodule.mem_map.mpr ⟨ν G0 ρ0, nu_dual μ ν hν hG0 hρ0, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

end Formal

theorem FactorsLE_of_index {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] {p : ℕ} {be : V → V' → Kf}
    {A : Submodule O V} {A' : Submodule O V'} {D : ℝ} {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ)
    (hcard : Fintype.card I = n) (x : I → V) (y : I → V') (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (z : O)
    (M : Matrix I I O) (hz : z ≠ 0) (hv : vLEO p z D)
    (hM : ∀ i j, ∑ l, be (x i) (y l) * algebraMap O Kf (M l j) = if i = j then algebraMap O Kf z else 0) :
    FactorsLE p be A A' n D := by
  unfold FactorsLE
  right
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => x (e i), fun i => y (e i), fun i => hx _, fun i => hy _, z, M.submatrix e e, hz, hv, fun i j => ?_⟩
  simp only [Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun l => be (x (e i)) (y l) * algebraMap O Kf (M l (e j))), hM]
  simp [e.injective.eq_iff]

theorem othW_dom {n' m : ℕ} {TT : Finset (Fin n')} {lam0 : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant lam0) :
    IsDominant (othW TT lam0) := by
  show ∀ s, Antitone (othW TT lam0 s)
  intro s
  simp only [othW]
  split_ifs
  · exact antitone_const
  · exact h s

theorem Ar_add {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Ar 1 lam0 = Ar 1 (topW TT lam0) + Ar 1 (othW TT lam0) := by
  unfold Ar
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lamAt topW othW
  by_cases hs : s ∈ TT <;> by_cases he : Even (s : ℕ) <;> simp [hs, he]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeIndep
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

def mapE {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq) (e : Edge W Qq k) :
    Edge W Qq k := ⟨e.src.map (nt_phi W g), e.tgt.map (nt_phi W g)⟩

theorem mapE_inv {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq)
    (e : Edge W Qq k) : mapE g (mapE g⁻¹ e) = e := by
  have hid : (nt_phi W g).comp (nt_phi W g⁻¹) = LinearMap.id := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, LinearMap.id_apply]
  cases e with
  | mk src tgt =>
    simp only [mapE, Edge.mk.injEq]
    constructor <;> rw [← Submodule.map_comp, hid, Submodule.map_id]

def RestFunct : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ g : GL (Fin (m + 1)) R.Qq, ∃ T : Vsp R.Kf lam0 ≃ₗ[R.Kf] Vsp R.Kf lam0,
      (∀ L : Submodule R.W (Fin (m + 1) → R.Qq), IsLattice R.W L →
        ∀ x, x ∈ HL (O := R.O) R.ι R.σ lam0 L ↔ T x ∈ HL (O := R.O) R.ι R.σ lam0 (L.map (nt_phi R.W g))) ∧
      (∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
        ∀ x, x ∈ HLe p R.ι R.σ R.w lam0 e ↔ T x ∈ HLe p R.ι R.σ R.w lam0 (mapE g e))

section Formal

variable {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V] [Module O V]
  [IsScalarTower O Kf V]

theorem scale_alt (T : V ≃ₗ[Kf] V) (c : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {x : V}
    (hx : x ∈ scale c M) : T x ∈ scale c M' := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨T y, (h y).1 hy, by simp⟩

theorem comp_symm_mem_dualLat_of_mem_iff (T : V ≃ₗ[Kf] V) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {φ : Module.Dual Kf V}
    (hφ : φ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M) : φ.comp T.symm.toLinearMap ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M' := by
  intro v hv
  exact hφ (T.symm v) ((h _).2 (by rwa [LinearEquiv.apply_symm_apply]))

theorem comp_symm_mem_scale_dualLat_of_mem_iff (T : V ≃ₗ[Kf] V) (c : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M')
    {φ : Module.Dual Kf V} (hφ : φ ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O Kf M)) :
    φ.comp T.symm.toLinearMap ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O Kf M') := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ.comp T.symm.toLinearMap, comp_symm_mem_dualLat_of_mem_iff T h hψ, by ext v; simp⟩

theorem apply_mem_scale_scale_of_mem_iff (T : V ≃ₗ[Kf] V) (c d : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {x : V}
    (hx : x ∈ scale c (scale d M)) : T x ∈ scale c (scale d M') := by
  have hs : ∀ y, y ∈ M' ↔ T.symm y ∈ M := fun y => by rw [h (T.symm y), LinearEquiv.apply_symm_apply]
  have hiff : ∀ y, y ∈ scale d M ↔ T y ∈ scale d M' := fun y =>
    ⟨fun hy => scale_alt T d h hy, fun hy => by
      have := scale_alt T.symm d hs hy
      rwa [LinearEquiv.symm_apply_apply] at this⟩
  exact scale_alt T c hiff hx

theorem scaled_dual_lattice_transport (T : V ≃ₗ[Kf] V) (c d : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M')
    {φ : Module.Dual Kf V} (hφ : φ ∈ scale c (scale d (Formalism.GradedWeylDivisibility.dualLat O Kf M))) :
    φ.comp T.symm.toLinearMap ∈ scale c (scale d (Formalism.GradedWeylDivisibility.dualLat O Kf M')) := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ.comp T.symm.toLinearMap, comp_symm_mem_scale_dualLat_of_mem_iff T d h hψ, by ext v; simp⟩

end Formal

theorem restEdge_of (hFun : RestFunct) : RestEdge := by
  classical
  intro p n' R m lam0 hDom t c n D e e' he he' hfac
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  obtain ⟨g', hg', hsrc', htgt'⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e' he'
  have hug : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 hg
  have hug' : IsUnit g' := (Matrix.isUnit_iff_isUnit_det _).2 hg'
  let γ : GL (Fin (m + 1)) R.Qq := hug'.unit * hug.unit⁻¹
  have hγg : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq) * g = g' := by
    have : γ * hug.unit = hug'.unit := by simp [γ]
    have h2 := congrArg Units.val this
    simpa using h2
  have hee : e' = mapE γ e := by
    cases e with
    | mk s tg =>
      cases e' with
      | mk s' tg' =>
        simp only at hsrc htgt hsrc' htgt'
        simp only [mapE]
        rw [hsrc, htgt, hsrc', htgt', map_colSpan, map_colSpan, ← Matrix.mul_assoc, hγg]
  obtain ⟨T, hT1, hT2⟩ := hFun p n' R m lam0 hDom γ
  have hedge : ∀ e'' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e'' → IsEdge p n' 1 (mapE γ⁻¹ e'') :=
    fun e'' h => nt_edge_map p n' 1 γ⁻¹ _ _ h
  have hsrcC : ∀ x, x ∈ CCL R lam0 t c e → T x ∈ CCL R lam0 t c (mapE γ e) := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact scale_alt T _ (hT1 e.src he.1) hx.1.1
    · exact scale_alt T _ (hT2 e he) hx.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').src = e.src := by
        show e''.src.map (nt_phi R.W γ⁻¹) = e.src
        rw [h2]
        exact nt_map_inv γ e.src
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hx
      have h7 := apply_mem_scale_scale_of_mem_iff T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  have htgtC : ∀ y, y ∈ CCL' R lam0 t c e → y.comp T.symm.toLinearMap ∈ CCL' R lam0 t c (mapE γ e) := by
    intro y hy
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT1 e.tgt he.2.1) hy.1.1
    · exact comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT2 e he) hy.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').tgt = e.tgt := by
        show e''.tgt.map (nt_phi R.W γ⁻¹) = e.tgt
        rw [h2]
        exact nt_map_inv γ e.tgt
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL'_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hy
      have h7 := scaled_dual_lattice_transport T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  rw [hee]
  rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact Or.inl h0
  · refine Or.inr ⟨fun i => T (x i), fun l => (y l).comp T.symm.toLinearMap, fun i => hsrcC _ (hx i),
      fun l => htgtC _ (hy l), z, M, hz, hv, fun i j => ?_⟩
    rw [← hM i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    unfold be
    rw [LinearMap.comp_apply, ← map_smul]
    simp

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LpRingIndepOf
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def RestOIso : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (φW : R₁.W ≃+* R₂.W),
    ∃ φO : R₁.O ≃+* R₂.O, (∀ x, φO (R₁.jO x) = R₂.jO (φW x)) ∧ φO R₁.w = R₂.w

theorem restRSIso_of (hW : WittIdent) (hO : RestOIso) : RestRSIso := by
  intro p n' R₁ R₂
  have s₁ := R₁.std.1
  have s₂ := R₂.std.1
  haveI : Fact (Nat.Prime p) := ⟨s₁.prime⟩
  haveI := s₁.frac_alt
  haveI := s₂.frac_alt
  haveI := s₁.frac_O
  haveI := s₂.frac_O
  obtain ⟨φ₁, h₁⟩ := hW p n' R₁.W R₁.Qq R₁.O R₁.Kf R₁.ι R₁.σ R₁.jO R₁.w s₁
  obtain ⟨φ₂, h₂⟩ := hW p n' R₂.W R₂.Qq R₂.O R₂.Kf R₂.ι R₂.σ R₂.jO R₂.w s₂
  obtain ⟨φO, hj, hw⟩ := hO p n' R₁ R₂ (φ₁.symm.trans φ₂)
  let φQ : R₁.Qq ≃+* R₂.Qq := IsFractionRing.ringEquivOfRingEquiv (φ₁.symm.trans φ₂)
  let φK : R₁.Kf ≃+* R₂.Kf := IsFractionRing.ringEquivOfRingEquiv φO
  have hWQ : ∀ x, φQ (algebraMap R₁.W R₁.Qq x) = algebraMap R₂.W R₂.Qq ((φ₁.symm.trans φ₂) x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hOK : ∀ x, φK (algebraMap R₁.O R₁.Kf x) = algebraMap R₂.O R₂.Kf (φO x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hσ : ∀ x, φQ (R₁.σ x) = R₂.σ (φQ x) := by
    have key : (φQ : R₁.Qq →+* R₂.Qq).comp (R₁.σ : R₁.Qq →+* R₁.Qq) =
        (R₂.σ : R₂.Qq →+* R₂.Qq).comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      obtain ⟨v, rfl⟩ := φ₁.surjective u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [h₁ v, hWQ, hWQ]
      simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
      rw [h₂ v]
    exact fun x => RingHom.congr_fun key x
  have hι : ∀ x, φK (R₁.ι x) = R₂.ι (φQ x) := by
    have key : (φK : R₁.Kf →+* R₂.Kf).comp R₁.ι = R₂.ι.comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [s₁.ι_comp, hOK, hj, hWQ, s₂.ι_comp]
    exact fun x => RingHom.congr_fun key x
  exact ⟨⟨φ₁.symm.trans φ₂, φQ, φO, φK, hWQ, hOK, hι, hσ, hj, hw⟩⟩

theorem lpRingIndep_of'' (hW : WittIdent) (hO : RestOIso) : LPRingIndep := lpRingIndep_of' (restRSIso_of hW hO)

end Formalism.MainNotions.flipOneThree.Pf

end
end

module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.ColumnAlgebra.PiColElAdd
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockHomomorphism
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.InvSmulEqOfSmulEq
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.Stab

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.BesselEstimates.ValLtOneOfNabs
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScaledNontrivialCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScaledNontrivialCharacter
open ValuativeRel MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CharConductor

theorem exists_conductor_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k),
    valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧
      ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  intro k _ _ _ _ ψ hψ a c ha hc
  classical
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hc0 : valuation k c ≠ 0 := by
    intro h0
    rw [map_eq_zero] at h0
    exact hc (by rw [h0, AddChar.map_zero_eq_one])
  obtain ⟨m, hm⟩ := exists_pow_lt₀ ha (Units.mk0 (γ / valuation k c) (div_ne_zero hγ hc0))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc0)] at hm
  have hex : ∃ r : ℕ, ∀ μ ∈ 𝒪[k], ψ (μ * a ^ r * c) = 1 := by
    refine ⟨m, fun μ hμ => hball _ ?_⟩
    have hμ1 : valuation k μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
    rw [map_mul, map_mul, map_pow]
    calc valuation k μ * valuation k a ^ m * valuation k c
        ≤ 1 * valuation k a ^ m * valuation k c := by gcongr
      _ = valuation k a ^ m * valuation k c := by rw [one_mul]
      _ < γ := hm
  have hfind := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hfind
    exact hc (by simpa using hfind 1 (one_mem _))
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin := Nat.find_min hex (m := r) (by omega)
  push Not at hmin
  obtain ⟨μ, hμ, hne⟩ := hmin
  refine ⟨μ * a ^ r * c, hne, ⟨r, μ, hμ, rfl⟩, fun s hs => ?_⟩
  have h := hfind (s * μ) (mul_mem hs hμ)
  rw [hr] at h
  have e : s * a * (μ * a ^ r * c) = s * μ * a ^ (r + 1) * c := by ring
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CharConductor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScaledNontrivialCharacterStatement
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaled_nontrivial_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k), valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧ ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | exact GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | (intros; apply GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step <;> assumption)
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel
open scoped Pointwise

namespace PositivityTheory.RgUd.Form.LeviSmoothness.besselOf

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bessel_finite {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : IsPsd B)
    (u : ℕ → V) (v : V) (hself : ∀ i, B (u i) v = B (u i) (u i)) (horth : ∀ i j, i ≠ j → B (u i) (u j) = 0)
    (I : ℕ) : ∑ i ∈ Finset.range I, (B (u i) (u i)).re ≤ (B v v).re := by
  set S := ∑ i ∈ Finset.range I, u i with hS
  have h0 := hB.2 (v - S)
  have e1 : B (v - S) (v - S) = B v v - B v S - B S v + B S S := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  have e2 : B S v = ∑ i ∈ Finset.range I, B (u i) (u i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hself i
  have e3 : B v S = ∑ i ∈ Finset.range I, starRingEnd ℂ (B (u i) (u i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB.1 (u i) v, hself i]
  have e4 : B S S = ∑ i ∈ Finset.range I, B (u i) (u i) := by
    rw [hS]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => horth j i hj) (fun h => absurd hi h)]
  rw [e1, e2, e3, e4] at h0
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.conj_re] at h0
  linarith

theorem isLat_sup {m : ℕ} {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') : IsLat (A ⊔ A') := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩
  have hc : IsCompact ((A : Set (Fin (m + 1) → k)) + (A' : Set (Fin (m + 1) → k))) := hA.1.add hA'.1
  refine hc.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hA.2)) ?_
  intro x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hx
  exact Set.add_mem_add hy hw

theorem val_lt_one_of_nabs {z : kˣ} (hz : nabs k z < 1) : valuation k (z : k) < 1 := by
  by_contra hc
  push Not at hc
  have h1 : valuation k ((1 : kˣ) : k) ≤ valuation k (z : k) := by simpa using hc
  have := (nabs_le_iff (1 : kˣ) z).2 h1
  rw [nabs_one] at this
  linarith

def Mz (ψ : AddChar k Circle) (m : ℕ) (b : k) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ t : Fin (m + 1) → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1}
  zero_mem' := by intro t _; simp
  add_mem' := by
    intro x y hx hy t ht
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, hx t ht, hy t ht, one_mul]
  neg_mem' := by
    intro x hx t ht
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_neg, mul_neg, AddChar.map_neg_eq_inv, hx t ht, inv_one]

theorem isLat_Mz {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (m : ℕ) {b : k} (hb : b ≠ 0) :
    IsLat (Mz ψ m b) :=
  GlobalTheory.T.character_annihilator_integer_lattice k ψ hψ hψ1 (m + 1) b hb

theorem smul_mem_Mz {ψ : AddChar k Circle} {m : ℕ} {b c : k} (hc : c ∈ 𝒪[k]) {x : Fin (m + 1) → k}
    (hx : x ∈ Mz ψ m b) : c • x ∈ Mz ψ m b := by
  intro t ht
  rw [dotProduct_smul, smul_eq_mul, ← smul_eq_mul c, ← smul_dotProduct]
  exact hx (c • t) fun j => by simpa using mul_mem hc (ht j)

theorem exists_sep {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (m : ℕ) {a : k}
    (ha : valuation k a < 1) :
    ∃ d : k, ψ d ≠ 1 ∧ ∀ c : k, c ∈ 𝒪[k] → Pi.single (Fin.last m) (c * d) ∈ Mz ψ m a := by
  obtain ⟨c₀, hc₀⟩ : ∃ c, ψ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hψ1 (DFunLike.ext _ _ (fun c => by rw [hcon c, AddChar.one_apply]))
  obtain ⟨d, hd, -, hd2⟩ := GlobalTheory.T.exists_scaled_nontrivial_character k ψ hψ a c₀ ha hc₀
  refine ⟨d, hd, fun c hc t ht => ?_⟩
  rw [dotProduct_single]
  have := hd2 (t (Fin.last m) * c) (mul_mem (ht _) hc)
  rw [← this]
  congr 1
  ring

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem B_smul_smul {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (α β : ℂ) (x y : W) :
    B (α • x) (β • y) = α * (starRingEnd ℂ β * B x y) := by
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]

theorem nabs_pow (x : kˣ) (n : ℕ) : nabs k (x ^ n) = nabs k x ^ n := by
  induction n with
  | zero => simp [nabs_one]
  | succ n ih => rw [pow_succ, GlobalTheory.SmGL.nabs_mul' k, ih, pow_succ]

theorem B_colEl (hB : Lv ψ h π s B) (y : Fin (m + 1) → k) (a b : V) :
    B (π (colEl k m N h y) a) (π (colEl k m N h y) b) = B a b := by
  have hmem : unip k (m + 1) (Multiplicative.ofAdd y) ∈ Mir k (m + 1) := MirU_le_Mir k (m + 1) ⟨_, rfl⟩
  have e := hB.mir _ hmem a b
  rw [ColumnElementGluing.det_unip, nabs_one, Real.one_rpow, Complex.ofReal_one, one_mul] at e
  exact e

theorem B_scal (hB : Lv ψ h π s B) (z : kˣ) (i : ℕ) (a b : V) :
    B (π (scalAt k (m + 1) N (by omega) (z ^ i)) a) (π (scalAt k (m + 1) N (by omega) (z ^ i)) b) =
      ((nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B a b := by
  set g : GL (Fin (m + 1)) k := Units.map (algebraMap k (Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toMonoidHom (z ^ i)
    with hg
  have hmem : glEmb k (m + 1) g ∈ Mir k (m + 1) := glEmb_mem_Mir k (m + 1) g
  have e := hB.mir _ hmem a b
  rw [ColumnElementGluing.blkAt_glEmb h g, ColumnElementGluing.det_glEmb] at e
  have hdet : Matrix.GeneralLinearGroup.det g = (z ^ i) ^ (m + 1) := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Units.coe_map]
    change (algebraMap k (Matrix (Fin (m + 1)) (Fin (m + 1)) k) ((z ^ i : kˣ) : k)).det = _
    rw [Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    push_cast
    rfl
  rw [hdet, nabs_pow, nabs_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (nabs_pos' k z).le] at e
  show B (π (blkAt k (m + 1) N (by omega) g) a) (π (blkAt k (m + 1) N (by omega) g) b) = _
  rw [e]
  congr 3
  push_cast
  ring

theorem dens_bessel_of (hB : Lv ψ h π s B)
    (hstab : ∀ (K : Subgroup (GL (Fin (m + 1)) k)), IsOpen (K : Set (GL (Fin (m + 1)) k)) →
      ∀ {A₀ : AddSubgroup (Fin (m + 1) → k)}, IsLat A₀ →
      ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v → FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
        ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
          ((A₀.relIndex A₁ : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A₁ v) w) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀)
    {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hD : IsDens ψ h π A₀ B B') (z : kˣ) (hz : nabs k z < 1) (v : V) :
    Summable fun i : ℕ => nabs k z ^ (-((i : ℝ) * (m + 1) * s)) *
      (B' (π (scalAt k (m + 1) N (by omega) (z ^ i)) v) (π (scalAt k (m + 1) N (by omega) (z ^ i)) v)).re := by
  have h1 : m + 1 ≤ N := by omega
  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} (ha : π a v = v) (hb : π b v = v) =>
        show π (a * b) v = v by rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := show π 1 v = v by rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} (ha : π a v = v) => show π a⁻¹ v = v by
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let K : Subgroup (GL (Fin (m + 1)) k) := S.comap (blkAt k (m + 1) N h1)
  have hK : IsOpen (K : Set (GL (Fin (m + 1)) k)) := (hB.smooth v).preimage (ColumnElementGluing.continuous_blkAt (m + 1) N h1)
  have hvK : FixK h1 π K v := fun g hg => hg
  obtain ⟨A₁, hA₁, -, hst⟩ := hstab K hK hA₀
  have hzv : valuation k (z : k) < 1 := val_lt_one_of_nabs hz
  obtain ⟨d, hd, hdM⟩ := exists_sep hB.cont hB.ne m hzv
  have hM : IsLat (Mz ψ m (z : k)) := isLat_Mz hB.cont hB.ne m z.ne_zero
  let A : AddSubgroup (Fin (m + 1) → k) := A₁ ⊔ Mz ψ m (z : k)
  have hA : IsLat A := isLat_sup hA₁ hM
  have h1A : A₁ ≤ A := le_sup_left
  have hMA : Mz ψ m (z : k) ≤ A := le_sup_right
  have hzO : (z : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hzv.le
  let σ : ℕ → GL (Fin N) k := fun i => scalAt k (m + 1) N h1 (z ^ i)
  have hfix : ∀ i, FixK h1 π K (π (σ i) v) := by
    intro i g hg
    show π (blkAt k (m + 1) N h1 g) (π (scalAt k (m + 1) N h1 (z ^ i)) v) = π (scalAt k (m + 1) N h1 (z ^ i)) v
    rw [← Module.End.mul_apply, ← map_mul, ← ColumnElementGluing.scalAt_comm_blkAt h1 (z ^ i) g, map_mul, Module.End.mul_apply,
      hvK g hg]
  let a : ℕ → V := fun i => avg ψ h π (xi0 k m) A (π (σ i) v)
  have hval : ∀ i, B' (π (σ i) v) (π (σ i) v) = ((A₀.relIndex A : ℕ) : ℂ) * B (a i) (π (σ i) v) := by
    intro i
    obtain ⟨A₂, hA₂, -, hv2⟩ := hD (π (σ i) v) (π (σ i) v)
    have hA3 : IsLat (A ⊔ A₂) := isLat_sup hA hA₂
    rw [hv2 (A ⊔ A₂) hA3 le_sup_right, hst _ _ (hfix i) (hfix i) (A ⊔ A₂) hA3 (h1A.trans le_sup_left),
      ← hst _ _ (hfix i) (hfix i) A hA h1A]
  let u : ℕ → V := fun i => π (σ i)⁻¹ (a i)
  have hσu : ∀ i, π (σ i) (u i) = a i := fun i => by
    show π (σ i) (π (σ i)⁻¹ (a i)) = a i
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsc : ∀ i (x y : V), B (π (σ i) x) (π (σ i) y) = ((nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B x y :=
    fun i x y => B_scal hB z i x y
  have hcpos : ∀ i : ℕ, 0 < nabs k z ^ ((i : ℝ) * (m + 1) * s) := fun i => Real.rpow_pos_of_pos (nabs_pos' k z) _
  have hself : ∀ i, B (u i) v = B (u i) (u i) := by
    intro i
    have e : B (a i) (π (σ i) v) = B (a i) (avg ψ h π (xi0 k m) A (π (σ i) v)) :=
      alg.avg_selfadj hB (xi0 k m) hA (π (σ i) v) (π (σ i) v)
    change B (a i) (π (σ i) v) = B (a i) (a i) at e
    rw [← hσu i, hsc, hsc] at e
    exact mul_left_cancel₀ (by exact_mod_cast (hcpos i).ne') e
  have heig : ∀ i (y : Fin (m + 1) → k), ((z ^ i : kˣ) : k) • y ∈ A →
      π (colEl k m N h y) (u i) = ((ψ (xi0 k m ⬝ᵥ ((z ^ i : kˣ) : k) • y) : Circle) : ℂ) • u i := by
    intro i y hy
    show π (colEl k m N h y) (π (σ i)⁻¹ (a i)) = _ • π (σ i)⁻¹ (a i)
    have hc := ColumnElementGluing.scalAt_conj_colEl h (z ^ i) y
    have hc' : colEl k m N h y * (σ i)⁻¹ = (σ i)⁻¹ * colEl k m N h (((z ^ i : kˣ) : k) • y) := by
      show colEl k m N h y * (scalAt k (m + 1) N h1 (z ^ i))⁻¹ =
        (scalAt k (m + 1) N h1 (z ^ i))⁻¹ * colEl k m N h (((z ^ i : kˣ) : k) • y)
      rw [← hc]; group
    rw [← Module.End.mul_apply, ← map_mul, hc', map_mul, Module.End.mul_apply]
    have e := ColumnElementGluing.avg_eigen ψ h π hB.cont hB.smooth (xi0 k m) A hA (π (σ i) v) _ hy
    change π (colEl k m N h (((z ^ i : kˣ) : k) • y)) (a i) = _ at e
    rw [e, map_smul]
  have horth0 : ∀ i j, i < j → B (u i) (u j) = 0 := by
    intro i j hij
    obtain ⟨l, rfl⟩ : ∃ l, j = i + (l + 1) := ⟨j - i - 1, by omega⟩
    have hzl : valuation k ((z : k) ^ (l + 1)) < 1 := by
      rw [map_pow]; exact pow_lt_one₀ zero_le hzv (by omega)
    have h1z : valuation k (1 - (z : k) ^ (l + 1)) = 1 := Valuation.map_one_sub_of_lt _ hzl
    have h1z0 : (1 - (z : k) ^ (l + 1)) ≠ 0 := by
      intro e; rw [e, map_zero] at h1z; exact zero_ne_one h1z
    let c : k := (1 - (z : k) ^ (l + 1))⁻¹
    have hcO : c ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by simp only [c, map_inv₀, h1z, inv_one]; exact le_rfl)
    let w : Fin (m + 1) → k := Pi.single (Fin.last m) (c * d)
    have hwM : w ∈ Mz ψ m (z : k) := hdM c hcO
    let y : Fin (m + 1) → k := (((z ^ i)⁻¹ : kˣ) : k) • w
    have hy1 : ((z ^ i : kˣ) : k) • y = w := by
      simp only [y, smul_smul, Units.mul_inv, one_smul]
    have hy2 : ((z ^ (i + (l + 1)) : kˣ) : k) • y = ((z : k) ^ (l + 1)) • w := by
      simp only [y, smul_smul]
      congr 1
      push_cast
      rw [pow_add, mul_assoc, mul_comm ((z : k) ^ (l + 1)), ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ z.ne_zero),
        one_mul]
    have e1 := heig i y (hy1 ▸ hMA hwM)
    have e2 := heig (i + (l + 1)) y (hy2 ▸ hMA (smul_mem_Mz (pow_mem hzO _) hwM))
    rw [hy1] at e1
    rw [hy2] at e2
    have hinv := B_colEl hB y (u i) (u (i + (l + 1)))
    rw [e1, e2, B_smul_smul] at hinv
    have hxw : xi0 k m ⬝ᵥ w = c * d := by simp [w, xi0]
    have hxw2 : xi0 k m ⬝ᵥ ((z : k) ^ (l + 1)) • w = (z : k) ^ (l + 1) * (c * d) := by
      rw [dotProduct_smul, hxw, smul_eq_mul]
    rw [hxw, hxw2] at hinv
    have hsplit : c * d = (z : k) ^ (l + 1) * (c * d) + d := by
      have : c * (1 - (z : k) ^ (l + 1)) = 1 := inv_mul_cancel₀ h1z0
      linear_combination d * this
    set β : Circle := ψ ((z : k) ^ (l + 1) * (c * d))
    have hα : ((ψ (c * d) : Circle) : ℂ) = (β : ℂ) * ((ψ d : Circle) : ℂ) := by
      rw [hsplit, AddChar.map_add_eq_mul]; push_cast; rfl
    rw [hα] at hinv
    have hb1 : starRingEnd ℂ (β : ℂ) * (β : ℂ) = 1 := ColumnElementGluing.conj_circle_mul_self β
    have hd1 : ((ψ d : Circle) : ℂ) ≠ 1 := fun e => hd (Subtype.ext (by simpa using e))
    have : ((ψ d : Circle) : ℂ) * B (u i) (u (i + (l + 1))) = B (u i) (u (i + (l + 1))) := by
      linear_combination hinv - (((ψ d : Circle) : ℂ) * B (u i) (u (i + (l + 1)))) * hb1
    have : (((ψ d : Circle) : ℂ) - 1) * B (u i) (u (i + (l + 1))) = 0 := by linear_combination this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hd1)
  have horth : ∀ i j, i ≠ j → B (u i) (u j) = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hl | hl
    · exact horth0 i j hl
    · rw [hB.psd.1 (u j) (u i), horth0 j i hl, map_zero]
  have hterm : ∀ i : ℕ, nabs k z ^ (-((i : ℝ) * (m + 1) * s)) * (B' (π (σ i) v) (π (σ i) v)).re =
      (A₀.relIndex A : ℝ) * (B (u i) (u i)).re := by
    intro i
    rw [hval i, ← hσu i, hsc i, hself i]
    rw [show ((A₀.relIndex A : ℕ) : ℂ) * (((nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B (u i) (u i)) =
      (((A₀.relIndex A : ℝ) * nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B (u i) (u i) by push_cast; ring]
    rw [Complex.re_ofReal_mul, Real.rpow_neg (nabs_pos' k z).le]
    have := (hcpos i).ne'
    field_simp
  refine summable_of_sum_range_le (c := (A₀.relIndex A : ℝ) * (B v v).re) (fun i => ?_) (fun I => ?_)
  · exact le_of_le_of_eq (mul_nonneg (Nat.cast_nonneg _) (hB.psd.2 _)) (hterm i).symm
  · calc ∑ i ∈ Finset.range I, nabs k z ^ (-((i : ℝ) * (m + 1) * s)) *
          (B' (π (σ i) v) (π (σ i) v)).re
        = ∑ i ∈ Finset.range I, (A₀.relIndex A : ℝ) * (B (u i) (u i)).re := Finset.sum_congr rfl fun i _ => hterm i
      _ = (A₀.relIndex A : ℝ) * ∑ i ∈ Finset.range I, (B (u i) (u i)).re := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (bessel_finite B hB.psd u v hself horth I) (Nat.cast_nonneg _)

end

end PositivityTheory.RgUd.Form.LeviSmoothness.besselOf
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.TwistedKernels.TwKerColElStable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPsdIsotropicRadical
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPsdIsotropicRadical
namespace GlobalTheory.CompanionTheory.HermitianForm

theorem re_pairing_eq_zero_of_psd {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v, 0 ≤ (B v v).re) (v : V) (hv : B v v = 0) (u : V) : (B v u).re = 0 := by
  have hb : 0 ≤ (B u u).re := hpos u
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (B v u).re + t ^ 2 * (B u u).re := by
    intro t
    have h := hpos (v + (t : ℂ) • u)
    have e : B (v + (t : ℂ) • u) (v + (t : ℂ) • u)
        = B v v + (t : ℂ) * B v u + (t : ℂ) * B u v + (t : ℂ) * (t : ℂ) * B u u := by
      simp only [map_add (f := _), LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Complex.conj_ofReal]
      ring
    rw [e, hv, hB v u] at h
    simp only [zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.mul_im, zero_mul, sub_zero, add_zero] at h
    nlinarith [h]
  set a := (B v u).re with ha
  set b := (B u u).re with hb'
  have hb1 : 0 < b + 1 := by linarith
  have h := key (-a / (b + 1))
  have e2 : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
      = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [e2] at h
  have h3 : 0 ≤ -(a ^ 2 * (b + 2)) := by
    by_contra hc
    push Not at hc
    have : -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0 := div_neg_of_neg_of_pos hc (by positivity)
    linarith
  have h4 : a ^ 2 * (b + 2) ≤ 0 := by linarith
  have h5 : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < a ^ 2 * (b + 2) := mul_pos hc (by linarith)
    linarith
  have h6 : a ^ 2 = 0 := le_antisymm h5 (sq_nonneg a)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h6

theorem pairing_eq_zero_of_psd : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) →
    (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  intro V _ _ B hB hpos v hv w
  have hre := re_pairing_eq_zero_of_psd B hB hpos v hv w
  have him := re_pairing_eq_zero_of_psd B hB hpos v hv (Complex.I • w)
  have e : B v (Complex.I • w) = -Complex.I * B v w := by
    simp only [map_smulₛₗ, smul_eq_mul, Complex.conj_I]
  rw [e] at him
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

end GlobalTheory.CompanionTheory.HermitianForm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPsdIsotropicRadicalStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_psd_isotropic_radical : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | exact GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | (intros; apply GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd <;> assumption)
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.props

theorem toUnits_val (z : Circle) : ((Circle.toUnits z : ℂˣ) : ℂ) = (z : ℂ) := rfl

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.LeviSmoothness PositivityTheory.RgUd.Form.U.Atom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem colInv (hB : Lv ψ h π s B) (x : Fin (m + 1) → k) (v w : V) :
    B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
  have e := hB.mir _ (unip_mem_Mir m x) v w
  have hd : Matrix.GeneralLinearGroup.det (unip k (m + 1) (Multiplicative.ofAdd x)) = 1 := det_unip (m + 1) _
  rw [hd] at e
  have h1 : nabs k (1 : kˣ) ^ s = 1 := by
    have : nabs k (1 : kˣ) = 1 := by simp [nabs]
    rw [this, Real.one_rpow]
  rw [h1, Complex.ofReal_one, one_mul] at e
  exact e

theorem isLat_sup {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') : IsLat (A ⊔ A') :=
  ⟨isCompact_sup A A' hA.1 hA'.1, AddSubgroup.isOpen_mono le_sup_left hA.2⟩

theorem avg_idem (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) :
    avg ψ h π ξ A (avg ψ h π ξ A v) = avg ψ h π ξ A v := by
  have e := PositivityTheory.RgUd.Form.U.Atom.avg_avg h π ψ hB.cont hB.smooth ξ ξ hA hA le_rfl v
  rw [if_pos (fun _ _ => rfl)] at e
  exact e

theorem form_avg_self (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A)
    (v : V) : B (avg ψ h π ξ A v) v = B (avg ψ h π ξ A v) (avg ψ h π ξ A v) := by
  have e1 := form_avg h π ψ hB.cont hB.smooth B (colInv hB) ξ hA (avg ψ h π ξ A v) v
  rw [avg_idem hB ξ hA v] at e1
  exact e1

theorem dens_psd (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') : IsPsd B' := by
  refine ⟨fun v w => ?_, fun v => ?_⟩
  · obtain ⟨A₁, hA₁, -, e₁⟩ := hD v w
    obtain ⟨A₂, hA₂, -, e₂⟩ := hD w v
    have hA := isLat_sup hA₁ hA₂
    rw [e₁ _ hA le_sup_left, e₂ _ hA le_sup_right,
      form_avg h π ψ hB.cont hB.smooth B (colInv hB) (xi0 k m) hA w v, hB.psd.1 (avg ψ h π (xi0 k m) (A₁ ⊔ A₂) v) w,
      map_mul, map_natCast]
  · obtain ⟨A₁, hA₁, -, e₁⟩ := hD v v
    rw [e₁ _ hA₁ le_rfl, form_avg_self hB _ hA₁ v]
    rw [show ((A₀.relIndex A₁ : ℕ) : ℂ) = ((A₀.relIndex A₁ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (hB.psd.2 _)

theorem twKer_colEl_stable (hB : Lv ψ h π s B) (x : Fin (m + 1) → k) {z : V}
    (hz : z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) :
    π (colEl k m N h x) z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
  unfold twKer at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨hm, hc⟩ := ColumnElementGluing.colEl_conj_derUnip ψ h x u
    refine Submodule.subset_span ⟨⟨_, hm⟩, π (colEl k m N h x) v, ?_⟩
    rw [hc, map_sub, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    simp [mul_assoc]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem avg_twKer (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {z : V}
    (hz : z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) :
    avg ψ h π ξ A z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
  obtain ⟨p, hp, -⟩ := exists_avgData h π ψ hB.cont hB.smooth ξ hA z ⊤ isOpen_univ
  rw [avg_eq h π ψ hp]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_)
  exact twKer_colEl_stable hB t hz

theorem dens_kills2 (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') {z : V} (hz : z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) (w : V) :
    B' z w = 0 := by
  obtain ⟨A₁, hA₁, -, e₁⟩ := hD z w
  rw [e₁ _ hA₁ le_rfl, hB.kills _ (avg_twKer hB _ hA₁ hz) w, mul_zero]

theorem dens_kills (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') : Kills ψ π (m + 1) B' := by
  intro v hv
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, v₀, rfl⟩ := hy
    obtain ⟨x, u', hu, hc⟩ := ColumnElementGluing.derUnip_decomp ψ h u
    intro w
    have hsplit : π (u : GL (Fin N) k) v₀ - ((lvlChar k ψ N (m + 1) u : ℂˣ) : ℂ) • v₀ =
        π (colEl k m N h x) (π (u' : GL (Fin N) k) v₀ - ((lvlChar k ψ N (m + 2) u' : ℂˣ) : ℂ) • v₀) +
          ((lvlChar k ψ N (m + 2) u' : ℂˣ) : ℂ) •
            (π (colEl k m N h x) v₀ - ((ψ (xi0 k m ⬝ᵥ x) : Circle) : ℂ) • v₀) := by
      rw [hc, hu, map_mul, Module.End.mul_apply, map_sub, map_smul, smul_sub, smul_smul]
      simp only [Units.val_mul, toUnits_val]
      rw [mul_comm ((lvlChar k ψ N (m + 2) u' : ℂˣ) : ℂ)]
      abel
    rw [hsplit, map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      dens_kills2 hB hD (twKer_colEl_stable hB x (Submodule.subset_span ⟨u', v₀, rfl⟩)) w, zero_add]
    obtain ⟨A₁, hA₁, -, e₁⟩ := hD (π (colEl k m N h x) v₀ - ((ψ (xi0 k m ⬝ᵥ x) : Circle) : ℂ) • v₀) w
    obtain ⟨Ax, hAx1, hAx2, hxA⟩ := exists_lat_mem (m + 1) x
    have hA := isLat_sup hA₁ ⟨hAx1, hAx2⟩
    rw [e₁ _ hA le_sup_left, sub_eq_add_neg, ← neg_smul, avg_add h π ψ hB.cont hB.smooth _ hA,
      avg_smul h π ψ hB.cont hB.smooth _ hA, avg_colEl h π ψ hB.cont hB.smooth _ hA
        (AddSubgroup.mem_sup_right hxA), neg_smul, ← sub_eq_add_neg, sub_self, map_zero, LinearMap.zero_apply,
      mul_zero, smul_zero]
  | zero => intro w; simp
  | add a b _ _ ha hb => intro w; rw [map_add (f := _), LinearMap.add_apply, ha w, hb w, add_zero]
  | smul c a _ ha => intro w; rw [map_smul, LinearMap.smul_apply, ha w, smul_zero]

theorem dens_rad (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') (v : V) (hv : B' v v = 0) :
    v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) ⊔ LinearMap.ker B := by
  obtain ⟨A₁, hA₁, hA01, e₁⟩ := hD v v
  have hc : ((A₀.relIndex A₁ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (relIndex_ne_zero' A₁ A₀ hA₁.1 hA₀.2 hA01)
  rw [e₁ _ hA₁ le_rfl, form_avg_self hB _ hA₁ v] at hv
  have h0 : B (avg ψ h π (xi0 k m) A₁ v) (avg ψ h π (xi0 k m) A₁ v) = 0 := (mul_eq_zero.1 hv).resolve_left hc
  have hker : avg ψ h π (xi0 k m) A₁ v ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker]
    exact LinearMap.ext fun w => GlobalTheory.T.hermitian_psd_isotropic_radical V B hB.psd.1 hB.psd.2 _ h0 w
  have e : v = (v - avg ψ h π (xi0 k m) A₁ v) + avg ψ h π (xi0 k m) A₁ v := by abel
  rw [e]
  exact Submodule.add_mem_sup (ColumnElementGluing.sub_avg_mem ψ h π hB.cont hB.smooth A₁ hA₁ v) hker

end PositivityTheory.RgUd.Form.LeviSmoothness.props
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.BlockContinuity.ContinuousBlkAt
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel
open scoped Pointwise

namespace PositivityTheory.RgUd.Form.LeviSmoothness.Ex

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLat_sup {m : ℕ} {A B : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hB : IsLat B) : IsLat (A ⊔ B) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩
  have e : ((A ⊔ B : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) =
      (A : Set (Fin (m + 1) → k)) + (B : Set (Fin (m + 1) → k)) := by
    ext x
    rw [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
    rfl
  rw [e]
  exact hA.1.add hB.1

theorem exists_lat (m : ℕ) : ∃ A₀ : AddSubgroup (Fin (m + 1) → k), IsLat A₀ := by
  refine ⟨AddSubgroup.pi Set.univ fun _ => (𝒪[k]).toAddSubgroup, ?_, ?_⟩
  · have hc : IsCompact ((𝒪[k] : Set k)) := isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[k]))
    have e : ((AddSubgroup.pi Set.univ fun _ : Fin (m + 1) => (𝒪[k]).toAddSubgroup :
        AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k) := by
      ext x
      simp [AddSubgroup.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => hc
  · have ho : IsOpen ((𝒪[k] : Set k)) := by
      first
        | exact IsValuativeTopology.isOpen_integer
        | exact Valuation.isOpen_integer _
        | exact (valuation k).isOpen_integer
        | exact isOpen_integer
    have e : ((AddSubgroup.pi Set.univ fun _ : Fin (m + 1) => (𝒪[k]).toAddSubgroup :
        AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k) := by
      ext x
      simp [AddSubgroup.mem_pi]
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => ho

section

variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem exists_fixK (hπ : IsSmooth π) (v w : V) :
    ∃ K : Subgroup (GL (Fin (m + 1)) k), IsOpen (K : Set (GL (Fin (m + 1)) k)) ∧
      FixK (by omega) π K v ∧ FixK (by omega) π K w :=
  by apply _root_.UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK <;> assumption

theorem avg_adj (hherm : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hsa : ∀ (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)), IsLat A → ∀ v w,
      B (avg ψ h π ξ A v) w = B (avg ψ h π ξ A v) (avg ψ h π ξ A w))
    (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (x w : V) :
    B (avg ψ h π ξ A x) w = B x (avg ψ h π ξ A w) := by
  calc B (avg ψ h π ξ A x) w = B (avg ψ h π ξ A x) (avg ψ h π ξ A w) := hsa ξ A hA x w
    _ = starRingEnd ℂ (B (avg ψ h π ξ A w) (avg ψ h π ξ A x)) := hherm _ _
    _ = starRingEnd ℂ (B (avg ψ h π ξ A w) x) := by rw [← hsa ξ A hA w x]
    _ = B x (avg ψ h π ξ A w) := (hherm _ _).symm

theorem dens_exists_of (hB : Lv ψ h π s B)
    (hsa : ∀ (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)), IsLat A → ∀ v w,
      B (avg ψ h π ξ A v) w = B (avg ψ h π ξ A v) (avg ψ h π ξ A w))
    (hstab : ∀ (K : Subgroup (GL (Fin (m + 1)) k)), IsOpen (K : Set (GL (Fin (m + 1)) k)) →
      ∀ {A₀ : AddSubgroup (Fin (m + 1) → k)}, IsLat A₀ →
      ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v → FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
        ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
          ((A₀.relIndex A₁ : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A₁ v) w)
    {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) :
    ∃ B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsDens ψ h π A₀ B B' ∧ ∀ K : Subgroup (GL (Fin (m + 1)) k),
      IsOpen (K : Set (GL (Fin (m + 1)) k)) → ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v →
        FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
          B' v w = ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w := by
  classical

  let T : AddSubgroup (Fin (m + 1) → k) → V → V → ℂ := fun A v w =>
    ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w

  have hex : ∀ v w : V, ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ A, IsLat A → A₁ ≤ A → T A v w = T A₁ v w := by
    intro v w
    obtain ⟨K, hK, hv, hw⟩ := exists_fixK (h := h) hB.smooth v w
    obtain ⟨A₁, hA₁, h01, hst⟩ := hstab K hK hA₀
    exact ⟨A₁, hA₁, h01, fun A hAl hle => hst v w hv hw A hAl hle⟩
  choose L hL h0L hLs using hex
  let f : V → V → ℂ := fun v w => T (L v w) v w
  have hf : ∀ v w A, IsLat A → L v w ≤ A → f v w = T A v w := fun v w A hA hle => (hLs v w A hA hle).symm
  have hherm := hB.psd.1
  have hadj := avg_adj (ψ := ψ) (h := h) (π := π) hherm hsa

  have big : ∀ A₁ A₂ A₃ : AddSubgroup (Fin (m + 1) → k), IsLat A₁ → IsLat A₂ → IsLat A₃ →
      IsLat (A₁ ⊔ A₂ ⊔ A₃) ∧ A₁ ≤ A₁ ⊔ A₂ ⊔ A₃ ∧ A₂ ≤ A₁ ⊔ A₂ ⊔ A₃ ∧ A₃ ≤ A₁ ⊔ A₂ ⊔ A₃ :=
    fun A₁ A₂ A₃ h1 h2 h3 => ⟨isLat_sup (isLat_sup h1 h2) h3, le_sup_left.trans le_sup_left,
      le_sup_right.trans le_sup_left, le_sup_right⟩
  let B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f
    (fun v₁ v₂ w => by
      obtain ⟨hA, h1, h2, h3⟩ := big (L (v₁ + v₂) w) (L v₁ w) (L v₂ w) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2, hf _ _ _ hA h3]
      simp only [T]
      rw [hadj _ hA, hadj _ hA, hadj _ hA, map_add (f := _), LinearMap.add_apply, mul_add])
    (fun c v w => by
      obtain ⟨hA, h1, h2, -⟩ := big (L (c • v) w) (L v w) (L v w) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2]
      simp only [T, RingHom.id_apply, smul_eq_mul]
      rw [hadj _ hA, hadj _ hA, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun v w₁ w₂ => by
      obtain ⟨hA, h1, h2, h3⟩ := big (L v (w₁ + w₂)) (L v w₁) (L v w₂) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2, hf _ _ _ hA h3]
      simp only [T]
      rw [map_add (f := _), mul_add])
    (fun c v w => by
      obtain ⟨hA, h1, h2, -⟩ := big (L v (c • w)) (L v w) (L v w) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2]
      simp only [T, smul_eq_mul]
      rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      ring)
  have hB'f : ∀ v w, B' v w = f v w := fun v w => rfl
  refine ⟨B', fun v w => ⟨L v w, hL v w, h0L v w, fun A hA hle => by rw [hB'f, hf v w A hA hle]⟩, ?_⟩
  intro K hK
  obtain ⟨A₁, hA₁, h01, hA⟩ := hstab K hK hA₀
  refine ⟨A₁, hA₁, h01, fun v w hv hw A hA' hle => ?_⟩
  have hs := isLat_sup hA' (hL v w)
  have e1 := hf v w (A ⊔ L v w) hs le_sup_right
  have e2 := hA v w hv hw A hA' hle
  have e3 := hA v w hv hw (A ⊔ L v w) hs (hle.trans le_sup_left)
  rw [hB'f, e1]
  exact e3.trans e2.symm

end

end PositivityTheory.RgUd.Form.LeviSmoothness.Ex
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.SelfAdjointBounds.ReLeOfSelfadj
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem re_le_of_selfadj {V : Type} [AddCommGroup V] [Module ℂ V] {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : IsPsd B) (u v : V)
    (h : B u v = B u u) : (B u u).re ≤ (B v v).re := by
  have h1 := hB.2 (v - u)
  have h2 := hB.1 u v
  rw [h] at h2
  simp only [map_sub, LinearMap.sub_apply, Complex.sub_re] at h1
  rw [h2, h, Complex.conj_re] at h1
  linarith

end PositivityTheory.RgUd.Form.LeviSmoothness.asm
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.Final

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

theorem stepForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : StepForm k := by
  intro ψ hψ hψ1 m N hN V _ _ π hπ s B hpsd hk hmir
  have hB : Lv ψ hN π s B := ⟨hψ, hψ1, hπ, hpsd, hk, hmir⟩
  obtain ⟨A₀, hA₀⟩ := Ex.exists_lat (k := k) m
  obtain ⟨B', hD, hU⟩ := Ex.dens_exists_of hB (fun ξ A hA v w => alg.avg_selfadj hB ξ hA v w)
    (fun K hK _ hA₀ => stab.stab' hB K hK hA₀) hA₀
  refine ⟨B', props.dens_psd hB hA₀ hD, props.dens_kills hB hA₀ hD, props.dens_rad hB hA₀ hD, mir.dens_mir hB hA₀ hD,
    fun K hK => ?_, fun z hz v => besselOf.dens_bessel_of hB (fun K hK _ hA₀ => stab.stab' hB K hK hA₀) hA₀ hD z hz v⟩
  obtain ⟨A₁, hA₁, h01, hA⟩ := hU K hK
  refine ⟨(A₀.relIndex A₁ : ℝ), fun v hv => ?_⟩
  have e := hA v v hv hv A₁ hA₁ le_rfl
  rw [e]
  have hsa := alg.avg_selfadj hB (xi0 k m) hA₁ v v
  have key := asm.re_le_of_selfadj hpsd (avg ψ hN π (xi0 k m) A₁ v) v hsa
  have hc : ((A₀.relIndex A₁ : ℕ) : ℂ) = ((A₀.relIndex A₁ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.re_ofReal_mul, hsa]
  exact mul_le_mul_of_nonneg_left key (Nat.cast_nonneg _)

end PositivityTheory.RgUd.Form.LeviSmoothness.Final

module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMul
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMul
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacCentral

theorem subQuot_apply_of_smul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (y : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :
    subQuot S T g y = c • y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hs : S.toRepresentation g s = c • s := Subtype.ext (h s)
  show Submodule.Quotient.mk (S.toRepresentation g s) = _
  rw [hs, Submodule.Quotient.mk_smul]

theorem exists_step_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : jhMult σ ρ ≠ 0) :
    ∃ S T : Subrepresentation ρ, Nonempty ((subQuot S T).Equiv σ) := by
  by_contra hc
  refine h (le_antisymm (iSup₂_le fun r hr => ?_) bot_le)
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · simp
  · obtain ⟨S, T, -, -, hi⟩ := hr
    exact absurd ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hi ⟨0, hpos⟩⟩ hc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviEmb_scalar {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (t : kˣ) :
    leviEmb k (stdBlocks d hd) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) =
      Matrix.GeneralLinearGroup.scalar (Fin N) t := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [leviEmb_apply_ne k _ _ hab]
    have : (stdBlocks d hd) ⟨a, i⟩ ≠ (stdBlocks d hd) ⟨b, j⟩ := fun h => by
      have := (stdBlocks d hd).injective h
      exact hab (congrArg Sigma.fst this)
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, this]

theorem nabs_det_scalar (n : ℕ) (t : kˣ) :
    nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t)) =
      nabs k t ^ n := by
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

theorem deltaHalf_scalar (d : Fin 2 → ℕ) (t : kˣ) :
    deltaHalf k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
  have h0 : modExp (fun a => Fin (d a)) (0 : Fin 2) = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have h1 : modExp (fun a => Fin (d a)) (1 : Fin 2) = -(d 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hm : modulus k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
    have hp := (nabs_pos' k t).ne'
    rw [modulus, Fin.prod_univ_two, h0, h1, nabs_det_scalar, nabs_det_scalar, zpow_natCast, zpow_neg,
      zpow_natCast, ← pow_mul, ← pow_mul, mul_comm (d 0) (d 1)]
    exact mul_inv_cancel₀ (pow_ne_zero _ hp)
  apply Units.ext
  rw [val_deltaHalf, hm]
  simp

theorem piTensor_apply_of_smul {h : ℕ} (x : Fin h → IrrGL (k := k)) (g : ∀ a, GL (Fin (x a).1) k)
    (c : Fin h → ℂ) (hc : ∀ a v, (x a).rep (g a) v = c a • v)
    (w : PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :
    piTensor (fun a => (x a).rep) g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | add y z hy hz => rw [map_add (f := _), hy, hz, smul_add]
  | smul_tprod r y =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [hc]
    exact MultilinearMap.map_smul_univ _ _ _

theorem smul_eq_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : ρ.Equiv σ) {g : G} {c c' : ℂ} (hρ : ∀ v, ρ g v = c • v) (hσ : ∀ w, σ g w = c' • w) :
    c' = c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨y, rfl⟩ := E.toLinearEquiv.surjective w
  have hE : E.toIntertwiningMap (ρ g y) = σ g (E.toIntertwiningMap y) :=
    E.toIntertwiningMap.isIntertwining _ _ g y
  rw [hρ, hσ, map_smul] at hE
  have h2 : (c - c') • E.toLinearEquiv y = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hE
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact (sub_eq_zero.1 h3).symm
  · exact absurd h3 hw

theorem scalar_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  intro k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hc h0 h1
  obtain ⟨S, T, ⟨E⟩⟩ := exists_step_of_jhMult_ne_zero (show jhMult (piTensor fun a => (x a).rep)
    (GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π) ≠ 0 from hj)
  let g : Levi k (fun a => Fin (x a).1) := fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t
  have hjac : ∀ v, GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v := by
    intro v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [jac_mk, show deltaHalf k (fun a => Fin (x a).1) g = 1 from deltaHalf_scalar _ t,
      show leviEmb k (stdBlocks (fun a => (x a).1) hd) g = _ from leviEmb_scalar _ hd t, hc]
    simp [Submodule.Quotient.mk_smul]
  let cc : Fin 2 → ℂ := ![c0, c1]
  have hcc : ∀ a v, (x a).rep (g a) v = cc a • v := by
    intro a v
    fin_cases a
    · exact h0 v
    · exact h1 v
  haveI := GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL k x
  have hfin := smul_eq_of_equiv E (subQuot_apply_of_smul S T hjac)
    (piTensor_apply_of_smul x g cc hcc)
  rw [Fin.prod_univ_two] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.JacCentral

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMulStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_two_factor_central_character_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  first | exact @GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | exact GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | (intros; apply GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormula
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegScalar

theorem absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) : absPow k (n : ℂ) = absPow k 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, absPow_add, ih, pow_succ]

theorem absPow_pow_comm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (t : kˣ) :
    (((absPow k (a : ℂ) ^ d) t : ℂˣ) : ℂ) = ((absPow k (d : ℂ) t : ℂˣ) : ℂ) ^ a := by
  rw [absPow_natCast, absPow_natCast, ← pow_mul, mul_comm a d, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_mul,
    Units.val_pow_eq_pow_val]

theorem prod_mul_pow (l : ℕ) (c e : ℂ) :
    ∏ a : Fin l, (c * e ^ (a : ℕ)) = c ^ l * e ^ (l * (l - 1) / 2) := by
  rw [Fin.prod_univ_eq_prod_range (fun a => c * e ^ a) l, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

theorem scalarBy_of_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : Segment k) (y : IrrGL (k := k)) : IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c →
      Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  intro hL t c hc
  obtain ⟨hd, -, f, hf, -⟩ := hL
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Γ.first.2.rep.smooth Γ.first.2.rep.irr
  have hωc : ((ω t : ℂˣ) : ℂ) = c := by
    haveI := Model.nontrivial_of_isIrreducible Γ.first.2.rep.irr
    obtain ⟨w, hw⟩ := exists_ne (0 : Γ.first.2.rep.V)
    have h1 : ((ω t : ℂˣ) : ℂ) • w = c • w := (hω t w).symm.trans (hc w)
    exact smul_left_injective ℂ hw h1
  have hterm : ∀ a : Fin Γ.len, HasCentralChar (Γ.term a).rep (ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) :=
    fun a => UnitaryOrder.hasCentralChar_nu Γ.first hω ((a : ℕ) : ℂ)
  have hsc : ∀ v, y.rep (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) v =
      (∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Γ.term a).1) hd)
      (fun a => (Γ.term a).rep) _ hterm t w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  have h2 : ∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ) =
      c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2) := by
    rw [← prod_mul_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [MonoidHom.mul_apply, Units.val_mul, hωc, absPow_pow_comm]
  rw [← h2]
  exact hsc

end GlobalTheory.CompanionTheory.SegScalar

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormulaStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_central_character_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Segment k) (y : IrrGL (k := k)), IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c → Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | exact GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | (intros; apply GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegree
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel Matrix

namespace GlobalTheory.CompanionTheory.ScalarTwist

theorem acts_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (w : W) : σ g w = c • w := by
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w
  show σ g (φ.toIntertwiningMap v) = c • φ.toIntertwiningMap v
  rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]

theorem scalarBy_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ) (h : Zl.ScalarBy x t c) :
    Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext; simp [GeneralLinearGroup.scalar]
  refine acts_of_equiv (x.twEquiv (absPow k s) (isSmoothChar_absPow s)) (g := GeneralLinearGroup.scalar (Fin x.1) t) ?_
  intro v
  rw [twist_apply, h v, detChar_apply, hdet, smul_smul]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.ScalarTwist
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegreeStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_twist_pow_degree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | exact GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | (intros; apply GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBounds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBounds
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.TopNilp

theorem nabs_absPow_of_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  intro k _ _ _ _ t ht
  have hpos : 0 < nabs k t := nabs_pos' k t
  refine ⟨hpos, ?_, fun d => ?_⟩
  · by_contra hge
    have h1 : valuation k ((1 : kˣ) : k) ≤ valuation k (t : k) :=
      (nabs_le_iff 1 t).1 (by rw [nabs_one k]; exact not_lt.1 hge)
    rw [Units.val_one, map_one] at h1
    obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hr0 : r ≠ 0 := by simpa using hr
    have hnh : cball (Units.mk0 r hr0) ∈ 𝓝 (0 : k) :=
      (isOpen_cball _).mem_nhds (by simp [cball])
    obtain ⟨n, hn⟩ := (ht.eventually hnh).exists
    have h2 : valuation k ((t : k) ^ n) ≤ valuation k r := hn
    rw [map_pow] at h2
    exact absurd ((one_le_pow₀ h1).trans h2) (not_le.2 hr1)
  · rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le]

end GlobalTheory.CompanionTheory.TopNilp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBoundsStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracting_unit_abs_pow_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  first | exact @GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero | exact GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero | (intros; apply GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealPowPartialSegmentLtOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealPowPartialSegmentLtOne
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Segment

private theorem two_mul_triangle_add_mul_eq (d l₀ l₁ : ℕ) (h₀ : 1 ≤ l₀) (h₁ : 1 ≤ l₁) :
    2 * (d * (l₀ * l₁ + l₀ * (l₀ - 1) / 2)) * (l₀ + l₁) =
      2 * (d * ((l₀ + l₁) * (l₀ + l₁ - 1) / 2)) * l₀ + d * ((l₀ + l₁) * l₀ * l₁) := by
  obtain ⟨a, rfl⟩ : ∃ a, l₀ = a + 1 := ⟨l₀ - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, l₁ = b + 1 := ⟨l₁ - 1, by omega⟩
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hp : 2 * ((a + 1) * a / 2) = (a + 1) * a :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self a)
  have hq : 2 * ((a + b + 1 + 1) * (a + b + 1) / 2) = (a + b + 1 + 1) * (a + b + 1) :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self (a + b + 1))
  generalize (a + 1) * a / 2 = p at hp ⊢
  generalize (a + b + 1 + 1) * (a + b + 1) / 2 = q at hq ⊢
  zify at hp hq ⊢
  linear_combination ((d : ℤ) * (a + b + 1 + 1)) * hp - ((d : ℤ) * (a + 1)) * hq

theorem top_piece_exponent_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 →
    r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 →
    r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  intro α r d l0 l1 hα0 hα1 hr hd hl0 hl1 h
  have key := two_mul_triangle_add_mul_eq d l0 l1 hl0 hl1
  set T := (l0 + l1) * (l0 + l1 - 1) / 2
  set S := l0 * l1 + l0 * (l0 - 1) / 2
  have hpow : (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) = α ^ (d * ((l0 + l1) * l0 * l1)) := by
    calc (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1))
        = (r ^ (l0 + l1)) ^ (2 * l0) * α ^ (2 * (d * S) * (l0 + l1)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 2 <;> ring
      _ = (r ^ (l0 + l1) * α ^ (d * T)) ^ (2 * l0) * α ^ (d * ((l0 + l1) * l0 * l1)) := by
          rw [key, pow_add α, mul_pow (r ^ (l0 + l1)), ← pow_mul α (d * T),
            show d * T * (2 * l0) = 2 * (d * T) * l0 by ring, ← mul_assoc ((r ^ (l0 + l1)) ^ (2 * l0))]
      _ = α ^ (d * ((l0 + l1) * l0 * l1)) := by rw [h, one_pow, one_mul]
  have hlt : α ^ (d * ((l0 + l1) * l0 * l1)) < 1 :=
    pow_lt_one₀ hα0.le hα1
      (Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).ne'
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) := one_le_pow₀ hc
  rw [hpow] at h1
  exact absurd hlt (not_lt.mpr h1)

end GlobalTheory.CompanionTheory.Segment
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealPowPartialSegmentLtOneStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_pow_partial_segment_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 → r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 → r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one | exact GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one | (intros; apply GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalar
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.ScalarUniq

theorem scalarBy_unique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ) (h : Zl.ScalarBy x t c) (h' : Zl.ScalarBy x t c') : c = c' := by
  have hirr : x.rep.IsIrreducible := x.2.rep.irr
  have hnt : Nontrivial x.2.rep.V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial : Nontrivial (Subrepresentation x.rep)).exists_pair_ne
    refine hab ?_
    ext v
    simp [Subsingleton.elim v 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have e : c • v = c' • v := (h v).symm.trans (h' v)
  exact smul_left_injective ℂ hv e

end GlobalTheory.CompanionTheory.ScalarUniq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalarStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_eq_of_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
  first | exact @GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | exact GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | (intros; apply GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrable
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegLink

theorem one_le_deg_of_isLSeg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {Δ : Segment k} {y : IrrGL (k := k)} (hL : IsLSeg Δ y.rep) : 1 ≤ y.1 := by
  obtain ⟨hd, -⟩ := hL
  have hterm : ∀ a, (Δ.term a).fst = Δ.d := fun a => rfl
  rw [← hd]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos

theorem norm_top_eq (r A : ℝ) (d d0 l0 l1 m : ℕ) (h : d0 = d) :
    (r * (A ^ l1) ^ d) ^ l0 * (A ^ d0) ^ m = r ^ l0 * A ^ (d * (l0 * l1 + m)) := by
  subst h
  ring

theorem centredSegSqInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  intro k _ _ _ _ hCas hIA hLJ Δ y hL hU
  have hN : 1 ≤ y.1 := one_le_deg_of_isLSeg hL
  have hmax : Zls.MaxExpStrict y.rep := by
    intro x hd hpos hjm t ht c hc
    obtain ⟨Γ, ⟨hlen, hfirst⟩, hΓ⟩ := GlobalTheory.T.segment_jacquet_two_factor_split k Δ y.1 _ y.rep hLJ hL x hd hpos hjm
    obtain ⟨hα0, hα1, hnorm⟩ := GlobalTheory.T.contracting_unit_abs_pow_bounds k t ht
    obtain ⟨c0, hc0⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k Δ.first.fst _ Δ.first.rep Δ.first.snd.rep.smooth
      Δ.first.snd.rep.irr (hIA k _ _ _ Δ.first.snd.rep.smooth Δ.first.snd.rep.irr) t
    obtain ⟨cy, hcy⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k y.fst _ y.rep y.snd.rep.smooth y.snd.rep.irr
      (hIA k _ _ _ y.snd.rep.smooth y.snd.rep.irr) t
    have hprod := GlobalTheory.T.jacquet_two_factor_central_character_mul k y.fst _ y.rep x hd hjm t cy (c 0) (c 1) hcy (hc 0) (hc 1)
    have hcy1 : ‖cy‖ = 1 := hU t cy hcy
    have hy1 := hU t _ (GlobalTheory.T.segment_rep_central_character_formula k Δ y hL t c0 hc0)
    rw [norm_mul, norm_pow, norm_pow, hnorm, ← pow_mul] at hy1
    have hr : 0 < ‖c0‖ := by
      rcases (norm_nonneg c0).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_pow (Nat.pos_iff_ne_zero.mp Δ.len_pos), zero_mul] at hy1
        exact zero_ne_one hy1
    have hlen2 : (Γ 0).len + (Γ 1).len = Δ.len := by rw [← hlen, Fin.sum_univ_two]
    rw [← hlen2] at hy1
    have hb0 : Zc.below Γ 0 = (Γ 1).len := by
      simp [Zc.below, Finset.sum_filter, Fin.sum_univ_two]
    have hf0 : (Γ 0).first.fst = Δ.first.fst := by rw [hfirst 0]; rfl
    have hG0 : Zl.ScalarBy (Γ 0).first t
        (c0 * ↑((GlobalTheory.SmGL.absPow k ↑(Zc.below Γ 0)) t) ^ Δ.first.fst) := by
      rw [hfirst 0]
      exact GlobalTheory.T.central_character_twist_pow_degree k Δ.first t c0 _ hc0
    have he0 := GlobalTheory.T.central_character_eq_of_scalar k (x 0) t _ _ (hc 0) (GlobalTheory.T.segment_rep_central_character_formula k (Γ 0) (x 0) (hΓ 0) t _ hG0)
    have hn0 : ‖c 0‖ = ‖c0‖ ^ (Γ 0).len * GlobalTheory.SplitWeil.nabs k t ^
        (Δ.first.fst * ((Γ 0).len * (Γ 1).len + (Γ 0).len * ((Γ 0).len - 1) / 2)) := by
      rw [he0, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, hnorm, hnorm, hb0]
      exact norm_top_eq _ _ _ _ _ _ _ hf0
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := Fin.ext (by omega)
      subst hj0
      have hp : (∏ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 0), ‖c i‖) = ‖c 0‖ := by
        simp [Finset.prod_filter, Fin.prod_univ_two]
      rw [hp, hn0]
      exact GlobalTheory.T.real_pow_partial_segment_lt_one _ _ _ _ _ hα0 hα1 hr Δ.d_pos (Γ 0).len_pos (Γ 1).len_pos hy1
    · rw [Fin.prod_univ_two, ← norm_mul, hprod, hcy1]
  exact @hCas y.1 _ _ _ y.rep hN y.snd.rep.smooth y.snd.rep.irr (fun t c hc => hU t c hc) hmax

end GlobalTheory.CompanionTheory.SegLink
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrableStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centred_segment_square_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  first | exact @GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | exact GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | (intros; apply GlobalTheory.CompanionTheory.SegLink.centredSegSqInt <;> assumption)
end
end

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace Zls.FreeSingleHomotopyEquivDiscreteChains

theorem sspectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  exact GlobalTheory.T.hecke_spectral_of_strict_exponent

theorem ssqint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π → Zls.HeckeSpectral π → IsSqIntCoeff π := by
  exact GlobalTheory.T.square_integrable_of_hecke_spectral

theorem casselmanSuffSq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) : Zls.CasselmanSuffSq k := by
  intro N V _ _ π _ hs hi hu he
  exact ssqint k N V π hs hi (hA k N V π hs hi) hu (sspectral k N V π hs hi hA hF he)

theorem sseglink : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  exact GlobalTheory.T.centred_segment_square_integrable

theorem centredSegSqInt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) (hJ : Zc.LSegJacquet k) :
    Zz.CentredSegSqInt k :=
  sseglink k (casselmanSuffSq k hA hF) hA hJ

end Zls.FreeSingleHomotopyEquivDiscreteChains

end

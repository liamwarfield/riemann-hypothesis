module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCell
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCell
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem locSec_parab_mir_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  set e := GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) with he
  obtain ⟨b, hbc, hb1, hbw⟩ := GlobalTheory.CompanionTheory.BZRes.exists_rowSec (k := k) (Fin.last (i + t))
  obtain ⟨W, hW⟩ : ∃ W : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k,
      ∀ u, W u = (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
    ⟨fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)),
      fun _ => rfl⟩
  have hWc : Continuous W := by
    have hWeq : W = fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
      funext hW
    rw [hWeq]
    exact continuous_pi fun j =>
      (Units.continuous_coe_inv (M := Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)).matrix_elem
        (Fin.last (i + t)) j
  have hone : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      GlobalTheory.BZMir.eLast k (i + t) := by
    funext j
    by_cases hj : j = Fin.last (i + t)
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.eLast, Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  have hrow : ∀ q p : GL (Fin (i + t + 1)) k, p ∈ GlobalTheory.BZMir.Mir k (i + t) →
      (↑(q * p)⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
        (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    intro q p hp
    have hp' := (GlobalTheory.BZMir.mem_Mir_iff k p⁻¹).1 (Subgroup.inv_mem _ hp)
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply_eq_vecMul, hp']
    simp only [GlobalTheory.BZMir.eLast, Matrix.single_one_vecMul]
    rfl
  have hW1 : W 1 = Pi.single (Fin.last (i + t)) 1 := by
    rw [hW, inv_one, Units.val_one, hone]
    rfl
  have hbW : ContinuousAt (fun u => b (W u)) 1 := by
    refine ContinuousAt.comp (f := W) (g := b) ?_ hWc.continuousAt
    rw [hW1]
    exact hbc
  have hbW1 : b (W 1) = 1 := by rw [hW1, hb1]
  unfold GlobalTheory.CompanionTheory.BZRes.LocSec
  intro OQ hOQ OP hOP
  have h1 : (fun u => (b (W u))⁻¹) ⁻¹' OQ ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    hbW.inv.preimage_mem_nhds (by
      show OQ ∈ 𝓝 (b (W 1))⁻¹
      rw [hbW1, inv_one]
      exact hOQ)
  have h2 : (fun u => b (W u) * u) ⁻¹' OP ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    (hbW.mul continuousAt_id).preimage_mem_nhds (by
      show OP ∈ 𝓝 (b (W 1) * 1)
      rw [hbW1, mul_one]
      exact hOP)
  have h3 : (fun u => W u (Fin.last (i + t))) ⁻¹' {x | x ≠ 0} ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    ((continuous_apply _).comp hWc).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds (by simp [hW1]))
  refine ⟨_, Filter.inter_mem h1 (Filter.inter_mem h2 h3), ?_⟩
  rintro u ⟨hu1, hu2, hu3⟩ hu
  unfold GlobalTheory.CompanionTheory.BZRes.dcos at hu
  obtain ⟨q, hq, p, hp, hqp⟩ := hu
  simp only [one_mul, mul_one] at hqp
  have hbw' := hbw (W u) hu3
  have hWu : W u = (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    rw [hW, hqp]
    exact hrow q p hp
  have hbQ : b (W u) ∈ GlobalTheory.SmGL.parab k e := by
    rw [GlobalTheory.SmGL.mem_parab_iff]
    rintro (_ | _) (_ | _) r c hlt
    all_goals first | exact absurd hlt (by decide) | skip
    rw [hbw']
    by_cases hr : e ⟨true, r⟩ = Fin.last (i + t)
    · rw [hr, Matrix.updateRow_self, hWu, ← hr]
      exact (GlobalTheory.SmGL.mem_parab_iff.1 (Subgroup.inv_mem _ hq)) true false r c hlt
    · rw [Matrix.updateRow_ne hr, Matrix.one_apply_ne]
      intro hrc
      exact absurd (e.injective hrc) (by simp)
  have hpP : b (W u) * u ∈ GlobalTheory.BZMir.Mir k (i + t) := by
    rw [GlobalTheory.BZMir.mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, hbw', Matrix.updateRow_self, hW,
      ← Matrix.mul_apply_eq_vecMul, Units.inv_mul, hone]
  refine ⟨(b (W u))⁻¹, Subgroup.inv_mem _ hbQ, hu1, b (W u) * u, hpP, hu2, ?_⟩
  simp

end GlobalTheory.CompanionTheory.BZRes

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCellStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_closed_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | exact GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | (intros; apply GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCell
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCell
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wPerm_last {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e, ePG_false_last]

theorem vecMul_wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k))
      (wGL k h : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
  ext c
  rw [Matrix.single_one_vecMul]
  show (1 : Matrix _ _ k) (wPerm h (stdSum h (Sum.inl (Fin.last i)))) c = _
  rw [wPerm_last]
  simp [eLast, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem vecMul_wGL_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k) := by
  rw [← vecMul_wGL (k := k) h, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem mem_parab_of_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k)
    (y : Fin (i + t + 1) → k)
    (hg : (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix _ _ k).updateRow (stdSum h (Sum.inl (Fin.last i))) y) :
    g ∈ parab k (two (stdSum h)) := by
  rw [mem_parab_iff]
  intro a b x z hab
  have hab' : a = true ∧ b = false := by
    clear x z
    revert hab
    cases a <;> cases b <;> decide
  obtain ⟨rfl, rfl⟩ := hab'
  have hne : two (stdSum h) ⟨true, x⟩ ≠ stdSum h (Sum.inl (Fin.last i)) := by
    intro e
    have := (stdSum h).injective e
    simp at this
  have hne2 : two (stdSum h) ⟨true, x⟩ ≠ two (stdSum h) ⟨false, z⟩ := by
    intro e
    have := (two (stdSum h)).injective e
    simp at this
  rw [hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]

theorem locSec_wGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1) : LocSec (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  intro OQ hOQ OP hOP
  set a₁ := stdSum h (Sum.inl (Fin.last i)) with ha₁
  set w := wGL k h with hw
  obtain ⟨b, hbc, hb1, hb⟩ := exists_rowSec (k := k) a₁
  let y : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k := fun u =>
    vecMul (eLast k (i + t)) (((w * u)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
  have hyc : Continuous y :=
    continuous_const.matrix_vecMul (Units.continuous_val.comp (continuous_const.mul continuous_id).inv)
  have hy1 : y 1 = Pi.single a₁ 1 := by
    simp only [y, mul_one]
    exact vecMul_wGL_inv h
  have hBc : ContinuousAt (fun u => b (y u)) 1 :=
    ContinuousAt.comp (f := y) (g := b) (by rw [hy1]; exact hbc) hyc.continuousAt
  have hB1 : b (y 1) = 1 := by rw [hy1, hb1]
  have hS : ContinuousAt (fun u => (b (y u))⁻¹) 1 := hBc.inv
  have hP : ContinuousAt (fun u => w⁻¹ * b (y u) * w * u) 1 :=
    ((continuousAt_const.mul hBc).mul continuousAt_const).mul continuousAt_id
  have hS' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), (b (y u))⁻¹ ∈ OQ :=
    hS.eventually_mem (by simpa [hB1] using hOQ)
  have hP' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), w⁻¹ * b (y u) * w * u ∈ OP :=
    hP.eventually_mem (by simpa [hB1] using hOP)
  have hne : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), y u a₁ ≠ 0 := by
    have : ContinuousAt (fun u => y u a₁) 1 := ((continuous_apply a₁).comp hyc).continuousAt
    exact this.eventually_ne (by rw [hy1]; simp)
  refine ⟨_, hS'.and (hP'.and hne), ?_⟩
  rintro u ⟨h1, h2, h3⟩ -
  have hBm := hb (y u) h3
  refine ⟨(b (y u))⁻¹, inv_mem (mem_parab_of_row h _ _ hBm), h1, w⁻¹ * b (y u) * w * u, ?_, h2, by group⟩
  show vecMul (eLast k (i + t)) _ = eLast k (i + t)
  have e1 : vecMul (vecMul (eLast k (i + t)) ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k))
      (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = y u := by
    rw [vecMul_wGL_inv h, hBm, Matrix.single_one_vecMul]
    exact Matrix.updateRow_self
  have e2 : vecMul (y u) ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
    simp only [y]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have e3 : ((w⁻¹ * b (y u) * w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
        (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
          ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [e3, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e1, e2]

end GlobalTheory.CompanionTheory.BZRes

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCellStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), LocSec (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.locSec_wGL | exact GlobalTheory.CompanionTheory.BZRes.locSec_wGL | (intros; apply GlobalTheory.CompanionTheory.BZRes.locSec_wGL <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionMeasurable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionMeasurable
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.Fibre

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem chi_at_fibreF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id D.hR
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hJt := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJt R
  obtain ⟨-, -, -, -, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
  obtain ⟨g, -, hg⟩ := hlift (M + 1) _ hJt
  have hcoord := (GlobalTheory.T.gram_block_one_schur_coordinates F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀).1 x hx
  have hd : Module.finrank F E = 2 := D.hCM.2.2.1
  set u : R := ((a x : Rˣ) : R) with hu
  have huE : IsUnit (u ⊗ₜ[F] (1 : E)) :=
    (Units.isUnit (a x)).map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)
  have hy00 : gramR R σ (blockOne (algebraMap F E t) J) y₀ 0 0 = algebraMap F R t ⊗ₜ[F] (1 : E) := by
    rw [hy₀]; rfl
  have hG : gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀) 0 0 =
      x ⊗ₜ[F] (1 : E) := by
    rw [gramR_scl_tmul, hy00, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have hq : u ^ 2 * algebraMap F R t = x := (D.hsq x hx).symm
    rw [mul_one, mul_one, ← pow_two, hq]
  have hs0 : s0 R (gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀)) = x :=
    corner_half_trace_of_pure_tensor R b hd x _ hG
  have hsT : sTil σ J t s a (scl (u ⊗ₜ[F] (1 : E)) y₀) = s y₀ := by
    unfold sTil
    rw [hs0]
    congr 1
    funext i j
    simp only [scl, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hu, Units.mul_inv]
    exact mul_one _
  have hsec := congrFun (D.hsec y₀ hy₀) 0
  have hcons : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      (Fin.cons (scl (u ⊗ₜ[F] (1 : E)) y₀ 0)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (fun j => Fin.cons (c j) (X j))) :
          Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) := by
    intro c X
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have e : (Fin.cons (u ⊗ₜ[F] (1 : E)) (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) =
          (u ⊗ₜ[F] (1 : E)) • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) := by
        funext k
        refine Fin.cases ?_ (fun l => ?_) k <;> simp
      simp only [Fin.cons_zero, vec, actW, actTup]
      rw [e, Matrix.mulVec_smul]
      simp only [actW, actTup] at hsec
      rw [hsec]
      funext k
      simp [scl, mul_comm]
    · simp [vec, actW, actTup]
  have hfree : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      LinearIndependent (R ⊗[F] E)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) ↔
      LinearIndependent (R ⊗[F] E) X := fun c X =>
    (GlobalTheory.T.linearIndependent_unitary_action_iff F E R σ (M + 1) (n + 1) _ (s y₀) _).trans
      (GlobalTheory.T.linearIndependent_extend_by_unit_vector (R ⊗[F] E) M n _ huE c X)
  have hmem : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) ∈
        (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) ↔
      X ∈ {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
    intro c X
    have hinv := (hact (n + 1)).2.2.2 (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)
    constructor
    · rintro ⟨-, h⟩
      exact (hfree c X).1 h
    · intro hX
      refine ⟨?_, (hfree c X).2 hX⟩
      have h3 := hcoord c X (g (vec (u ⊗ₜ[F] (1 : E)) c X)) (hg _).symm
      simp only [Set.mem_preimage, hinv]
      refine ⟨g (vec (u ⊗ₜ[F] (1 : E)) c X), ?_, (hg _).symm⟩
      change s0 R _ ∈ B₀
      rw [h3.1]; exact hx
  haveI := hBor n M
  haveI := hBor (n + 1) (M + 1)
  have hUd : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    (GlobalTheory.T.linearly_independent_frames_open F E σ D.hCM R D.hR n M).measurableSet
  have hψ : ∀ c : Fin n → R ⊗[F] E, Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
      φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) := by
    intro c
    have hv : Continuous fun X : Fin n → Fin M → R ⊗[F] E => vec (u ⊗ₜ[F] (1 : E)) c X := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · refine continuous_pi fun k => ?_
        refine Fin.cases ?_ (fun l => ?_) k
        · exact continuous_const
        · exact (continuous_apply l).comp (continuous_apply j)
    have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
        actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) :=
      (hact (n + 1)).1.comp (continuous_const.prodMk hv)
    exact hφ.comp hc.measurable
  unfold GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi
  rw [hsT]
  refine lintegral_congr fun c => ?_
  calc _ = ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}.indicator (fun X =>
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))) X
        ∂(coordW R b lam n M) := by
        refine lintegral_congr fun X => ?_
        rw [hcons c X]
        by_cases h : X ∈ {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem c X).2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem c X).1 h'))]
    _ = ∫⁻ X in {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X},
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))
        ∂(coordW R b lam n M) := lintegral_indicator hUd _
    _ = _ := D.hm'.2.1 _ (hψ c)

end GlobalTheory.CompanionTheory.SW.StageF.Fibre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionMeasurableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_lintegral_blockOne_eq_iterated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | exact GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionConstructedFromDoubleCoset
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTail
theorem UpperTheory.Reformulated.B.Ylb7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {C : Set G},
      IsCompact C →
        ∀ {n : Set (G × G)}, IsOpen n → (∀ c ∈ C, (c, (1 : G)) ∈ n) → ∃ O ∈ nhds (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n := by
  intro G _ _ C hC n hn h
  have hsub : C ×ˢ ({1} : Set G) ⊆ n := by
    rintro ⟨c, u⟩ ⟨hc, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    exact h c hc
  obtain ⟨U, V, _, hV, _, hV1, hUV⟩ := generalized_tube_lemma hC isCompact_singleton hn hsub
  refine ⟨V, hV.mem_nhds (hV1 rfl), ?_⟩
  intro c hc u hu
  exact hUV ⟨‹C ⊆ U› hc, hu⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionConstructedFromDoubleCoset
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem exists_nhds_one_tube {G : Type} [Group G] [TopologicalSpace G] {C : Set G} (hC : IsCompact C)
    {n : Set (G × G)} (hn : IsOpen n) (h : ∀ c ∈ C, (c, (1 : G)) ∈ n) :
    ∃ O ∈ 𝓝 (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n :=
  _root_.UpperTheory.Reformulated.B.Ylb7.main hC hn h

theorem finite_image_of_rightInvariant {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] {W : Type}
    (φ : P → W) (K' : Subgroup P) (hK' : IsOpen (K' : Set P)) (hinv : ∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p)
    {C : Set P} (hC : IsCompact C) : (φ '' C).Finite := by
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => {p : P | c⁻¹ * p ∈ K'}) (fun c _ => by
    have ho : IsOpen {p : P | c⁻¹ * p ∈ K'} := hK'.preimage (continuous_const.mul continuous_id)
    exact ho.mem_nhds (by simp [K'.one_mem]))
  refine (t.finite_toSet.image φ).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨c, hc, hcp⟩ := Set.mem_iUnion₂.1 (ht hp)
  refine ⟨c, hc, ?_⟩
  have := hinv c _ hcp
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem exists_openSubgroup_consistent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} :
    LocSec Q P x → ∀ (σ : Representation ℂ Q W₁), IsSmooth σ → ∀ (φ : P → W₁),
    (∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ p' = σ q (φ p)) →
    ∀ (K' : Subgroup P), IsOpen (K' : Set P) → (∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p) →
    ∀ (C : Set P), IsCompact C → ∀ (Y : Set G), IsOpen Y → (∀ c ∈ C, x * (c : G) ∈ Y) →
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (∀ c ∈ C, ∀ κ ∈ K, x * (c : G) * κ ∈ Y) ∧
      ∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c) := by
  intro hL σ hσ φ hφ K' hK' hinv C hC Y hY hCY
  have hfin : (φ '' C).Finite := finite_image_of_rightInvariant φ K' hK' hinv hC

  have hopenQ : IsOpen {q : Q | ∀ v ∈ φ '' C, σ q v = v} := by
    have e : {q : Q | ∀ v ∈ φ '' C, σ q v = v} = ⋂ v ∈ φ '' C, {q : Q | σ q v = v} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact hfin.isOpen_biInter fun v _ => hσ v
  obtain ⟨UQ, hUQ, hUQe⟩ := isOpen_induced_iff.1 hopenQ
  have h1UQ : (1 : G) ∈ UQ := by
    have : (1 : Q) ∈ (Subtype.val : Q → G) ⁻¹' UQ := by
      rw [hUQe]
      intro v _
      simp
    exact this
  have hfix : ∀ s : Q, (s : G) ∈ UQ → ∀ c ∈ C, σ s (φ c) = φ c := by
    intro s hs c hc
    have : s ∈ (Subtype.val : Q → G) ⁻¹' UQ := hs
    rw [hUQe] at this
    exact this _ ⟨c, hc, rfl⟩

  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hK'
  have h1U : (1 : G) ∈ U := by
    have : (1 : P) ∈ (Subtype.val : P → G) ⁻¹' U := by
      rw [hUe]
      exact K'.one_mem
    exact this
  have hC' : IsCompact ((Subtype.val : P → G) '' C) := hC.image continuous_subtype_val
  obtain ⟨OP, hOP, hOPc⟩ := exists_nhds_one_tube hC' (n := {z : G × G | z.1⁻¹ * z.2 * z.1 ∈ U})
    (hU.preimage (by fun_prop)) (by
      rintro _ ⟨c, -, rfl⟩
      simpa using h1U)
  obtain ⟨O, hO, hOs⟩ := hL UQ (hUQ.mem_nhds h1UQ) OP hOP
  obtain ⟨O₁, hO₁, hO₁c⟩ := exists_nhds_one_tube hC'
    (n := {z : G × G | z.1 * z.2 * z.1⁻¹ ∈ interior O ∧ x * z.1 * z.2 ∈ Y})
    ((isOpen_interior.preimage (by fun_prop)).inter (hY.preimage (by fun_prop))) (by
      rintro _ ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa using mem_interior_iff_mem_nhds.2 hO
      · simpa using hCY c hc)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean O₁ hO₁
  have hVc : ∀ c ∈ C, ∀ κ ∈ (V : Subgroup G),
      (c : G) * κ * (c : G)⁻¹ ∈ interior O ∧ x * (c : G) * κ ∈ Y := fun c hc κ hκ =>
    hO₁c _ ⟨c, hc, rfl⟩ κ (hV hκ)
  refine ⟨(V : Subgroup G), V.isOpen, fun c hc κ hκ => (hVc c hc κ hκ).2, ?_⟩
  intro c hc κ hκ q p' hq
  have huO : (c : G) * κ * (c : G)⁻¹ ∈ O := interior_subset (hVc c hc κ hκ).1

  have hmem : x * ((c : G) * κ * (c : G)⁻¹) ∈ dcos Q P x := by
    refine ⟨(q : G)⁻¹, Q.inv_mem q.2, (p' : G) * (c : G)⁻¹, P.mul_mem p'.2 (P.inv_mem c.2), ?_⟩
    calc x * ((c : G) * κ * (c : G)⁻¹) = (q : G)⁻¹ * ((q : G) * x * (c : G) * κ) * (c : G)⁻¹ := by group
      _ = (q : G)⁻¹ * x * ((p' : G) * (c : G)⁻¹) := by rw [hq]; group
  obtain ⟨s, hsQ, hsU, p₂, hp₂, hp₂O, he⟩ := hOs _ huO hmem

  have hconj : (c : G)⁻¹ * p₂ * (c : G) ∈ U := hOPc _ ⟨c, hc, rfl⟩ p₂ hp₂O
  have hκ' : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ K' := by
    have : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ (Subtype.val : P → G) ⁻¹' U := hconj
    rw [hUe] at this
    exact this
  have hval : φ (⟨p₂, hp₂⟩ * c) = φ c := by
    have := hinv c _ hκ'
    rwa [show c * (c⁻¹ * ⟨p₂, hp₂⟩ * c) = ⟨p₂, hp₂⟩ * c by group] at this
  have hrel : (((⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q)) : G) * x * ((⟨p₂, hp₂⟩ * c : P) : G) = x * (p' : G) := by
    have : (q : G) * s * x * (p₂ * (c : G)) = (q : G) * (s * x * p₂) * (c : G) := by group
    show (q : G) * s * x * (p₂ * (c : G)) = x * (p' : G)
    rw [this, ← he, ← hq]
    group
  have hsplit : (⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q) = q * ⟨s, hsQ⟩ := rfl
  rw [hφ _ _ _ hrel, hval, hsplit, map_mul, Module.End.mul_apply, hfix ⟨s, hsQ⟩ hsU c hc]

end GlobalTheory.CompanionTheory.BZRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionConstructedFromDoubleCosetStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_constructed_from_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NonarchimedeanGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G}, LocSec Q P x → ∀ (σ : Representation ℂ Q W₁), IsSmooth σ → ∀ (φ : P → W₁), (∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ p' = σ q (φ p)) → ∀ (K' : Subgroup P), IsOpen (K' : Set P) → (∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p) → ∀ (C : Set P), IsCompact C → ∀ (Y : Set G), IsOpen Y → (∀ c ∈ C, x * (c : G) ∈ Y) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (∀ c ∈ C, ∀ κ ∈ K, x * (c : G) * κ ∈ Y) ∧ ∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.exists_openSubgroup_consistent | exact GlobalTheory.CompanionTheory.BZRes.exists_openSubgroup_consistent | (intros; apply GlobalTheory.CompanionTheory.BZRes.exists_openSubgroup_consistent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvolutionCompatiblePolynomial
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CTAevalMulEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct

namespace GlobalTheory.CompanionTheory.AdjointPoly

theorem cT_aeval_mul_eq :
    ∀ (K : Type) [Field K] (s : K →+* K) (n : ℕ) (A H₀ : Matrix (Fin n) (Fin n) K) (a : K[X]),
      cT s A * H₀ * A = H₀ → aeval A a * A = 1 →
      ∀ f : K[X], cT s (aeval A f) * H₀ = H₀ * aeval A ((f.map s).comp a) := by
  intro K _ s n A H₀ a hA ha f
  have hcomm : A * aeval A a = aeval A a * A := by
    have h : aeval A (X * a) = aeval A (a * X) := by rw [mul_comm]
    simpa only [map_mul, aeval_X] using h
  have hAB : A * aeval A a = 1 := hcomm.trans ha
  have hstep : cT s A * H₀ = H₀ * aeval A a := by
    calc cT s A * H₀ = cT s A * H₀ * (A * aeval A a) := by rw [hAB, mul_one]
      _ = (cT s A * H₀ * A) * aeval A a := by simp only [mul_assoc]
      _ = H₀ * aeval A a := by rw [hA]
  have cT_mul : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P * Q) = cT s Q * cT s P := by
    intro P Q
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have cT_add : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P + Q) = cT s P + cT s Q := by
    intro P Q
    ext i j
    simp [cT]
  have cT_C : ∀ c : K, cT s (algebraMap K (Matrix (Fin n) (Fin n) K) c)
      = algebraMap K (Matrix (Fin n) (Fin n) K) (s c) := by
    intro c
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  induction f using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Polynomial.map_C, Polynomial.C_comp]
    rw [cT_C, Algebra.commutes]
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.map_add (f := _), Polynomial.add_comp, cT_add, add_mul, mul_add, hp, hq]
  | monomial k c ih =>
    have e1 : aeval A (C c * X ^ (k + 1)) = A * aeval A (C c * X ^ k) := by
      have h : aeval A (C c * X ^ (k + 1)) = aeval A (X * (C c * X ^ k)) := by
        congr 1; ring
      rw [h, map_mul, aeval_X]
    have e2 : ((C c * X ^ (k + 1) : K[X]).map s).comp a
        = ((C c * X ^ k : K[X]).map s).comp a * a := by
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, pow_succ]
      ring
    rw [e1, e2, cT_mul, mul_assoc, hstep, ← mul_assoc, ih, mul_assoc,
      map_mul (aeval A) (((C c * X ^ k : K[X]).map s).comp a) a]

end GlobalTheory.CompanionTheory.AdjointPoly
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvolutionCompatiblePolynomial
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.HermFixed

theorem dvd_of_monic_irreducible_factors {K : Type} [Field K] {P d : K[X]} (hs : P.Separable)
    (h : ∀ Q : K[X], Q.Monic → Irreducible Q → Q ∣ P → Q ∣ d) : P ∣ d := by
  by_cases hd : d = 0
  · simp [hd]
  have hP0 : P ≠ 0 := hs.ne_zero
  have hnd : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hs.squarefree
  refine (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP0 hd).2 ?_
  refine (Multiset.le_iff_subset hnd).2 fun Q hQ => ?_
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
  have hmon : Q.Monic := by
    rw [← hnorm]
    exact Polynomial.monic_normalize hirr.ne_zero
  have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
  exact UniqueFactorizationMonoid.mem_normalizedFactors_iff' hd |>.2 ⟨hirr, hnorm, h Q hmon hirr hdvd⟩

theorem dvd_map_comp_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
    (m r₀ : E[X]) (hr : Q.1 ∣ X * r₀ - 1)
    (hfix : invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) :
    Q.1 ∣ (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m := by
  have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 hr
  rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
  have hR : AdjoinRoot.mk Q.1 r₀ = (AdjoinRoot.root Q.1)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hinv : invol Q (AdjoinRoot.mk Q.1 m : Fld Q)
      = AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀) := by
    show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
      (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
    rw [AdjoinRoot.lift_mk, ← hR, Polynomial.comp, Polynomial.hom_eval₂, eval₂_map]
    rfl
  have heq : AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = AdjoinRoot.mk Q.1 m := hinv.symm.trans hfix
  refine AdjoinRoot.mk_eq_zero.1 ?_
  rw [map_sub, heq, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := by
  intro E _ _ _ n γ₀ hell H₀ hH _ hiso m hfix
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hAB : aeval γ₀.val r₀ * γ₀.val = 1 := by rw [← hr₀, Units.inv_mul]
  have key := GlobalTheory.CompanionTheory.AdjointPoly.cT_aeval_mul_eq E (IsCMField.complexConj E).toRingEquiv.toRingHom n
    γ₀.val H₀ r₀ hiso hAB m
  have hdvd : γ₀.val.charpoly ∣
      (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m :=
    dvd_of_monic_irreducible_factors hsep fun Q hmon hirr hQ =>
      dvd_map_comp_sub ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ m r₀
        (hQ.trans hPr) (hfix _ ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ hQ)
  have heq : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = aeval γ₀.val m := by
    obtain ⟨t, ht⟩ := hdvd
    have h0 : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m) = 0 := by
      rw [ht, map_mul, Matrix.aeval_self_charpoly, zero_mul]
    rwa [map_sub, sub_eq_zero] at h0
  have hH' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ = H₀ := hH
  have hmul : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m)
      = cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ₀.val m)
        * cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ := by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  show cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) = H₀ * aeval γ₀.val m
  rw [hmul, hH', key, heq]

end GlobalTheory.CompanionTheory.HermFixed
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvolutionCompatiblePolynomialStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_compatible_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := by
  first | exact @GlobalTheory.CompanionTheory.HermFixed.main | exact GlobalTheory.CompanionTheory.HermFixed.main | (intros; apply GlobalTheory.CompanionTheory.HermFixed.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionCompatible
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.Unfold1F

open GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {t : F} {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E} {lam : Measure R}
  {m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)}
  {m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)}
  {s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)}
  {B₀ : Set R} {a : R → Rˣ} {κ₁ cm : Rˣ → ℝ≥0}

theorem measurableSet_usetF (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    MeasurableSet (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, hsigc, htrc, -, hbw, -, hgramc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, hbor, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hg (M + 1) _ hJ'
  have hq : Continuous fun v : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E =>
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) v) := by
    unfold s0
    exact continuous_const.mul (htrc.comp ((hgramc (n + 1) (M + 1) _).matrix_elem 0 0))
  have hset : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' BsetF R σ B₀) =
      (fun v : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E =>
        s0 R (gramR R σ (blockOne (algebraMap F E t) J) v)) ⁻¹' B₀ := by
    ext v
    constructor
    · rintro ⟨S, hS, hSe⟩
      simpa [BsetF, hSe] using hS
    · intro hv
      refine ⟨g v, ?_, (hg v).symm⟩
      simpa [BsetF, ← hg v] using hv
  have hfree := GlobalTheory.T.linearly_independent_frames_open F E σ D.hCM R D.hR (n + 1) (M + 1)
  unfold UsetF
  rw [hset]
  exact (D.hB₀.preimage hq).measurableSet.inter hfree.measurableSet

theorem chi_eq_zero_F
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀) :
    GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) y = 0 := by
  unfold GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi
  have hz : ∀ Z : Fin n → Fin (M + 1) → R ⊗[F] E,
      (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ (Fin.cons (y 0) Z) = 0 := by
    intro Z
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨⟨S, hS, hSe⟩, -⟩
    apply hy
    rw [← corner_half_trace_gram_cons R σ _ y Z, ← hSe]
    exact hS
  simp [hz]

end Main

theorem first_step_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  have hUm : MeasurableSet (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurableSet_usetF D
  have hφ' := hφ.indicator hUm
  have hchi := measurable_chi D₀ hφ'

  obtain ⟨-, -, -, hbor1, hg1⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R 1
  obtain ⟨g₁, hg₁c, hg₁⟩ := hg1 (M + 1) _ hJ'
  obtain ⟨hUo, -, -, -, -, hae⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  have hU₁ : MeasurableSet {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
      IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} := by
    have : {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} = g₁ ⁻¹' Unt σ R 1 := by
      ext X
      simp [Unt, hg₁ X]
    rw [this]
    exact (hUo.preimage hg₁c).measurableSet
  obtain ⟨hh, hh2, hh3⟩ := hermScal_main F E σ D.hCM R d b
  have hemb : MeasurableEmbedding (hermScal R σ) := (hh.homeomorph _).measurableEmbedding
  have hs0 : ∀ x : R, s0 R ((hermScal R σ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = x :=
    fun x => hh.injective (hh2 (hermScal R σ x))
  set χ := GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) with hχ
  have hzero : ∀ y, s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀ → χ y = 0 :=
    fun y hy => chi_eq_zero_F φ hy

  have e1 : ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hUm]
    exact GlobalTheory.T.lintegral_coordW_succ_eq_iterated_of_unitary_section F E σ D.hCM M _ hJ' R D.hR d b lam D.hlam n (sTil σ J t s a) (measurable_sTil D₀) _ hφ'
  have e2 : ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) =
      ∫⁻ y in {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hU₁]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}
    · exact (Set.indicator_of_mem hy χ).symm
    · rw [Set.indicator_of_notMem hy, hzero y fun h => hy (isUnit_gram D₀ h)]
  have e3 := D.hm₁.2.1 χ hchi
  rw [← hh3 lam D.hlam, hemb.lintegral_map] at e3
  have e4 : ∫⁻ x, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam = ∫⁻ x in B₀, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam := by
    rw [← lintegral_indicator D.hB₀.measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ B₀
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hae (hermScal R σ x)] with y hy
      refine hzero y ?_
      rw [hy, hs0]
      exact hx
  rw [e1, e2, e3, e4]
  refine setLIntegral_congr_fun D.hB₀.measurableSet fun x hx => ?_
  have hm : m₁ (hermScal R σ x) =
      κ₁ (a x) • (m₁ (hermScal R σ (algebraMap F R t))).map (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) := by
    have := D.hscale (a x)
    rwa [← D.hsq x hx] at this
  have hsm : Measurable (scl (N := M + 1) (n := 1) (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) :=
    measurable_scl.comp (measurable_const.prodMk measurable_id)
  simp only [hm]
  rw [lintegral_smul_measure, lintegral_map hchi hsm]
  rfl

end GlobalTheory.CompanionTheory.SW.StageF.Unfold1F
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionCompatibleStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | exact GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free <;> assumption)
end
end

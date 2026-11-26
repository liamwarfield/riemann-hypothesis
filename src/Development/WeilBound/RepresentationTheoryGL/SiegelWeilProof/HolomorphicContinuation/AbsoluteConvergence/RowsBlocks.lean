module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw IwaPf

variable {n : ℕ}

theorem detU1 : CayleyBlocksInvertible := by
  intro n y
  have hg : InG (mR y) := y.2
  refine ⟨det_ne (mR y) hg Complex.I (by norm_num [Complex.ext_iff]), ?_⟩
  show (-(Complex.I • toBlocks₂₁ (mR y)) + toBlocks₂₂ (mR y)).det ≠ 0
  rw [← neg_smul]
  exact det_ne (mR y) hg (-Complex.I) (by norm_num [Complex.ext_iff])

theorem rows_blocks (g : M2 n) (h : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have hr := inG_rows g h
  rw [← fromBlocks_toBlocks g] at hr
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] at hr
  have h22 := congrArg Matrix.toBlocks₂₂ hr
  simp at h22
  exact (neg_add_eq_zero.mp h22).symm

def kmat (U1 U2 : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (U1 + U2)) ((Complex.I / 2) • (U1 - U2)) (-((Complex.I / 2) • (U1 - U2)))
    ((1 / 2 : ℂ) • (U1 + U2))

theorem kmat_unit (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) :
    (kmat U1 U2)ᴴ * kmat U1 U2 = 1 := by
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  rw [← fromBlocks_one]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

theorem kmat_inG (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) : InG (kmat U1 U2) := by
  unfold InG JJ
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, neg_neg, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

private theorem mul_inv_mul_proj_of_ker_iff (g : M2 n) (h : InG g) : u1 g * (u1 g)ᴴ = u2 g * (u2 g)ᴴ := by
  have hr := rows_blocks g h
  simp only [u1, u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hr]
  simp only [Complex.star_def, Complex.conj_I]
  module

private theorem proj_mul_mul_proj_of_ker_iff (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (Y : M2 n) :
    toBlocks₂₁ (Y * (kmat U1 U2)ᴴ) =
      (1 / 2 : ℂ) • (((-Complex.I) • u1 Y) * U1ᴴ + (Complex.I • u2 Y) * U2ᴴ) := by
  rw [← fromBlocks_toBlocks Y]
  simp only [u1, u2, kmat, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, conjTranspose_smul, conjTranspose_add, conjTranspose_sub, conjTranspose_neg,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_neg, smul_sub]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

private theorem inv_mul_unitary_of_mul_conjTranspose_eq (a b : Matrix (Fin n) (Fin n) ℂ) (hab : a * aᴴ = b * bᴴ) (h2d : b.det ≠ 0) :
    (b⁻¹ * a) * (b⁻¹ * a)ᴴ = 1 ∧ a * (b⁻¹ * a)ᴴ = b := by
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr h2d
  have hbH : IsUnit bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr h2d)
  have haV : a * (b⁻¹ * a)ᴴ = b := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, hab, Matrix.mul_assoc,
      mul_nonsing_inv _ hbH, Matrix.mul_one]
  refine ⟨?_, haV⟩
  rw [Matrix.mul_assoc, haV, nonsing_inv_mul b hbu]

theorem iwa : Iwa := by
  intro n y
  have hg : InG (mR y) := y.2
  obtain ⟨_, h2d⟩ := detU1 n y
  obtain ⟨hVV, haV⟩ := inv_mul_unitary_of_mul_conjTranspose_eq (u1 (mR y)) (u2 (mR y)) (mul_inv_mul_proj_of_ker_iff (mR y) hg) h2d
  have hVu := mul_eq_one_comm.mp hVV
  have h1' : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * 1 = 1 := by simp
  have hK := kmat_unit _ 1 hVu h1'
  have hK' := mul_eq_one_comm.mp hK
  let kGL : GL (Fin n ⊕ Fin n) ℂ := ⟨kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1, _, hK', hK⟩
  have hkG : kGL ∈ GR n := kmat_inG _ 1 hVu h1'
  let k : GR n := ⟨kGL, hkG⟩
  have hkK : k ∈ KR n := by
    show InK (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)
    exact ⟨kmat_inG _ 1 hVu h1', hK⟩
  refine ⟨y * k⁻¹, k, ?_, hkK, (inv_mul_cancel_right y k).symm⟩
  show toBlocks₂₁ (mR (y * k⁻¹)) = 0
  have hm : mR (y * k⁻¹) = mR y * (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)ᴴ := rfl
  rw [hm, proj_mul_mul_proj_of_ker_iff, Matrix.smul_mul, Matrix.smul_mul, haV, conjTranspose_one, Matrix.mul_one]
  simp

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
noncomputable section

open MeasureTheory Set Filter Topology Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem factorL : FactorL := by
  intro G _ S l C hC hcont hlin hbd
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hl0 : l 0 = 0 := by
    have h := hbd 0 S.zero_mem 0 (by simp)
    simpa using h
  let lS : S →ₗ[ℂ] ℂ :=
    { toFun := fun F => l F.1
      map_add' := fun F₁ F₂ => by
        have h := hlin 1 F₁.1 F₁.2 F₂.1 F₂.2
        simpa using h
      map_smul' := fun a F => by
        have h := hlin a F.1 F.2 0 S.zero_mem
        simpa [hl0] using h }
  let R : S →ₗ[ℂ] C(C, ℂ) :=
    { toFun := fun F => ⟨fun x => F.1 x, (hcont F.1 F.2).comp continuous_subtype_val⟩
      map_add' := fun F₁ F₂ => by
        ext x
        simp
      map_smul' := fun a F => by
        ext x
        simp }
  have hRnorm : ∀ F : S, ‖l F.1‖ ≤ ‖R F‖ := by
    intro F
    apply hbd F.1 F.2
    intro x hx
    exact (R F).norm_coe_le_norm ⟨x, hx⟩
  have hker : LinearMap.ker R ≤ LinearMap.ker lS := by
    intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h := hRnorm F
    rw [hF, norm_zero] at h
    exact norm_le_zero_iff.mp h
  let f : LinearMap.range R →ₗ[ℂ] ℂ :=
    ((LinearMap.ker R).liftQ lS hker).comp
      (R.quotKerEquivRange.symm : LinearMap.range R →ₗ[ℂ] S ⧸ LinearMap.ker R)
  have hf : ∀ F : S, f ⟨R F, LinearMap.mem_range_self R F⟩ = l F.1 := by
    intro F
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hfb : ∀ v : LinearMap.range R, ‖f v‖ ≤ 1 * ‖v‖ := by
    rintro ⟨v, F, rfl⟩
    rw [hf F, one_mul]
    exact hRnorm F
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range R) (f.mkContinuous 1 hfb)
  refine ⟨g, fun F hFS hF => ?_⟩
  have h1 := hg ⟨R ⟨F, hFS⟩, LinearMap.mem_range_self R _⟩
  rw [LinearMap.mkContinuous_apply, hf] at h1
  exact h1.symm

theorem kRCpt : KRCpt := by
  intro n
  let S : Set (M2 n) := {g | InG g ∧ gᴴ * g = 1}
  have hcl : IsClosed S := by
    show IsClosed ({g : M2 n | InG g} ∩ {g : M2 n | gᴴ * g = 1})
    apply IsClosed.inter
    · exact isClosed_eq
        ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hsub : S ⊆ univ.pi (fun _ => univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro g hg i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu : g ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hg.2
    exact entry_norm_bound_of_unitary hu i j
  have hcpt : IsCompact S :=
    (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) 1))).of_isClosed_subset
      hcl hsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hcpt
  have hinv : ∀ g : S, g.1 * g.1ᴴ = 1 := fun g => mul_eq_one_comm.mp g.2.2
  let u : S → GL (Fin n ⊕ Fin n) ℂ := fun g => ⟨g.1, g.1ᴴ, hinv g, g.2.2⟩
  have hu : Continuous u :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩
  let ψ : S → KR n := fun g => ⟨⟨u g, g.2.1⟩, g.2⟩
  have hψ : Continuous ψ := (hu.subtype_mk _).subtype_mk _
  have hsurj : Function.Surjective ψ := by
    intro k
    refine ⟨⟨mR k.1, k.2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  exact Function.Surjective.compactSpace hψ hsurj

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TwistedScalarSection
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def aZ {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def twistedScalarSection {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) : ℂ := M.det ^ e * f0 p q M

def TSBFacts : Prop :=
  CayleyBlocksInvertible → ∀ (n p q : ℕ) (e : ℤ),
    CompactSpace (KR n) ∧ Continuous (mR : GR n → M2 n) ∧ Continuous (F0 p q e : GR n → ℂ) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ), ∃ a : GR n, IsDil X t a) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ) (a : GR n), IsDil X t a → mR a = aZ X t) ∧
    ∀ (X : Fin n → ℝ) (C : Set (GR n)), IsCompact C → ∃ U : Set ℂ, IsOpen U ∧ (∀ t : ℝ, (t : ℂ) ∈ U) ∧
      ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U) ∧
      ∀ y ∈ C, DifferentiableOn ℂ (fun z => twistedScalarSection p q e (mR y * aZ X z)) U

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_group_lower_left_block : Continuous (fun g : GR n => (mR g).toBlocks₂₁) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inl

theorem continuous_group_lower_right_block : Continuous (fun g : GR n => (mR g).toBlocks₂₂) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inr

theorem continuous_first_cayley_block_map : Continuous (fun g : GR n => u1 (mR g)) := by
  unfold u1
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).add continuous_group_lower_right_block

theorem continuous_second_cayley_block_map : Continuous (fun g : GR n => u2 (mR g)) := by
  unfold u2
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).neg.add continuous_group_lower_right_block

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hdet : Continuous (fun g : GR n => (mR g).det) := continuous_mR.matrix_det
  have h1 : Continuous (fun g : GR n => (u1 (mR g)).det) := continuous_first_cayley_block_map.matrix_det
  have h2 : Continuous (fun g : GR n => (u2 (mR g)).det) := continuous_second_cayley_block_map.matrix_det
  have hne : ∀ g : GR n, (mR g).det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g : GL (Fin n ⊕ Fin n) ℂ))).ne_zero
  show Continuous (fun g : GR n =>
    (mR g).det ^ e * ((u1 (mR g)).det ^ (-(p : ℤ)) * (u2 (mR g)).det ^ (-(q : ℤ))))
  exact (hdet.zpow₀ e fun g => Or.inl (hne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  unfold hLoc
  exact ((continuous_first_cayley_block_map.matrix_det).norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

theorem hLoc_nonneg (g : GR n) : 0 ≤ hLoc g := by
  unfold hLoc
  positivity

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

theorem first_cayley_block_one : u1 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u1, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem second_cayley_block_one : u2 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u2, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 (n := n) p q e 1 = 1 := by
  simp only [F0, f0, first_cayley_block_one, second_cayley_block_one]
  simp [mR]

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerSt
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def NDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n) (H : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → ∀ f : ℝ → GR n, (∀ σ : ℝ, mR (f σ) = nU ((σ : ℂ) • H)) → ∀ g : GR n,
      (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ, HasDerivAt (fun σ : ℝ => sL R (g * f σ)) (sL (DN ε t H R) (g * f s)) s

def MDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n) (H : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → ∀ f : ℝ → GR n,
      (∀ σ : ℝ, mR (f σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H)))) →
      ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ,
        HasDerivAt (fun σ : ℝ => sL R (g * f σ)) (sL (DM ε c H R) (g * f s)) s

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjSt
noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

def kM {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (a + b)) ((Complex.I / 2) • (a - b)) (-((Complex.I / 2) • (a - b))) ((1 / 2 : ℂ) • (a + b))

def KIso : Prop := ∀ n : ℕ,
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, a ∈ unitaryGroup (Fin n) ℂ → b ∈ unitaryGroup (Fin n) ℂ →
      ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b) ∧
  (∀ a b a' b' : Matrix (Fin n) (Fin n) ℂ, kM a b * kM a' b' = kM (a * a') (b * b')) ∧ kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 ∧
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, u1 (kM a b) = a ∧ u2 (kM a b) = b) ∧
  (∀ a : Matrix (Fin n) (Fin n) ℂ, (kM a a).toBlocks₂₁ = 0) ∧
  ∀ k : GR n, k ∈ KR n → u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
    mR k = kM (u1 (mR k)) (u2 (mR k))

def RepKer : Prop := ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (V : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ V →
    (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ a : H, (fun x => φ (a * x)) ∈ V) →
    ∃ κ : H → ℂ, Continuous κ ∧ (∀ f : H → ℂ, Continuous f → (fun x => ∫ v, κ v * f (x * v) ∂μ) ∈ V) ∧
      ∀ φ ∈ V, ∀ x, ∫ v, κ v * φ (x * v) ∂μ = φ x

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FlatEq
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def FlatEq : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (Q Q' : PX m n),
    (∀ k : GR n, InK (mR k) → sL Q k = sL Q' k) → ∀ y, sL Q y = sL Q' y

def Basis : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)],
    ∀ W : Submodule ℂ (PX m n), FiniteDimensional ℂ W → (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) →
    ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν → Continuous κ →
      (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
      (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
      ∀ P ∈ W, ∃ (N : ℕ) (yy : Fin N → GR n) (QQ : Fin N → PX m n) (cc : Fin N → ℂ) (M : ℂ → Matrix (Fin N) (Fin N) ℂ),
        (∀ j, QQ j ∈ W) ∧ (∀ y, sL P y = ∑ j, cc j * sL (QQ j) y) ∧ M 0 = 1 ∧ (∀ i j, Differentiable ℂ fun w => M w i j) ∧
        (∀ i, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * yy i) ∂ν = sL (QQ i) y') ∧
        ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν =
          (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y'

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BlocksRel
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem ext_mR {g h : GR n} (e : mR g = mR h) : g = h := Subtype.ext (Units.ext e)

def dg (X : Fin n → ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)

theorem dg_mul (X : Fin n → ℝ) (s s' : ℝ) : dg X s * dg X s' = dg X (s + s') := by
  rw [dg, dg, dg, diagonal_mul_diagonal]
  congr 1
  funext j
  rw [← Complex.ofReal_mul, ← Real.exp_add, add_mul]

theorem dg_zero (X : Fin n → ℝ) : dg X 0 = 1 := by
  simp [dg]

theorem isDil_iff {X : Fin n → ℝ} {s : ℝ} {g : GR n} (h : IsDil X s g) :
    mR g = fromBlocks (dg X s) 0 0 (dg X (-s)) := by
  rw [h]
  simp only [dg, neg_mul]

theorem dil_mul {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s s' : ℝ) :
    a (s + s') = a s * a s' := by
  apply ext_mR
  rw [mR_mul, isDil_iff (ha _), isDil_iff (ha _), isDil_iff (ha _), fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, dg_mul, neg_add]

theorem dil_zero {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : a 0 = 1 := by
  apply ext_mR
  rw [isDil_iff (ha _), mR_one, neg_zero, dg_zero, fromBlocks_one]

theorem dil_up {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : IsUp (a s) := by
  show toBlocks₂₁ (mR (a s)) = 0
  rw [isDil_iff (ha s), toBlocks_fromBlocks₂₁]

theorem dil_inv {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : (a s)⁻¹ = a (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← dil_mul ha, add_neg_cancel, dil_zero ha]

theorem up_mul {y g : GR n} (hy : IsUp y) (hg : IsUp g) : IsUp (y * g) := by
  show toBlocks₂₁ (mR (y * g)) = 0
  have hy' : toBlocks₂₁ (mR y) = 0 := hy
  have hg' : toBlocks₂₁ (mR g) = 0 := hg
  rw [mR_mul, ← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR g), hy', hg',
    fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem cont_dil {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : Continuous a := by
  have hc : Continuous fun s : ℝ => fromBlocks (dg X s) 0 0 (dg X (-s)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        dg, diagonal_apply, Matrix.zero_apply] <;> (try split_ifs) <;> fun_prop
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨hc.congr fun s => (isDil_iff (ha s)).symm, ?_⟩
  refine (hc.comp continuous_neg).congr fun s => ?_
  simp only [Function.comp_apply]
  rw [← isDil_iff (ha (-s)), ← dil_inv ha s]
  rfl

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilations
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun a => ε a = false) = Finset.univ.filter fun a => ¬ ε a = true := by
    ext a; simp
  rw [h2]
  exact h

theorem bS_herm (X : Fin n → ℝ) (h : ℝ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : (bS X h b).IsHermitian := by
  have hD : (diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)))ᴴ = diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    exact Complex.conj_ofReal _
  unfold bS Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD, hb.eq, Matrix.mul_assoc]

theorem derivative_vacuum_of_parts (hG : GaussPart) (hH : GroupPart) : DerivativeVacuumDilations := by
  intro m n ε c t p q e sL ρ hL X a hA y r
  obtain ⟨hadd, ha0, hup, hcont, hupmul, hdec, hconj, hcellinv, hdense, hF0⟩ := hH n X a hA
  obtain ⟨C, hC0, hcell⟩ := hL.cell
  have hpq : p + q = m := by
    rcases hL.sign with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact cnt_add ε
    · rw [add_comm]; exact cnt_add ε
  have hneg : ∀ h : ℝ, a (-h) * a h = 1 := by
    intro h; rw [← hadd, neg_add_cancel, ha0]

  have L1 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 →
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) y) 0 := by
    intro Q y hy
    obtain ⟨y₁, g, b, hy₁, hb, hg, rfl⟩ := hdec y hy
    have hfun : (fun h => sL Q (y₁ * g * a h)) = fun h => (F0 p q e y₁ * C) *
        (Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) := by
      funext h
      have e1 : y₁ * g * a h = (y₁ * a (-h)) * (a h * g * a h) := by
        calc y₁ * g * a h = y₁ * (a (-h) * a h) * g * a h := by rw [hneg, mul_one]
          _ = _ := by group
      have e2 : F0 p q e (y₁ * a (-h)) = F0 p q e y₁ * F0 p q e (a (-h)) := by
        rw [← hL.vac, hL.law 1 _ _ hy₁, hL.vac]
      have e3 : F0 p q e (a (-h)) = Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) := by
        rw [hF0, hpq]
      rw [e1, hL.law Q _ _ (hupmul y₁ hy₁ (-h)), e2, e3, hcell Q _ _ (bS_herm X h hb) (hconj g b hg h)]
      ring
    rw [hfun]
    have hv : sL (dil c X Q) (y₁ * g) = (F0 p q e y₁ * C) * secN ε c t (dil c X Q) b := by
      rw [hL.law _ _ _ hy₁, hcell _ _ _ hb hg]; ring
    rw [hv]
    exact (hG m n ε c t hL.cpos X b hb Q).const_mul _

  have L2 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∀ s,
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y hy s
    have h0 := L1 Q (y * a s) (hcellinv y hy s)
    have h0' : HasDerivAt (fun h => sL Q (y * a s * a h)) (sL (dil c X Q) (y * a s)) (s - s) := by
      rw [sub_self]; exact h0
    have h1 := HasDerivAt.comp_sub_const s s h0'
    have hf : (fun x => sL Q (y * a x)) = fun x => sL Q (y * a s * a (x - s)) := by
      funext x
      rw [mul_assoc, ← hadd, add_sub_cancel]
    rw [hf]
    exact h1
  have hjc : ∀ (Q : PX m n), Continuous (fun z : GR n × ℝ => sL Q (z.1 * a z.2)) := fun Q =>
    (hL.cont Q).comp (continuous_fst.mul (hcont.comp continuous_snd))

  have L3 : ∀ (Q : PX m n) (s : ℝ) (y : GR n),
      sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) := by
    intro Q s
    have hc1 : Continuous fun y : GR n => sL Q (y * a s) - sL Q y :=
      ((hL.cont Q).comp (continuous_id.mul continuous_const)).sub (hL.cont Q)
    have hc2 : Continuous fun y : GR n => ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hjc (dil c X Q)) continuous_const
    intro y0
    refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) y0
    intro y hy
    show sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u)
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a x)) x :=
      fun x _ => L2 Q y hy x
    have hint : IntervalIntegrable (fun u => sL (dil c X Q) (y * a u)) volume 0 s :=
      ((hL.cont (dil c X Q)).comp (continuous_const.mul hcont)).intervalIntegrable 0 s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, ha0, mul_one]
  have L4 : ∀ (Q : PX m n) (y : GR n) (s : ℝ),
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y s
    have hgc : Continuous fun u => sL (dil c X Q) (y * a u) := (hL.cont _).comp (continuous_const.mul hcont)
    have h1 := (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
    have h2 := h1.const_add (sL Q y)
    have hf : (fun h => sL Q (y * a h)) = fun x => sL Q y + ∫ u in (0 : ℝ)..x, sL (dil c X Q) (y * a u) := by
      funext x
      rw [← L3 Q x y]; ring
    rw [hf]
    exact h2
  have L5 : ∀ k : ℕ, iteratedDeriv k (fun s => F0 p q e (y * a s)) = fun s => sL ((dil c X ^ k) 1) (y * a s) := by
    intro k
    induction k with
    | zero => funext s; simp [hL.vac]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(L4 _ y s).deriv, pow_succ', Module.End.mul_apply]
  refine ⟨?_, ?_⟩
  · rw [L5 r]
    have := L4 ((dil c X ^ r) 1) y 0
    rw [ha0, mul_one, ← Module.End.mul_apply, ← pow_succ'] at this
    exact this
  · rw [L5 r]
    show sL ((dil c X ^ r) 1) (y * a 0) = _
    rw [ha0, mul_one]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

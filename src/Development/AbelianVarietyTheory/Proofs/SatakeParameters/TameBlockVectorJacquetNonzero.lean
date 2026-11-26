module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

abbrev sizes (r t : ℕ) : Fin (t + 1) → ℕ := Fin.cons r (fun _ => 1)

theorem sum_sizes (r t : ℕ) : ∑ a, sizes r t a = r + t := by simp [sizes, Fin.sum_cons]

def blocks (r t : ℕ) : (Σ a : Fin (t + 1), Fin (sizes r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sizes r t)

theorem blocks_zero (r t : ℕ) (i : Fin r) : blocks r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  have hv := stdBlocks_val (sizes r t) (sum_sizes r t) 0 i
  haveI : IsEmpty (Fin ((0 : Fin (t + 1)) : ℕ)) := by simp only [Fin.val_zero]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hv
  exact hv

theorem blocks_succ (r t : ℕ) (j : Fin t) (i : Fin (sizes r t j.succ)) :
    blocks r t ⟨j.succ, i⟩ = Fin.natAdd r j := by
  ext
  have hi : (i : ℕ) = 0 := by have := i.2; simp [sizes] at this; omega
  simp [blocks, stdBlocks_val, hi, Fin.sum_univ_succ, sizes]

def zeroIdx (r t : ℕ) (j : Fin t) : Fin (sizes r t j.succ) := ⟨0, by simp [sizes]⟩

theorem natAdd_eq (r t : ℕ) (j : Fin t) : Fin.natAdd r j = blocks r t ⟨j.succ, zeroIdx r t j⟩ :=
  (blocks_succ r t j _).symm

theorem blk_castAdd (r t : ℕ) (i : Fin r) : blk (blocks r t) (Fin.castAdd t i) = 0 := by
  unfold blk; rw [← blocks_zero, Equiv.symm_apply_apply]

theorem blk_natAdd (r t : ℕ) (j : Fin t) : blk (blocks r t) (Fin.natAdd r j) = j.succ := by
  unfold blk; rw [natAdd_eq, Equiv.symm_apply_apply]

theorem natAdd_ne_castAdd {r t : ℕ} (i : Fin t) (j : Fin r) : Fin.natAdd r i ≠ Fin.castAdd t j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem det_of_lowerLeft {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0) :
    M.det = (M.submatrix (Fin.castAdd t) (Fin.castAdd t)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; simp [Matrix.toBlocks₂₁, h0]
  rw [this, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem det_lowerRight {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0)
    (h1 : M.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1) :
    (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = M.det := by
  rw [det_of_lowerLeft M h0, h1, det_one, one_mul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def stab {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (v : W) : Subgroup G :=
  GlobalTheory.DoubleCosetSetoid.repStabilizer ρ v

theorem KOne_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsTame χ) {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    KOne k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  have hKO := GlobalTheory.StepData.KOne_le_KO hh
  have hm := GlobalTheory.StepData.mem_KOne.1 hh
  have hM : GlobalTheory.StepData.MaxM (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) - 1) := by
    intro i j
    have := hm (Fin.natAdd r i) (Fin.natAdd r j)
    simpa [Matrix.one_apply] using this
  obtain ⟨g', hg', hgv⟩ := GlobalTheory.StepData.exists_mem_KOne hM
  have hu := GlobalTheory.StepData.det_of_mem_KOne hg'
  have key := hv h hKO (fun i j => by
      have := hm (Fin.natAdd r i) (Fin.castAdd t j)
      simpa [Matrix.one_apply, natAdd_ne_castAdd i j] using this)
    (fun i j => by
      have := hm (Fin.castAdd t i) (Fin.castAdd t j)
      simpa [Matrix.one_apply] using this)
    (Matrix.GeneralLinearGroup.det g') (by rw [Matrix.GeneralLinearGroup.val_det_apply, hgv])
  show π h v = v
  rw [key, hχ _ hu, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipRad_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (blocks r t) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hh.1
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j =>
    mem_parab.1 hP _ _ (by rw [blk_castAdd, blk_natAdd]; exact Fin.succ_pos i)
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rw [← blocks_zero]
      exact (hD 0 i i).trans (Matrix.one_apply_eq _)
    · rw [if_neg hij]
      rw [← blocks_zero, ← blocks_zero]
      exact (hD 0 i j).trans (Matrix.one_apply_ne hij)
  have hdet : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 1 := by
    rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply, det_eq_one_of_mem_unipRad k hh.1,
      Units.val_one]
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by
      have := congrFun (congrFun h1 i) j
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) 1 (by rw [hdet, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_leviEmb {α n : Type} {m : α → Type} [Fintype α] [DecidableEq α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (y : Levi k m) (hy : ∀ a, GlobalTheory.StepData.IntM (y a).val) :
    GlobalTheory.StepData.IntM (leviEmb k e y).val := by
  intro p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective q
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    exact hy a i j
  · rw [leviEmb_apply_ne k e y h]
    exact zero_mem _

abbrev single {r t : ℕ} (j : Fin t) (g : GL (Fin (sizes r t j.succ)) k) : Levi k (fun a => Fin (sizes r t a)) :=
  Pi.mulSingle j.succ g

theorem single_mem_KO {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) (a : Fin (t + 1)) : single j g a ∈ KO k (Fin (sizes r t a)) := by
  by_cases ha : a = j.succ
  · subst ha
    rw [single, Pi.mulSingle_eq_same]
    exact hg
  · rw [single, Pi.mulSingle_eq_of_ne ha]
    exact one_mem _

theorem deltaHalf_single {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) : deltaHalf k (fun a => Fin (sizes r t a)) (single j g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (single_mem_KO j hg a)

theorem act_single {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) (j : Fin t)
    {g : GL (Fin (sizes r t j.succ)) k} (hg : g ∈ KO k (Fin (sizes r t j.succ))) :
    π (leviEmb k (blocks r t) (single j g)) v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (blocks r t) (single j g) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (single_mem_KO j hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (single_mem_KO j hg a))
  have h0 : ∀ (i : Fin t) (j' : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j') = 0 := fun i j' => by
    rw [natAdd_eq, ← blocks_zero]
    exact leviEmb_apply_ne k _ _ (Fin.succ_ne_zero i) _ _
  have hx0 : single j g 0 = 1 := Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j).symm _
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    have hx0' : ((single j g 0 : GL (Fin (sizes r t 0)) k) : Matrix (Fin (sizes r t 0)) (Fin (sizes r t 0)) k) = 1 := by
      rw [hx0, Units.val_one]
    ext i i'
    rw [Matrix.submatrix_apply, ← blocks_zero, ← blocks_zero, hdef]
    exact (leviEmb_apply_same k (blocks r t) (single j g) 0 i i').trans (congrFun (congrFun hx0' i) i')
  have key := hv h hKO (fun i j' => by simp [h0]) (fun i j' => by
      have := congrFun (congrFun h1 i) j'
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) (Matrix.GeneralLinearGroup.det g) (by
      rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply h, hdef, det_leviEmb k,
        Finset.prod_eq_single j.succ (fun b _ hb => by rw [single, Pi.mulSingle_eq_of_ne hb, map_one]) (by simp),
        single, Pi.mulSingle_eq_same])
  exact key

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

theorem exists_jacquet_ne_zero_of_isBlockVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (e : (Σ a : Fin (t + 1), Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) a)) ≃ Fin (r + t)) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), x ≠ 0 ∧ ∀ (j : Fin t) (g : GL (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) k), g ∈ GlobalTheory.SplitWeil.KO k (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) → GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j.succ g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x := by
  intro hP k _ _ _ _ r t χ π v hχ hv0 hv
  refine ⟨blocks r t, Submodule.Quotient.mk v, ?_, ?_⟩
  · intro hx
    apply hv0
    refine hP k (r + t) (t + 1) _ (blocks r t) π v ?_ hx
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro j g hg
    rw [GlobalTheory.SmGL.jac_mk, deltaHalf_single j hg, act_single hv j hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlock

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzeroStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_block_vector_jacquet_nonzero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (e : (Σ a : Fin (t + 1), Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) a)) ≃ Fin (r + t)) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), x ≠ 0 ∧ ∀ (j : Fin t) (g : GL (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) k), g ∈ GlobalTheory.SplitWeil.KO k (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) → GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j.succ g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x := by
  first | exact @GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec | exact GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec | (intros; apply GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne

namespace TwistAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem matrix_eq_zero_of_isNilpotent {K : Type*} [Field K] {M : Matrix (Fin 1) (Fin 1) K}
    (hM : IsNilpotent M) : M = 0 := by
  have h1 := Matrix.isNilpotent_trace_of_isNilpotent hM
  rw [Matrix.trace_fin_one] at h1
  ext i j
  fin_cases i; fin_cases j
  simpa using h1.eq_zero

theorem end_eq_zero_of_isNilpotent {f : Module.End ℂ (Fin 1 → ℂ)} (hf : IsNilpotent f) : f = 0 := by
  have h1 := matrix_eq_zero_of_isNilpotent (hf.map
    (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ))
  have h2 : (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) f =
      (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) 0 := by
    rw [h1, map_zero]
  exact (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ).injective h2

theorem twGL_det_val (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l))
    (g : G E Ω) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • (ρ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Algebra.smul_def]

variable {t : Ine (F := E) A →* Multiplicative ℤ_[l]}

theorem isMonodromy_zero_of_line {χ : G E Ω →* GL (Fin 1) (Qbar l)} {N : Matrix (Fin 1) (Fin 1) (Qbar l)}
    (hN : IsMonodromy t χ N) : IsMonodromy t χ 0 := by
  rwa [matrix_eq_zero_of_isNilpotent hN.1] at hN

theorem isMonodromy_twGL {ρ : G E Ω →* GL (Fin a) (Qbar l)} {χ : G E Ω →* GL (Fin 1) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} (hN : IsMonodromy t ρ N) (hχ : IsMonodromy t χ 0) :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨-, U', hU', H'⟩ := hχ
  refine ⟨h1, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [twGL_det_val, H' σ hσ.2, H σ hσ.1]
  simp

theorem wdMat_twGL {φ : Weil h} (hφ : deg φ = 1) (ρ : G E Ω →* GL (Fin a) (Qbar l))
    (χ : G E Ω →* GL (Fin 1) (Qbar l)) (N : Matrix (Fin a) (Fin a) (Qbar l)) (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N g =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • wdMat t hφ ρ N g := by
  rw [wdMat, wdMat, twGL_det_val, smul_mul_assoc]

theorem isFrobSS_tensor_line {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {N : Module.End ℂ V} {a₀ : WDRep h V}
    {ψ : Weil h → Module.End ℂ (Fin 1 → ℂ)} {b₀ : WDRep h (Fin 1 → ℂ)}
    (ha : IsFrobSS ρ N a₀) (hb : IsFrobSS ψ 0 b₀) :
    IsFrobSS (fun g => TensorProduct.map (ρ g) (ψ g)) (N.rTensor (Fin 1 → ℂ)) (a₀.tensor b₀) := by
  have hψ : ∀ g, b₀.ρ g = ψ g := fun g =>
    (sub_eq_zero.mp (end_eq_zero_of_isNilpotent (hb.2 g).2)).symm
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1, LinearMap.lTensor_zero, add_zero], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ, hψ]
    show TensorProduct.map _ _ * TensorProduct.map _ _ = TensorProduct.map _ _ * TensorProduct.map _ _
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, (ha.2 g).1.eq]
  · rw [WDRep.tensor_ρ, hψ]
    have e1 : TensorProduct.map (ρ g) (ψ g) - TensorProduct.map (a₀.ρ g) (ψ g) =
        (ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ) * (ψ g).lTensor V :=
      TensorProduct.ext' fun x y => by simp [TensorProduct.sub_tmul]
    rw [e1]
    have hc : Commute ((ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ)) ((ψ g).lTensor V) := by
      show _ * _ = _ * _
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    exact hc.isNilpotent_mul_right ((ha.2 g).2.map (Module.End.rTensorAlgHom ℂ V (Fin 1 → ℂ)))

def lineEquiv (V : Type) [AddCommGroup V] [Module ℂ V] : TensorProduct ℂ V (Fin 1 → ℂ) ≃ₗ[ℂ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V)

@[simp] theorem lineEquiv_tmul (V : Type) [AddCommGroup V] [Module ℂ V] (x : V) (y : Fin 1 → ℂ) :
    lineEquiv V (x ⊗ₜ y) = y 0 • x := by
  simp [lineEquiv]

end TwistAway


open TwistAway in
theorem wdOf_twGL_det : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf h hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf h hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.WeilDeligne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.TwistAway in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (h := h) hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAdd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DirectSumLocal

open Module

noncomputable def splitEquiv (k : Type) [Field k] (a b : ℕ) : (Fin (a + b) → k) ≃ₗ[k] (Fin a → k) × (Fin b → k) :=
  (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) k k)

theorem splitEquiv_sumRep {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r₁ : Γ →* GL (Fin a) k)
    (r₂ : Γ →* GL (Fin b) k) (g : Γ) (v : Fin (a + b) → k) :
    splitEquiv k a b ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : Matrix _ _ k).mulVec v) =
      (((r₁ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).1, ((r₂ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).2) := by
  ext i
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl

end GlobalTheory.DirectSumLocal

namespace GlobalTheory.DirectSumLocal

theorem isdRE_sumRep_and_multE_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ) (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1), (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧ ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ), Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw LL' a b r₁ r₂
  obtain ⟨T⟩ := hT
  have he : ∀ g v, splitEquiv (↥LL'.1) a b (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) g v) =
      (Bw.repE LL' r₁ g (splitEquiv (↥LL'.1) a b v).1, Bw.repE LL' r₂ g (splitEquiv (↥LL'.1) a b v).2) := by
    intro g v
    exact splitEquiv_sumRep r₁ r₂ _ v
  obtain ⟨h1, -, h3⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T Bw.Kw LL' (Fin (a + b) → ↥LL'.1)
    (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂)) (Fin a → ↥LL'.1) (Bw.repE LL' r₁) (Fin b → ↥LL'.1)
    (Bw.repE LL' r₂) (splitEquiv (↥LL'.1) a b) he
  refine ⟨?_, fun τ' c => h3 τ' c⟩
  unfold Formalism.BasicNotions.LocBridge.IsdRE
  unfold Formalism.MainNotions.N.IsDR at h1
  simpa only [Module.finrank_fin_fun] using h1

end GlobalTheory.DirectSumLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAddStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ) (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1), (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧ ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ), Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := by
  first | exact @GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add | exact GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add | (intros; apply GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.EmptyFirstBlock

section Reindex

variable {R : Type} [CommRing R] {t : ℕ} {c : Bool → ℕ}

def trueEquiv (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) : Fin (c true) ≃ Fin t :=
  Equiv.ofBijective (fun i => f ⟨true, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact absurd i.2 (by omega)
    | true => exact ⟨i, rfl⟩⟩

def reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    GL m R →* GL n R :=
  Units.map (Matrix.reindexAlgEquiv R R e).toRingEquiv.toMonoidHom

theorem val_reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m R) (i j : n) :
    (reindexGL e g : Matrix n n R) i j = (g : Matrix m m R) (e.symm i) (e.symm j) := rfl

theorem det_reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m R) : Matrix.GeneralLinearGroup.det (reindexGL e g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  have : (reindexGL e g : Matrix n n R) = (g : Matrix m m R).submatrix e.symm e.symm := by
    ext i j; rfl
  rw [this, Matrix.det_submatrix_equiv_self]

def liftT (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (h : GL (Fin t) R) :
    SmGL.Levi R (fun j => Fin (c j)) :=
  Pi.mulSingle (M := fun j => GL (Fin (c j)) R) true (reindexGL (trueEquiv f hc).symm h)

theorem leviEmb_liftT (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (h : GL (Fin t) R) :
    SmGL.leviEmb R f (liftT f hc h) = h := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | false => exact absurd i.2 (by omega)
  | true =>
    cases b with
    | false => exact absurd j.2 (by omega)
    | true =>
      rw [SmGL.leviEmb_apply_same]
      simp [liftT, val_reindexGL, trueEquiv]
      rfl

theorem eq_one_of_mem_unipRad (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) {g : GL (Fin t) R}
    (hg : g ∈ SmGL.unipRad R f) : g = 1 := by
  obtain ⟨-, h2⟩ := SmGL.mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | false => exact absurd i.2 (by omega)
  | true =>
    cases b with
    | false => exact absurd j.2 (by omega)
    | true =>
      rw [h2 true i j]
      simp [Matrix.one_apply]

end Reindex

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {t : ℕ} {c : Bool → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem twKer_eq_bot (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    (π : Representation ℂ (GL (Fin t) k) W) : twKer π (SmGL.unipRad k f) 1 = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro _ ⟨n, v, rfl⟩
  have : (n : GL (Fin t) k) = 1 := eq_one_of_mem_unipRad f hc n.2
  simp [this]

theorem deltaHalf_eq_one (hc : c false = 0) (g : SmGL.Levi k (fun j => Fin (c j))) :
    SmGL.deltaHalf k (fun j => Fin (c j)) g = 1 := by
  haveI : IsEmpty (Fin (c false)) := by rw [hc]; infer_instance
  rw [SmGL.deltaHalf_apply, Fintype.prod_bool]
  have h1 : SmGL.modExp (fun j => Fin (c j)) true = 0 := by
    simp only [SmGL.modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g false) = 1 := by
    ext; simp [Matrix.det_isEmpty]
  have h0 : SmGL.absPow k 0 = 1 := by
    ext x; simp [SmGL.val_absPow]
  rw [h1, h2]
  simp [h0]

theorem jac_liftT_mk (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    (π : Representation ℂ (GL (Fin t) k) W) (h : GL (Fin t) k) (w : W) :
    SmGL.jac f π (liftT f hc h) (Submodule.Quotient.mk w) = Submodule.Quotient.mk (π h w) := by
  rw [SmGL.jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, leviEmb_liftT]

theorem subrep_dichotomy (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    {π : Representation ℂ (GL (Fin t) k) W} (hπ : π.IsIrreducible)
    (S : Subrepresentation (SmGL.jac f π)) : S = ⊥ ∨ S = ⊤ := by
  let T : Subrepresentation π := ⟨S.toSubmodule.comap (twKer π (SmGL.unipRad k f) 1).mkQ,
    fun h w hw => by
      show Submodule.Quotient.mk (π h w) ∈ S.toSubmodule
      rw [← jac_liftT_mk f hc]
      exact S.apply_mem_toSubmodule _ hw⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun u hu => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : w ∈ T.toSubmodule := hu
    rw [h] at this
    have hw : w = 0 := (Submodule.mem_bot ℂ).1 this
    rw [hw]
    exact Submodule.zero_mem _
  · right
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun u _ => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : w ∈ T.toSubmodule := by rw [h]; trivial
    exact this

end Main

end GlobalTheory.EmptyFirstBlock

namespace GlobalTheory.EmptyFirstBlock

section Tensor

theorem tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (x : ∀ i, X i) (hx : ∀ i, x i ≠ 0) : PiTensorProduct.tprod ℂ x ≠ 0 := by
  have : ∀ i, ∃ φ : Module.Dual ℂ (X i), φ (x i) ≠ 0 := fun i => by
    by_contra h
    push_neg at h
    exact hx i ((Module.forall_dual_apply_eq_zero_iff ℂ (x i)).1 h)
  choose φ hφ using this
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h0
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at this
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hφ i) this

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reindexGL_mem_KO {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {h : GL m k} (hh : h ∈ KO k m) : reindexGL e h ∈ KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  exact ⟨reindexGL e h0, Units.ext (Matrix.ext fun i j => rfl)⟩

theorem isSpherical_twist_of_empty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin t) k) W) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin t) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (χ : kˣ →* ℂˣ) (z : (s true).V), IsSmooth π → π.IsIrreducible → c false = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (GlobalTheory.SmGL.jac f π) → z ≠ 0 → (∀ g ∈ KO k (Fin (c true)), (s true).ρ g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z) → IsSpherical (GlobalTheory.SmGL.twist π (detChar (Fin t) χ⁻¹)) := by
  intro k _ _ _ _ t W _ _ π c f s χ z _ hπ hc hsub hz0 hz
  haveI := nontrivial_of_irreducible (s false).irr
  obtain ⟨w0, hw0⟩ := exists_ne (0 : (s false).V)
  let x : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) w0 z j
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    cases j
    · exact hw0
    · exact hz0
  have hX : PiTensorProduct.tprod ℂ x ≠ 0 := tprod_ne_zero x hx
  obtain ⟨S, F, hF⟩ := hsub
  rcases subrep_dichotomy f hc hπ S with rfl | rfl
  · exfalso
    obtain ⟨u, hu⟩ := hF (PiTensorProduct.tprod ℂ x)
    exact hX (by rw [← hu, show u = 0 from Subtype.ext u.2, map_zero])
  let j : (SmGL.jac f π).IntertwiningMap (⊤ : Subrepresentation (SmGL.jac f π)).toRepresentation :=
    ⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩
  let G := F.comp j
  have hG : Function.Surjective G := fun w => by
    obtain ⟨u, rfl⟩ := hF w
    exact ⟨u.1, rfl⟩
  have hGi : Function.Injective G := by
    refine (injective_iff_map_eq_zero G).2 fun y hy => ?_
    rcases subrep_dichotomy f hc hπ G.ker with h | h
    · have : y ∈ G.ker := hy
      rw [h] at this
      exact this
    · exfalso
      obtain ⟨u, hu⟩ := hG (PiTensorProduct.tprod ℂ x)
      have : u ∈ G.ker := by rw [h]; trivial
      exact hX (hu ▸ this)
  obtain ⟨u, hu⟩ := hG (PiTensorProduct.tprod ℂ x)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hX
    rw [← hu, Submodule.Quotient.mk_zero, map_zero]
  have key : ∀ h ∈ KO k (Fin t), π h v = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • v := by
    intro h hh
    have hg' : reindexGL (trueEquiv f hc).symm h ∈ KO k (Fin (c true)) := reindexGL_mem_KO _ hh
    have hdet := det_reindexGL (R := k) (trueEquiv f hc).symm h
    have htens : (piTensor fun j => (s j).ρ) (liftT f hc h) (PiTensorProduct.tprod ℂ x) =
        (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • PiTensorProduct.tprod ℂ x := by
      rw [piTensor_tprod]
      have hfun : (fun a => (s a).ρ (liftT f hc h a) (x a)) =
          Function.update x true ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • x true) := by
        funext a
        cases a
        · simp [liftT, x]
        · simp [liftT, x, hz _ hg', hdet]
      rw [hfun, MultilinearMap.map_update_smul, Function.update_eq_self]
      rfl
    have h1 : G (SmGL.jac f π (liftT f hc h) (Submodule.Quotient.mk v)) =
        G ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • Submodule.Quotient.mk v) := by
      rw [G.isIntertwining, hu, map_smul, hu, htens]
    have h2 := hGi h1
    rw [jac_liftT_mk f hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, twKer_eq_bot f hc,
      Submodule.mem_bot, sub_eq_zero] at h2
    exact h2
  show fixed (GlobalTheory.SmGL.twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t)) ≠ ⊥
  intro hbot
  have hmem : v ∈ fixed (GlobalTheory.SmGL.twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t)) := by
    intro h
    show GlobalTheory.SmGL.twist π (detChar (Fin t) χ⁻¹) (h : GL (Fin t) k) v = (((1 : _ →* ℂˣ) h : ℂˣ) : ℂ) • v
    rw [twist_apply, key h h.2, smul_smul]
    simp
  rw [hbot] at hmem
  exact hv0 ((Submodule.mem_bot ℂ).1 hmem)

end GlobalTheory.EmptyFirstBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlockStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_of_jacquet_constituent_empty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin t) k) W) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin t) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (χ : kˣ →* ℂˣ) (z : (s true).V), IsSmooth π → π.IsIrreducible → c false = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (GlobalTheory.SmGL.jac f π) → z ≠ 0 → (∀ g ∈ KO k (Fin (c true)), (s true).ρ g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z) → IsSpherical (GlobalTheory.SmGL.twist π (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block | exact GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block | (intros; apply GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.CuspRow

theorem block_unique_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  intro k _ _ _ _ d V _ _ σ s' b f X _ _ ρ hσ hX hsub j j' hj hj'
  by_contra hne
  have hU : GlobalTheory.SmGL.unipRad k f ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨f ⟨j, ⟨0, hj⟩⟩, f ⟨j', ⟨0, hj'⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
    · exact ⟨f ⟨j', ⟨0, hj'⟩⟩, f ⟨j, ⟨0, hj⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
  have hs := hσ.2 s' b f hU
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor X hX
  obtain ⟨S, g, hg⟩ := hsub
  have hS : Subsingleton S.toSubmodule := inferInstance
  exact not_subsingleton _ (Function.Surjective.subsingleton hg)

end GlobalTheory.SmGL.CuspRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlockStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_jacquet_subquotient_at_most_one_nonempty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  first | exact @GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | exact GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | (intros; apply GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiExteriorTensorIsSubquotientOfForall
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiExteriorTensorIsSubquotientOfForall
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory

open PiTensorProduct

theorem piTensor_isSubquotient_of_forall : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := by
  intro α _ _ Γ _ X Y _ _ _ _ ρ ρ' h
  choose S f hf using h
  let ι : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ') :=
    { toLinearMap := PiTensorProduct.map fun a => (S a).toSubmodule.subtype
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        rfl }
  let π : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ) :=
    { toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        congr 1
        funext a
        exact (f a).isIntertwining _ _ (g a) (x a) }
  have hι : Function.Injective ι := by
    choose r hr using fun a => LinearMap.exists_leftInverse_of_injective (S a).toSubmodule.subtype
      (S a).toSubmodule.ker_subtype
    have : (PiTensorProduct.map r) ∘ₗ (PiTensorProduct.map fun a => (S a).toSubmodule.subtype)
        = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hr]
      exact PiTensorProduct.map_id
    exact Function.LeftInverse.injective (g := PiTensorProduct.map r) fun z => LinearMap.congr_fun this z
  have hπ : Function.Surjective π := by
    show Function.Surjective (PiTensorProduct.map fun a => (f a).toLinearMap)
    rw [← LinearMap.range_eq_top]
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    choose y hy using fun a => hf a (x a)
    exact ⟨PiTensorProduct.tprod ℂ y, by
      show PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext a
      exact hy a⟩
  exact (IsSubquotient.of_surjective π hπ).trans (IsSubquotient.of_injective ι hι)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiExteriorTensorIsSubquotientOfForallStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piExteriorTensor_isSubquotient_of_forall : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := by
  first | exact @GlobalTheory.piTensor_isSubquotient_of_forall | exact GlobalTheory.piTensor_isSubquotient_of_forall | (intros; apply GlobalTheory.piTensor_isSubquotient_of_forall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeeperCongruenceConjIntoCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeeperCongruenceConjIntoCongruence
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjCong

theorem exists_cong_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (g : GAf L n), 0 < N → ∃ M : ℕ, 0 < M ∧ ∀ κ, NG.Cong L n (N * M) κ → NG.Cong L n N (g⁻¹ * κ * g) := by
  intro L _ _ _ n N g hN
  obtain ⟨M, hM, h⟩ := Formalism.IndefR.principalLevelFrame.congConj_holds L n g N hN
  exact ⟨M, hM, fun κ hκ => h κ (NG.Cong.of_mul_right L n hκ)⟩

end GlobalTheory.ConjCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeeperCongruenceConjIntoCongruenceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deeper_congruence_conj_into_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (g : GAf L n), 0 < N → ∃ M : ℕ, 0 < M ∧ ∀ κ, NG.Cong L n (N * M) κ → NG.Cong L n N (g⁻¹ * κ * g) := by
  first | exact @GlobalTheory.ConjCong.exists_cong_conj | exact GlobalTheory.ConjCong.exists_cong_conj | (intros; apply GlobalTheory.ConjCong.exists_cong_conj <;> assumption)
end
end

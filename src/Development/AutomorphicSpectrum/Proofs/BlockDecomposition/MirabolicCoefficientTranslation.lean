module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLie
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair

section Alg

variable {k : Type} [Field k]

theorem uM_mul_uM (n : ℕ) (x y : Fin n → k) : uM n x * uM n y = uM n (x + y) := by
  unfold uM
  rw [← map_mul]
  rfl

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  have hrow : ∀ j : Fin n, GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j
    simp [GlobalTheory.BZMir.glEmbMat]
  have hcorner : GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
    simp [GlobalTheory.BZMir.glEmbMat]
  have hminor : (GlobalTheory.BZMir.glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [GlobalTheory.BZMir.glEmbMat, Fin.succAbove_last]
  have hsign : ((-1 : k) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [Matrix.det_succ_row (GlobalTheory.BZMir.glEmbMat k n A) (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, hcorner, hminor, hsign, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, one_mul]

theorem det_one_add_colMat (n : ℕ) (v : Fin n → k) : (1 + colMat k n v).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = Fin.last n
    · subst hi
      simp [GlobalTheory.BZMir.colMat]
    · simp [GlobalTheory.BZMir.colMat, hi]
  · intro i j hji
    change j < i at hji
    have hj : j ≠ Fin.last n := by
      intro h
      subst h
      exact absurd hji (not_lt.mpr (Fin.le_last i))
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp [GlobalTheory.BZMir.colMat, hj]

theorem det_uM (n : ℕ) (y : Fin n → k) :
    GeneralLinearGroup.det ((uM n y : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.MirPair.det_one_add_colMat n y

theorem det_levi (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact GlobalTheory.CompanionTheory.MirPair.det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)

theorem uM_mul_levi (n : ℕ) (g : GL (Fin n) k) (x : Fin n → k) :
    uM n x * levi k n g =
      levi k n g * uM n (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) := by
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n g
    (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))
  have hx : (g : Matrix (Fin n) (Fin n) k) *ᵥ (Multiplicative.toAdd
      (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))) = x := by
    rw [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hx] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact h.symm

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem coef_rules (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) (hB : TwInv T T' B s) :
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (uM (n + 1) y) v) v' x = coef T B v v' (x + y)) ∧
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B v (T' (uM (n + 1) y) v') x = coef T B v v' (x - y)) ∧
    (∀ (g : GL (Fin (n + 1)) k) (x : Fin (n + 1) → k) (v : V) (v' : V'),
      coef T B (T (levi k (n + 1) g) v) (T' (levi k (n + 1) g) v') x =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) *
          coef T B v v' (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
  unfold GlobalTheory.CompanionTheory.MirPair.TwInv at hB
  have hT : ∀ (a b : GlobalTheory.BZMir.Mir k (n + 1)) (w : V), T a (T b w) = T (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM]
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    have hxy : y + (x - y) = x := by abel
    have h := hB (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) y) (T (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) (x - y)) v) v'
    rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_uM, map_one, Units.val_one, one_mul,
      hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM, hxy] at h
    exact h
  · intro g x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_levi, ← hT, hB, GlobalTheory.SmGL.detChar_apply,
      GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_levi]

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslationStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_coefficient_translation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), TwInv T T' B s → (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (uM (n + 1) y) v) v' x = coef T B v v' (x + y)) ∧ (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B v (T' (uM (n + 1) y) v') x = coef T B v v' (x - y)) ∧ (∀ (g : GL (Fin (n + 1)) k) (x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (levi k (n + 1) g) v) (T' (levi k (n + 1) g) v') x = ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * coef T B v v' (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.coef_rules | exact GlobalTheory.CompanionTheory.MirPair.coef_rules | (intros; apply GlobalTheory.CompanionTheory.MirPair.coef_rules <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPair
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPair
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegGenNu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_after {n : ℕ} (a : Fin n) :
    ∑ b ∈ Finset.univ.filter (fun b => a < b), 1 = (Fin.rev a : ℕ) := by
  have h : Finset.univ.filter (fun b : Fin n => a < b) = Finset.Ioi a := by
    ext b; simp
  rw [h]
  simp [Fin.val_rev]
  omega

theorem isLSeg_fine (G : Segment k) (a : Fin G.len) :
    IsLSeg (topCut G (fun _ => 1) (fun _ => one_pos) a) (dec G a).rep := by
  have hc : (dec G a).IsCusp := G.isCusp_term _
  have e : topCut G (fun _ => 1) (fun _ => one_pos) a = Segment.single (dec G a) hc := by
    refine Segment.ext_first ?_ rfl
    show G.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), 1 : ℕ) : ℂ) = G.first.nu ((Fin.rev a : ℕ) : ℂ)
    rw [card_after]
  rw [e]
  exact (single_spec hc).2.1

theorem exists_cut (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL (k := k)} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) :
    ∃ Γ : Fin G.len → Segment k, IsTopCut G' Γ ∧ ∀ a, IsLSeg (Γ a) (dec G a).rep := by
  have hd : ∑ a, (dec G a).1 = x.1 := (sum_dec G).trans h.deg_eq
  have hpos : ∀ a, 0 < (dec G a).1 := fun a => (G.isCusp_term _).1
  have h1 : jm (dec G) hd x.rep = 1 :=
    (hJ G x.rep h _ (dec G) hd hpos).1
      ⟨_, isTopCut_topCut G (fun _ => 1) (fun _ => one_pos) (by simp), isLSeg_fine G⟩
  by_contra hn
  have h0 := (hJ G' x.rep h' _ (dec G) hd hpos).2 hn
  rw [h1] at h0
  exact one_ne_zero h0

theorem card_le_len {G : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut G Γ) : s ≤ G.len := by
  rw [← h.1]
  calc s = ∑ _ : Fin s, 1 := by simp
    _ ≤ ∑ a, (Γ a).len := Finset.sum_le_sum fun a _ => (Γ a).len_pos

theorem first_eq (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL (k := k)} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) : G.first = G'.first := by
  obtain ⟨Γ, hΓ, hL⟩ := exists_cut hJ h h'
  obtain ⟨Γ', hΓ', -⟩ := exists_cut hJ h' h
  have hle := card_le_len hΓ
  have hle' := card_le_len hΓ'
  have hlen : G.len = G'.len := le_antisymm hle hle'
  have hpos := G.len_pos
  let l : Fin G.len := ⟨G.len - 1, by omega⟩
  have hl1 : (Γ l).len = 1 := by
    by_contra hne
    have h2 : 1 < (Γ l).len := by have := (Γ l).len_pos; omega
    have hlt : ∑ _ : Fin G.len, 1 < ∑ a, (Γ a).len :=
      Finset.sum_lt_sum (fun a _ => (Γ a).len_pos) ⟨l, Finset.mem_univ _, h2⟩
    rw [hΓ.1, ← hlen] at hlt
    simp at hlt
  have hb : below Γ l = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (l : ℕ) < b := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    have h4 := b.2
    have h5 : (l : ℕ) = G.len - 1 := rfl
    omega
  have hf : (Γ l).first = G'.first := by
    rw [hΓ.2 l, hb]
    simp
  have e : Γ l = Segment.single G'.first G'.isCusp_first := Segment.ext_first hf hl1
  have h6 : IsLSeg (Γ l) G'.first.rep := by
    rw [e]
    exact (single_spec _).2.1
  have h7 : dec G l = G.first := by
    have h8 : ((Fin.rev l : Fin G.len) : ℕ) = 0 := by
      simp only [Fin.val_rev, l]
      omega
    show G.first.nu (((Fin.rev l : Fin G.len) : ℕ) : ℂ) = G.first
    rw [h8]
    simp
  rw [← h7]
  exact eq_of_isLSeg (hL l) h6

theorem lSegGeneric_of_nuPair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (_hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJ : Zc.LSegJacquet k)
    (hP : GlobalTheory.BZSeg.NuPair k) : GlobalTheory.BZSeg.LSegGeneric k := by
  intro Δ N V _ _ π hπ
  by_contra hg
  obtain ⟨α, β, β', hd, hd', hα, hβ, hββ, h1, h2⟩ :=
    hP N V π hπ.hasSupport.isSmooth hπ.hasSupport.isIrreducible hg
  have hpos : ∀ a, 0 < (![α, β] a).1 := by
    intro a
    fin_cases a
    · exact hα
    · exact hβ
  have hpos' : ∀ a, 0 < (![β', α.nu 1] a).1 := by
    intro a
    fin_cases a
    · exact hββ ▸ hβ
    · exact hα
  have hcut : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![α, β] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![α, β] hd hpos).2 hn
    rw [h0] at h1
    simp at h1
  have hcut' : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![β', α.nu 1] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![β', α.nu 1] hd' hpos').2 hn
    rw [h0] at h2
    simp at h2
  obtain ⟨Γ, hΓ, hL⟩ := hcut
  obtain ⟨Γ', hΓ', hL'⟩ := hcut'
  have e1 : IsLSeg ((Γ 0).nu 1) (α.nu 1).rep := GlobalTheory.isLSeg_nu (hL 0) 1
  have e2 : IsLSeg (Γ' 1) (α.nu 1).rep := hL' 1
  have e3 : (Γ 0).first.nu 1 = (Γ' 1).first := first_eq hJ e1 e2
  have hb : below Γ' 1 = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (1 : Fin 2) < b := (Finset.mem_filter.1 hb).2
    exact absurd h3 (by omega)
  rw [hΓ.2 0, hΓ'.2 1, hb, IrrGL.nu_nu] at e3
  have e4 : Δ.first.nu (((below Γ 0 + 1 : ℕ)) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ) := by
    simpa using e3
  have e5 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 e4
  omega

end GlobalTheory.CompanionTheory.SegGenNu

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPairStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_generic_of_jacquet_nu_pair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.LSegGeneric k := by
  first | exact @GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | exact GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | (intros; apply GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShear
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShear
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_leviMir (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

theorem tendsto_shearGL_zero (n : ℕ) :
    Filter.Tendsto (shearGL (k := k) n) (𝓝 0) (𝓝 1) := by
  have key : ∀ b : Fin (n + 1) → k, 1 + b (Fin.last n) ≠ 0 →
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b ∧
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    intro b hb
    have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
      simp [GlobalTheory.BZMir.eLast, dotProduct_single]
    have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
        b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [vecMulVec_mul_vecMulVec, hd]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
      rw [← mul_one_add]
      exact inv_mul_cancel₀ hb
    have hmul : (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) *
        (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) = 1 := by
      rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
        one_smul, add_sub_cancel_right]
    have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
      ⟨⟨_, _, hmul, mul_eq_one_comm.mp hmul⟩, rfl⟩
    have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dite_eq_left hu]
      exact hu.unit_spec
    refine ⟨hcoe, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hcoe]
    exact hmul
  have h0 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) := by
    have h := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using h
  have hev : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, 1 + b (Fin.last n) ≠ 0 := by
    have h1 : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, valuation k (b (Fin.last n)) < 1 :=
      (continuous_apply (Fin.last n)).continuousAt.preimage_mem_nhds
        (show {x : k | valuation k x < 1} ∈ 𝓝 ((fun b : Fin (n + 1) → k => b (Fin.last n)) 0) from h0)
    filter_upwards [h1] with b hb h
    have h2 := (valuation k).map_one_add_of_lt hb
    rw [h, map_zero] at h2
    exact zero_ne_one h2
  have hv : Continuous fun b : Fin (n + 1) → k => vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul (continuous_apply j)
  have hv0 : vecMulVec (GlobalTheory.BZMir.eLast k n) (0 : Fin (n + 1) → k) = 0 := by
    ext i j
    simp [vecMulVec_apply]
  have h1 : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b)
      (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun b : Fin (n + 1) → k =>
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
      continuous_const.add hv
    simpa [hv0] using hc.tendsto (0 : Fin (n + 1) → k)
  have hinv0 : Filter.Tendsto (fun b : Fin (n + 1) → k => (1 + b (Fin.last n))⁻¹) (𝓝 0) (𝓝 1) := by
    have h : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + b (Fin.last n)) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun b : Fin (n + 1) → k => (1 : k) + b (Fin.last n) :=
        continuous_const.add (continuous_apply (Fin.last n))
      simpa using hc.tendsto (0 : Fin (n + 1) → k)
    simpa using h.inv₀ one_ne_zero
  have h2 : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) (𝓝 0) (𝓝 1) := by
    have hconst : Filter.Tendsto (fun _ : Fin (n + 1) → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
        (𝓝 0) (𝓝 1) := tendsto_const_nhds
    have h := hconst.sub (hinv0.smul (hv.tendsto 0))
    simpa [hv0] using h
  have h1' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h1.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).1.symm
  have h2' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h2.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).2.symm
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply, inv_one, Units.val_one]
  exact h1'.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2')

theorem shear_fix_vector {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) :
    ∃ r : kˣ, valuation k (r : k) < 1 ∧
      ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  have hopen : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have htend : Filter.Tendsto (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b))
      (𝓝 0) (𝓝 1) := by
    have h := ((GlobalTheory.CompanionTheory.MirPair.continuous_leviMir (k := k) (n + 1)).tendsto 1).comp (GlobalTheory.CompanionTheory.MirPair.tendsto_shearGL_zero (k := k) n)
    rw [map_one] at h
    exact h
  have hΩ : (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) ⁻¹'
      {g | T g v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) :=
    htend (hopen.mem_nhds (by simp))
  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.exists_box_subset hΩ
  haveI : (valuation k).IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (valuation k)).1 inferInstance
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  by_cases hr1 : valuation k (r : k) < 1
  · exact ⟨r, hr1, fun b hb => hr hb⟩
  · refine ⟨Units.mk0 x hx0, by simpa using hx1, fun b hb => hr ?_⟩
    intro j
    have h1 : valuation k (b j) ≤ valuation k x := hb j
    show valuation k (b j) ≤ valuation k (r : k)
    exact le_trans h1 (le_trans hx1.le (not_lt.mp hr1))

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShearStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_small_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ v : V, ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | exact GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | (intros; apply GlobalTheory.CompanionTheory.MirPair.shear_fix_vector <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembership
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembership
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearLat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dotProduct_eLast {n : ℕ} (b : Fin (n + 1) → k) : b ⬝ᵥ eLast k n = b (Fin.last n) := by
  simp [eLast, dotProduct_single]

theorem isUnit_one_add {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0) :
    IsUnit (1 + vecMulVec (eLast k n) b) := by
  rw [Matrix.isUnit_iff_isUnit_det, vecMulVec_eq (ι := Unit),
    det_one_add_replicateCol_mul_replicateRow, dotProduct_eLast]
  exact h.isUnit

theorem shearGL_mulVec {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0)
    (x : Fin (n + 1) → k) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x =
      x + (b ⬝ᵥ x) • eLast k n := by
  have e : ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
    unfold shearGL
    rw [dite_eq_left (isUnit_one_add b h)]
    rfl
  rw [e, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem dotProduct_shear {n : ℕ} (b x : Fin (n + 1) → k) :
    b ⬝ᵥ (x + (b ⬝ᵥ x) • eLast k n) = (1 + b (Fin.last n)) * (b ⬝ᵥ x) := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_eLast, smul_eq_mul]
  ring

theorem exists_bound {n : ℕ} (g : GL (Fin (n + 1)) k) :
    ∃ C : kˣ, 1 ≤ valuation k (C : k) ∧
      (∀ i, valuation k (((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) ≤ valuation k (C : k)) ∧
      ∀ i j, valuation k (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) ≤
        valuation k (C : k) := by
  let f : Option (Fin (n + 1) ⊕ Fin (n + 1) × Fin (n + 1)) → k := fun o =>
    match o with
    | none => 1
    | some (.inl i) => ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i
    | some (.inr p) => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p.1 p.2
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun o => valuation k (f o)
  have h1 : 1 ≤ valuation k (f i₀) := by simpa [f] using hi₀ none
  have hne : f i₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact absurd h1 (by simp)
  exact ⟨Units.mk0 _ hne, h1, fun i => hi₀ (some (.inl i)), fun i j => hi₀ (some (.inr (i, j)))⟩

theorem mul_mem_cball {a u : k} {p C t : kˣ} (hp : valuation k (p : k) ≤ 1)
    (ha : a ∈ cball (p * C⁻¹ * t)) (hu : valuation k u ≤ valuation k (C : k)) : a * u ∈ cball t := by
  have ha' : valuation k a ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := ha
  show valuation k (a * u) ≤ valuation k (t : k)
  calc valuation k (a * u) = valuation k a * valuation k u := map_mul _ _ _
    _ ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) * valuation k (C : k) := mul_le_mul' ha' hu
    _ = valuation k (p : k) * valuation k (t : k) := by
        rw [← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
    _ ≤ valuation k (t : k) := mul_le_of_le_one_left' hp

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  intro k _ _ _ _ n g
  obtain ⟨C, hC1, hu, hH⟩ := exists_bound g
  obtain ⟨p₀, hp0, hp1⟩ : ∃ p : k, p ≠ 0 ∧ valuation k p < 1 := Valuation.IsNontrivial.exists_lt_one
  obtain ⟨p, rfl⟩ : ∃ p : kˣ, (p : k) = p₀ := ⟨Units.mk0 _ hp0, rfl⟩
  have hCi : valuation k ((C⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ hC1
  have hr1 : valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) < 1 := by
    simp only [Units.val_mul, map_mul]
    exact lt_of_le_of_lt ((mul_le_of_le_one_right' hCi).trans (mul_le_of_le_one_right' hCi)) hp1
  refine ⟨p * C⁻¹ * C⁻¹, hr1, fun b hb t x => ?_⟩
  have hlast : valuation k (b (Fin.last n)) < 1 := lt_of_le_of_lt (hb (Fin.last n)) hr1
  have hone : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hlast
  have hne : 1 + b (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hone
    exact zero_ne_one hone
  rw [shearGL_mulVec b hne x]
  have hGS : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (x + (b ⬝ᵥ x) • eLast k n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
        (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) := by
    rw [mulVec_add, mulVec_smul]
  have hd : ∀ z : Fin (n + 1) → k, b ⬝ᵥ z =
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) := by
    intro z
    rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hw : b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈
      box (n + 1) (p * C⁻¹) := by
    intro j
    change ∑ i, b i * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j ∈ cball (p * C⁻¹)
    refine Finset.sum_induction _ (· ∈ cball (p * C⁻¹)) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
    have h1 : valuation k (b i) ≤ valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) := hb i
    show valuation k (b i * _) ≤ valuation k ((p * C⁻¹ : kˣ) : k)
    rw [map_mul]
    refine (mul_le_mul' h1 (hH i j)).trans (le_of_eq ?_)
    rw [← map_mul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hdot : ∀ y ∈ box (n + 1) t,
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ y ∈
        cball (p * C⁻¹ * t) := by
    intro y hy
    refine dotProduct_mem_cball (s := t) ?_ hy
    rwa [mul_inv_cancel_right]
  have hp : valuation k (p : k) ≤ 1 := hp1.le
  constructor
  · intro h i
    have h2 : (1 + b (Fin.last n)) * (b ⬝ᵥ x) ∈ cball (p * C⁻¹ * t) := by
      rw [← dotProduct_shear, hd (x + (b ⬝ᵥ x) • eLast k n)]
      exact hdot _ h
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      have h2' : valuation k ((1 + b (Fin.last n)) * (b ⬝ᵥ x)) ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := h2
      rw [map_mul, hone, one_mul] at h2'
      exact h2'
    rw [hGS] at h
    have e : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) i =
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
          (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n)) i +
        -((b ⬝ᵥ x) * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) := by
      simp
    rw [e]
    exact add_mem_cball (h i) (neg_mem_cball (mul_mem_cball hp h3 (hu i)))
  · intro h i
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      rw [hd x]
      exact hdot _ h
    rw [hGS]
    exact add_mem_cball (h i) (mul_mem_cball hp h3 (hu i))

end GlobalTheory.CompanionTheory.MirPair.ShearLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembershipStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_preserves_box_membership : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.ShearLat.main | exact GlobalTheory.CompanionTheory.MirPair.ShearLat.main | (intros; apply GlobalTheory.CompanionTheory.MirPair.ShearLat.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMap
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem continuous_castM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ), Continuous (sO k i t) := by
  intro k _ _ _ _ i t
  exact (GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.continuous_sEmb k ((i + 1) + t)).comp (continuous_castM k _)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMapStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_shifted_orbit_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), Continuous (sO k i t) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq
open Matrix
open PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.EllProp

theorem twConj_twConj {G : Type*} [Group G] (θ : Monoid.End G) (x g d : G) :
    twConj θ x (twConj θ g d) = twConj θ (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem orbit_preimage_eq {G : Type*} [Group G] (θ : Monoid.End G) (g d : G) (C : Set G) :
    {x | twConj θ x (twConj θ g d) ∈ C} = (fun y => g⁻¹ * y) '' {y | twConj θ y d ∈ C} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]
  constructor
  · intro h
    exact ⟨g * x, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem ellProperOf : EllProperOf := by
  intro hD hP _ n d hd C hC
  obtain ⟨g, d', z, h1, h2, h3, rfl⟩ := hD n d hd
  rw [orbit_preimage_eq]
  exact (hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)

end GlobalTheory.CompanionTheory.EllProp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentCharacterTrivial
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentCharacterTrivial
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qO_extTensor_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : MirUin k (i + 1)) (hu : mirChar k ψ i u = 1) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1) v) = qO τ σ ψ v := by
  intro k _ _ _ _ i t ψ τ σ u hu v
  let L : (τ.V ⊗[ℂ] σ.V) →ₗ[ℂ] (τ.V ⊗[ℂ] σ.V) :=
    extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1)
  have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (u : Mir k (i + 1)) : ℂˣ) : ℂ) = 1 := by
    have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) u
    simpa using congrArg Units.val this
  have ha : ∀ a : τ.V, (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (u : Mir k (i + 1)) a = τ.ρ (u : Mir k (i + 1)) a := by
    intro a
    refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
    rw [hd, one_smul]
  have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 = 1 := map_one _
  have hb : ∀ b : σ.V, (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 b = b := fun b => LinearMap.congr_fun hρ b
  have e : ∀ (a : τ.V) (b : σ.V), L (a ⊗ₜ[ℂ] b) = (τ.ρ (u : Mir k (i + 1)) a) ⊗ₜ[ℂ] b := fun a b =>
    (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
      ((u : Mir k (i + 1)), 1) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) (ha a) (hb b))
  have hq : ∀ a : τ.V, (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (u : Mir k (i + 1)) a) =
      (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ a := by
    intro a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    unfold twKer
    apply Submodule.subset_span
    exact ⟨u, a, by simp [hu]⟩
  have key : ∀ w : τ.V ⊗[ℂ] σ.V, qO τ σ ψ (L w) = qO τ σ ψ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      rw [e]
      exact congrArg (fun x => TensorProduct.tmul ℂ x b) (hq a)
  exact key v

end GlobalTheory.CompanionTheory.BZPhiPG
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentCharacterTrivialStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariant_unipotent_character_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : MirUin k (i + 1)) (hu : mirChar k ψ i u = 1) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1) v) = qO τ σ ψ v := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.qO_extTensor_unip | exact GlobalTheory.CompanionTheory.BZPhiPG.qO_extTensor_unip | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.qO_extTensor_unip <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.NormPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem norm_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    (d * u⁻¹) * thE E n (d * u⁻¹) = nrm d := by
  obtain ⟨h1, h2⟩ := hu
  have hθ : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h1, map_mul, map_inv, hθ, inv_inv, nrm]
  group

theorem polE_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    polE (d * u⁻¹) = (nrm d).val.charpoly := by
  rw [polE, norm_translate hu]

theorem map_thetaE (τ : E →+* ℂ) (d : GL (Fin n) E) :
    GeneralLinearGroup.map τ (thetaE E n d) =
      thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d) := by
  apply Units.ext
  ext i j
  have hv : ∀ g : GL (Fin n) E, ((GeneralLinearGroup.map τ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = g.val.map τ := fun _ => rfl
  rw [hv, thetaR_val, thetaR_val, ← map_inv, hv]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  exact IsCMField.complexEmbedding_complexConj E τ _

theorem charpoly_map_nrm (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (GeneralLinearGroup.map τ d * thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d)).val.charpoly =
      (nrm d).val.charpoly.map τ := by
  rw [← map_thetaE, ← map_mul, ← Matrix.charpoly_map]
  rfl

theorem isRegEll_iff_mem_Ell (d : GL (Fin n) E) : IsRegEll d ↔ (nrm d).val.charpoly ∈ Ell E n := by
  have hm : (nrm d).val.charpoly.Monic := Matrix.charpoly_monic _
  constructor
  · intro h
    refine ⟨hm, by simp, h.1, fun τ z hz => ?_⟩
    exact h.2 τ z (Polynomial.isRoot_of_mem_roots hz)
  · rintro ⟨-, -, hs, hr⟩
    exact ⟨hs, fun τ z hz => hr τ z ((Polynomial.mem_roots (hm.map τ).ne_zero).2 hz)⟩

theorem polEq : PolEq := by
  intro E _ _ _ n u hu d
  rw [polE_translate hu]
  refine ⟨isRegEll_iff_mem_Ell d, fun v => ⟨charpoly_map_nrm v.embedding d, fun h => ?_⟩⟩
  unfold EllC
  rw [charpoly_map_nrm]
  exact ⟨h.1.map, fun z hz => h.2 v.embedding z hz⟩

end GlobalTheory.CompanionTheory.NormPoly
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnits
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalThetaTopology

theorem locallyCompact_units {M : Type} [Ring M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
    [LocallyCompactSpace M] : LocallyCompactSpace Mˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_units {M : Type} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M)).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2Space_units {M : Type} [Monoid M] [TopologicalSpace M] [T2Space M] : T2Space Mˣ :=
  Units.isEmbedding_embedProduct.t2Space

theorem top_GL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  exact ⟨locallyCompact_units, secondCountable_units, t2Space_units⟩

theorem continuous_thetaR {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (σ : A →+* A)
    (hσ : Continuous σ) (n : ℕ) : Continuous (thetaR σ n) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map hσ).matrix_transpose,
    (Units.continuous_val.matrix_map hσ).matrix_transpose⟩

theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E := by
  let b := Module.finBasis ℚ E
  exact Function.Injective.countable b.equivFun.injective

theorem countable_GL (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h

theorem continuous_thF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = fun g =>
      PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g * (PhiU n (Af E))⁻¹ :=
    funext fun g => thetaGL_eq n (Af E) _ g
  rw [h]
  exact (continuous_const.mul (continuous_thetaR _ (continuous_conjFin _) n)).mul continuous_const

theorem topo : Topo := by
  intro E _ _ _ n
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨c1, c2, -⟩ := top_GL (R := ℂ) n
  exact ⟨top_GL n, top_GL n, ⟨c1, c2⟩, countable_GL E n, continuous_thF E n,
    continuous_thetaR _ Complex.continuous_conj n⟩

end GlobalTheory.CompanionTheory.LocalThetaTopology
end
end

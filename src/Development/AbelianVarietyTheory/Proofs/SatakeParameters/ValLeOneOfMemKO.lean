module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
noncomputable section

namespace GlobalTheory.BlockType

open GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_one_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {h : GL n k} (hh : h ∈ KO k n) (a b : n) :
    valuation k (h.val a b) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hh
  exact (g.val a b).2

theorem val_col_lt {n : Type} [Fintype n] [DecidableEq n] {h g : GL n k} (hh : h ∈ KO k n) (b : n)
    (hg : ∀ c, valuation k ((g.val - 1) c b) < 1) (a : n) : valuation k ((h.val * (g.val - 1)) a b) < 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun c _ => by
    rw [map_mul]; exact Right.mul_lt_one_of_le_of_lt (val_le_one_of_mem_KO hh a c) (hg c)


variable (k) in
def blockGrp (r t : ℕ) : Subgroup (GL (Fin (r + t)) k) where
  carrier := {h | h ∈ KO k (Fin (r + t)) ∧
    ∀ (a : Fin (r + t)) (j : Fin r), valuation k ((h.val - 1) a (Fin.castAdd t j)) < 1}
  one_mem' := ⟨(KO k _).one_mem, fun a j => by simp⟩
  mul_mem' := by
    rintro h g ⟨hh, h1⟩ ⟨hg, g1⟩
    refine ⟨(KO k _).mul_mem hh hg, fun a j => ?_⟩
    have e : ((h * g).val - 1) = h.val * (g.val - 1) + (h.val - 1) := by
      simp only [Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_lt _ (val_col_lt hh _ (fun c => g1 c j) a) (h1 a j)
  inv_mem' := by
    rintro h ⟨hh, h1⟩
    refine ⟨(KO k _).inv_mem hh, fun a j => ?_⟩
    have e : ((h⁻¹ : GL (Fin (r + t)) k).val - 1) = -((h⁻¹ : GL (Fin (r + t)) k).val * (h.val - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]; abel
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    exact val_col_lt ((KO k _).inv_mem hh) _ (fun c => h1 c j) a


open Classical in
def blockChar {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) : ℂ :=
  if hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 0 then 0 else (χ (Units.mk0 _ hd) : ℂ)

theorem blockChar_eq {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) (u : kˣ)
    (hu : (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) : blockChar χ h = χ u := by
  have hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := hu ▸ u.ne_zero
  rw [blockChar, dite_eq_right hd]
  congr 2
  ext; simp [hu]

theorem mem_blockGrp {r t : ℕ} {h : GL (Fin (r + t)) k} (hK : h ∈ KO k (Fin (r + t)))
    (h1 : ∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1)
    (h2 : ∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) :
    h ∈ blockGrp k r t := by
  refine ⟨hK, fun a j => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · have := h2 i j
    simpa [Matrix.sub_apply, Matrix.one_apply, Fin.castAdd_inj] using this
  · have := h1 i j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simpa [Matrix.sub_apply, Matrix.one_apply, hne] using this

theorem isBlockVec_of {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W)
    (hv : ∀ h ∈ blockGrp k r t, π h v = blockChar χ h • v) : GlobalTheory.SplitRead.IsBlockVec χ π v := by
  intro h hK h1 h2 u hu
  rw [hv h (mem_blockGrp hK h1 h2), blockChar_eq χ h u hu]

theorem kOne_le_blockGrp (r t : ℕ) : KOne k (Fin (r + t)) ≤ blockGrp k r t := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨⟨g, rfl⟩, fun a j => ?_⟩
  have hg' : ∀ a b, IsLocalRing.residue 𝒪[k] (g.val a b) = (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a b := by
    intro a b
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val a b) hg
    simpa using this
  have hm : g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hg']
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e]
  have := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val - 1) a (Fin.castAdd t j) =
      ((g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) : 𝒪[k]) : k) := by
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e] <;> rfl
  rw [e]; exact this

theorem blockChar_kOne {r t : ℕ} (χ : kˣ →* ℂˣ) (hχ : IsTame χ) {h : GL (Fin (r + t)) k}
    (hh : h ∈ KOne k (Fin (r + t))) : blockChar χ h = 1 := by
  obtain ⟨g, hg, rfl⟩ := hh
  have hg' : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val) hg
    ext a b
    have h2 := congrArg (fun M : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k] => M (Fin.natAdd r a) (Fin.natAdd r b)) this
    simpa [Matrix.one_apply, Fin.natAdd_inj] using h2
  have hm : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, RingHom.map_det, RingHom.mapMatrix_apply, hg', Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    rw [show ((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : k) =
      algebraMap 𝒪[k] k (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  have hne : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) ≠ 0 := by
    intro h0
    have : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 : 𝒪[k]) : k) = -1 := by
      push_cast; rw [h0]; ring
    rw [this, Valuation.map_neg, map_one] at hv
    exact lt_irrefl _ hv
  rw [blockChar_eq χ _ (Units.mk0 _ hne) e.symm, hχ (Units.mk0 _ hne) (by simpa using hv)]
  simp

end GlobalTheory.BlockType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem admissible_of_rank_one_unitary : ∀ (D : D7) (T : WDTie D.nd D.naut), RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → Formalism.MainNotions.SumRepresentations.adm7 D := by
  intro D T hT h2
  exact (GlobalTheory.T.tempered_of_rank_one_unitary D T hT h2).1

end GlobalTheory.RowTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.TwistLG

open Formalism.MainNotions.SumRepresentations.At

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have h1 := W.smul_mem (((χ g)⁻¹ : kˣ) : k) (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at h1
    exact h1
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) : IsSSRep (twGL ρ χ) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 h1, h2⟩

theorem cont_twGL [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_val]
  refine Continuous.smul (M := k) ?_ hρ
  have e : ∀ g, (((Matrix.GeneralLinearGroup.det.comp χ) g : kˣ) : k) =
      (χ g : Matrix (Fin 1) (Fin 1) k).det := fun g => rfl
  simp only [e]
  exact hχ.matrix_det

theorem charpoly_eq_of_dense [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    [Infinite k] (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem etaT_char_etaTinv (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} := by
  have u1 := A.etaT_unr w
  obtain ⟨u2, f2⟩ := A.etaTinv_def w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  obtain ⟨b, hb⟩ : ∃ b, A.frobEig (A.locG A.etaT w) = {b} :=
    Multiset.card_eq_one.mp (by rw [A.frobEig_card _ u1, A.locG_dim])
  have hb0 : b ≠ 0 := by
    intro h0
    apply A.frobEig_ne_zero _ u1
    rw [hb, h0]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at f2
  have hu := A.unr_char _ _ d2 u1 u2
  have hf := A.frobEig_char _ _ b⁻¹ u1 u2 d2 f2
  rw [hb, Multiset.map_singleton, mul_inv_cancel₀ hb0] at hf
  rw [A.unr_eq_lpUnr _ hu, hf]

theorem param_twist (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u s : ℝ) :
    A.lpChar (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpTw (A.locG A.etaTinv w) s) =
      A.lpTw (A.locG π w) (s + u) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  have c3 := (hLP w (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) s d2 d2).2.2.1
  have c2 := (hLP w (A.locG (A.tw π A.etaT) w) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) u
    d2 d2).2.1
  have c4 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3, c2, A.lpTw_add, A.locG_tw, c4, etaT_char_etaTinv N A w, c5, add_comm]

end Glob

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end Main

end GlobalTheory.TwistLG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTieLP

open GlobalTheory.WeilDeligne

theorem matrix_charpoly_smul {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (c : ℂ) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  by_cases hc : c = 0
  · subst hc
    ext i
    rw [zero_smul, Matrix.charpoly_zero, coeff_scaleRoots, M.charpoly_natDegree_eq_dim, coeff_X_pow]
    by_cases hi : i = Fintype.card n
    · subst hi
      have := M.charpoly_monic.coeff_natDegree
      rw [M.charpoly_natDegree_eq_dim] at this
      simp [this]
    · rcases lt_or_gt_of_ne hi with h | h
      · have : Fintype.card n - i ≠ 0 := by omega
        simp [hi, this]
      · simp [hi, coeff_eq_zero_of_natDegree_lt (p := M.charpoly) (by rwa [M.charpoly_natDegree_eq_dim])]
  · apply Polynomial.funext
    intro t
    have h1 : (M.charpoly.scaleRoots c).eval (c * (t / c)) = c ^ M.charpoly.natDegree * M.charpoly.eval (t / c) := by
      simpa using scaleRoots_eval₂_mul (RingHom.id ℂ) (t / c) c (p := M.charpoly)
    rw [mul_div_cancel₀ _ hc, M.charpoly_natDegree_eq_dim] at h1
    rw [h1, Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
    split_ifs <;> field_simp

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, matrix_charpoly_smul,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_line {V L : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L] (hL : Module.finrank ℂ L = 1)
    (f : Module.End ℂ V) (c : ℂ) :
    (TensorProduct.map f (c • (1 : Module.End ℂ L))).charpoly = f.charpoly.scaleRoots c := by
  let e : L ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq L ℂ (by simp [hL])
  let E : TensorProduct ℂ V L ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ x, E (TensorProduct.map f (c • (1 : Module.End ℂ L)) x) = (c • f) (E x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v l =>
      simp [E, TensorProduct.map_tmul, smul_comm c, map_smul]
  have h2 : E.conj (TensorProduct.map f (c • (1 : Module.End ℂ L))) = c • f := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := E.surjective v
    simpa [LinearEquiv.conj_apply] using key x
  rw [← charpoly_smul_end, ← h2, LinearEquiv.charpoly_conj]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem inePol_char {a c : WD h} (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (a.inePol σ).scaleRoots z := by
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    rw [WD.lpDim_mk] at hc
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk,
      WDRep.tensor_ρ, h1, charpoly_map_line hc]

end GlobalTheory.RowTieLP

theorem GlobalTheory.RowTieLP.main : ∀ (D : D7), WDTie D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut := by
  intro D T w a b χ χ' s h1 h2
  obtain ⟨l1, l2, l3, l4, l5⟩ := (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ _ _ T).2.1 w a b χ χ' s h1 h2
  refine ⟨l1, l2, l3, l4, l5, fun σ hσ => ⟨⟨?_, ?_⟩, fun c hc => ?_⟩⟩
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]
    exact GlobalTheory.WeilDeligne.WD.charPol_monic _ _
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.charPol_natDegree, T.dim]
  · rw [T.inePol w χ σ hσ] at hc
    have hd : (T.e w χ).lpDim = 1 := by rw [T.dim, h1]
    rw [T.inePol w _ σ hσ, T.char _ _ _ h1, T.inePol w a σ hσ]
    exact GlobalTheory.RowTieLP.inePol_char hd hσ hc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem charLaws_of_tie (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) : GlobalTheory.TypeLeaf.CharLaws D := fun w a χ χ' h1 h2 =>
  let H := h.1 w a a χ χ' 0 h1 h2
  ⟨H.2.2.2.1, H.2.2.2.2.1⟩

theorem isoLoc_one (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem cuspidalStrongMultiplicityOne_of_analytic (D : D7) (h : Formalism.MainNotions.SumRepresentations.adm5 D) : GlobalTheory.TypeLeaf.MultOne D := by
  intro a π π' ha hloc
  have hp := h.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
    (Filter.Eventually.of_forall fun w => by rw [isoLoc_one, isoLoc_one, hloc w])
  rw [List.singleton_perm_singleton] at hp
  exact eq_of_heq (Formalism.BasicNotions.Part.mk.inj hp).2.1

theorem etaShift (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) (τ : D.host.E →+* ℂ) :
    ∀ z ∈ D.naut.infG D.naut.etaTinv τ, ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := h.2.1.2.1 τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have hc' : (D.R.t : ℂ) = 2 * c + 1 := by exact_mod_cast hc
  rw [h2] at hz
  rcases h1 with e | e <;> rw [e] at hz <;> simp at hz <;> subst hz
  · exact ⟨-(c + 1), by push_cast; rw [hc']; ring⟩
  · exact ⟨-c, by push_cast; rw [hc']; ring⟩

theorem pointPar (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tie0 D) (h5 : Formalism.MainNotions.SumRepresentations.adm5 D) : GlobalTheory.TypeLeaf.PointPar D :=
  GlobalTheory.TypeLeaf.pointPar_of_twist D
    (GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D (charLaws_of_tie D hT) (cuspidalStrongMultiplicityOne_of_analytic D h5))
    hT.2.1.1.1 (etaShift D hT)

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem mapRep_mapRep {Γ : Type} [Group Γ] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  simp [mapRep]

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (x : Γ) :
    ((mapRep f ρ x : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ x : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
  simp [mapRep]

theorem isSSRep_map {Γ : Type} [Group Γ] {K L : Type} [Field K] [CharZero K] [Field L] {a : ℕ}
    (f : K →+* L) (ρ : Γ →* GL (Fin a) K) (h : IsSSRep ρ) : IsSSRep (mapRep f ρ) := by
  letI : Algebra K L := f.toAlgebra
  exact ssAscent K L Γ a ρ h

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)


include A in
theorem charZero_Kf (i : N.Loc) : CharZero (Kf N i) :=
  (RingHom.charZero_iff (ϕ := A.iotaQ i) (A.iotaQ i).injective).2 inferInstance

theorem isRepOfSig_transport {i i' : N.Loc} (φ : N.O i' ≃+* N.O i) (hφc : Continuous φ)
    (hφι : ∀ z, iotaO N A i (φ z) = iotaO N A i' z) (Sig : List (Formalism.BasicNotions.Part A.CG))
    (ρ₀ : G H.E N.Om →* GL (Fin R.r) (N.O i')) (h : IsRepOfSig N A i' Sig ρ₀) :
    IsRepOfSig N A i Sig (mapRep φ.toRingHom ρ₀) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [coe_mapRep]
    exact h1.matrix_map hφc
  · haveI := charZero_Kf N A i'
    let ψ : Kf N i' ≃+* Kf N i := IsFractionRing.ringEquivOfRingEquiv φ
    have e : mapRep (algebraMap (N.O i) (Kf N i)) (mapRep φ.toRingHom ρ₀) =
        mapRep ψ.toRingHom (mapRep (algebraMap (N.O i') (Kf N i')) ρ₀) := by
      rw [mapRep_mapRep, mapRep_mapRep]
      congr 1
      ext z
      simp [ψ]
    rw [e]
    exact isSSRep_map ψ.toRingHom _ h2
  · refine h3.mono fun w hw B σ hB hσ => ?_
    rw [coe_mapRep, Matrix.charpoly_map, Polynomial.map_map]
    have : (iotaO N A i).comp φ.toRingHom = iotaO N A i' := by
      ext z
      exact hφι z
    rw [this]
    exact hw B σ hB hσ

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

end GlobalTheory.RowRepOcc
end
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
noncomputable section

namespace GlobalTheory.ParamRep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

theorem charpoly_smul_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod := by
  have h := (IsAlgClosed.splits (u • M).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _)
  rw [GlobalTheory.RowTie.EigTwist.roots_charpoly_smul_matrix] at h
  exact h

theorem charpoly_smul_of_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (h : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  rw [charpoly_smul_eq_prod, h, roots_multiset_prod_X_sub_C]

theorem prod_Icc_eq_fin {M : Type*} [CommMonoid M] (F : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Icc 1 t, F c = ∏ c : Fin t, F ((c : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => by rw [add_comm]

theorem charpoly_block {k : Type*} [CommRing k] {r t : ℕ} (M : Matrix (Fin r) (Fin r) k) (d : Fin t → k) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 (Matrix.diagonal d))).charpoly =
      M.charpoly * ∏ c, (X - C (d c)) := by
  rw [Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]
  congr 1
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_diagonal]

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E q) : v ∉ placesOver E p := by
  intro hv'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h1 : (1 : 𝓞 E) ∈ v.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv') (v.asIdeal.mul_mem_left _ hv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem locG_tw_tw (hL : Formalism.MainNotions.SumRepresentations.At.TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) :
    A.locG (A.tw (A.tw π A.etaTinv) A.etaT) w = A.locG π w := by
  obtain ⟨h1, h2⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  have d2 := A.locG_dim A.etaT w
  have hu2 := A.etaT_unr w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ hu2).trans d2)
  have hc0 : c ≠ 0 := by
    have := A.frobEig_ne_zero _ hu2
    rw [hc] at this
    simpa [eq_comm] using this
  have hu := A.unr_char _ _ d2 h1 hu2
  have hf : A.frobEig (A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w)) = {1} := by
    rw [A.frobEig_char _ _ c h1 hu2 d2 hc, h2, hc]
    simp [hc0]
  have he : A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w) = A.lpUnr w {1} := by
    rw [A.unr_eq_lpUnr _ hu, hf]
  obtain ⟨-, -, -, e1, e2, -⟩ := hL w (A.locG π w) (A.locG π w) (A.locG A.etaTinv w) (A.locG A.etaT w) 0 d1 d2
  rw [A.locG_tw, A.locG_tw, e1, he, e2]

theorem hecke_split (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    (hB : IsBCV N A i P (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv))
    {w : PlE H} (hw : SplitOut N i w) (hu : A.unr (A.locG (A.tw π A.etaTinv) w))
    {B : ValuationSubring N.Om} {σ : G H.E N.Om} (hBw : IsPlaceOver (F := H.E) B w)
    (hσ : IsFrob (F := H.E) B (normV w) σ) :
    (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) := by
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have e3 := hB.2.2.2.1 w hw.1
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, e5]
  simp

theorem galPol_twist {w : PlE H} (π : A.CG R.r) (hu : A.unr (A.locG π w)) (u : ℂ)
    (hξ : A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {u}) :
    galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) =
      (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map (· * u)).map fun α => X - C α).prod := by
  obtain ⟨h1, -⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ h1).trans d1)
  rw [A.frobEig_tw _ _ h1, hd, Multiset.map_singleton, Multiset.singleton_inj] at hξ
  unfold galPol
  rw [A.locG_tw, A.frobEig_tw _ _ (A.unr_char _ _ d1 hu h1), A.frobEig_char _ _ d hu h1 d1 hd,
    A.frobEig_tw _ _ hu]
  simp only [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
  simp only [Function.comp]
  rw [← hξ]
  have hq : ((normV w : ℕ) : ℂ) ^ (((1 - (R.nV : ℝ)) / 2 : ℝ) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ (((1 - (R.r : ℝ)) / 2 : ℝ) : ℂ) *
        ((normV w : ℕ) : ℂ) ^ ((-(R.t : ℝ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ (normV_ne_zero w)]
    congr 1
    rw [Ranks.nV]
    push_cast
    ring
  rw [hq]
  congr 2
  ring

theorem map_smul_matrix {k l : Type*} [CommRing k] [CommRing l] {n : Type*} (f : k →+* l) (c : k)
    (M : Matrix n n k) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

section Twist

variable {Γ : Type} [Group Γ]

theorem coe_twGL {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((χ g : kˣ) : k) • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  show algebraMap k (Matrix (Fin n) (Fin n) k) ((χ g : kˣ) : k) * _ = _
  rw [← Algebra.smul_def]

theorem twGL_twGL_inv {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ⁻¹) χ = ρ := by
  ext g : 2
  rw [coe_twGL, coe_twGL, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
  simp

theorem mapRep_twGL {k l : Type} [CommRing k] [CommRing l] {n : ℕ} (f : k →+* l) (ρ : Γ →* GL (Fin n) k)
    (χ : Γ →* kˣ) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) =
      Formalism.MainNotions.SumRepresentations.At.twGL (mapRep f ρ) ((Units.map f.toMonoidHom).comp χ) := by
  ext g : 2
  rw [coe_twGL, mapRep_twGL_coe]
  rfl

theorem isSSRep_twGL {k : Type} [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := by
  have key : ∀ W : Submodule k (Fin n → k), IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
    intro W
    refine ⟨fun hW g v hv => ?_, fun hW g v hv => ?_⟩
    · have h1 := hW g v hv
      rw [coe_twGL, Matrix.smul_mulVec] at h1
      exact (W.smul_mem_iff (χ g).ne_zero).1 h1
    · rw [coe_twGL, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW g v hv)
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 h1, h2⟩

end Twist

end GlobalTheory.ParamRep

section Final

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

end Final
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitThetaCorrespondenceOfLocalPairings
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem split_theta_correspondence_of_local_pairings : ∀ D : D7, (∀ i, PairLift D.nd D.naut i) → Formalism.MainNotions.SumRepresentations.adm3 D := by
  intro D h i σ P hθ w hw
  exact GlobalTheory.RowTie.splitLift_of_pairLift _ _ _ D.nd D.naut i (h i) σ P hθ w hw

end GlobalTheory.RowTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharEtaBack
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsoLocAppendSingleton
noncomputable section

namespace GlobalTheory.LocCongrRoad

open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

private theorem foldr_lpSum_lpTw_lpChar (hL : CharSum N A) {w : PlE H} (x c : A.LP w) (hc : A.lpDim c = 1)
    (s : ℝ) (L : List ℝ) :
    L.foldr (fun k acc => A.lpSum (A.lpTw (A.lpChar x c) (s - k)) acc) (A.lpZero w) =
      A.lpChar (L.foldr (fun k acc => A.lpSum (A.lpTw x (s - k)) acc) (A.lpZero w)) c := by
  induction L with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) c 0 hc).2.2).symm
  | cons k L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, (hL w _ _ c 0 hc).1, (hL w _ (A.lpZero w) c _ hc).2.1]

theorem spehLoc_twist (hL : CharSum N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  simp only [A.locG_tw]
  exact foldr_lpSum_lpTw_lpChar N A hL (A.locG p.π w) (A.locG χ w) (A.locG_dim χ w) _ _

theorem isoLoc_twist (hL : CharSum N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) (A.locG χ w) 0 hχ).2.2).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [spehLoc_twist N A hL p χ w, ih, (hL w _ _ _ 0 hχ).1]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil => exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

end GlobalTheory.LocCongrRoad
end
end

noncomputable section

namespace GlobalTheory.GoodDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem charSum_of_tie (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut)
    (hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b) :
    GlobalTheory.LiftLeaf.CharSum D.nd D.naut := by
  intro w a b χ s hχ
  obtain ⟨h1, h2, -⟩ := hT w a b χ χ s hχ hχ
  refine ⟨h1, h2, ?_⟩
  have h := (hT w (D.naut.lpZero w) (D.naut.lpZero w) χ χ 0 hχ hχ).1
  rw [D.naut.lpSum_zero] at h
  refine hc w _ _ (D.naut.lpChar (D.naut.lpZero w) χ) ?_
  rw [← h, D.naut.lpSum_comm, D.naut.lpSum_zero]

theorem lpChar_eta_back (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut) (w : PlE D.host) (a : D.naut.LP w) :
    D.naut.lpChar (D.naut.lpChar a (D.naut.locG D.naut.etaTinv w)) (D.naut.locG D.naut.etaT w) = a := by
  have hu := D.naut.etaT_unr w
  obtain ⟨hu', he⟩ := D.naut.etaTinv_def w
  have hcard := D.naut.frobEig_card _ hu
  rw [D.naut.locG_dim] at hcard
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hc0 : c ≠ 0 := by
    intro h0
    apply D.naut.frobEig_ne_zero _ hu
    rw [hc, h0]
    exact Multiset.mem_singleton_self _
  rw [hc, Multiset.map_singleton] at he
  have key := GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c hu' hu (D.naut.locG_dim _ w) he hc
    (inv_mul_cancel₀ hc0)
  obtain ⟨-, -, -, h4, h5, -⟩ := hT w a a (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0
    (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)
  rw [h4, key, h5]

end GlobalTheory.GoodDepthZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
noncomputable section

namespace GlobalTheory.VolAt

open Formalism.MainNotions.G Matrix

def homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) : Submodule W (Matrix (Fin k') (Fin k) Qq) where
  carrier := {x | ∀ z ∈ A, x *ᵥ z ∈ B}
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact B.zero_mem
  add_mem' := fun hx hy z hz => by rw [Matrix.add_mulVec]; exact B.add_mem (hx z hz) (hy z hz)
  smul_mem' := fun c x hx z hz => by
    rw [Matrix.smul_mulVec]
    exact B.smul_mem c (hx z hz)

theorem mem_homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) (x : Matrix (Fin k') (Fin k) Qq) :
    x ∈ homLat W A B ↔ ∀ z ∈ A, x *ᵥ z ∈ B := Iff.rfl

end GlobalTheory.VolAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgTAll
section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AlgTAll
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.ThLoc.Alg

theorem algTAll : Formalism.L2.KerInert.AlgTAll := by
  intro D cc δ B χ hcc hδ hχ N N' L L' hA t ht α
  have hC : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hT := GlobalTheory.Mem.Col2.JetAlgebraic.ta_thMoved B hC hA.2.2.1 hA.2.2.2
  have h := (GlobalTheory.Mem.Col2.JetAlgebraic.TA.comb (cc := cc) (δ := δ) (Finset.univ : Finset Unit)
    (fun _ => Base.chiFac χ N N' L L') (fun _ => B.thMoved N N' L L')
    (fun _ => GlobalTheory.MomT.FromComb.chiFac_mem hχ hA) (fun _ => hT)).2
  have e : (fun z => ∑ _a ∈ (Finset.univ : Finset Unit), Base.chiFac χ N N' L L' * B.thMoved N N' L L' z) =
      B.eNat χ N N' L L' := by
    funext z
    simp [Base.eNat]
  rw [e] at h
  obtain ⟨a, ha, hat⟩ := ht
  exact h t (GlobalTheory.ThetaAlgebraic.sat_of_nsmul ha
    (GlobalTheory.Mem.Col2.JetAlgebraic.la_le_sat hC hA.2.2.1 hA.2.2.2 hat)) α

end GlobalTheory.ThLoc.Alg
end
end

namespace GlobalTheory.ThLoc

theorem algTAll : Formalism.L2.KerInert.AlgTAll := GlobalTheory.ThLoc.Alg.algTAll

end GlobalTheory.ThLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PendTThFLtOfKapLawLt
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwU

theorem pendT_ThF_lt_of_kapLawLt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; KapLawLt X ℂ_[p] (thFOf X pos F) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La') ∧ ∀ v, ∀ j < X.mm, XiEx X ℂ_[p] (thFOf X pos F) v j → XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j := by
  intro p _ X _ E hfin hst g hLT T pos F
  intro hK
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  have h1 : ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La' := by
    rintro j hj ⟨c, L⟩ La' hL hL'
    change thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin (thFOf X pos F)) j (c, L) La' = _
    rw [thN_eq]
    generalize delt X hfin j c L = δ
    have hL2 : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul δ⁻¹ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ δ⁻¹ L).2 hL
    have := hK j hj c _ La' δ hL2 hL'
    rw [lsmul_lsmul_inv] at this
    exact this.symm
  refine ⟨h1, ?_⟩
  rintro v j hj ⟨Ξ, u, u', hu, hu', hΞ⟩
  refine ⟨Ξ, u, u', hu, hu', fun La La' hL hL' => ?_⟩
  rw [h1 j hj La La' hL hL']
  exact hΞ La La' hL hL'

end GlobalTheory.TwU
end
end

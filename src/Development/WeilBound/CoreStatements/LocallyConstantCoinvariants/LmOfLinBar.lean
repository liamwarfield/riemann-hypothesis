module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLinearFunctionals
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsUnitDetOfCartan
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Ar.RT

theorem det_ne_zero_of_cartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hx : star v ≠ 0 := fun e => hv (by simpa using congrArg star e)
  have := h.2.2 (star v) hx
  rw [star_star, hMv, dotProduct_zero] at this
  simp at this


open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem isUnit_det_of_cartan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (s : ℂ) (θ : Matrix (Fin n) (Fin n) ℂ)
    (h : IsCartan (s • J.map τ) θ) : IsUnit J.det := by
  refine isUnit_iff_ne_zero.mpr fun h0 => det_ne_zero_of_cartan h ?_
  rw [Matrix.det_smul, show (J.map τ).det = τ J.det from (RingHom.map_det τ J).symm, h0, map_zero, mul_zero]


end GlobalTheory.CompanionTheory.Ar.RT

end
end

section -- merged from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ActsFormula
section -- merged from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.EqZeroOfLocW
section -- merged from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdExistsInv
section -- merged from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdMulRight
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Sgl

variable {F : Type} [Field F] [NumberField F] {v : Pl F}

theorem ev_sgl (x : Fv F v) : evFin F v (sgl v x) = x := evalV_singleFin_self v x

theorem mul_sgl (a : AF F) (x : Fv F v) : a * sgl v x = sgl v (evFin F v a * x) := by
  refine Prod.ext (mul_zero _) ?_
  change a.2 * singleFin v x = singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2 * x)
  refine af_ext fun u => ?_
  rw [map_mul]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]

theorem kd_at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} : At (evFin F v) z ↔ sgl v 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · have := h (1 - sgl v 1) (by rw [map_sub, map_one, ev_sgl, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · rw [← h, smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]

theorem at_sgl_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (x : Fv F v) (z : M) : At (evFin F v) (sgl v x • z) :=
  fun u hu => by rw [smul_smul, mul_sgl, hu, zero_mul, map_zero, zero_smul]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_map {M N : Type} [AddCommGroup M] [Module (AF F) M] [AddCommGroup N] [Module (AF F) N] (f : M →ₗ[AF F] N) {z : M}
    (h : At (evFin F v) z) : At (evFin F v) (f z) := fun u hu => by rw [← map_smul, h u hu, map_zero]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_add {M : Type} [AddCommGroup M] [Module (AF F) M] {z z' : M} (h : At (evFin F v) z) (h' : At (evFin F v) z') :
    At (evFin F v) (z + z') := fun u hu => by rw [smul_add, h u hu, h' u hu, add_zero]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_sub {M : Type} [AddCommGroup M] [Module (AF F) M] {z z' : M} (h : At (evFin F v) z) (h' : At (evFin F v) z') :
    At (evFin F v) (z - z') := fun u hu => by rw [smul_sub, h u hu, h' u hu, sub_zero]

end Sgl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β γ : Type}

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_mul_right [Fintype β] {z : Matrix α β (AE F E)} (h : At (evFin F v) z) (m : Matrix β γ (AE F E)) :
    At (evFin F v) (z * m) := fun u hu => by rw [← Matrix.smul_mul, h u hu, Matrix.zero_mul]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_mul_left [Fintype β] {z : Matrix β γ (AE F E)} (h : At (evFin F v) z) (m : Matrix α β (AE F E)) :
    At (evFin F v) (m * z) := fun u hu => by rw [← Matrix.mul_smul, h u hu, Matrix.mul_zero]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At.kd_transpose {z : Matrix α β (AE F E)} (h : At (evFin F v) z) : At (evFin F v) zᵀ :=
  fun u hu => by rw [← Matrix.transpose_smul, h u hu, Matrix.transpose_zero]

theorem kd_at_matrix {z : Matrix α β (AE F E)} : At (evFin F v) z ↔ ∀ i j, At (evFin F v) (z i j) :=
  ⟨fun h i j u hu => congrFun (congrFun (h u hu) i) j, fun h u hu => Matrix.ext fun i j => h i j u hu⟩

def secM (sec : Fv F v × Fv F v → AE F E) (P Q : Matrix α β (Fv F v)) : Matrix α β (AE F E) := Matrix.of fun i j => sec (P i j, Q i j)

namespace IsSec

variable (h : IsSec σ t sec)
include h

theorem atM (P Q : Matrix α β (Fv F v)) : At (evFin F v) (secM sec P Q) := kd_at_matrix.2 fun _ _ => h.at' _

theorem fstM (P Q : Matrix α β (Fv F v)) : (secM sec P Q).map (piW t) = P := Matrix.ext fun _ _ => h.fst _

theorem sndM (P Q : Matrix α β (Fv F v)) : (secM sec P Q).map (piW (t.comp σ)) = Q := Matrix.ext fun _ _ => h.snd _

theorem extM {z z' : Matrix α β (AE F E)} (ha : At (evFin F v) (z - z')) (h1 : z.map (piW t) = z'.map (piW t))
    (h2 : z.map (piW (t.comp σ)) = z'.map (piW (t.comp σ))) : z = z' := Matrix.ext fun i j =>
  sub_eq_zero.1 (h.ext _ (kd_at_matrix.1 ha i j) (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j)
    (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j))

theorem conj1 (z : Matrix α β (AE F E)) : (z.map (cA σ)).map (piW t) = z.map (piW (t.comp σ)) := Matrix.ext fun _ _ => (h.conj _).1

theorem conj2 (z : Matrix α β (AE F E)) : (z.map (cA σ)).map (piW (t.comp σ)) = z.map (piW t) := Matrix.ext fun _ _ => (h.conj _).2

theorem smul1 (a : AF F) (z : Matrix α β (AE F E)) : (a • z).map (piW t) = evFin F v a • z.map (piW t) :=
  Matrix.ext fun _ _ => (h.smul _ _).1

theorem smul2 (a : AF F) (z : Matrix α β (AE F E)) : (a • z).map (piW (t.comp σ)) = evFin F v a • z.map (piW (t.comp σ)) :=
  Matrix.ext fun _ _ => (h.smul _ _).2

variable [Fintype β] [DecidableEq β]

theorem exists_gl (g₁ g₂ : GL β (Fv F v)) : ∃ g : GL β (AE F E), At (evFin F v) ((g : Matrix β β (AE F E)) - 1) ∧
    (g : Matrix β β (AE F E)).map (piW t) = g₁ ∧ (g : Matrix β β (AE F E)).map (piW (t.comp σ)) = g₂ := by
  have k1 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW t) = a := fun a b => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.fstM]; abel
  have k2 : ∀ a b : Matrix β β (Fv F v), (1 + secM sec (a - 1) (b - 1)).map (piW (t.comp σ)) = b := fun a b => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), h.sndM]; abel
  have k3 : ∀ a b a' b' : Matrix β β (Fv F v), a * a' = 1 → b * b' = 1 →
      (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) = 1 := fun a b a' b' e1 e2 => by
    refine h.extM ?_ ?_ ?_
    · have : (1 + secM sec (a - 1) (b - 1)) * (1 + secM sec (a' - 1) (b' - 1)) - 1 =
          secM sec (a - 1) (b - 1) * (1 + secM sec (a' - 1) (b' - 1)) + secM sec (a' - 1) (b' - 1) := by noncomm_ring
      rw [this]
      exact ((h.atM _ _).kd_mul_right _).kd_add (h.atM _ _)
    · rw [Matrix.map_mul, k1, k1, e1, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, k2, k2, e2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨1 + secM sec (g₁.1 - 1) (g₂.1 - 1), 1 + secM sec ((g₁⁻¹).1 - 1) ((g₂⁻¹).1 - 1), k3 _ _ _ _ g₁.mul_inv g₂.mul_inv,
    k3 _ _ _ _ g₁.inv_mul g₂.inv_mul⟩, ?_, k1 _ _, k2 _ _⟩
  rw [Units.val_mk, add_sub_cancel_left]
  exact h.atM _ _

theorem unit_rel {J : Matrix β β (AE F E)} (g : UG (cA σ) J) :
    (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t))ᵀ * J.map (piW t) *
      ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW (t.comp σ)) = J.map (piW t) := by
  have := congrArg (fun m : Matrix β β (AE F E) => m.map (piW t))
    (show ((g : GL β (AE F E)) : Matrix β β (AE F E))ᵀ * J * ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (cA σ) = J from g.2)
  rwa [Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map] at this

theorem exists_ug {J : Matrix β β (AE F E)} {ε : Fv F v} (hJ : J.map (piW (t.comp σ)) = ε • (J.map (piW t))ᵀ)
    (hu : IsUnit (J.map (piW t))) (g₀ : GL β (Fv F v)) : ∃ g : UG (cA σ) J,
      At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1) ∧
      ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀ := by
  obtain ⟨B, hB⟩ := hu
  let gT : GL β (Fv F v) := ⟨(g₀.1)ᵀ, ((g₀⁻¹).1)ᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
  obtain ⟨g, ha, h1, h2⟩ := h.exists_gl g₀ (B⁻¹ * gT⁻¹ * B)
  have key : (g₀.1)ᵀ * B.1 * (B⁻¹ * gT⁻¹ * B).1 = B.1 := by
    have : gT * B * (B⁻¹ * gT⁻¹ * B) = B := by group
    exact congrArg Units.val this
  refine ⟨⟨g, ?_⟩, ha, h1⟩
  change (g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) = J
  refine h.extM ?_ ?_ ?_
  · have e : (g : Matrix β β (AE F E))ᵀ * J * (g : Matrix β β (AE F E)).map (cA σ) - J =
        ((g : Matrix β β (AE F E)) - 1)ᵀ * (J * (g : Matrix β β (AE F E)).map (cA σ)) +
          J * ((g : Matrix β β (AE F E)) - 1).map (cA σ) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), transpose_sub, transpose_one]
      noncomm_ring
    rw [e]
    exact (ha.kd_transpose.kd_mul_right _).kd_add (At.kd_mul_left (kd_at_matrix.2 fun i j => h.atConj _ (kd_at_matrix.1 ha i j)) _)
  · rw [Matrix.map_mul, Matrix.map_mul, h.conj1, Matrix.transpose_map, h1, h2, ← hB, key]
  · rw [Matrix.map_mul, Matrix.map_mul, h.conj2, Matrix.transpose_map, h1, h2, hJ, ← hB, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have := congrArg Matrix.transpose key
    rwa [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this

theorem ug_ext {J : Matrix β β (AE F E)} (hu : IsUnit (J.map (piW t))) {g g' : UG (cA σ) J}
    (ha : At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1))
    (ha' : At (evFin F v) (((g' : GL β (AE F E)) : Matrix β β (AE F E)) - 1))
    (e : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = ((g' : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t)) :
    g = g' := by
  refine Subtype.ext (Units.ext (h.extM (by simpa using ha.kd_sub ha') e ?_))
  have h1 := h.unit_rel g
  have h2 := h.unit_rel g'
  rw [← e] at h2
  have hg : IsUnit (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t))ᵀ :=
    (Matrix.isUnit_transpose _).2 ((g : GL β (AE F E)).isUnit.map (piW t).mapMatrix)
  exact (hg.mul hu).mul_left_cancel (h1.trans h2.symm)

end IsSec

end PositivityTheory.KCo
end
end

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] {α β : Type} [Fintype α] [Fintype β]

def ofM (Y : Matrix α β k) : α × β → k := fun p => Y p.1 p.2

def toM (y : α × β → k) : Matrix α β k := Matrix.of fun i j => y (i, j)

omit [Field k] [Fintype α] [Fintype β] in
@[simp] theorem toM_ofM (Y : Matrix α β k) : toM (ofM Y) = Y := rfl

omit [Field k] [Fintype α] [Fintype β] in
@[simp] theorem ofM_toM (y : α × β → k) : ofM (toM y) = y := rfl

theorem dot_ofM (Y Z : Matrix α β k) : ofM Y ⬝ᵥ ofM Z = trace (Yᵀ * Z) := by
  simp only [dotProduct, ofM, Fintype.sum_prod_type, trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) : schr ψ a (schr ψ b φ) = ψ (⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)) • schr ψ (a + b) φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc,
    add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) + ⅟(2 : R) = 1 := invOf_two_add_invOf_two
  linear_combination (a.1 ⬝ᵥ b.2) * (-h)

variable [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k]

theorem schr_mem [Invertible (2 : k)] {ψ : AddChar k ℂ} (hψ : Continuous ψ) {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k))
    {φ : (κ → k) → ℂ} (h : φ ∈ SB (κ → k)) : schr ψ w φ ∈ SB (κ → k) := by
  haveI := nonarch_field k
  have hl := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ
  refine ⟨(hl.comp_continuous (by fun_prop)).mul (h.1.comp_continuous (by fun_prop)), ?_⟩
  exact (h.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left

variable [DecidableEq β]

def rm (g : GL β k) : (α × β → k) ≃ₜ (α × β → k) where
  toFun y := ofM (toM y * g.1)
  invFun y := ofM (toM y * (g⁻¹).1)
  left_inv y := by simp only [toM_ofM, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ofM_toM]
  right_inv y := by simp only [toM_ofM, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ofM_toM]
  continuous_toFun := continuous_pi fun p => by simp only [ofM, toM, Matrix.mul_apply, of_apply]; fun_prop
  continuous_invFun := continuous_pi fun p => by simp only [ofM, toM, Matrix.mul_apply, of_apply]; fun_prop

def rmL (g : GL β k) : Module.End ℂ ((α × β → k) → ℂ) := LinearMap.funLeft ℂ ℂ (rm g)

theorem rmL_apply (g : GL β k) (Φ : (α × β → k) → ℂ) (y) : rmL g Φ y = Φ (ofM (toM y * g.1)) := rfl

theorem rmL_mem (g : GL β k) {Φ : (α × β → k) → ℂ} (h : Φ ∈ SB (α × β → k)) : rmL g Φ ∈ SB (α × β → k) :=
  ⟨h.1.comp_continuous (rm g).continuous, h.2.comp_homeomorph (rm g)⟩

theorem rmL_inv (g : GL β k) (Φ : (α × β → k) → ℂ) : rmL g⁻¹ (rmL g Φ) = Φ := funext fun y => by
  simp only [rmL_apply, toM_ofM, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ofM_toM]

theorem rmL_schr [Invertible (2 : k)] (ψ : AddChar k ℂ) (g : GL β k) (w) (Φ : (α × β → k) → ℂ) :
    rmL g (schr ψ w Φ) = schr ψ (ofM (toM w.1 * (g⁻¹).1), ofM (toM w.2 * (g.1)ᵀ)) (rmL g Φ) := funext fun y => by
  have e1 : ofM (toM y * g.1) ⬝ᵥ w.2 = y ⬝ᵥ ofM (toM w.2 * (g.1)ᵀ) := by
    rw [← ofM_toM w.2, ← ofM_toM y, dot_ofM, dot_ofM]
    simp only [toM_ofM, transpose_mul, Matrix.mul_assoc]
    rw [trace_mul_comm, Matrix.mul_assoc]
  have e2 : w.1 ⬝ᵥ w.2 = ofM (toM w.1 * (g⁻¹).1) ⬝ᵥ ofM (toM w.2 * (g.1)ᵀ) := by
    rw [dot_ofM, transpose_mul, Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc _ (g.1)ᵀ, ← transpose_mul,
      Units.inv_mul, transpose_one, Matrix.mul_one, ← dot_ofM]; rfl
  have e3 : ofM (toM y * g.1) + w.1 = ofM (toM (y + ofM (toM w.1 * (g⁻¹).1)) * g.1) := by
    have : toM (y + ofM (toM w.1 * (g⁻¹).1)) = toM y + toM w.1 * (g⁻¹).1 := rfl
    rw [this, Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]; rfl
  simp only [rmL_apply, schr]
  rw [e1, e3, ← e2]

omit [DecidableEq β] [ValuativeRel k] [IsNonarchimedeanLocalField k] [Field k] in
theorem kd_exists_inv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) : ∃ j : (Y → ℂ) →ₗ[ℂ] (X → ℂ),
      (∀ Φ ∈ SB Y, j Φ ∈ SB X ∧ ι (j Φ) = Φ) ∧ ∀ φ ∈ SB X, j (ι φ) = φ := by
  let e : SB X ≃ₗ[ℂ] SB Y := LinearEquiv.ofBijective (ι.restrict fun φ h => hb.1 h)
    ⟨fun a b h => Subtype.ext (hb.2.1 a.2 b.2 (congrArg Subtype.val h)), fun b => by
      obtain ⟨a, ha, e⟩ := hb.2.2 b.2
      exact ⟨⟨a, ha⟩, Subtype.ext e⟩⟩
  obtain ⟨j, hj⟩ := LinearMap.exists_extend ((SB X).subtype ∘ₗ e.symm.toLinearMap)
  have h1 : ∀ Φ (h : Φ ∈ SB Y), j Φ = (e.symm ⟨Φ, h⟩).1 := fun Φ h => LinearMap.congr_fun hj ⟨Φ, h⟩
  have h2 : ∀ Φ ∈ SB Y, j Φ ∈ SB X ∧ ι (j Φ) = Φ := fun Φ h => by
    rw [h1 Φ h]
    exact ⟨(e.symm _).2, congrArg Subtype.val (e.apply_symm_apply ⟨Φ, h⟩)⟩
  exact ⟨j, h2, fun φ h => hb.2.1 (h2 _ (hb.1 h)).1 h (h2 _ (hb.1 h)).2⟩

end Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}


variable (σ t JA JB) in
structure Grams : Prop where
  uA : IsUnit (JA.map (piW t))
  uB : IsUnit (JB.map (piW t))
  sym : ∃ ε : Fv F v, ε * ε = 1 ∧ JA.map (piW (t.comp σ)) = ε • (JA.map (piW t))ᵀ ∧
    JB.map (piW (t.comp σ)) = (-ε) • (JB.map (piW t))ᵀ


variable (σ t JA JB) in
def coord (u : Matrix α β (AE F E)) : (α × β → Fv F v) × (α × β → Fv F v) :=
  (ofM (-(JA.map (piW t) * u.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ)), ofM (-u.map (piW t)))

theorem symp_eq (h : IsSec σ t sec) (hG : Grams σ t JA JB) {u : Matrix α β (AE F E)} (hu : At (evFin F v) u)
    (u' : Matrix α β (AE F E)) : symp (R := AF F) (cA σ) (-1) JA JB u u' = sgl v
      ((coord σ t JA JB u).1 ⬝ᵥ (coord σ t JA JB u').2 - (coord σ t JA JB u').1 ⬝ᵥ (coord σ t JA JB u).2) := by
  obtain ⟨ε, hε, hA, hB⟩ := hG.sym
  have e : hTens (cA σ) JA JB u u' = trace (JAᵀ * u * JB * (u'.map (cA σ))ᵀ) := by
    simp only [hTens, trace, diag, Matrix.mul_apply, dotProduct, transpose_apply, map_apply, Finset.sum_mul]
    calc _ = ∑ i, ∑ k, ∑ j, ∑ l, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ j, ∑ i, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_congr rfl fun k _ => by
        rw [Finset.sum_comm]
        calc _ = ∑ j, ∑ l, ∑ i, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => by ring
  have ha : At (evFin F v) (-1 * hTens (cA σ) JA JB u u') := fun a ha => by
    rw [e, ← mul_smul_comm, ← trace_smul, (((hu.kd_mul_left JAᵀ).kd_mul_right JB).kd_mul_right _) a ha, trace_zero, mul_zero]
  rw [symp, h.trace _ ha, e]
  congr 1
  simp only [map_mul, map_neg, map_one, AddMonoidHom.map_trace, Matrix.map_mul, transpose_map, h.conj1, h.conj2, hA, hB, coord, dot_ofM,
    transpose_smul, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, smul_eq_mul, transpose_neg,
    transpose_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, trace_neg]
  set A := JA.map (piW t)
  set B := JB.map (piW t)
  set P := u.map (piW t)
  set Q := u.map (piW (t.comp σ))
  set P' := u'.map (piW t)
  set Q' := u'.map (piW (t.comp σ))
  have e1 : trace (B * (Q'ᵀ * Aᵀ) * P) = trace (Aᵀ * P * B * Q'ᵀ) := by
    rw [Matrix.mul_assoc (Aᵀ * P), trace_mul_comm (Aᵀ * P)]; simp only [Matrix.mul_assoc]
  have e2 : trace (B * (Qᵀ * Aᵀ) * P') = trace (A * Q * Bᵀ * P'ᵀ) := by
    rw [← trace_transpose, transpose_mul, trace_mul_comm]; simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e1, e2]
  linear_combination (trace (A * Q * Bᵀ * P'ᵀ)) * hε

end PositivityTheory.KCo
end
end

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}

theorem locW_smul (a : AF F) (w : (κ → AF F) × (κ → AF F)) : locW v (a • w) = evFin F v a • locW v w :=
  Prod.ext (funext fun i => map_mul (evFin F v) _ _) (funext fun i => map_mul (evFin F v) _ _)

theorem locW_add (w w' : (κ → AF F) × (κ → AF F)) : locW v (w + w') = locW v w + locW v w' :=
  Prod.ext (funext fun i => map_add (evFin F v) _ _) (funext fun i => map_add (evFin F v) _ _)

theorem eq_zero_of_locW {w : (κ → AF F) × (κ → AF F)} (ha : At (evFin F v) w) (h : locW v w = 0) : w = 0 := by
  rw [← kd_at_iff.1 ha]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have : evFin F v (w.1 i) = 0 := congrFun (congrArg Prod.fst h) i
    change sgl v 1 * w.1 i = 0
    rw [mul_comm, mul_sgl, this, zero_mul, map_zero]
  · have : evFin F v (w.2 i) = 0 := congrFun (congrArg Prod.snd h) i
    change sgl v 1 * w.2 i = 0
    rw [mul_comm, mul_sgl, this, zero_mul, map_zero]

theorem ev_dot (a b : κ → AF F) : evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ fun i => evFin F v (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul]

theorem coord_add (u u' : Matrix α β (AE F E)) : coord σ t JA JB (u + u') = coord σ t JA JB u + coord σ t JA JB u' := by
  simp only [coord, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, neg_add]
  rfl

theorem coord_smul (h : IsSec σ t sec) (a : AF F) (u : Matrix α β (AE F E)) :
    coord σ t JA JB (a • u) = evFin F v a • coord σ t JA JB u := by
  simp only [coord, h.smul1, h.smul2, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]
  rfl

theorem exists_coord (h : IsSec σ t sec) (hG : Grams σ t JA JB) (w : (α × β → Fv F v) × (α × β → Fv F v)) :
    ∃ u, At (evFin F v) u ∧ coord σ t JA JB u = w ∧ (w.1 = 0 → u.map (piW (t.comp σ)) = 0) := by
  obtain ⟨A, hA⟩ := hG.uA
  obtain ⟨B, hB⟩ := hG.uB
  refine ⟨secM sec (-toM w.2) (-((A⁻¹).1 * toM w.1 * ((B⁻¹).1)ᵀ)), h.atM _ _, ?_, fun h0 => ?_⟩
  · rw [coord, h.fstM, h.sndM, ← hA, ← hB, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.mul_one]
    rfl
  · rw [h.sndM, h0, show toM (0 : α × β → Fv F v) = 0 from rfl, Matrix.mul_zero, Matrix.zero_mul, neg_zero]

theorem coord_inj (h : IsSec σ t sec) (hG : Grams σ t JA JB) {u : Matrix α β (AE F E)} (ha : At (evFin F v) u)
    (h0 : coord σ t JA JB u = 0) : u = 0 := by
  obtain ⟨A, hA⟩ := hG.uA
  obtain ⟨B, hB⟩ := hG.uB
  have h1 : -(JA.map (piW t) * u.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ) = 0 := congrArg toM (congrArg Prod.fst h0)
  have h2 : -u.map (piW t) = 0 := congrArg toM (congrArg Prod.snd h0)
  refine h.extM (by rwa [sub_zero]) (by rw [neg_eq_zero.1 h2, Matrix.map_zero _ (map_zero _)]) ?_
  rw [neg_eq_zero, ← hA, ← hB] at h1
  have := congrArg (fun m => (A⁻¹).1 * m * ((B⁻¹).1)ᵀ) h1
  simp only [Matrix.mul_zero, Matrix.zero_mul] at this
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul,
    transpose_one, Matrix.mul_one, ← Matrix.map_zero (piW (t.comp σ)) (map_zero _)] at this

theorem exists_e (h : IsSec σ t sec) (hG : Grams σ t JA JB) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) :
    ∃ e : ((α × β → Fv F v) × (α × β → Fv F v)) ≃ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)),
      (∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) ∧
      ∀ u, e (coord σ t JA JB u) = locW v (d.e u) := by
  choose s hs1 hs2 _ using exists_coord h hG
  have key : ∀ u, locW v (d.e (s (coord σ t JA JB u))) = locW v (d.e u) := fun u => by
    have : s (coord σ t JA JB u) = sgl v 1 • u := by
      refine sub_eq_zero.1 (coord_inj h hG ((hs1 _).kd_sub (at_sgl_smul _ _)) ?_)
      rw [sub_eq_add_neg, ← neg_smul, coord_add, coord_smul h, hs2, map_neg, ev_sgl, neg_smul, one_smul, add_neg_cancel]
    rw [this, map_smul, locW_smul, ev_sgl, one_smul]
  let f : ((α × β → Fv F v) × (α × β → Fv F v)) →ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun w => locW v (d.e (s w))
      map_add' := fun w w' => by rw [← locW_add, ← map_add (f := _), ← key (s w + s w'), coord_add, hs2, hs2]
      map_smul' := fun a w => by
        have := key (sgl v a • s w)
        rw [coord_smul h, hs2, ev_sgl, map_smul, locW_smul, ev_sgl] at this
        exact this }
  have hb : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun w hw => ?_, fun w => ?_⟩
    · have h1 : s w = 0 := d.e.map_eq_zero_iff.1 (eq_zero_of_locW ((hs1 w).kd_map d.e.toLinearMap) hw)
      rw [← hs2 w, h1, ← zero_smul (AF F) (0 : Matrix α β (AE F E)), coord_smul h, map_zero, zero_smul]
    · refine ⟨coord σ t JA JB (d.e.symm (fun i => sgl v (w.1 i), fun i => sgl v (w.2 i))), (key _).trans ?_⟩
      rw [LinearEquiv.apply_symm_apply]
      exact Prod.ext (funext fun i => ev_sgl _) (funext fun i => ev_sgl _)
  refine ⟨LinearEquiv.ofBijective f hb, fun w w' => ?_, key⟩
  have := congrArg (evFin F v) ((d.form (s w) (s w')).symm.trans (symp_eq h hG (hs1 w) (s w')))
  rwa [ev_sgl, hs2, hs2, map_sub, ev_dot, ev_dot] at this


variable (t ψ) in
structure LM (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (ι : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((α × β → Fv F v) → ℂ)) : Prop where
  bij : Set.BijOn ι (SB (κ → Fv F v) : Set _) (SB (α × β → Fv F v) : Set _)
  Heisenberg₂ : ∀ u, ∀ φ ∈ SB (κ → Fv F v), ι (schr (psiV ψ v) (locW v (d.e u)) φ) = schr (psiV ψ v) (coord σ t JA JB u) (ι φ)

theorem exists_lm (hM : ModelEx) (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t JA JB)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) : ∃ ι, LM t ψ d ι := by
  obtain ⟨e, h1, h2⟩ := exists_e h hG d
  obtain ⟨ι, hb, hι⟩ := hM _ κ (α × β) (psiV ψ v) ((hA.psi F ψ hψ).2 v).1 ((hA.psi F ψ hψ).2 v).2 e h1
  exact ⟨ι, hb, fun u φ hφ => by rw [← h2, hι _ φ hφ]⟩

theorem coord_actB (h : IsSec σ t sec) (g : UG (cA σ) JB) (g₀ : GL β (Fv F v))
    (hg : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀) (u : Matrix α β (AE F E)) :
    coord σ t JA JB (actB (cA σ) g u) =
      (ofM (toM (coord σ t JA JB u).1 * (g₀⁻¹).1), ofM (toM (coord σ t JA JB u).2 * (g₀.1)ᵀ)) := by
  have h1 := h.unit_rel g
  rw [hg] at h1
  have h2 : (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW (t.comp σ)))ᵀ * (JB.map (piW t))ᵀ =
      (JB.map (piW t))ᵀ * (g₀⁻¹).1 := by
    have := congrArg (fun m => mᵀ * (g₀⁻¹).1) h1
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
    exact this
  simp only [coord, actB, toM_ofM, Matrix.map_mul, transpose_map, hg, Matrix.neg_mul, Matrix.mul_assoc, h2]

theorem acts_scalar (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t JA JB)
    {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {ι} (hι : LM t ψ d ι)
    {j : ((α × β → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)} (hj : ∀ Φ ∈ SB _, j Φ ∈ SB _ ∧ ι (j Φ) = Φ)
    {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)} (hom : IsSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (g : UG (cA σ) JB) (ha : At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1)) (g₀ : GL β (Fv F v))
    (hg : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (om g) φ (c • j (rmL g₀ (ι φ))) := by
  obtain ⟨e, -, he⟩ := exists_e h hG d
  have hc := ((hA.psi F ψ hψ).2 v).1
  have m : ∀ (a : GL β (Fv F v)), ∀ φ ∈ SB (κ → Fv F v), rmL a (ι φ) ∈ SB _ := fun a φ hφ => rmL_mem a (hι.bij.1 hφ)
  have inv : ∀ (a : GL β (Fv F v)), ∀ φ ∈ SB (κ → Fv F v), j (rmL a⁻¹ (ι (j (rmL a (ι φ))))) = φ := fun a φ hφ => by
    rw [(hj _ (m a φ hφ)).2, rmL_inv]
    exact hι.bij.2.1 (hj _ (hι.bij.1 hφ)).1 hφ (hj _ (hι.bij.1 hφ)).2
  have hh : ∀ w, ∀ φ ∈ SB (κ → Fv F v), ι (schr (psiV ψ v) (e w) φ) = schr (psiV ψ v) w (ι φ) := fun w φ hφ => by
    obtain ⟨u, -, rfl, -⟩ := exists_coord h hG w
    rw [he, hι.Heisenberg₂ u φ hφ]
  refine hA.act F κ ψ hψ v (om g) (fun w => d.e (actB (cA σ) g (d.e.symm w))) (j ∘ₗ rmL g₀ ∘ₗ ι) (j ∘ₗ rmL g₀⁻¹ ∘ₗ ι)
    (fun w => e (ofM (toM (e.symm w).1 * (g₀⁻¹).1), ofM (toM (e.symm w).2 * (g₀.1)ᵀ))) (hom.pres g) (hom.adm g)
    (fun w Φ hΦ => ?_) (fun φ hφ => ⟨(hj _ (m _ φ hφ)).1, (hj _ (m _ φ hφ)).1, inv _ φ hφ, ?_⟩) (fun w φ hφ => ?_) fun w => ⟨?_, ?_⟩
  · have := hom.impl g (d.e.symm w) Φ hΦ
    simpa only [Darboux.rho, LinearEquiv.apply_symm_apply] using this
  · simpa only [inv_inv, LinearMap.comp_apply] using inv g₀⁻¹ φ hφ
  · obtain ⟨w, rfl⟩ := e.surjective w
    have h1 := (hj _ (m g₀ φ hφ))
    refine hι.bij.2.1 (hj _ (m _ _ (schr_mem hc _ hφ))).1 (schr_mem hc _ h1.1) ?_
    simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    rw [(hj _ (m _ _ (schr_mem hc _ hφ))).2, hh _ _ h1.1, h1.2, hh _ _ hφ, rmL_schr]
  · obtain ⟨u, rfl⟩ := d.e.surjective w
    simp only [LinearEquiv.symm_apply_apply]
    rw [← he, ← he, LinearEquiv.symm_apply_apply, coord_actB h g g₀ hg]
  · obtain ⟨u, rfl⟩ := d.e.surjective w
    simp only [LinearEquiv.symm_apply_apply]
    rw [← map_sub, show actB (cA σ) g u - u = u * (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1)ᵀ by
      rw [actB, transpose_sub, transpose_one, Matrix.mul_sub, Matrix.mul_one]]
    exact (ha.kd_transpose.kd_mul_left u).kd_map d.e.toLinearMap

end PositivityTheory.KCo
end
end

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}

theorem schr_box {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ']
    (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁) (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Function.comp_apply, mul_add, AddChar.map_add_eq_mul]
  rw [show (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl from rfl, show (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr from rfl]
  ring

theorem schr_zero' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (φ : (κ → R) → ℂ) :
    schr ψ (0, 0) φ = φ := by
  funext x
  simp [schr]

def tensL (v : Pl F) (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ r
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _

def boxL {R κ κ' : Type} (Φ₂ : (κ' → R) → ℂ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) where
  toFun Φ := boxFun Φ Φ₂
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _

theorem tens_box (φ₁ φ₂ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r r) = boxFun (tens (evFin F v) φ₁ r) (tens (evFin F v) φ₂ r) :=
  funext fun _ => mul_mul_mul_comm _ _ _ _

theorem Grams.dbl (hG : Grams σ t JA JB) : Grams σ t JA (dbl JB) := by
  have e : ∀ f : AE F E →+* Fv F v, (GlobalTheory.WeilM.dbl JB).map f = fromBlocks (JB.map f) 0 0 (-JB.map f) := fun f => by
    rw [GlobalTheory.WeilM.dbl, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  obtain ⟨ε, h1, h2, h3⟩ := hG.sym
  refine ⟨hG.uA, ?_, ε, h1, h2, ?_⟩
  · rw [e, Matrix.isUnit_iff_isUnit_det, det_fromBlocks_zero₂₁, det_neg]
    have := (Matrix.isUnit_iff_isUnit_det _).1 hG.uB
    exact this.mul ((isUnit_one.neg.pow _).mul this)
  · rw [e, e, h3, fromBlocks_transpose, fromBlocks_smul]
    simp

theorem acts_formula (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t JA JB)
    {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {ι} (hι : LM t ψ d ι) {χ : Chr F E}
    {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)} (hom : IsWeilB (cA σ) (adeleClass F) ψ (-1) JA JB d χ om)
    (g : UG (cA σ) JB) (ha : At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1)) (g₀ : GL β (Fv F v))
    (hg : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀) :
    ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om g) φ φ₁ ∧
      ι φ₁ = ((chrW χ t (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card α : ℂ) / 2)) • rmL g₀ (ι φ) := by
  obtain ⟨hs, dd, omd, hdd, hsd, hR, hbox⟩ := hom
  obtain ⟨hc, h1⟩ := (hA.psi F ψ hψ).2 v
  obtain ⟨j, hj, hj'⟩ := kd_exists_inv hι.bij
  obtain ⟨c, hcA⟩ := acts_scalar hA hψ h hG hι hj hs g ha g₀ hg
  suffices hcs : c = (chrW χ t (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card α : ℂ) / 2) from fun φ hφ =>
    have := hj _ (rmL_mem g₀ (hι.bij.1 hφ))
    ⟨_, Submodule.smul_mem _ _ this.1, hcA φ hφ, by rw [map_smul, this.2, hcs]⟩
  have hG2 := hG.dbl
  obtain ⟨ε, -, -, hε⟩ := hG2.sym
  obtain ⟨ι₂, hι₂⟩ := exists_lm hM hA hψ h hG2 dd
  obtain ⟨j₂, hj₂, -⟩ := kd_exists_inv hι₂.bij
  let X₀ : GL (β ⊕ β) (Fv F v) := ⟨fromBlocks 1 0 (-1) 1, fromBlocks 1 0 1 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩
  let P₀ : GL (β ⊕ β) (Fv F v) := ⟨fromBlocks g₀.1 0 (g₀.1 - 1) 1, fromBlocks (g₀⁻¹).1 0 ((g₀⁻¹).1 - 1) 1,
    by simp [fromBlocks_multiply, Matrix.sub_mul], by simp [fromBlocks_multiply, Matrix.sub_mul]⟩
  obtain ⟨x, hxa, hx⟩ := h.exists_ug hε hG2.uB X₀
  obtain ⟨p, hpa, hp⟩ := h.exists_ug hε hG2.uB P₀
  obtain ⟨gd, hgd⟩ := GlobalTheory.CompanionTheory.ThetaMember.exists_dbl_elem g
  obtain ⟨tt, hta, ht1, ht2⟩ := h.exists_gl g₀ 1
  have atm : ∀ {a b : Matrix (β ⊕ β) (β ⊕ β) (AE F E)}, At (evFin F v) (a - 1) → At (evFin F v) (b - 1) →
      At (evFin F v) (a * b - 1) := fun {a b} h1 h2 => by
    rw [show a * b - 1 = (a - 1) * b + (b - 1) by noncomm_ring]
    exact (h1.kd_mul_right _).kd_add h2
  have hga : At (evFin F v) (((gd : GL (β ⊕ β) (AE F E)) : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) - 1) := by
    rw [hgd, kd_at_matrix]
    rintro (i | i) (k | k) u hu
    · simpa [Matrix.one_apply, Sum.inl.injEq] using kd_at_matrix.1 ha i k u hu
    all_goals simp [Matrix.one_apply]
  have hxp : x * p = gd * x := h.ug_ext hG2.uB (atm hxa hpa) (atm hga hxa) (by
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx, hp, hgd, fromBlocks_map, hg,
      Matrix.map_zero _ (map_zero (piW t)), Matrix.map_one _ (map_zero (piW t)) (map_one _), X₀, P₀]
    simp [fromBlocks_multiply]
    abel)
  have cy : ∀ f : AE F E →+* Fv F v, (diagCols β : Matrix (β ⊕ β) β (AE F E)).map f = fromRows 1 1 := fun f => by
    rw [diagCols, fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have hpt : ((p : GL (β ⊕ β) (AE F E)) : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) * (diagCols β : Matrix (β ⊕ β) β (AE F E)) =
      (diagCols β : Matrix (β ⊕ β) β (AE F E)) * (tt : Matrix β β (AE F E)) := by
    refine h.extM ?_ ?_ ?_
    · have := (hpa.kd_mul_right (diagCols β)).kd_sub (hta.kd_mul_left (diagCols β))
      rwa [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, sub_sub_sub_cancel_right] at this
    · rw [Matrix.map_mul, Matrix.map_mul, hp, ht1, cy]
      simp [P₀, fromBlocks_mul_fromRows, fromRows_mul]
    · rw [Matrix.map_mul, Matrix.map_mul, ht2, cy, Units.val_one, Matrix.mul_one]
      have h2 := h.unit_rel p
      rw [hp] at h2
      have h3 : (P₀.1)ᵀ * (dbl JB).map (piW t) * fromRows (1 : Matrix β β (Fv F v)) (1 : Matrix β β (Fv F v)) =
          (dbl JB).map (piW t) * fromRows (1 : Matrix β β (Fv F v)) (1 : Matrix β β (Fv F v)) := by
        rw [dbl, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), Matrix.mul_assoc]
        simp [P₀, fromBlocks_transpose, fromBlocks_mul_fromRows, Matrix.sub_mul]
      obtain ⟨U, hU⟩ := ((Matrix.isUnit_transpose _).2 P₀.isUnit).mul hG2.uB
      have h4 := congrArg (fun m => (U⁻¹).1 * (m * fromRows (1 : Matrix β β (Fv F v)) (1 : Matrix β β (Fv F v)))) h2
      rwa [← h3, ← hU, Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc (U⁻¹).1 U.1, U.inv_mul, Matrix.one_mul,
        Matrix.one_mul] at h4
  obtain ⟨l, hl, hli, φ₀, hφ₀, r, hr, hrr, hne⟩ := hA.diag F κ ψ v
  have hl0 : ∀ z : Matrix α β (AE F E), ∀ Φ ∈ schA F (κ ⊕ κ), l (dd.rho ψ (fromCols z z) Φ) = l Φ := fun z Φ hΦ => by
    rw [Darboux.rho, hdd]; exact hli _ _ Φ hΦ
  have hsie := hR l hl (fun z Φ hΦ => by
    rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one]; exact hl0 z Φ hΦ) p tt hpt
  have hdet : At (evFin F v) (((GeneralLinearGroup.det tt : (AE F E)ˣ) : AE F E) - 1) := by
    rw [kd_at_iff, smul_sub, GeneralLinearGroup.val_det_apply]
    have e1 : (1 - sgl v 1 : AF F) • ((tt : Matrix β β (AE F E)) - 1) = 0 := hta _ (by rw [map_sub, map_one, ev_sgl, sub_self])
    let q := Ideal.Quotient.mk (Ideal.span {algebraMap (AF F) (AE F E) (sgl v 1)})
    have e2 : q.mapMatrix (tt : Matrix β β (AE F E)) = 1 := Matrix.ext fun a b => by
      have e3 := kd_at_iff.1 (kd_at_matrix.1 hta a b)
      rw [← map_one q.mapMatrix]
      exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨_, by rw [mul_comm, ← Algebra.smul_def]; exact e3⟩)
    have e4 : q ((tt : Matrix β β (AE F E)).det - 1) = 0 := by rw [map_sub, RingHom.map_det, e2, det_one, map_one q, sub_self]
    obtain ⟨a, ea⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 e4)
    rw [← smul_sub, ← ea, mul_comm, ← Algebra.smul_def]
    exact kd_at_iff.1 (at_sgl_smul 1 a)
  obtain ⟨i1, i2⟩ := h.idele (GeneralLinearGroup.det tt) (gdet g₀) hdet
    (by rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, ht1]; rfl)
    (by rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, ht2, Units.val_one, det_one])
  rw [i1, i2] at hsie
  have hs' : ((GlobalTheory.SplitWeil.nabs (Fv F v) (gdet g₀) ^ ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) =
      apow (gdet g₀) ((Fintype.card α : ℂ) / 2) := by
    rw [apow, Complex.ofReal_cpow (GlobalTheory.SplitWeil.Model.nabs_pos _).le]; push_cast; rfl
  rw [hs'] at hsie
  set s := (chrW χ t (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card α : ℂ) / 2)
  have xx : ∀ Φ, omd x⁻¹ (omd x Φ) = Φ := fun Φ => by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have k1 : ∀ Φ ∈ schA F (κ ⊕ κ), l (omd x⁻¹ (omd gd Φ)) = s * l (omd x⁻¹ Φ) := fun Φ hΦ => by
    rw [← hsie _ (hsd.pres x⁻¹ Φ hΦ), ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      show x⁻¹ * gd = p * x⁻¹ by rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hxp, mul_inv_cancel_right]]
  have k2 : ∀ u : Matrix α β (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ Φ ∈ schA F (κ ⊕ κ),
      l (omd x⁻¹ (dd.rho ψ (fromCols u 0) Φ)) = l (omd x⁻¹ Φ) := fun u hu h0 Φ hΦ => by
    have e : actB (cA σ) x (fromCols u u) = fromCols u 0 := by
      have a1 : ∀ u' : Matrix α β (AE F E), At (evFin F v) u' → At (evFin F v) (fromCols u u') := fun u' h' a ha => by
        ext i (k | k)
        · exact kd_at_matrix.1 hu i k a ha
        · exact kd_at_matrix.1 h' i k a ha
      refine h.extM (((a1 u hu).kd_mul_right _).kd_sub (a1 0 fun _ _ => smul_zero _)) ?_ ?_
      · rw [actB, Matrix.map_mul, transpose_map, hx, fromCols_map, fromCols_map, Matrix.map_zero _ (map_zero _)]
        simp [X₀, fromBlocks_transpose, fromCols_mul_fromBlocks]
      · rw [actB, Matrix.map_mul, fromCols_map, fromCols_map, h0, Matrix.map_zero _ (map_zero _), fromCols_zero, Matrix.zero_mul]
    have := hsd.impl x (fromCols u u) _ (hsd.pres x⁻¹ Φ hΦ)
    rw [e, ← Module.End.mul_apply (omd x) (omd x⁻¹), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [← this, xx, hl0 u _ (hsd.pres x⁻¹ Φ hΦ)]
  have hφne : φ₀ ≠ 0 := fun e => hne (by
    rw [e, show boxFun (tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r) (tens (evFin F v) 0 r) = 0 from
      funext fun _ => by simp [boxFun, tens], map_zero])
  have hbS := GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ₀ hφ₀
  have hbne : boxFun φ₀ φ₀ ≠ 0 := fun e => by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hφne
    exact mul_ne_zero hy hy (congrFun e (Sum.elim y y))
  have rest := hA.rest F κ v r φ₀ hφ₀ hφne hr
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, hnz⟩ : ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ → Fv F v),
      l (omd x⁻¹ (boxFun (tens (evFin F v) φ₁ r) (tens (evFin F v) φ₂ r))) ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨c₂, hc₂⟩ := acts_scalar hA hψ h hG2 hι₂ hj₂ hsd x hxa X₀ hx
    have := hC _ (κ ⊕ κ) (psiV ψ v) hc h1 _ hbS hbne (l ∘ₗ omd x⁻¹ ∘ₗ tensL v (boxFun r r)) (fun w => by
      rw [schr_box]
      exact (congrArg (fun Φ => l (omd x⁻¹ Φ)) (tens_box _ _ r)).trans (hno _ (schr_mem hc _ hφ₀) _ (schr_mem hc _ hφ₀))) _
      (Submodule.smul_mem _ c₂ (hj₂ _ (rmL_mem X₀ (hι₂.bij.1 hbS))).1)
    refine hne ?_
    rw [← tens_box, ← xx (tens _ _ _), hc₂ _ hbS _ hrr]
    exact this
  let m : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ := l ∘ₗ omd x⁻¹ ∘ₗ boxL (tens (evFin F v) φ₂ r) ∘ₗ tensL v r
  have bm : ∀ φ ∈ SB (κ → Fv F v), boxFun (tens (evFin F v) φ r) (tens (evFin F v) φ₂ r) ∈ schA F (κ ⊕ κ) := fun φ hφ =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ (rest φ hφ).2 _ (rest φ₂ hφ₂).2
  obtain ⟨a, hm⟩ := GlobalTheory.CompanionTheory.WeilCoinv.exists_eq_mul_apply_zero _ (α × β) (psiV ψ v) hc h1 (m ∘ₗ j) fun y Φ hΦ => by
    obtain ⟨u, hu, hco, h0⟩ := exists_coord h hG (0, y)
    obtain ⟨e1, e2⟩ := hj Φ hΦ
    have e3 : j (schr (psiV ψ v) (0, y) Φ) = schr (psiV ψ v) (locW v (d.e u)) (j Φ) := by
      rw [← hj' _ (schr_mem hc _ e1), hι.Heisenberg₂ u _ e1, hco, e2]
    have e4 := hA.Heisenberg₂ F κ ψ v (d.e u) (hu.kd_map d.e.toLinearMap) (j Φ) r (rest _ e1)
    change l (omd x⁻¹ (boxFun (tens _ (j _) r) _)) = l (omd x⁻¹ (boxFun (tens _ (j Φ) r) _))
    rw [e3, ← e4, ← k2 u hu (h0 rfl) _ (bm _ e1), Darboux.rho, hdd, schr_box, map_zero]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.fst_zero, Prod.snd_zero, neg_zero, schr_zero']
  have hm' : ∀ φ ∈ SB (κ → Fv F v), m φ = a * ι φ 0 := fun φ hφ => by
    rw [← hm _ (hι.bij.1 hφ), LinearMap.comp_apply m j, hj' φ hφ]
  have f1 := k1 _ (bm φ₁ hφ₁)
  rw [hbox g gd hgd _ (rest _ hφ₁).2 _ (rest _ hφ₂).2, hcA φ₁ hφ₁ r (rest _ hφ₁)] at f1
  have f2 := hj _ (rmL_mem g₀ (hι.bij.1 hφ₁))
  change m (c • _) = s * m φ₁ at f1
  rw [map_smul, hm' _ f2.1, f2.2, rmL_apply, show toM (0 : α × β → Fv F v) = 0 from rfl, Matrix.zero_mul,
    show ofM (0 : Matrix α β (Fv F v)) = 0 from rfl, ← hm' _ hφ₁, smul_eq_mul] at f1
  exact mul_right_cancel₀ hnz f1

end PositivityTheory.KCo
end
end

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}

theorem Grams.swap (hG : Grams σ t JA JB) : Grams σ t JB JA := by
  obtain ⟨ε, h1, h2, h3⟩ := hG.sym
  exact ⟨hG.uB, hG.uA, -ε, by rw [neg_mul_neg, h1], h3, by rw [neg_neg, h2]⟩

theorem bij_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) (e : Z ≃ₜ Y) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ e ∘ₗ ι) (SB X : Set _) (SB Z : Set _) := by
  have hb' : Set.BijOn (LinearMap.funLeft ℂ ℂ e) (SB Y : Set _) (SB Z : Set _) := by
    refine ⟨fun Φ h => ?_, fun a _ b _ h => funext fun y => ?_, fun Φ h => ⟨Φ ∘ e.symm, ?_, funext fun z => by simp⟩⟩
    · exact And.intro (h.1.comp_continuous e.continuous) (h.2.comp_homeomorph e)
    · simpa using congrFun h (e.symm y)
    · exact And.intro (h.1.comp_continuous e.symm.continuous) (h.2.comp_homeomorph e.symm)
  exact hb'.comp hb

def swH (k α β : Type) [TopologicalSpace k] : (β × α → k) ≃ₜ (α × β → k) := Homeomorph.piCongrLeft (Y := fun _ => k) (Equiv.prodComm β α)

theorem swH_apply {k α β : Type} [TopologicalSpace k] (y : β × α → k) : swH k α β y = fun p => y p.swap := by
  funext p
  simp [swH, Homeomorph.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

def ofH (k α β : Type) [TopologicalSpace k] : Matrix α β k ≃ₜ (α × β → k) where
  toFun := ofM
  invFun := toM
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

theorem LM.swap {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {ι} (hι : LM t ψ d ι)
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} (hd : ∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) :
    LM t ψ d' (LinearMap.funLeft ℂ ℂ (swH (Fv F v) α β) ∘ₗ ι) := by
  refine ⟨bij_comp hι.bij _, fun u φ hφ => funext fun y => ?_⟩
  have e1 : (coord σ t JA JB uᵀ).1 = fun p => (coord σ t JB JA u).1 p.swap := by
    have : JA.map (piW t) * uᵀ.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ =
        (JB.map (piW t) * u.map (piW (t.comp σ)) * (JA.map (piW t))ᵀ)ᵀ := by
      rw [transpose_mul, transpose_mul, transpose_transpose, transpose_map, Matrix.mul_assoc]
    rw [coord, this]; rfl
  have e2 : (coord σ t JA JB uᵀ).2 = fun p => (coord σ t JB JA u).2 p.swap := rfl
  have dt : ∀ a b : β × α → Fv F v, (fun p : α × β => a p.swap) ⬝ᵥ (fun p => b p.swap) = a ⬝ᵥ b := fun a b =>
    (Equiv.prodComm α β).sum_comp fun p => a p * b p
  rw [← transpose_transpose u, hd, transpose_transpose]
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hι.Heisenberg₂ _ φ hφ, schr, swH_apply, e1, e2, dt]
  rfl

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}

theorem incM_map (h : IsSec σ t sec) {a b : Type} (J : Matrix a b E) : (incM F J).map (piW t) = J.map t :=
  Matrix.ext fun i j => by rw [incM, map_apply, map_apply, map_apply]; exact (h.inc (J i j)).1

theorem incM_map' (h : IsSec σ t sec) {a b : Type} (J : Matrix a b E) (i j) :
    (incM F J).map (piW (t.comp σ)) i j = t (σ (J i j)) := by rw [incM, map_apply, map_apply]; exact (h.inc (J i j)).2

theorem co_eq (h : IsSec σ t sec) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) =
      toM (coord σ t (incM F X.J) (incM F W.J) u).1 := by
  rw [coord, incM_map h, incM_map h, toM_ofM, Units.val_one, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem coord_snd {u : Matrix α β (AE F E)} : (coord σ t JA JB u).2 = 0 ↔ u.map (piW t) = 0 :=
  ⟨fun h => neg_eq_zero.1 (congrArg toM h), fun h => by rw [coord, h, neg_zero]; rfl⟩

theorem coord_fst {u : Matrix α β (AE F E)} (h : u.map (piW (t.comp σ)) = 0) : (coord σ t JA JB u).1 = 0 := by
  rw [coord, h, Matrix.mul_zero, Matrix.zero_mul, neg_zero]; rfl

theorem linBar_of_lm (hA : AdSt) (hU : ActsUniq) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι}
    (hι : LM t ψ M.co ι) : M.IsLinBar ψ t 1 1 (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)) ∘ₗ ι) := by
  have k : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      ι φ₁ = schr (psiV ψ v) (coord σ t (incM F X.J) (incM F W.J) u) (ι φ) := fun u hu φ hφ φ₁ ha => by
    rw [hU F _ v _ φ hφ _ _ ha (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ)]
    exact hι.Heisenberg₂ u φ hφ
  refine ⟨bij_comp hι.bij _, fun u hu h0 φ hφ φ₁ _ ha Y => ?_, fun u hu h0 φ hφ φ₁ _ ha x hx hx0 => ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, k u hu φ hφ φ₁ ha, schr, coord_snd.2 h0, dotProduct_zero, mul_zero,
      add_zero, AddChar.map_zero_eq_one, one_mul, co_eq h]
    rfl
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, k u hu φ hφ φ₁ ha, schr, coord_fst h0, zero_dotProduct, mul_zero,
      add_zero, co_eq h, symp_eq h hG hx, sub_zero]
    rfl

theorem lm_of_linBar (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) : LM t ψ M.co (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι) := by
  have hc := ((hA.psi F ψ hψ).2 v).1
  obtain ⟨e, he1, he⟩ := exists_e h hG M.co
  set ι' := LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι
  have a1 : ∀ y, ∀ φ ∈ SB _, ι' (schr (psiV ψ v) (e (y, 0)) φ) = schr (psiV ψ v) (y, 0) (ι' φ) := fun y φ hφ => funext fun z => by
    obtain ⟨u, hu, hco, -⟩ := exists_coord h hG (y, 0)
    have := hι.trans u hu (coord_snd.1 (congrArg Prod.snd hco)) φ hφ _ (schr_mem hc _ hφ)
      (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ) (toM z)
    rw [co_eq h, hco] at this
    rw [← hco, he, hco]
    simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
    exact this
  have a2 : ∀ y, ∀ φ ∈ SB _, ι' (schr (psiV ψ v) (e (0, y)) φ) = schr (psiV ψ v) (0, y) (ι' φ) := fun y φ hφ => funext fun z => by
    obtain ⟨u, hu, hco, h0⟩ := exists_coord h hG (0, y)
    obtain ⟨x, hx, hcx, -⟩ := exists_coord h hG (z, 0)
    have := hι.mult u hu (h0 rfl) φ hφ _ (schr_mem hc _ hφ) (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ) x hx
      (coord_snd.1 (congrArg Prod.snd hcx))
    rw [co_eq h, symp_eq h hG hx, hco, hcx] at this
    rw [← hco, he, hco]
    simp only [schr, zero_dotProduct, mul_zero, add_zero, sub_zero] at this ⊢
    exact this
  refine ⟨bij_comp hι.bij _, fun u φ hφ => ?_⟩
  rw [← he]
  obtain ⟨y, z⟩ := coord σ t (incM F X.J) (incM F W.J) u
  have b := a1 y _ (schr_mem hc (e (0, z)) hφ)
  rw [a2 z φ hφ, schr_schr, schr_schr, he1, ← map_add (f := _), map_smul] at b
  simp only [Prod.mk_add_mk, add_zero, zero_add] at b
  exact smul_right_injective _ (AddChar.val_isUnit _ _).ne_zero b

def DictX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), B.IsGood σ → (∃ r s, X.IsHerm σ B r s) →
    (∃ r s, W.IsSkew σ B r s) → M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      (∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g₀) ∧
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ ι, M.IsLinBar B.ψ t 1 1 ι →
        (∀ g ∈ UAt σ X (evFin F v), ∀ g₀ : GL (Fin n) (Fv F v), (mat g).map (piW t) = g₀ →
          Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)

theorem dictX_of (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hS : SecSt) (hU : ActsUniq) : DictX := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨⟨sec, h⟩, -⟩ := hS F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm hM hA hB.std h hG M.co
  obtain ⟨hR, ⟨d', hd', hL⟩, -⟩ := hom
  obtain ⟨ε, -, hε, hε'⟩ := hG.sym
  refine ⟨⟨_, linBar_of_lm hA hU h hG hι₀⟩, fun g₀ => h.exists_ug hε hG.uA g₀, fun g₀ => h.exists_ug hε' hG.uB g₀, fun ι hι => ?_⟩
  have lm := lm_of_linBar hA hB.std h hG hι
  refine ⟨fun g hg g₀ e φ hφ => ?_, fun g hg g₀ e φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG.swap (lm.swap hd') hL.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Yᵀ)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, swH_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, apow_one, Matrix.mul_one]
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [← transpose_transpose (g₀.1ᵀ * Y), transpose_mul, transpose_transpose]
    rfl
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG lm hR.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Y)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, one_mul, apow_one, transpose_one, Matrix.one_mul]
    exact this

theorem dictSt_of (hX : DictX) (hS : SecSt) : DictSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB h1 h2 _ hom hχX hχW v t
  obtain ⟨e, s1, s2, k⟩ := hX F E σ n d B X W M om χX χW hB h1 h2 hom v t
  have hu := (hS F E σ hB.cm v t).2
  refine ⟨e, _, _, hu χW hχW, hu χX hχX, fun _ _ h => Or.inl h, fun ι hι => ⟨fun g hg => ⟨_, (k ι hι).1 g hg
    (GeneralLinearGroup.map (piW t) g.1) rfl⟩, fun g₀ => ?_, fun g hg => ⟨_, (k ι hι).2 g hg (GeneralLinearGroup.map (piW t) g.1) rfl⟩,
      fun g₀ => ?_⟩⟩
  · obtain ⟨g, hg, e⟩ := s1 g₀
    exact ⟨g, hg, (k ι hι).1 g hg g₀ e⟩
  · obtain ⟨g, hg, e⟩ := s2 g₀
    exact ⟨g, hg, (k ι hι).2 g hg g₀ e⟩

end PositivityTheory.KCo

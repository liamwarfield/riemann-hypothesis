module

public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ)

structure Cover : Type 1 where

  c' : Coeff T.Q.l
  hle : T.Q.c.F ≤ c'.F

  d : DeltaDat (T.Q.Xo j) c' 0

  σ₂ : d.c₂.F →+* ℂ
  U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r
  dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r
  cc₂ : U₂.Comp → ℂ

variable {T j σ}

namespace Cover

variable (C : Cover T j σ)

def inc : T.Q.c.F →+* C.d.c₂.F := (C.d.eF : C.c'.F →+* C.d.c₂.F).comp (incF T.Q.c C.c' C.hle)

def rd (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂) (rdU C.U₂ f₂)

def IsPull (f : T.R j) (f₂ : Rul C.d.Xo₂ C.d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [Algebra T.Q.c.F k] [Algebra C.c'.F k] [Algebra C.d.c₂.F k] (h : AlgOver T.Q.c C.c' C.hle k),
    (∀ x : C.c'.F, algebraMap C.d.c₂.F k (C.d.eF x) = algebraMap C.c'.F k x) →
    ∀ (y₂ : FrPt C.d.Xo₂ C.d.c₂ k) (y : FrPt (T.Q.Xo j) C.c' k), FrOver C.d y₂ y →
      evR C.d.Xo₂ C.d.c₂ f₂ y₂ = evR (T.Q.Xo j) T.Q.c f (y.res C.hle h)

def IsUnif : Prop :=
  C.d.IsLev ∧ C.d.l₂.A = 1 ∧ C.σ₂.comp C.inc = σ ∧ IsUnf C.U₂ ∧
    (∀ h, (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom) ∧
    ∃ (hr : (T.V j σ).rank = D.R.r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
      (F : FamilyUnif C.d.Xo₂ (C.σ₂.comp (IntermediateField.inclusion C.d.c₂.le).toRingHom)
        (fun i => relab C.d.c₂ C.σ₂ (e i).1))
      (ik : C.U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (C.U₂.X k).Λ)
      (th : ∀ k, (C.U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k, ModelW (T.V j σ) hr (C.U₂.X k)) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
        DictLat C.U₂ (T.V j σ) hr C.dict₂ (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) e F ik φ th
          (T.x₀ j σ)

def IsPinned (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  CUnit C.cc₂ ∧ ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → C.rd a f₂ = T.phiJ j σ a f

def cuspSec (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul C.d.Xo₂ C.d.c₂) :=
  {f₂ | f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n ∧ rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n)}

def ratForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (GA D (T.V j σ) → ℂ) := C.rd a '' C.cuspSec a n

def intForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) :
    Set (GA D (T.V j σ) → ℂ) :=
  C.rd a '' {f₂ | f₂ ∈ C.cuspSec a n ∧ ∀ la ∈ S, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v f₂}

theorem intForms_subset (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) :
    C.intForms a n S ⊆ C.ratForms a n := Set.image_mono fun _ h => h.1

end Cover

variable (T j σ)

def baseForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (GA D (T.V j σ) → ℂ) :=
  T.phiJ j σ a '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}

def baseInt (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) :
    Set (GA D (T.V j σ) → ℂ) :=
  T.phiJ j σ a '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) ∧
    ∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f}

end GlobalTheory.CoverRead
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
noncomputable section

open Matrix Formalism.IndefR.Datum

namespace GlobalTheory.ExportSeries

section Flat

variable {k R : Type} [CommRing k] [CommRing R] {r n : ℕ}


open Classical in
def flat (ν : kˣ →* Rˣ) (y : Matrix (Fin r) (Fin n) k) : R :=
  if h : IsUnit (topL r y).det then ((ν h.unit : Rˣ) : R) else 0

theorem flat_of_isUnit (ν : kˣ →* Rˣ) {y : Matrix (Fin r) (Fin n) k} {u : kˣ} (h : (topL r y).det = u) :
    flat ν y = ((ν u : Rˣ) : R) := by
  have hu : IsUnit (topL r y).det := h ▸ u.isUnit
  have hu' : hu.unit = u := Units.ext (by rw [IsUnit.unit_spec, h])
  unfold flat
  rw [dite_eq_left hu, hu']

theorem flat_of_not_isUnit (ν : kˣ →* Rˣ) {y : Matrix (Fin r) (Fin n) k} (h : ¬ IsUnit (topL r y).det) :
    flat ν y = 0 := by
  unfold flat
  rw [dite_eq_right h]

theorem topL_mul (hr : r ≤ n) (g : Matrix (Fin r) (Fin r) k) (y : Matrix (Fin r) (Fin n) k) :
    topL r (g * y) = g * topL r y := by
  ext i j
  have hj : j.val < n := lt_of_lt_of_le j.isLt hr
  simp [topL, Matrix.mul_apply, hj]

theorem flat_mul (hr : r ≤ n) (ν : kˣ →* Rˣ) (g : GL (Fin r) k) (y : Matrix (Fin r) (Fin n) k) :
    flat ν ((g : Matrix (Fin r) (Fin r) k) * y) = ((ν (GeneralLinearGroup.det g) : Rˣ) : R) * flat ν y := by
  have hdet : (topL r ((g : Matrix (Fin r) (Fin r) k) * y)).det =
      (GeneralLinearGroup.det g : k) * (topL r y).det := by
    rw [topL_mul hr, Matrix.det_mul]
    rfl
  by_cases hu : IsUnit (topL r y).det
  · rw [flat_of_isUnit ν (u := GeneralLinearGroup.det g * hu.unit) (by rw [hdet, Units.val_mul, hu.unit_spec]),
      flat_of_isUnit ν (u := hu.unit) hu.unit_spec.symm, map_mul, Units.val_mul]
  · have hu' : ¬ IsUnit (topL r ((g : Matrix (Fin r) (Fin r) k) * y)).det := by
      rw [hdet, Units.isUnit_units_mul]
      exact hu
    rw [flat_of_not_isUnit ν hu', flat_of_not_isUnit ν hu, mul_zero]

end Flat

section Univ

variable {k : Type} [Field k] {r n : ℕ}


open Classical in
def prim (y : Matrix (Fin r) (Fin n) k) : ℚ := if LinearIndependent k y.row then 1 else 0

def Compl (U : Submodule k (Fin n → k)) (y : Matrix (Fin r) (Fin n) k) : Prop :=
  Submodule.span k (Set.range y.row) ⊔ U = ⊤

variable (k r n) in
abbrev Planes : Type := {U : Submodule k (Fin n → k) // Module.finrank k U + r = n}

instance [Finite k] : Finite (Planes k r n) :=
  haveI : Finite (Submodule k (Fin n → k)) := Finite.of_injective _ SetLike.coe_injective
  Subtype.finite

theorem finrank_quot (U : Planes k r n) : Module.finrank k ((Fin n → k) ⧸ U.1) = r := by
  have h1 := Submodule.finrank_quotient_add_finrank U.1
  have h2 := U.2
  rw [Module.finrank_fin_fun] at h1
  omega


variable (k r n) in
structure DetBases where

  form : ∀ U : Planes k r n, ((Fin n → k) ⧸ U.1) [⋀^Fin r]→ₗ[k] k
  ne : ∀ U, form U ≠ 0

def DetBases.std (k : Type) [Field k] (r n : ℕ) : DetBases k r n where
  form U := (Module.finBasisOfFinrankEq k _ (finrank_quot U)).det
  ne _ := Module.Basis.det_ne_zero _

def dU (β : DetBases k r n) (U : Planes k r n) (y : Matrix (Fin r) (Fin n) k) : k :=
  β.form U fun i => U.1.mkQ (y.row i)

theorem dU_ne_zero_iff (β : DetBases k r n) (U : Planes k r n) (y : Matrix (Fin r) (Fin n) k) :
    dU β U y ≠ 0 ↔ Compl U.1 y := by
  have hspan : Submodule.span k (Set.range fun i => U.1.mkQ (y.row i)) = ⊤ ↔ Compl U.1 y := by
    have hr : (Set.range fun i => U.1.mkQ (y.row i)) = U.1.mkQ '' Set.range y.row := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, Submodule.map_mkQ_eq_top, Compl, sup_comm]
  have hcard : Fintype.card (Fin r) = Module.finrank k ((Fin n → k) ⧸ U.1) := by
    rw [Fintype.card_fin, finrank_quot U]
  unfold dU
  rw [← hspan]
  constructor
  · intro hne
    have hli : LinearIndependent k (fun i => U.1.mkQ (y.row i)) := by
      by_contra hdep
      exact hne ((β.form U).map_linearDependent _ hdep)
    exact hli.span_eq_top_of_card_eq_finrank' hcard
  · intro htop
    have hli : LinearIndependent k (fun i => U.1.mkQ (y.row i)) :=
      linearIndependent_of_top_le_span_of_card_eq_finrank htop.ge hcard
    have hb := (β.form U).map_basis_ne_zero_iff (Module.Basis.mk hli htop.ge)
    rw [Module.Basis.coe_mk] at hb
    exact hb.2 (β.ne U)

theorem dU_mul (β : DetBases k r n) (U : Planes k r n) (g : Matrix (Fin r) (Fin r) k) (y : Matrix (Fin r) (Fin n) k) :
    dU β U (g * y) = g.det * dU β U y := by
  let e := Module.finBasisOfFinrankEq k ((Fin n → k) ⧸ U.1) (finrank_quot U)
  have hrow : ∀ i, U.1.mkQ ((g * y).row i) = ∑ j, g i j • U.1.mkQ (y.row j) := by
    intro i
    have hgy : (g * y).row i = ∑ j, g i j • y.row j := by
      ext c
      simp [Matrix.mul_apply, Matrix.row, Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hgy, map_sum]
    simp only [map_smul]
  have hM : e.toMatrix (fun i => U.1.mkQ ((g * y).row i)) =
      e.toMatrix (fun i => U.1.mkQ (y.row i)) * g.transpose := by
    ext a i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.toMatrix_apply, hrow, map_sum, map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  unfold dU
  rw [(β.form U).eq_smul_basis_det e]
  simp only [AlternatingMap.smul_apply, Module.Basis.det_apply, hM, Matrix.det_mul, Matrix.det_transpose, smul_eq_mul]
  ring

variable [Finite k] {C : Type} [AddCommGroup C]


open Classical in
def univTerm (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k) (U : Planes k r n) :
    AddMonoidAlgebra ℚ C :=
  if h : Compl U.1 y then
    AddMonoidAlgebra.single (Multiplicative.toAdd (κ (Units.mk0 _ ((dU_ne_zero_iff β U y).2 h)))) 1
  else 0

def univ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k) : AddMonoidAlgebra ℚ C :=
  haveI := Fintype.ofFinite (Planes k r n)
  ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ • ∑ U : Planes k r n, univTerm β κ y U

def univCoef (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (c : C) (y : Matrix (Fin r) (Fin n) k) : ℚ :=
  (univ β κ y).coeff c

theorem univCoef_eq (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (c : C) (y : Matrix (Fin r) (Fin n) k) :
    univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      Nat.card {U : Planes k r n // ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c} := by
  classical
  haveI := Fintype.ofFinite (Planes k r n)
  have hterm : ∀ U : Planes k r n, (univTerm β κ y U).coeff c =
      if ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases hC : Compl U.1 y
    · rw [dite_eq_left hC, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases hE : ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c
      · obtain ⟨u, hu, hc⟩ := hE
        have hmk : Units.mk0 _ ((dU_ne_zero_iff β U y).2 hC) = u := Units.ext (by simp [hu])
        rw [hmk, if_pos hc, if_pos ⟨u, hu, hc⟩]
      · rw [if_neg hE, if_neg]
        exact fun hc => hE ⟨_, rfl, hc⟩
    · rw [dite_eq_right hC, if_neg, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      rintro ⟨u, hu, -⟩
      exact hC ((dU_ne_zero_iff β U y).1 (hu ▸ u.ne_zero))
  unfold univCoef univ
  rw [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [hterm]
  clear hterm
  rw [Finset.sum_boole, smul_eq_mul]
  congr 2
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun U => by simp)

structure IsAdmissible (κ : kˣ →* Multiplicative C) (Φ : C → Matrix (Fin r) (Fin n) k → ℚ) : Prop where
  den : ∀ c y, ∃ (m : ℕ) (z : ℤ), Φ c y * (Nat.card k : ℚ) ^ m = z
  equiv : ∀ (g : GL (Fin r) k) c y,
    Φ c (((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * y) =
      Φ (c + Multiplicative.toAdd (κ (GeneralLinearGroup.det g))) y

theorem isAdmissible_univCoef (β : DetBases k r n) (κ : kˣ →* Multiplicative C) : IsAdmissible κ (univCoef β κ) := by
  refine { den := ?_, equiv := ?_ }
  · intro c y
    have hq : (Nat.card k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    refine ⟨r * (n - r), Nat.card {U : Planes k r n // ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c}, ?_⟩
    rw [univCoef_eq, mul_comm, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
    simp
  · intro g c y
    rw [univCoef_eq, univCoef_eq]
    congr 2
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro U
    set a := GeneralLinearGroup.det g
    have hd : dU β U (((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * y) = ((a⁻¹ : kˣ) : k) * dU β U y := by
      rw [dU_mul]
      congr 1
    rw [hd]
    constructor
    · rintro ⟨u, hu, hc⟩
      refine ⟨a * u, ?_, ?_⟩
      · rw [Units.val_mul, hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      · rw [map_mul, toAdd_mul, hc, add_comm]
    · rintro ⟨u, hu, hc⟩
      refine ⟨a⁻¹ * u, ?_, ?_⟩
      · rw [Units.val_mul, hu]
      · rw [map_mul, toAdd_mul, hc, map_inv, toAdd_inv]
        abel

end Univ

end GlobalTheory.ExportSeries

end
end

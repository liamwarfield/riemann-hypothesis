module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InvTransposeIso

def ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) : GL n A →* GL m A where
  toFun g := ⟨((g⁻¹).1ᵀ).submatrix e.symm e.symm, (g.1ᵀ).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.submatrix_one_equiv]⟩
  map_one' := Units.ext (by ext i j; simp [Matrix.one_apply])
  map_mul' g h := Units.ext (by
    show (((g * h)⁻¹).1ᵀ).submatrix e.symm e.symm =
      ((g⁻¹).1ᵀ).submatrix e.symm e.symm * ((h⁻¹).1ᵀ).submatrix e.symm e.symm
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, ← Units.val_mul, _root_.mul_inv_rev])

theorem ctr_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : (ctr e g).1 = ((g⁻¹).1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_inv_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ((ctr e g)⁻¹).1 = (g.1ᵀ).submatrix e.symm e.symm := rfl

theorem ctr_ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ctr e.symm (ctr e g) = g :=
  Units.ext (by rw [ctr_val, ctr_inv_val]; ext i j; simp)

theorem key_rel {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (c : A →+* A)
    {H Hi K : Matrix n n A} (hHi : H * Hi = 1) (hK : Hi = -Kᵀ) (g : GL n A)
    (hg : (g.1.map c)ᵀ * H * g.1 = H) :
    (((g⁻¹).1ᵀ).map c)ᵀ * K * (g⁻¹).1ᵀ = K := by
  have hHiH : Hi * H = 1 := mul_eq_one_comm.1 hHi
  have h1 : g.1.map c * (g⁻¹).1.map c = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hY : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H = 1 := by
    calc (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H
        = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * ((g.1.map c)ᵀ * H * g.1) := by rw [hg]
      _ = (g⁻¹).1 * Hi * (g.1.map c * (g⁻¹).1.map c)ᵀ * H * g.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc _ Hi H, hHiH, Matrix.mul_one,
            Units.inv_mul]
  have hY' : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ = Hi := by
    calc _ = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * (H * Hi) := by rw [hHi, Matrix.mul_one]
      _ = Hi := by rw [← Matrix.mul_assoc, hY, Matrix.one_mul]
  have hKt : Kᵀ = -Hi := by rw [hK, neg_neg]
  apply Matrix.transpose_injective
  rw [Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hKt, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hY']

theorem reindex_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {J : Matrix m m A} {M : Matrix n n A}
    (h : (M.map c)ᵀ * J.submatrix e e * M = J.submatrix e e) :
    ((M.submatrix e.symm e.symm).map c)ᵀ * J * M.submatrix e.symm e.symm = J := by
  have hJ : J = (J.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
  have hM : ((M.submatrix e.symm e.symm).map c)ᵀ = ((M.map c)ᵀ).submatrix e.symm e.symm := rfl
  rw [hM]
  conv_lhs => rw [hJ]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h, ← hJ]

theorem ctr_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {H Hi : Matrix n n A} {J : Matrix m m A} (hHi : H * Hi = 1)
    (hK : Hi = -(Jᵀ.submatrix e e)) (g : GL n A) (hg : Formalism.UG.cT c g.1 * H * g.1 = H) :
    Formalism.UG.cT c (ctr e g).1 * J * (ctr e g).1 = J :=
  reindex_rel c e (key_rel c hHi hK g hg)

theorem inv_rel {K : Type} [Field K] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n K) (B : Matrix m m K) (e : n ≃ m) (h : A⁻¹ = -(Bᵀ.submatrix e e)) (hA : IsUnit A.det) :
    B⁻¹ = -(Aᵀ.submatrix e.symm e.symm) := by
  have h1 : A * -(Bᵀ.submatrix e e) = 1 := by rw [← h]; exact Matrix.mul_nonsing_inv A hA
  have h2 : -(B.submatrix e e) * Aᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_submatrix, Matrix.transpose_transpose,
      Matrix.transpose_one] at this
    exact this
  have h3 : Aᵀ * -(B.submatrix e e) = 1 := mul_eq_one_comm.1 h2
  have h4 : Aᵀ.submatrix e.symm e.symm * -B = 1 := by
    calc Aᵀ.submatrix e.symm e.symm * -B
        = Aᵀ.submatrix e.symm e.symm * (-(B.submatrix e e)).submatrix e.symm e.symm := by
          congr 1; ext i j; simp
      _ = (Aᵀ * -(B.submatrix e e)).submatrix e.symm e.symm := Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [h3, Matrix.submatrix_one_equiv]
  exact Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, ← Matrix.mul_neg]; exact h4)

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

theorem gram_inv_rel {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    W.gram⁻¹ = -(V.gramᵀ.submatrix e.symm e.symm) :=
  inv_rel V.gram W.gram e h (Formalism.L2.Theta.gram_det_ne V).isUnit

theorem mem_HR {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : ctr e (matHom V g) ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  have hHi : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK : (V.gram⁻¹).map (incA D) = -(((W.gram.map (incA D))ᵀ).submatrix e e) := by
    rw [h]; ext i j; simp
  exact ctr_rel (cA D) e hHi hK (matHom V g) g.2

theorem mem_UJ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (r : GL (Fin V.rank) D.host.E) (hr : r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    ctr e r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  exact ctr_rel _ e (Matrix.mul_nonsing_inv _ hdet) h r hr

def fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V →* GA D W where
  toFun g := (⟨ctr e (matHom V g), mem_HR e h g⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram)
  map_one' := Subtype.ext (by simp only [map_one]; rfl)
  map_mul' g g' := Subtype.ext (by simp only [map_mul]; rfl)

theorem mt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : Formalism.L2.Theta.mt W (fwd e h g) = ((Formalism.L2.Theta.mt V g⁻¹)ᵀ).submatrix e.symm e.symm := by
  show (ctr e (matHom V g)).1 = _
  rw [ctr_val, ← map_inv]; rfl

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

def iso {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V ≃* GA D W :=
  { fwd e h with
    invFun := fwd e.symm (gram_inv_rel e h)
    left_inv := fun g => Subtype.ext (ctr_ctr e g.1)
    right_inv := fun g => Subtype.ext (ctr_ctr e.symm g.1) }

theorem continuous_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    Continuous (fwd e h) := by
  have hv : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : GA D V => ((matHom V g)⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun g : GA D V => (((matHom V g)⁻¹).1ᵀ).submatrix e.symm e.symm
    exact hi.matrix_transpose.matrix_submatrix _ _
  · show Continuous fun g : GA D V => ((matHom V g).1ᵀ).submatrix e.symm e.symm
    exact hv.matrix_transpose.matrix_submatrix _ _

theorem fwd_GQ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (γ : GA D V) (hγ : γ ∈ GQ V) : fwd e h γ ∈ GQ W := by
  obtain ⟨r, hr, hrγ⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈
    HFin (AF D.host.F) D.sp.cm.sig V.gram)
  refine Subgroup.mem_subgroupOf.2 ⟨ctr e r, mem_UJ e h r hr, ?_⟩
  show Formalism.UG.bc (inclR (AF D.host.F)) (ctr e r) = ctr e γ.1
  rw [← hrγ]
  exact Units.ext (by ext i j; rfl)

theorem suppAt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (a : AE D) (g : GA D V) (hg : SuppAt a V g) : SuppAt a W (fwd e h g) := by
  have hYG : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hsub : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, hYG, Matrix.mul_one, neg_sub]
  intro i j
  have hij : (Formalism.L2.Theta.mt W (fwd e h g) - 1) i j = (Formalism.L2.Theta.mt V g⁻¹ - 1) (e.symm j) (e.symm i) := by
    rw [mt_fwd]
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply,
      e.symm.injective.eq_iff, eq_comm]
  rw [hij, hsub, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k (e.symm i)]

theorem det_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).det = (Formalism.L2.Theta.mt V g⁻¹).det := by
  rw [mt_fwd, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

theorem sub_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).submatrix e e = (Formalism.L2.Theta.mt V g⁻¹)ᵀ := by
  rw [mt_fwd]; ext i j; simp

theorem grp_contra : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  intro D T S' e₂ h
  exact ⟨iso e₂ h, continuous_fwd e₂ h, fun γ hγ => fwd_GQ e₂ h γ hγ, sub_fwd e₂ h,
    fun a g hg => suppAt_fwd e₂ h a g hg, det_fwd e₂ h⟩

end GlobalTheory.InvTransposeIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  first | exact @GlobalTheory.InvTransposeIso.grp_contra | exact GlobalTheory.InvTransposeIso.grp_contra | (intros; apply GlobalTheory.InvTransposeIso.grp_contra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOverPlace

theorem unrAt_of_unramAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F),
    IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  intro D χ v ε hε hu w hw x hx
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w x).1 hx
  have hc := GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E)
  obtain ⟨k0, k1, -⟩ := GlobalTheory.CMPrimeIdele.place_comp hc hε
  have key : χ (GlobalTheory.LFun.locIdele D.host.F w x) = 1 := by
    refine hu _ ?_ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w x).2 h1) (by
      rw [← map_inv]; exact (GlobalTheory.LFun.EulerTie.locIdele_int_iff w x⁻¹).2 h2)
    refine hc.ext' ?_ fun Q ↦ ?_
    · have k0' : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) ε) = 0 := k0
      have k2 : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) = 0 := by
        rw [map_sub, (GlobalTheory.LFun.EulerTie.parts_locIdele w x).1, map_one, sub_self]
      rw [map_mul, k0', zero_mul, k2]
    · rw [GlobalTheory.CMPrimeIdele.ev_mul]
      by_cases hQ : Q = w
      · subst hQ
        rw [k1 Q hw, one_mul]
      · have e : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) Q = 0 := by
          rw [map_sub, map_one]
          show GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (GlobalTheory.LFun.locIdele D.host.F w x : AE D) Q - 1 = 0
          rw [GlobalTheory.LFun.EulerTie.finComp_locIdele_ne hQ, sub_self]
        rw [e, mul_zero]
  show Circle.toUnits (χ (GlobalTheory.LFun.locIdele D.host.F w x)) = 1
  rw [key, map_one]

end GlobalTheory.UnrOverPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_above_place_of_trivial_units : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  first | exact @GlobalTheory.UnrOverPlace.unrAt_of_unramAt | exact GlobalTheory.UnrOverPlace.unrAt_of_unramAt | (intros; apply GlobalTheory.UnrOverPlace.unrAt_of_unramAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParams
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParams
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ c.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · rw [← hFx']; exact hF
  · rw [← hFx']; exact hPF

end GlobalTheory.EvenOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParamsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_theta_step_adjoint_nonzero_transferred_params : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  first | exact @GlobalTheory.EvenOnto.stepUp | exact GlobalTheory.EvenOnto.stepUp | (intros; apply GlobalTheory.EvenOnto.stepUp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterInUnitaryArchimedeanMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterInUnitaryArchimedeanMaxCompact
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CompactLine

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem commute_of_gen {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (A' : Matrix (Ix R S) β ℂ) (hCA : C * A' = 1) (g θ : Matrix β β ℂ) (Y : Mat R S) (hY : IsKC Y) (t : ℝ)
    (hθ : θ * C = C * Jm R S) (hg : g * C = C * NormedSpace.exp (t • Y)) : Commute g θ := by
  have h1 : Commute Y (Jm R S) := (GlobalTheory.CartanInt.UnitLog.isKC_iff_commute Y).1 hY
  have h2 : Commute (NormedSpace.exp (t • Y)) (Jm R S) := (h1.smul_left t).exp_left
  have h3 : g * θ * C = θ * g * C := by
    rw [Matrix.mul_assoc, hθ, ← Matrix.mul_assoc, hg, Matrix.mul_assoc θ, hg, ← Matrix.mul_assoc θ, hθ,
      Matrix.mul_assoc, Matrix.mul_assoc, h2.eq]
  calc g * θ = g * θ * C * A' := by rw [Matrix.mul_assoc _ C, hCA, Matrix.mul_one]
    _ = θ * g := by rw [h3, Matrix.mul_assoc _ C, hCA, Matrix.mul_one]

theorem exists_line_in_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb := by
  intro F E _ _ _ _ _ σ B n X r s hb hX k hk
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ (X.θ w) (hX.sig w) (hX.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  obtain ⟨γ, hγ, Y, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin n) r s
    B.emb (incM F X.J) 1 A X.θ hb.cm hA1 hAθ k hk.1 hk.2
  refine ⟨γ, hγ, hγ1, fun t => ⟨hγ.2 t, fun w => ?_⟩⟩
  obtain ⟨A', hAA⟩ := (hA w).2
  exact commute_of_gen (A w) A' hAA _ _ (Y w) (hKC w) t.toAdd (hAθ w) (hgen t.toAdd w)

end GlobalTheory.CompactLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterInUnitaryArchimedeanMaxCompactStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oneParameter_in_unitaryArchimedeanMaxCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb := by
  first | exact @GlobalTheory.CompactLine.exists_line_in_kInf | exact GlobalTheory.CompactLine.exists_line_in_kInf | (intros; apply GlobalTheory.CompactLine.exists_line_in_kInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.PolMul

open GlobalTheory.HeisDeriv GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def liftInf (z : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z)

theorem evI_liftInf (z : mixedEmbedding.mixedSpace F) : evI F (liftInf F z) = z := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = z
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z

theorem mul_liftInf_eq_zero {a : AF F} (ha : evI F a = 0) (z : mixedEmbedding.mixedSpace F) :
    a * liftInf F z = 0 := by
  have h1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ha)
  refine Prod.ext ?_ ?_
  · show a.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = 0
    rw [h1, zero_mul]
  · show a.2 * 0 = 0
    rw [mul_zero]

theorem actsD_mult {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (y : Fin n × Fin d → AF F) (hu : M.co.e u = (0, y))
    (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f) := by
  intro r _ x

  have he : ∀ t : ℝ, M.co.e (realAd F t • u) = (0, realAd F t • y) := by
    intro t
    rw [LinearEquiv.map_smul, hu]
    refine Prod.ext ?_ ?_ <;> simp
  set a : AF F := x ⬝ᵥ y with ha
  set K : ℂ := tens (evI F) (⇑f) r x with hK
  set c : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) with hc

  have hT : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) (⇑f) r) x = ψ (realAd F t * a) * K := by
    intro t
    simp only [Model.heisLine, Darboux.rho, he t, schr, zero_dotProduct, mul_zero, add_zero, dotProduct_smul,
      smul_eq_mul, ha, hK]

  have hAt : ∀ t : ℝ, At (evI F) (realAd F t * a) := by
    intro t v hv
    rw [smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero hv, zero_mul]
  have hψt : ∀ t : ℝ, ψ (realAd F t * a) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((t * c : ℝ)) : ℂ)) := by
    intro t
    rw [hψ.2.2 _ (hAt t), evI_mul, evI_realAd, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hfun : (fun t : ℝ => M.heisLine ψ u t (tens (evI F) (⇑f) r) x) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * (((t * c : ℝ)) : ℂ)) * K := by
    funext t
    rw [hT t, hψt t]
  have h0 : HasDerivAt (fun t : ℝ => ((t * c : ℝ) : ℂ)) ((1 * c : ℝ) : ℂ) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp
  have h2 := ((h0.const_mul (-(2 * Real.pi * Complex.I))).cexp).mul_const K

  have htr : trForm F y (fun i => evI F (x i)) = c := by
    rw [trForm_apply, hc, ha, dotProduct, evI_sum]
    simp only [evI_mul]
  rw [hfun]
  refine h2.congr_deriv ?_
  simp only [tens, hK, SchwartzMap.smulLeftCLM_apply_apply (mult F y).hasTemperateGrowth, mult_apply, htr, zero_mul,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, smul_eq_mul]
  ring

theorem model_mul {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w)
    (q : Fin n × Fin d → mixedEmbedding.mixedSpace F) (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ τ) :
    ∃ f₁ ∈ M.Pol ψ τ, ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by

  set y : Fin n × Fin d → AF F := fun i => liftInf F (q i) with hy
  set u := M.co.e.symm (0, y) with hu
  have hue : M.co.e u = (0, y) := by simp [hu]
  have hat : At (evI F) u := by
    intro v hv
    rw [← LinearEquiv.map_eq_zero_iff M.co.e, LinearEquiv.map_smul, hue]
    refine Prod.ext ?_ ?_
    · simp
    · funext i
      simp [hy, mul_liftInf_eq_zero hv]
  have hmem : SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f ∈ M.Pol ψ τ := by
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 u hat f (hf N hN) _ (actsD_mult M ψ hψ u y hue f)
  have hne : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(-(2 * Real.pi * Complex.I))⁻¹ • SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f,
    Submodule.smul_mem _ _ hmem, fun x => ?_⟩
  have htr : trForm F y x = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q := by
    rw [trForm_apply, GlobalTheory.GaussLine.pairInf_apply]
    simp only [hy, evI_liftInf]
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (mult F y).hasTemperateGrowth, mult_apply, htr,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GlobalTheory.PolMul

theorem GlobalTheory.PolMul.pol_mul_pairInf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (q : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F),
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')) x q : ℂ) * f x := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT q f hf
  exact GlobalTheory.PolMul.model_mul G.M B.ψ hT.base.std B.emb q f hf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTriple_polynomialFock_stable_mul_trace_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (q : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F),
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')) x q : ℂ) * f x := by
  first | exact @GlobalTheory.PolMul.pol_mul_pairInf | exact GlobalTheory.PolMul.pol_mul_pairInf | (intros; apply GlobalTheory.PolMul.pol_mul_pairInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerSurj

open GlobalTheory.MixModel (rat sandwich HypDec)
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition (isoPart midPart res IsIsoSplit)

variable {D : D7}

section Emb

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

def embMat : Matrix (Fin V.rank) (Fin H.rank) D.host.E := d.e * dH.qX + d.e' * dH.qY

theorem ee_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e) = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.ee

theorem e'e'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e') = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e'

theorem e'e_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e) = 1 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e

theorem ee'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e') = 1 := by
  have h := congrArg Matrix.conjTranspose d.e'e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one] at h
  exact h

theorem ei₀_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.i₀) = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_zero] at h
  exact h

theorem embMat_e : embMat d dH * dH.e = d.e := by
  have h1 := e'e_assoc dH
  have h0 := ee_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem embMat_e' : embMat d dH * dH.e' = d.e' := by
  have h1 := ee'_assoc dH
  have h0 := e'e'_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem iso_embMat : d.eᴴ * V.gram * embMat d dH = dH.eᴴ * H.gram := by
  have h1 : d.eᴴ * V.gram * d.e' = 1 := by
    rw [Matrix.mul_assoc]
    exact ee'_assoc d
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.ee, h1, Matrix.zero_mul, Matrix.one_mul,
    zero_add]
  rfl

theorem mid_embMat : d.i₀ᴴ * V.gram * embMat d dH = 0 := by
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.i₀e, d.i₀e', Matrix.zero_mul,
    Matrix.zero_mul, add_zero]

end Emb

section Form

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r) (W : HSp D)

theorem hO_rank_zero (hZ : Z.rank = 0) (x y : WO Z W) : hO Z W x y = 0 := by
  haveI : IsEmpty (Fin Z.rank) := by
    rw [hZ]
    infer_instance
  rw [GlobalTheory.MixModel.hO_eq_trace]
  simp [Matrix.trace]

theorem mul_embMat_jX (x : WO V W) : x * rat (embMat d dH) * dH.jX = x * d.jX := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e = rat d.e
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e]

theorem mul_embMat_jY (x : WO V W) : x * rat (embMat d dH) * dH.jY = x * d.jY := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e' = rat d.e'
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e']

theorem hO_split (hZ : Z.rank = 0) (x y : WO V W) :
    hO V W x y = hO V' W (x * rat d.i₀) (y * rat d.i₀) + hO H W (x * rat (embMat d dH)) (y * rat (embMat d dH)) := by
  rw [GlobalTheory.MixModel.HypDec.hO_coordS d, GlobalTheory.MixModel.HypDec.hO_coordS dH, hO_rank_zero W hZ,
    mul_embMat_jX d dH W x, mul_embMat_jX d dH W y, mul_embMat_jY d dH W x, mul_embMat_jY d dH W y]
  show _ = hO V' W (x * d.j0) (y * d.j0) + _
  abel

theorem symplOH_split (hZ : Z.rank = 0) (x y : WO V W) :
    symplOH V W x y =
      symplOH V' W (sandwich (rat 1) (rat d.i₀) x) (sandwich (rat 1) (rat d.i₀) y) +
        symplOH H W (sandwich (rat 1) (rat (embMat d dH)) x) (sandwich (rat 1) (rat (embMat d dH)) y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [hO_split d dH W hZ, map_add (f := _)]

end Form

section Res

variable {V V' H Z W : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

theorem sand_B (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat d.i₀) (isoPart V W d.e y + midPart V V' W d.i₀ x) = x := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat d.i₀ = 0 := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat d.i₀ = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, ei₀_assoc d, GlobalTheory.MixModel.rat_zero]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat d.i₀ = 1 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat d.i₀ = 1
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.iso,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V'), GlobalTheory.MixModel.rat_one]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, Matrix.mul_one, zero_add]

theorem sand_A (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat (embMat d dH)) (isoPart V W d.e y + midPart V V' W d.i₀ x) = isoPart H W dH.e y := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat (embMat d dH) =
      (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram).map (incA D) := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat (embMat d dH) = rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram)
    rw [← GlobalTheory.MixModel.rat_mul, hadj, hadj, iso_embMat]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat (embMat d dH) = 0 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat (embMat d dH) = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, mid_embMat,
      Matrix.mul_zero, GlobalTheory.MixModel.rat_zero]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero]

theorem surj_core (hZ : Z.rank = 0) (hsH : IsIsoSplit H Z dH.e dH.i₀) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (hμ : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) (f' : WO V' W → ℂ) (hf' : IsThetaFunO ψ V' W f') :
    ∃ f, IsThetaFunO ψ V W f ∧ f' = res V V' W d.e d.i₀ μ 𝓨 f := by
  obtain ⟨fH, hfH, hne⟩ := (GlobalTheory.TowerRestrict.res_theta D H Z W r dH.e dH.i₀ hsH ψ hψ μ 𝓨 hμ).2
  generalize hcv : res H Z W dH.e dH.i₀ μ 𝓨 fH 0 = c
  have hc : c ≠ 0 := by
    rintro rfl
    apply hne
    funext z
    have hz : z = 0 := by
      haveI : IsEmpty (Fin Z.rank) := by
        rw [hZ]
        infer_instance
      exact Matrix.ext fun _ j => isEmptyElim j
    subst hz
    exact hcv
  have hint : ∫ y in 𝓨, fH (isoPart H W dH.e y) ∂μ = c := by
    rw [← hcv]
    simp only [res, GlobalTheory.TowerRestrict.midPart_zero, add_zero]
  refine ⟨fun w => f' (sandwich (rat 1) (rat d.i₀) w) * (c⁻¹ • fH) (sandwich (rat 1) (rat (embMat d dH)) w), ?_, ?_⟩
  · exact GlobalTheory.MixModel.isThetaFunO_prod 1 d.i₀ 1 (embMat d dH) (symplOH_split d dH W hZ) hf'
      (GlobalTheory.OrientedHeis.theta_smul c⁻¹ hfH)
  · funext x
    simp only [res, sand_B, sand_A, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hint, inv_mul_cancel₀ hc, mul_one]

private theorem isIsoSplit_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm.trans (Nat.add_comm _ _ ▸ rfl)⟩
  · apply Fintype.linearIndependent_iff.2
    intro g hg
    have h1 : d.e.mulVec g = 0 := by
      funext k
      have hk := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, smul_eq_mul, Pi.zero_apply] at hk
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hk]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : (d.e'ᴴ * S.gram * d.e).mulVec g = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rw [d.e'e, Matrix.one_mulVec] at h2
    exact fun i => congrFun h2 i
  · rw [GlobalTheory.MixModel.cT_sig]
    exact d.ee
  · rw [hadj]
    exact d.iso
  · rw [hadj, Matrix.mul_assoc]
    exact ei₀_assoc d

end Res

theorem res_surjective : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f', IsThetaFunO ψ V' W f' → ∃ f, IsThetaFunO ψ V W f ∧ f' = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ f' hf'
  obtain ⟨d, hdC, hdB, -⟩ := GlobalTheory.T.exists_wittDecomposition_isotropicSplit_unipotent D V V' r C B hs
  subst hdC hdB
  exact surj_core d (GlobalTheory.Core.Rk.SWLaw.dblDec (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral r)) rfl
    (isIsoSplit_of_hypDec _ hs.frame.1) ψ hψ μ 𝓨 hμ f' hf'

end GlobalTheory.TowerSurj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_restriction_down_witt_tower_surjective : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f', IsThetaFunO ψ V' W f' → ∃ f, IsThetaFunO ψ V W f ∧ f' = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.TowerSurj.res_surjective | exact GlobalTheory.TowerSurj.res_surjective | (intros; apply GlobalTheory.TowerSurj.res_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (piInf)

namespace GlobalTheory.VacDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def IsGaussEq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    ∀ x, deriv (fun t : ℝ => M.heisLine ψ u' t Φ x) 0 = Complex.I * deriv (fun t : ℝ => M.heisLine ψ u t Φ x) 0

end GlobalTheory.VacDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFinRam

theorem finite_ramified : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  intro D χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  refine (GlobalTheory.Mem.UnrAe.finite_ramified H).subset fun w hw => ?_
  exact fun h => hw ((GlobalTheory.LFun.unrAt_iff_of_chrEq hH w).2 h)

end GlobalTheory.HeckeFinRam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  first | exact @GlobalTheory.HeckeFinRam.finite_ramified | exact GlobalTheory.HeckeFinRam.finite_ramified | (intros; apply GlobalTheory.HeckeFinRam.finite_ramified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacTransfer

variable {D : D7} {S X : HSp D} {n d : ℕ}

def archLine (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) : ℝ →+ WO S X where
  toFun t := cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
  map_zero' := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_zero]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 • u) = 0
    rw [h, zero_smul]
    exact map_zero cS
  map_add' s t := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_add (f := _)]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) • u) =
      cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) + cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
    rw [h, add_smul]
    exact map_add cS _ _

theorem archLine_apply (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) (t : ℝ) :
    archLine cS u t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) := rfl

end GlobalTheory.VacTransfer

end
end

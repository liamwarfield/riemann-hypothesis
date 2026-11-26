module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovMul

open GlobalTheory.Amp.Swap GlobalTheory.DegVol.Swap

variable {k r j : ℕ}

theorem upperIn_0 (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, h.ne]
  · simp [upperIn, upper, h, Matrix.one_apply]

private lemma wI_eq_mI (m : Fin (k + 1)) : wI k r m = UEmb.mI k r m := Fin.ext (by simp [wI, UEmb.mI])

theorem pOf_mul_we (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin (k + 1)) (b : Fin r) :
    (pOf k r q * uEmb k r u) (wI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (wI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_we, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

theorem pOf_mul_se (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (pOf k r q * uEmb k r u) (esI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (esI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_se, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

private lemma crd_eI_eI (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (eI k r a) (eI k r b) = upperIn β x.1 a b := by
  simp only [crd, pTop]
  exact pOf_mul_ee _ _ a b

private lemma crd_mI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (m : Fin (k + 1)) (b : Fin r) :
    crd k r j β x (UEmb.mI k r m) (eI k r b) = 0 := by
  rw [← wI_eq_mI]
  simp only [crd, pTop]
  exact pOf_mul_we _ _ m b

private lemma crd_esI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (esI k r a) (eI k r b) = 0 := by
  simp only [crd, pTop]
  exact pOf_mul_se _ _ a b

theorem upperIn_mul (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) :
    upperIn β w.1 = upperIn β p.1 * upperIn β q.1 := by
  ext a b
  have e : (crd k r j β p * crd k r j β q) (eI k r a) (eI k r b) = crd k r j β w (eI k r a) (eI k r b) := by
    rw [h]
  rw [crd_eI_eI, Matrix.mul_apply, UEmb.sum_idx] at e
  simp only [crd_mI_eI_eq_zero, crd_esI_eI_eq_zero, crd_eI_eI, mul_zero, Finset.sum_const_zero, add_zero] at e
  rw [← e, Matrix.mul_apply]

theorem upper_mul_entry (x y : UT r → ℂ) (i : UT r)
    (hx : ∀ l : UT r, l.1.2.val - l.1.1.val < i.1.2.val - i.1.1.val → x l = 0) :
    (upper x * upper y) i.1.1 i.1.2 = x i + y i := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab.ne]
  · simp only [upper, lt_irrefl, dif_neg, not_false_eq_true, if_true, dif_pos hab, one_mul, mul_one]
    exact add_comm _ _
  · rintro c ⟨hca, hcb⟩
    simp only [upper]
    by_cases h1 : a < c
    · by_cases h2 : c < b
      · have hl : c.val - a.val < b.val - a.val := by
          have := Fin.lt_def.mp h1; have := Fin.lt_def.mp h2; omega
        rw [dif_pos h1, hx ⟨(a, c), h1⟩ hl, zero_mul]
      · rw [dif_neg h2, if_neg hcb, mul_zero]
    · rw [dif_neg h1, if_neg (Ne.symm hca), zero_mul]

theorem first (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (i : UTin β)
    (hi : ∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) :
    w.1 i = p.1 i + q.1 i := by
  have e := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i.1.1.1 i.1.1.2) (upperIn_mul β p q w h)
  simp only [upperIn] at e
  rw [upper_mul_entry _ _ i.1] at e
  · simpa [upper, i.1.2, i.2] using e
  · intro l hl
    split_ifs with hβ
    · exact hi ⟨l, hβ⟩ hl
    · rfl

theorem cancel (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (hp : p.1 = 0) :
    pTop k r j p.2 * pTop k r j q.2 = pTop k r j w.2 := by
  have hm := upperIn_mul β p q w h
  rw [hp, upperIn_0, one_mul] at hm
  set U := upperIn β q.1 with hUdef
  have hT : U.IsUpperTriangular := by
    intro a b hba
    have h1 : ¬ a < b := not_lt.mpr hba.le
    have h2 : a ≠ b := ne_of_gt hba
    simp [hUdef, upperIn, upper, h1, h2]
  have hU : IsUnit U.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    simp [hUdef, upperIn, upper]
  have hV : uEmb k r U * uEmb k r U⁻¹ = 1 := by
    rw [← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ hU, UEmb.uEmb_one]
  have h' : pTop k r j p.2 * pTop k r j q.2 * uEmb k r U = pTop k r j w.2 * uEmb k r U := by
    have h2 := h
    simp only [crd, hp, upperIn_0, UEmb.uEmb_one, mul_one, hm] at h2
    rw [mul_assoc]
    exact h2
  calc pTop k r j p.2 * pTop k r j q.2
      = pTop k r j p.2 * pTop k r j q.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [mul_assoc _ (uEmb k r U), hV, mul_one]
    _ = pTop k r j w.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [h']
    _ = pTop k r j w.2 := by rw [mul_assoc, hV, mul_one]

private lemma eq_and_eq_of_pEl_eq (B B' : Fin r → Fin (k + 1) → ℂ) (S S' : Matrix (Fin r) (Fin r) ℂ)
    (h : pEl k r B S = pEl k r B' S') : B = B' ∧ S = S' := by
  have hB : B = B' := by
    funext b c
    simpa [Rad.pEl_ws] using
      congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (wI k r c) (esI k r b)) h
  subst hB
  refine ⟨rfl, ?_⟩
  ext a b
  simpa [Rad.pEl_es] using
    congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (eI k r a) (esI k r b)) h

theorem crd_mul : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  intro k r j β
  refine ⟨?_, fun p q w h => ⟨fun i hi => first β p q w h i hi, fun hp => ?_, fun hp hB => ?_⟩⟩
  · have hS : skewM (r := r) (fun _ => 0) (fun _ => 0) = 0 := by
      ext a b
      simp only [skewM, Matrix.zero_apply]
      split_ifs <;> simp
    simp only [crd, Prod.fst_zero, Prod.snd_zero, upperIn_0, UEmb.uEmb_one, mul_one, pTop, pOf,
      Pi.zero_apply, dite_eq_ite, ite_self, hS]
    exact Rad.pEl_zero
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf] at hc
    rw [Rad.pEl_mul] at hc
    have hB' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).1
    funext a c
    have e := congrFun (congrFun hB' a.1) c
    simpa [a.2] using e.symm
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf, hB, Pi.zero_apply, dite_eq_ite, ite_self] at hc
    rw [Rad.pEl_mul] at hc
    have hS' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).2
    simp only [Rad.herm_Hb] at hS'
    ext x
    · obtain ⟨⟨⟨a, b⟩, hab⟩, hj⟩ := x
      have e := congrFun (congrFun hS' a) b
      simp [skewM, hab, hj] at e
      simpa using e.symm
    · obtain ⟨a, ha⟩ := x
      have e := congrArg Complex.im (congrFun (congrFun hS' a) a)
      simp [skewM, ha] at e
      simpa using e.symm

end GlobalTheory.DegVol.RefCovMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLawStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commonStabilizerFromCoordinates_product_law : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  first | exact @GlobalTheory.DegVol.RefCovMul.crd_mul | exact GlobalTheory.DegVol.RefCovMul.crd_mul | (intros; apply GlobalTheory.DegVol.RefCovMul.crd_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdjointMemAndExistsIntegralPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdjointMemAndExistsIntegralPoint
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.RatElt

theorem hform_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

theorem cT_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (starRingEnd E) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply, starRingEnd_apply]

theorem unitary_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ e, τ (f e) = f (σ e)) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) : Formalism.UG.cT τ (g.map f) * J.map f * g.map f = J.map f := by
  have hc : Formalism.UG.cT τ (g.map f) = (Formalism.UG.cT σ g).map f := by
    ext i j
    simp [Formalism.UG.cT, hf]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hUJ : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J := hγ
  have hγH : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J := by rwa [cT_eq] at hUJ
  let γA : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) :=
    Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ
  have hγA : (γA : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  have hA : γA ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (γA : Matrix (Fin I.n) (Fin I.n) _) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γA = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [hγA]
    exact unitary_map (starRingEnd I.E) _ _ (fun e => Formalism.UG.P.csDual_sig_incl I.cm.sig e) _ _ hUJ

  let Mu : ∀ v, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Units.map (RingHom.mapMatrix (I.φ v)).toMonoidHom γ * (I.P_unit v).unit
  have hMu : ∀ v, (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [Mu, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hU : ∀ v, Mu v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    show Formalism.REAL.inUJ (I.ε v) (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ)
    unfold Formalism.REAL.inUJ
    set Q := I.P v with hQdef
    set G := (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) with hGdef
    have hQ : Q * Q⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
    have hQH : Q⁻¹ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
    have hGH : Gᴴ = (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ.map (I.φ v) := by
      ext i j
      simp only [G, conjTranspose_apply, Matrix.map_apply]
      rw [I.cm.cmUnram.2.1 (I.φ v)]
      rfl
    have hGJG : Gᴴ * (I.J.map (I.φ v) * (G * Q)) = I.J.map (I.φ v) * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGH, hGdef, ← Matrix.map_mul, ← Matrix.map_mul, hγH]
    rw [hMu, ← I.P_spec v, ← hQdef, ← hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q⁻¹ᴴ Qᴴ, hQH, Matrix.one_mul, ← Matrix.mul_assoc Q Q⁻¹, hQ, Matrix.one_mul, hGJG]
  exact ⟨⟨fun v => ⟨Mu v, hU v⟩, ⟨γA, hA⟩⟩, fun v => hMu v, hγA⟩

theorem adj_mem (I : AutInst) (x : I.GA) (T : Matrix (Fin I.n) (Fin I.n) I.E)
    (hT : ∀ y ∈ lamX I x, T *ᵥ y ∈ lamX I x) : ∀ y ∈ lamX I x, (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I x := by
  intro y hy
  obtain ⟨-, -, -, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  rw [hdual]
  intro z hz
  have hJ : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)
  have key : Formalism.UG.hform (starRingEnd I.E) I.J z ((I.J⁻¹ * Tᴴ * I.J) *ᵥ y) =
      Formalism.UG.hform (starRingEnd I.E) I.J (T *ᵥ z) y := by
    have hM : I.J * (I.J⁻¹ * Tᴴ * I.J) = Tᴴ * I.J := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
    rw [hform_eq, hform_eq, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
  rw [key]
  exact (hdual y).1 hy _ (hT z hz)

private lemma inv_mul_map_inclE_of_mem_lf (I : AutInst) (xf : I.Gf) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (hδ : ∀ y ∈ lamX I (1, xf), δ *ᵥ y ∈ lamX I (1, xf))
    (x : Fin I.n → (TensorProduct I.F I.E (Af I.F))) (hx : x ∈ I.Lf) :
    ((((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)))⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * ((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *ᵥ x ∈ I.Lf := by
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L hfin I.L_span g
  have hglob : Formalism.UG.CS.globLat g I.L = lamX I (1, xf) := (GlobalTheory.PointLattice.lamX_eq_globLat I (1, xf)).symm
  rw [hglob] at hrec

  have hspan : ∀ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))),
      δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨δ *ᵥ y, hδ y hy, ?_⟩
      funext i
      exact RingHom.map_mulVec _ _ _ _
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ =>
      rw [Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul s w _ h =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ s h
  have hu := (hrec ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, ← hL]
    exact hx)
  have h2 := (hrec _).1 (hspan _ hu)
  rw [← hL] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact h2

theorem adj_mem_and_exists_latGroup : ∀ (I : AutInst) (xf : I.Gf), (∀ T : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ lamX I (1, xf), T *ᵥ y ∈ lamX I (1, xf)) → ∀ y ∈ lamX I (1, xf), (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I (1, xf)) ∧ ∀ γ : Matrix (Fin I.n) (Fin I.n) I.E, γᴴ * I.J * γ = I.J → (∀ y ∈ lamX I (1, xf), γ *ᵥ y ∈ lamX I (1, xf)) → ∃ g ∈ latGroup I xf, ∀ v, uMat (g v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v := by
  intro I xf
  refine ⟨fun T hT => adj_mem I (1, xf) T hT, ?_⟩
  intro γ hγJ hγL
  have hdet : γ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hγJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    exact I.J_det h1.symm
  let γu : GL (Fin I.n) I.E := Matrix.nonsingInvUnit γ (isUnit_iff_ne_zero.mpr hdet)
  have hγu : (γu : Matrix (Fin I.n) (Fin I.n) I.E) = γ := rfl
  have hmemUJ : γu ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γu : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γu = I.J
    rw [cT_eq, hγu]
    exact hγJ
  obtain ⟨a, ha1, ha2⟩ := exists_point I γu hmemUJ
  refine ⟨a.1, ⟨a, ⟨γu, hmemUJ, ha1, ha2⟩, rfl, ?_⟩, ha1⟩
  have hδγ : (I.J⁻¹ * γᴴ * I.J) * γ = 1 := by
    rw [show (I.J⁻¹ * γᴴ * I.J) * γ = I.J⁻¹ * (γᴴ * I.J * γ) by simp only [Matrix.mul_assoc], hγJ,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.J_det)]
  have hδγA : (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
    rw [← Matrix.map_mul, hδγ]
    simp
  have ha2' : ((a.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hγu]
    exact ha2
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hmat : (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul]
    rw [ha2']
  have hprod : (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *
      (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) = 1 := by
    calc _ = ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
            ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hδγA, Matrix.mul_one, Units.inv_mul]
  show ((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  unfold Formalism.UG.stabGL
  intro x
  show x ∈ I.Lf ↔ (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x ∈ I.Lf
  rw [hmat]
  constructor
  · intro hx
    exact inv_mul_map_inclE_of_mem_lf I xf γ hγL x hx
  · intro hx
    have h1 := inv_mul_map_inclE_of_mem_lf I xf (I.J⁻¹ * γᴴ * I.J) (adj_mem I (1, xf) γ hγL) _ hx
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h1

end GlobalTheory.RadCov.RatElt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdjointMemAndExistsIntegralPointStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_mem_and_exists_integral_point : ∀ (I : AutInst) (xf : I.Gf), (∀ T : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ lamX I (1, xf), T *ᵥ y ∈ lamX I (1, xf)) → ∀ y ∈ lamX I (1, xf), (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I (1, xf)) ∧ ∀ γ : Matrix (Fin I.n) (Fin I.n) I.E, γᴴ * I.J * γ = I.J → (∀ y ∈ lamX I (1, xf), γ *ᵥ y ∈ lamX I (1, xf)) → ∃ g ∈ latGroup I xf, ∀ v, uMat (g v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v := by
  first | exact @GlobalTheory.RadCov.RatElt.adj_mem_and_exists_latGroup | exact GlobalTheory.RadCov.RatElt.adj_mem_and_exists_latGroup | (intros; apply GlobalTheory.RadCov.RatElt.adj_mem_and_exists_latGroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentralMapMemIntegralUnipotentFixingFrame
noncomputable section

namespace GlobalTheory.LoopC.Centre

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def nil (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  ∑ a, ∑ a', (c a a' • S.hT (e a')).smulRight (e a)

theorem nil_apply (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V) :
    nil e c x = ∑ a, ∑ a', (c a a' * S.hT (e a') x) • e a := by
  simp [nil]

theorem nil_eq_zero (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V)
    (hx : ∀ a, S.hT (e a) x = 0) : nil e c x = 0 := by
  rw [nil_apply]
  simp [hx]

theorem hT_nil (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) (a : Fin r) : S.hT (e a) (nil e c x) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [nil_apply, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun b' _ => ?_
  rw [LinearMap.map_smul, he, smul_zero]

def cen (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (LinearMap.id + nil e c) (LinearMap.id - nil e c)
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])

theorem cen_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) : cen e he c x = x + nil e c x := rfl

theorem cen_symm_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0)
    (c : Matrix (Fin r) (Fin r) E) (x : S.V) : (cen e he c).symm x = x - nil e c x := rfl

theorem cen_isom (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (hc : cᴴ = -c) : cen e he c ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hstar : ∀ a a', starRingEnd E (c a a') = -c a' a := by
    intro a a'
    have h := congrFun (congrFun hc a') a
    rw [starRingEnd_apply]
    simpa [Matrix.conjTranspose_apply] using h
  have hsym : ∀ u v, starRingEnd E (S.hT u v) = S.hT v u := S.herm.eq

  have hnn : ∀ x y, S.hT (nil e c x) (nil e c y) = 0 := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [nil_apply e c x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_nil e he c y a, smul_zero]

  have hcross : ∀ x y, S.hT (nil e c x) y + S.hT x (nil e c y) = 0 := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [nil_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.map_smul, smul_eq_mul, map_mul, RingHom.id_apply, hstar, hsym]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a' _ => ?_
    ring
  show ∀ x y, S.hT (cen e he c x) (cen e he c y) = S.hT x y
  intro x y
  rw [cen_apply, cen_apply]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hnn, add_zero]
  linear_combination hcross x y

theorem nil_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (e : Fin r → S.V)
    (heΛ : ∀ a, e a ∈ Λ) (c : Matrix (Fin r) (Fin r) (𝓞 E)) (x : S.V) (hx : x ∈ Λ) :
    nil e (c.map (algebraMap (𝓞 E) E)) x ∈ Λ := by
  rw [nil_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun a' _ => ?_
  have hd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    have h' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hΛ
    rw [h']
    exact hx
  have h1 : S.hT (e a') x ∈ (1 : Submodule (𝓞 E) E) := by
    have h2 := (Submodule.mem_iInf _).mp hd (e a')
    have h3 := (Submodule.mem_iInf _).mp h2 (heΛ a')
    exact h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  rw [Matrix.map_apply, ← ho, ← map_mul, algebraMap_smul]
  exact Λ.smul_mem _ (heΛ a)

theorem centre_gen {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (heΛ : ∀ a, F.fl.e a ∈ Λ)
    (c : Matrix (Fin r) (Fin r) (𝓞 E))
    (hc : (c.map (algebraMap (𝓞 E) E))ᴴ = -c.map (algebraMap (𝓞 E) E)) :
    ∃ n : S.V ≃ₗ[E] S.V, (n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b) ∧
      (∀ x ∈ orth S (Xsp F), n x = x) ∧
      ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : E) * S.hT (F.fl.e a') x) • F.fl.e a := by
  have hiso : ∀ a b, S.hT (F.fl.e a) (F.fl.e b) = 0 := F.fl.e_iso

  have hXz : ∀ a', ∀ x ∈ Xsp F, S.hT (F.fl.e a') x = 0 := by
    intro a' x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a')) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.mpr (hiso a' b)
    exact LinearMap.mem_ker.mp (hle hx)
  have hXe : ∀ a, F.fl.e a ∈ Xsp F := by
    intro a
    show F.fl.e a ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨a, rfl⟩

  have hfix : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x = x := by
    intro x hx
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    have h2 := (Submodule.mem_iInf _).mp hx (F.fl.e a')
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h2 (hXe a'))

  have hframe : ∀ b, cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) (frame F b) = frame F b := by
    intro b
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    induction b using Fin.lastCases with
    | last => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using F.fl.z_orth a'
    | cast i => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using hiso a' i

  have hflag : ∀ j, ∀ x ∈ Xflag F (j + 1),
      cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xflag F j := by
    intro j x hx
    have hle : Xflag F (j + 1) ≤ Xsp F := by
      show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ Submodule.span E (Set.range F.fl.e)
      exact Submodule.span_mono (Set.image_subset_range _ _)
    rw [cen_apply, nil_eq_zero _ _ _ (fun a' => hXz a' x (hle hx)), add_zero, sub_self]
    exact zero_mem _
  have horth : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xsp F := by
    intro x hx
    rw [hfix x hx, sub_self]
    exact zero_mem _

  have hmap : Formalism.HermitianLatticesTheory.gmap (cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E))) Λ = Λ := by
    show Submodule.map _ Λ = Λ
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x ∈ Λ
      rw [cen_apply]
      exact Λ.add_mem hx (nil_mem Λ hΛ _ heΛ c x hx)
    · intro y hy
      refine Submodule.mem_map.mpr ⟨y - nil F.fl.e (c.map (algebraMap (𝓞 E) E)) y,
        Λ.sub_mem hy (nil_mem Λ hΛ _ heΛ c y hy), ?_⟩
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) _ = y
      rw [← cen_symm_apply F.fl.e hiso _ y]
      exact LinearEquiv.apply_symm_apply _ y
  have hN : cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    exact ⟨⟨cen_isom _ _ _ hc, hmap⟩, hflag, horth⟩
  refine ⟨cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)), ⟨hN, hframe⟩, hfix, fun x => ?_⟩
  rw [cen_apply, nil_apply]
  rfl

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem centralMap_mem_integralUnipotentFixingFrame : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → (∀ a, F.fl.e a ∈ Λ) → ∀ c : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E), (c.map (algebraMap (𝓞 D.host.E) D.host.E))ᴴ = -c.map (algebraMap (𝓞 D.host.E) D.host.E) → ∃ n ∈ N1 D Λ F, (∀ x ∈ orth (hS D) (Xsp F), n x = x) ∧ ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : D.host.E) * (hS D).hT (F.fl.e a') x) • F.fl.e a := by
  intro D T F Λ hΛ heΛ c hc
  obtain ⟨n, h1, hfix, hform⟩ := centre_gen F Λ hΛ heΛ c hc
  exact ⟨n, h1, hfix, hform⟩

end GlobalTheory.LoopC.Centre

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_biorth {E : Type} [Field E] {n m : ℕ} {r : ℕ → ℕ}
    (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (hr : ∀ b, m ≤ b → r b = 0)
    (hn : n = ∑ b ∈ Finset.range m, r b)
    (hs : ∀ y : Fin n → E, ∃ u : ∀ b, Fin (r b) → E, y = ∑ b ∈ Finset.range m, T b *ᵥ u b) :
    ∃ T' : ∀ b, Matrix (Fin (r b)) (Fin n) E, Biorth r m T T' := by
  classical
  let Φ : ((b : Fin m) → Fin (r b) → E) →ₗ[E] (Fin n → E) :=
    ∑ b : Fin m, (T b).mulVecLin ∘ₗ LinearMap.proj b
  have hΦ : ∀ u : ∀ b, Fin (r b) → E, Φ (fun b => u b) = ∑ b ∈ Finset.range m, T b *ᵥ u b := by
    intro u
    rw [← Fin.sum_univ_eq_sum_range (fun b => T b *ᵥ u b)]
    simp [Φ]
  have hsurj : Function.Surjective Φ := fun y => by
    obtain ⟨u, hu⟩ := hs y
    exact ⟨_, (hΦ u).trans hu.symm⟩
  have hinj : Function.Injective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hn, Fin.sum_univ_eq_sum_range]
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let T' : ∀ b, Matrix (Fin (r b)) (Fin n) E := fun b =>
    if h : b < m then LinearMap.toMatrix'
      ((LinearMap.proj (⟨b, h⟩ : Fin m) : ((b : Fin m) → Fin (r b) → E) →ₗ[E] _) ∘ₗ e.symm.toLinearMap)
    else 0
  have hemp : ∀ b, ¬ b < m → IsEmpty (Fin (r b)) := fun b hb => by
    rw [hr b (by omega)]; infer_instance
  have hT' : ∀ (b : Fin m) y, T' b *ᵥ y = e.symm y b := fun b y => by
    simp only [T', dif_pos b.2]
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have H1 : ∀ (u : ∀ b, Fin (r b) → E) b, T' b *ᵥ (∑ c ∈ Finset.range m, T c *ᵥ u c) = u b := by
    intro u b
    by_cases hb : b < m
    · rw [hT' ⟨b, hb⟩, ← hΦ]
      exact congrFun (e.symm_apply_apply _) _
    · have := hemp b hb
      exact Subsingleton.elim _ _
  have H2 : ∀ b c v, T' b *ᵥ (T c *ᵥ v) = (Pi.single c v : ∀ b, Fin (r b) → E) b := by
    intro b c v
    rw [← H1 (Pi.single c v) b]
    congr 1
    by_cases hc : c < m
    · rw [Finset.sum_eq_single c (fun d _ hd => by simp [Pi.single_eq_of_ne hd])
        (fun h => absurd (Finset.mem_range.2 hc) h)]
      simp
    · have := hemp c hc
      obtain rfl : v = 0 := Subsingleton.elim _ _
      simp
  refine ⟨T', fun b => ?_, fun b c hbc => ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp [Pi.single_eq_of_ne hbc]
  · refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    obtain ⟨u, rfl⟩ := hs y
    simp only [Matrix.toLin'_apply]
    rw [Matrix.sum_mulVec, Matrix.one_mulVec]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Matrix.mulVec_mulVec, H1]

theorem exists_biorth_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsFullLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsFullLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  intro E _ _ n m F r hmono h0 hm hL hsat hrk
  letI := hL
  have hle : ∀ b, F b ≤ F m := fun b => by
    rcases le_total b m with h | h
    · exact hmono h
    · exact (hm b h).le
  have key : ∀ b, ∃ A : Submodule (𝓞 E) (Fin n → E), A ⊓ F b = ⊥ ∧ A ⊔ F b = F (b + 1) := by
    intro b
    refine exists_compl_of_saturated _ _ (hmono b.le_succ) (Submodule.FG.of_le hL.fg (hle _)) ?_
    intro c y hc hy hcy
    apply hsat _ y (hle _ hy)
    have hc' : (c : E) ≠ 0 := by simpa using hc
    rw [← Submodule.smul_mem_iff _ hc']
    exact Submodule.subset_span hcy
  choose A hA1 hA2 using key
  have hAF : ∀ b, A b ≤ F (b + 1) := fun b => hA2 b ▸ le_sup_left
  have hAr : ∀ b, Formalism.HN.rkK (A b) = r b := fun b => by
    have := AdaptedExists.rkK_add (hA1 b)
    rw [hA2, hrk] at this
    omega
  choose Λ T hΛ hT using fun b => AdaptedExists.exists_model (A b)
    (Submodule.FG.of_le hL.fg ((hAF b).trans (hle _))) (hAr b)
  have hdec : ∀ k, ∀ y ∈ F k, ∃ u : ∀ b, Fin (r b) → E, (∀ b, u b ∈ Λ b) ∧
      y = ∑ b ∈ Finset.range k, T b *ᵥ u b := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [h0, Submodule.mem_bot] at hy
      exact ⟨0, fun b => zero_mem _, by simpa using hy⟩
    | succ k ih =>
      intro y hy
      rw [← hA2] at hy
      obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨v, hv, rfl⟩ := (hT k a).1 ha
      obtain ⟨u, hu, rfl⟩ := ih z hz
      refine ⟨Function.update u k v, fun b => ?_, ?_⟩
      · by_cases hb : b = k
        · subst hb; simpa using hv
        · rw [Function.update_of_ne hb]; exact hu b
      · rw [Finset.sum_range_succ, add_comm, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [Function.update_of_ne (Finset.mem_range.1 hc).ne]
  have hr0 : ∀ b, m ≤ b → r b = 0 := fun b hb => by
    have := hrk b
    rw [hm b hb, hm (b + 1) (by omega)] at this
    omega
  have hsum : ∀ k, Formalism.HN.rkK (F k) = ∑ b ∈ Finset.range k, r b := by
    intro k
    induction k with
    | zero => rw [h0]; simp [Formalism.HN.rkK]
    | succ k ih => rw [hrk, ih, Finset.sum_range_succ]
  have hn : n = ∑ b ∈ Finset.range m, r b := by
    rw [← hsum, Formalism.HN.rkK, Submodule.IsFullLattice.span_eq_top (A := E) (M := F m)]
    simp
  obtain ⟨T', hB⟩ := exists_biorth T hr0 hn (fun y => by
    obtain ⟨c, hc, hcy⟩ := AdaptedExists.exists_smul_mem (L := F m) (x := y)
      (by rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := F m)]; trivial)
    obtain ⟨u, -, hu⟩ := hdec m _ hcy
    have hc' : (c : E) ≠ 0 := by simpa using hc
    refine ⟨fun b => (c : E)⁻¹ • u b, ?_⟩
    simp only [Matrix.mulVec_smul]
    rw [← Finset.smul_sum, ← hu, eq_inv_smul_iff₀ hc']
    rfl)
  refine ⟨T, T', Λ, hB, hΛ, fun k y => ⟨fun hy b => ?_, fun hy => ?_⟩⟩
  · obtain ⟨u, hu, rfl⟩ := hdec k y hy
    have h1 : T' b *ᵥ (∑ c ∈ Finset.range k, T c *ᵥ u c) = if b < k then u b else 0 := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec]
      split_ifs with hb
      · rw [Finset.sum_eq_single b (fun c _ hc => by rw [hB.2.1 b c hc.symm, Matrix.zero_mulVec])
          (fun h => absurd (Finset.mem_range.2 hb) h), hB.1, Matrix.one_mulVec]
      · refine Finset.sum_eq_zero fun c hc => ?_
        rw [hB.2.1 b c (by have := Finset.mem_range.1 hc; omega), Matrix.zero_mulVec]
    rw [h1]
    refine ⟨?_, fun h => if_neg (by omega)⟩
    split_ifs
    · exact hu b
    · exact zero_mem _
  · have h1 : y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.sum_mulVec, hB.2.2, Matrix.one_mulVec]
    rw [h1]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · rw [(hy b).2 hb, Matrix.mulVec_zero]; exact zero_mem _
    · exact hmono (show b + 1 ≤ k by omega) (hAF b ((hT b _).2 ⟨_, (hy b).1, rfl⟩))

end GlobalTheory.RadCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biorthogonal_frame_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsFullLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsFullLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  first
  | exact @GlobalTheory.RadCov.exists_biorth_of_saturated_flag
  | intro E _ _ n m F r hmono h0 hm hL hsat hrk
    obtain ⟨T, T', Λ, hB, hΛ, hmem⟩ :=
      GlobalTheory.RadCov.exists_biorth_of_saturated_flag E n m F r hmono h0 hm
        hL.toIsLattice hsat hrk
    refine ⟨T, T', Λ, hB, ?_, hmem⟩
    intro b
    let : Submodule.IsLattice E (Λ b) := hΛ b
    refine { span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro v _
    have hle : Submodule.span E (F m : Set (Fin n → E)) ≤
        (Submodule.span E (Λ b : Set (Fin (r b) → E))).comap (T' b).mulVecLin := by
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span ((hmem m x).1 hx b).1
    have hx : T' b *ᵥ (T b *ᵥ v) ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) :=
      hle (by rw [hL.span_eq_top]; trivial)
    rw [Matrix.mulVec_mulVec, hB.1 b, Matrix.one_mulVec] at hx
    exact hx
end
end

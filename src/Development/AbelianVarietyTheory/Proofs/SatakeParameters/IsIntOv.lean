module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

section Pure

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K]

def IsInt (x : K) : Prop := ∃ o : O, algebraMap O K o = x

def IntM {m n : ℕ} (x : Matrix (Fin m) (Fin n) K) : Prop := ∀ i j, IsInt O (x i j)

def GInt {n : ℕ} (x : GL (Fin n) K) : Prop := IntM O x.1 ∧ IntM O (x⁻¹).1

def Hk (p : O) (j : ℕ) {n : ℕ} (x : GL (Fin n) K) : Prop :=
  IntM O x.1 ∧ IntM O (algebraMap O K p • (x⁻¹).1) ∧ ∃ u : Oˣ, x.1.det = algebraMap O K (p ^ j * u)

def Reps {n : ℕ} {ι : Type} (x : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) : Prop :=
  (∀ γ ∈ R, ∃ k₁ k₂, GInt O k₁ ∧ GInt O k₂ ∧ ρ γ = k₁ * x * k₂) ∧
    ∀ k₁ k₂, GInt O k₁ → GInt O k₂ → ∃! γ, γ ∈ R ∧ GInt O ((ρ γ)⁻¹ * (k₁ * x * k₂))

variable {O}

theorem isInt_iff {x : K} : IsInt O x ↔ x ∈ (algebraMap O K).range := Iff.rfl

theorem intM_iff {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} :
    IntM O x ↔ ∃ A : Matrix (Fin m) (Fin n) O, A.map (algebraMap O K) = x := by
  constructor
  · intro h
    choose A hA using h
    exact ⟨Matrix.of A, by ext i j; simp [hA]⟩
  · rintro ⟨A, rfl⟩ i j
    exact ⟨A i j, rfl⟩

theorem IntM.mul {l m n : ℕ} {x : Matrix (Fin l) (Fin m) K} {y : Matrix (Fin m) (Fin n) K} (hx : IntM O x)
    (hy : IntM O y) : IntM O (x * y) := by
  rw [intM_iff] at hx hy ⊢
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  exact ⟨A * B, Matrix.map_mul⟩

theorem IntM.add {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x + y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a + b, by simp [ha, hb]⟩

theorem IntM.sub {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x - y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a - b, by simp [ha, hb]⟩

theorem IntM.transpose {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} (hx : IntM O x) : IntM O xᵀ := fun i j => hx j i

theorem intM_one {n : ℕ} : IntM O (1 : Matrix (Fin n) (Fin n) K) := fun i j => by
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Matrix.one_apply_ne h]⟩

theorem gInt_one {n : ℕ} : GInt O (1 : GL (Fin n) K) := ⟨intM_one, by rw [inv_one]; exact intM_one⟩

theorem GInt.mul {n : ℕ} {x y : GL (Fin n) K} (hx : GInt O x) (hy : GInt O y) : GInt O (x * y) := ⟨IntM.mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact IntM.mul hy.2 hx.2⟩

theorem GInt.inv {n : ℕ} {x : GL (Fin n) K} (hx : GInt O x) : GInt O x⁻¹ := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

end Pure

variable {D : D7}

abbrev Ov (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := v.adicCompletionIntegers D.host.F

theorem isInt_Ov {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v} :
    IsInt (Ov D v) x ↔ x ∈ v.adicCompletionIntegers D.host.F := ⟨fun ⟨o, h⟩ => h ▸ o.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

def Chart (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v) : Prop :=
  Function.Surjective π ∧ (∀ a, π a = 0 ↔ e * a = 0) ∧
    (∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y)) ∧
    ∀ a, finPart D (e * a) ∈ intAE D ↔ IsInt (Ov D v) (π a)

def Frame (V : HSp D) (e : AE D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : Prop :=
  ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V ↔
    ∀ i, IsInt (Ov D v) (((β⁻¹).1 *ᵥ fun k => π (y k)) i)

def rho (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : GA D V →* GL (Fin V.rank) (Fv D.host.F v) :=
  (MulAut.conj β⁻¹).toMonoidHom.comp ((Matrix.GeneralLinearGroup.map π).comp (matHom V))

theorem rho_val (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (rho V π β g).1 = (β⁻¹).1 * (mt V g).map π * β.1 := by
  simp only [rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
  rfl

end GlobalTheory.SplitHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivDual

section Abstract

variable {R : Type} [CommRing R] {n : ℕ}

def Dv (Λ : (Fin n → R) → Prop) (O : R → Prop) (e : R) (u : Fin n → R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, O (z i)) → Λ (e • B.mulVec z)) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • y = e • B.mulVec z) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i)) ∧
    (∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i))

theorem Dv.inv {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u u' : Fin n → R}
    {A A' : Matrix (Fin n) (Fin n) R} (he : e * e = e) (hA : A' * A = 1)
    (hu : ∀ i, u i * u' i.rev = 1) (h : Dv Λ O e u A) : Dv Λ O e u' A' := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have hcancel : ∀ y, A'.mulVec (e • A.mulVec y) = e • y := fun y => by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  let B' : Matrix (Fin n) (Fin n) R := Matrix.of fun a j => (A' * B) a j.rev * u j.rev
  have hB' : ∀ z, B'.mulVec z = A'.mulVec (B.mulVec fun i => u i * z i.rev) := fun z => by
    rw [Matrix.mulVec_mulVec]
    funext a
    simp only [B', Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    ring
  have hB'' : ∀ z : Fin n → R, B'.mulVec (fun i => u' i * z i) = A'.mulVec (B.mulVec fun i => z i.rev) := fun z => by
    rw [hB']
    congr 2
    funext i
    rw [← mul_assoc, hu, one_mul]
  refine ⟨B', fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := h4 (fun i => z i.rev) (fun i => hz _)
    rw [hB', ← Matrix.mulVec_smul, ← hyz, hcancel]
    obtain ⟨w, hw, hyw⟩ := h2 y hy
    rw [hyw]
    exact h1 w hw
  · obtain ⟨z, hz, hyz⟩ := h3 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB', ← Matrix.mulVec_smul]
    simp only [Fin.rev_rev]
    rw [← hyz, hcancel]
  · obtain ⟨z, hz, hyz⟩ := h2 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB'', ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hyz]
    simp only [Fin.rev_rev]
  · refine ⟨e • B.mulVec (fun i => z i.rev), h1 _ (fun i => hz _), ?_⟩
    rw [hB'', Matrix.mulVec_smul, smul_smul, he]

theorem Dv.mul {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u : Fin n → R}
    {A a a' b b' : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (hbb : b * b' = 1)
    (ha : ∀ y, Λ y ↔ Λ (a.mulVec y)) (hb : ∀ y, Λ y ↔ Λ (b.mulVec y))
    (h : Dv Λ O e u A) : Dv Λ O e u (a * A * b) := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have ea : ∀ y, a.mulVec (a'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, haa, Matrix.one_mulVec]
  have eb : ∀ y, b.mulVec (b'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  refine ⟨a * B, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    exact (ha _).1 (h1 z hz)
  · obtain ⟨z, hz, hyz⟩ := h2 (a'.mulVec y) ((ha _).2 (by rw [ea]; exact hy))
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hyz, Matrix.mulVec_smul, ea]
  · obtain ⟨z, hz, hyz⟩ := h3 (b.mulVec y) ((hb _).1 hy)
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]
  · obtain ⟨y, hy, hyz⟩ := h4 z hz
    refine ⟨b'.mulVec y, (hb _).2 (by rw [eb]; exact hy), ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]

end Abstract

theorem getD_dualLab (d : List ℤ) {n : ℕ} (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.rev.1 0 = -(d.getD i.1 0) := by
  subst hd
  have h1 : i.rev.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.rev.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  have := i.2
  congr 2
  omega

theorem divAt_iff {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V) :
    DivAt V e ϖ d α ↔ d.length = V.rank ∧ Dv (fun y => y ∈ LamHat V) (fun x => x ∈ intAE D) (finPart D e)
      (fun i => finPart D (incA D (ϖ ^ (d.getD i.1 0)))) (finMat D.sp.cm.sig V.gram α) := Iff.rfl

theorem divAt_inv_and_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  intro D V e ϖ d α he hϖ h
  rw [divAt_iff] at h
  obtain ⟨hd, h⟩ := h
  have hm : ∀ g g' : GA D V, finMat D.sp.cm.sig V.gram (g * g') =
      finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g' := fun g g' =>
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ g g'
  have h1 : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one _ _
  refine ⟨?_, fun a ha b hb => ?_⟩
  · rw [divAt_iff]
    refine ⟨by simpa [dualLab] using hd, h.inv (by rw [← map_mul, he]) ?_ fun i => ?_⟩
    · rw [← hm, inv_mul_cancel, h1]
    · rw [getD_dualLab d hd, ← map_mul, ← map_mul, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hϖ), map_one, map_one]
  · rw [divAt_iff, hm, hm]
    refine ⟨hd, h.mul (a' := finMat D.sp.cm.sig V.gram a⁻¹) (b' := finMat D.sp.cm.sig V.gram b⁻¹) ?_ ?_
      ha.2.1 hb.2.1⟩
    · rw [← hm, mul_inv_cancel, h1]
    · rw [← hm, mul_inv_cancel, h1]

end GlobalTheory.DivDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  first | exact @GlobalTheory.DivDual.divAt_inv_and_mul | exact GlobalTheory.DivDual.divAt_inv_and_mul | (intros; apply GlobalTheory.DivDual.divAt_inv_and_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
noncomputable section

namespace GlobalTheory.SplitLift

section General

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

open Formalism.UG

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_add (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_smul (σ : A →+* A) (a : A) (M : Matrix n n A) : cT σ (a • M) = σ a • cT σ M := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_involutive (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem exists_unitary (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (m m' : Matrix n n A)
    (h : e • (m * m') = e • (1 : Matrix n n A)) :
    ∃ g ∈ UJ σ J, (e + σ e) • ((g : Matrix n n A) - 1) = (g : Matrix n n A) - 1 ∧
      e • (g : Matrix n n A) = e • m := by
  have hKJ : K * J = 1 := mul_eq_one_comm.1 hJK
  have hK : cT σ K = K := by
    have h1 : cT σ K * J = 1 := by rw [← hJ, ← cT_mul, hJK, cT_one]
    calc cT σ K = cT σ K * (J * K) := by rw [hJK, mul_one]
      _ = K := by rw [← mul_assoc, h1, one_mul]
  have hee : σ e * σ e = σ e := by rw [← map_mul, he]
  have he'' : σ e * e = 0 := by rw [mul_comm, he']

  obtain ⟨x, hx⟩ : ∃ x, x = m - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = m' - 1 := ⟨_, rfl⟩
  have hm : m = 1 + x := by rw [hx]; abel
  have hm' : m' = 1 + y := by rw [hy]; abel
  have hab : (1 + e • x) * (1 + e • y) = 1 := by
    have h2 : e • (x + y + x * y) = 0 := by
      have : x + y + x * y = m * m' - 1 := by rw [hm, hm']; noncomm_ring
      rw [this, smul_sub, h, sub_self]
    calc (1 + e • x) * (1 + e • y) = 1 + (e • x + e • y + (e • x) * (e • y)) := by
          simp only [mul_add, add_mul, one_mul, mul_one]; abel
      _ = 1 := by
        rw [smul_mul_smul_comm, he, ← smul_add, ← smul_add, h2, add_zero]
  have hba : (1 + e • y) * (1 + e • x) = 1 := mul_eq_one_comm.1 hab
  let s : Matrix n n A → Matrix n n A := fun z => K * cT σ z * J
  have hs_mul : ∀ z w, s (z * w) = s w * s z := by
    intro z w
    show K * cT σ (z * w) * J = K * cT σ w * J * (K * cT σ z * J)
    rw [cT_mul]
    calc K * (cT σ w * cT σ z) * J = K * cT σ w * (J * K) * cT σ z * J := by rw [hJK]; noncomm_ring
      _ = _ := by noncomm_ring
  have hs_one : s 1 = 1 := by
    show K * cT σ 1 * J = 1
    rw [cT_one, mul_one, hKJ]
  have hs_e : ∀ z, s (1 + e • z) = 1 + σ e • s z := by
    intro z
    show K * cT σ (1 + e • z) * J = 1 + σ e • (K * cT σ z * J)
    rw [conjTransposeBy_ringInvolution_add, cT_one, conjTransposeBy_ringInvolution_smul, mul_add, add_mul, mul_one, hKJ, Matrix.mul_smul, Matrix.smul_mul]
  have hss : ∀ z, s (s z) = z := by
    intro z
    show K * cT σ (K * cT σ z * J) * J = z
    rw [cT_mul, cT_mul, conjTransposeBy_ringInvolution_involutive σ hσ, hJ, hK]
    calc K * (J * (z * K)) * J = (K * J) * z * (K * J) := by noncomm_ring
      _ = z := by rw [hKJ, one_mul, mul_one]
  have hcomm : ∀ z w : Matrix n n A, (1 + e • z) * (1 + σ e • w) = 1 + e • z + σ e • w ∧
      (1 + σ e • w) * (1 + e • z) = 1 + e • z + σ e • w := by
    intro z w
    constructor
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm e z (σ e) w, he', zero_smul]; simp
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm (σ e) w e z, he'', zero_smul]; simp; abel
  have hu : s ((1 + e • x) * s (1 + e • y)) * ((1 + e • x) * s (1 + e • y)) = 1 := by
    have hc : s (1 + e • x) * (1 + e • x) = (1 + e • x) * s (1 + e • x) := by
      rw [hs_e, (hcomm _ _).1, (hcomm _ _).2]
    rw [hs_mul, hss]
    calc (1 + e • y) * s (1 + e • x) * ((1 + e • x) * s (1 + e • y))
        = (1 + e • y) * (s (1 + e • x) * (1 + e • x)) * s (1 + e • y) := by simp only [mul_assoc]
      _ = ((1 + e • y) * (1 + e • x)) * (s (1 + e • x) * s (1 + e • y)) := by rw [hc]; simp only [mul_assoc]
      _ = 1 := by rw [← hs_mul, hba, hs_one, one_mul]
  have hg : (1 + e • x) * s (1 + e • y) = 1 + e • x + σ e • s y := by rw [hs_e, (hcomm _ _).1]
  refine ⟨⟨_, _, mul_eq_one_comm.1 hu, hu⟩, ?_, ?_, ?_⟩
  · show cT σ ((1 + e • x) * s (1 + e • y)) * J * ((1 + e • x) * s (1 + e • y)) = J
    generalize (1 + e • x) * s (1 + e • y) = g at hu
    calc cT σ g * J * g = (J * K) * (cT σ g * J * g) := by rw [hJK, one_mul]
      _ = J * (s g * g) := by simp only [s, mul_assoc]
      _ = J := by rw [hu, mul_one]
  · show (e + σ e) • ((1 + e • x) * s (1 + e • y) - 1) = (1 + e • x) * s (1 + e • y) - 1
    have : (1 + e • x) * s (1 + e • y) - 1 = e • x + σ e • s y := by rw [hg]; abel
    rw [this, smul_add, smul_smul, smul_smul, add_mul, add_mul, he, he', he'', hee, add_zero, zero_add]
  · show e • ((1 + e • x) * s (1 + e • y)) = e • m
    rw [hg, hm, smul_add, smul_add, smul_add, smul_smul, smul_smul, he, he', zero_smul, add_zero]

theorem exists_unitary_prod {B C : Type} [CommRing B] [CommRing C] (p : A →+* B) (q : A →+* C) (φ : A ≃+* B × C)
    (hφ : ∀ z, (φ z).1 = p z ∧ (φ z).2 = q z)
    (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (hinf : p e = 0) (m m' : Matrix n n C)
    (h : q e • (m * m') = q e • (1 : Matrix n n C)) :
    ∃ g ∈ UJ σ J, (∀ i j, (e + σ e) * ((g : Matrix n n A) - 1) i j = ((g : Matrix n n A) - 1) i j) ∧
      q e • (g : Matrix n n A).map q = q e • m := by
  have lift : ∀ M : Matrix n n C, ∃ N : Matrix n n A, N.map q = M := by
    intro M
    refine ⟨Matrix.of fun i j => φ.symm (0, M i j), Matrix.ext fun i j => ?_⟩
    show q (φ.symm (0, M i j)) = M i j
    rw [← (hφ _).2, RingEquiv.apply_symm_apply]
  obtain ⟨N, rfl⟩ := lift m
  obtain ⟨N', rfl⟩ := lift m'
  have hN : e • (N * N') = e • (1 : Matrix n n A) := by
    refine Matrix.ext fun i j => φ.injective (Prod.ext ?_ ?_)
    · rw [(hφ _).1, (hφ _).1, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul, hinf, zero_mul, zero_mul]
    · rw [← Matrix.map_mul, ← Matrix.map_one q (map_zero _) (map_one _)] at h
      rw [(hφ _).2, (hφ _).2, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul]
      exact congrFun (congrFun h i) j
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary σ hσ _ _ hJ hJK e he he' N N' hN
  refine ⟨g, hg, fun i j => congrFun (congrFun h1 i) j, Matrix.ext fun i j => ?_⟩
  have h3 : e * g.1 i j = e * N i j := congrFun (congrFun h2 i) j
  have h4 := congrArg q h3
  rw [map_mul, map_mul] at h4
  exact h4

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_lift : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ m m' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), finPart D e • (m * m') = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) → ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finPart D e • finMat D.sp.cm.sig V.gram g = finPart D e • m := by
  intro D V e he m m' h
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hinf : infPart D e = 0 := by
    obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
    have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
    rw [h6, RingHom.map_mul, h5, mul_zero]
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D) GlobalTheory.DualPairCheck.cA_cA _ _
    hJ hJK e he.1 he.2.1 hinf m m' h
  exact ⟨⟨g, hg⟩, h1, h2⟩

end GlobalTheory.SplitLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_split_place_component : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ m m' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), finPart D e • (m * m') = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) → ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finPart D e • finMat D.sp.cm.sig V.gram g = finPart D e • m := by
  first | exact @GlobalTheory.SplitLift.split_lift | exact GlobalTheory.SplitLift.split_lift | (intros; apply GlobalTheory.SplitLift.split_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLatBasis

theorem exists_matrix_of_isLattice {R K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {n : ℕ} (M : Submodule R (Fin n → K)) [Submodule.IsFullLattice K M] :
    ∃ B : GL (Fin n) K, ∀ x : Fin n → K, x ∈ M ↔
      ∀ i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i ∈ (algebraMap R K).range := by
  have := Submodule.IsLattice.finite K M
  have := Submodule.IsLattice.free K M
  have hr : Module.finrank R M = n := by
    rw [((Submodule.IsFullLattice.finrank_eq K M).trans (Module.finrank_fintype_fun_eq_card K)), Fintype.card_fin]
  let b : Module.Basis (Fin n) R M := Module.finBasisOfFinrankEq R M hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsFullLattice K
  let p := Pi.basisFun K (Fin n)
  let B : GL (Fin n) K := ⟨p.toMatrix c, c.toMatrix p, by simp, by simp⟩
  have hB : ∀ x i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i = c.repr x i := by
    intro x i
    have := congrFun (Module.Basis.toMatrix_mulVec_repr p c x) i
    exact this
  refine ⟨B, fun x => ?_⟩
  simp only [hB]
  constructor
  · intro hx i
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, algebraMap R K (b.repr ⟨x, hx⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [c, Module.Basis.extendOfIsFullLattice_apply, algebraMap_smul]
      exact this.symm
    have h2 := congrFun (c.repr_sum_self fun j => algebraMap R K (b.repr ⟨x, hx⟩ j)) i
    rw [← h1] at h2
    exact h2.symm
  · intro h
    choose r hr using h
    rw [← c.sum_repr x]
    refine sum_mem fun j _ => ?_
    rw [← hr, algebraMap_smul]
    refine M.smul_mem _ ?_
    simp [c]

theorem mul_mem_intAE (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem section_mem {A K ι κ : Type} [CommRing A] [Field K] (O : ValuationSubring K) (π : A →+* K) (σ : K → A) (ε : A)
    (I : Set A) (L : AddSubgroup (ι → A)) (h1 : ∀ a, π (σ a) = a) (h2 : ∀ x, σ (π x) = ε * x)
    (h3 : ∀ x, π x ∈ O → ε * x ∈ I) (h4 : ∀ a ∈ I, ∀ y ∈ L, (fun i => a * y i) ∈ L)
    (g : κ → ι → A) (hg : ∀ j, g j ∈ L) (w : ι → K)
    (hw : w ∈ Submodule.span O (Set.range fun j i => π (g j i))) : (fun i => σ (w i)) ∈ L := by
  have hε : ε ∈ I := by simpa using h3 1 (by simpa using one_mem O)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp only [h2]
    exact h4 _ hε _ (hg j)
  | zero =>
    have : σ 0 = 0 := by simpa using h2 0
    simp only [Pi.zero_apply, this]
    exact zero_mem L
  | add x y _ _ hx hy =>
    have : ∀ a b, σ (a + b) = ε * (σ a + σ b) := fun a b => by rw [← h2, map_add (f := _), h1, h1]
    simp only [Pi.add_apply, this]
    exact h4 _ hε _ (add_mem hx hy)
  | smul c x _ hx =>
    have : ∀ i, σ ((c • x) i) = (ε * σ c) * σ (x i) := fun i => by
      rw [mul_assoc, ← h2, map_mul, h1, h1]; rfl
    simp only [this]
    exact h4 _ (h3 _ (by rw [h1]; exact c.2)) _ hx


set_option maxHeartbeats 1000000 in
theorem exists_basis : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v) (s : Fv D.host.F v → Formalism.L2.Theta.AE D), e * e = e → (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) → (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) → (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) → ∃ B : GL (Fin V.rank) (Fv D.host.F v), ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (fun i => finPart D e * y i) ∈ LamHat V ↔ ∀ i, ((B⁻¹ : GL (Fin V.rank) (Fv D.host.F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v)).mulVec (fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D V e v π s _ h1 h2 h3 h4
  obtain ⟨k, x, hxL, hx⟩ := GlobalTheory.LatticeLocalGlobal.exists_generators V
  let φ : D.host.E →+* Fv D.host.F v := π.comp (Algebra.TensorProduct.includeRight
    (R := D.host.F) (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E)).toRingHom
  have hφ : ∀ a, φ a = π (1 ⊗ₜ[D.host.F] a) := fun _ => rfl
  let M : Submodule (v.adicCompletionIntegers D.host.F) (Fin V.rank → Fv D.host.F v) :=
    Submodule.span _ (Set.range fun j i => φ (V.frame.repr (x j) i))
  have hL : ∀ w ∈ V.L0, (fun i => φ (V.frame.repr w i)) ∈ M := by
    intro w hw
    obtain ⟨n, rfl⟩ := hx w hw
    have : (fun i => φ (V.frame.repr (∑ j, n j • x j) i)) = ∑ j, n j • fun i => φ (V.frame.repr (x j) i) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    rw [this]
    exact sum_mem fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _
  have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e' : V.V ≃ₗ⋆[D.host.E] V.V :=
      V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e'.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e' z ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
        Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hzy : V.hT (e' z) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hz)
      have hyz : V.hT y (e' z) = 0 := by
        have hh := V.herm.eq y (e' z)
        simp only [starRingEnd_apply, hzy, star_eq_zero] at hh
        exact hh
      simp [hyz]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e' z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hz' => hz0 (e'.map_eq_zero_iff.mp hz')) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  have hsp : ∀ w : V.V, (fun i => φ (V.frame.repr w i)) ∈
      Submodule.span (Fv D.host.F v) (M : Set (Fin V.rank → Fv D.host.F v)) := by
    intro w
    have hw : w ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [hfull]; trivial
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span (hL w hw)
    | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      exact zero_mem _
    | add a b _ _ ha hb =>
      simp only [map_add (f := _), Finsupp.coe_add, Pi.add_apply]
      exact add_mem ha hb
    | smul c a _ ha =>
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact Submodule.smul_mem _ (φ c) ha
  have : Submodule.IsFullLattice (Fv D.host.F v) M := by
    haveI : Submodule.IsLattice (Fv D.host.F v) M :=
      Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _))
    refine ⟨?_⟩
    rw [eq_top_iff, ← (Pi.basisFun (Fv D.host.F v) (Fin V.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun (Fv D.host.F v) (Fin V.rank) i = fun j => φ (V.frame.repr (V.frame i) j) := by
      funext j
      simp only [Pi.basisFun_apply, Module.Basis.repr_self, Pi.single_apply, Finsupp.single_apply, eq_comm (a := i)]
      split_ifs <;> simp
    rw [this]
    exact hsp _
  obtain ⟨B, hB⟩ := exists_matrix_of_isLattice M
  have hε : finPart D e ∈ intAE D := by simpa using (h3 1).2 (by rw [RingHom.map_one]; exact one_mem _)
  have hπε : π (finPart D e) = 1 := by
    have := h1 (π 1)
    rwa [h2, mul_one, RingHom.map_one] at this
  have hto : ∀ z ∈ LamHat V, (fun i => π (z i)) ∈ M := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hy
      have ha' : π (a ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ Formalism.UG.Ov D.host.F v :=
        (h3 _).1 (mul_mem_intAE D hε (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩))
      have hu' := M.smul_mem ⟨_, ha'⟩ (hL _ hu)
      convert hu' using 1
      funext i
      rw [V.frame.repr_sum_self]
      show _ = π _ * π _
      rw [← RingHom.map_mul]
      congr 1
      show _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] u i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | zero =>
      simp only [Pi.zero_apply, RingHom.map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, RingHom.map_add (f := _)]
      exact add_mem hy hz
    | neg y _ hy =>
      simp only [Pi.neg_apply, RingHom.map_neg]
      exact neg_mem hy
  refine ⟨B, fun y => ?_⟩
  have hR : ∀ t : Fv D.host.F v, t ∈ (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).range ↔
      t ∈ Formalism.UG.Ov D.host.F v := fun t => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨t, h⟩, rfl⟩⟩
  have hB' := hB fun j => π (y j)
  simp only [hR] at hB'
  rw [← hB']
  constructor
  · intro h
    have := hto _ h
    simpa only [RingHom.map_mul, hπε, one_mul] using this
  · intro h
    have hg : ∀ j, (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] V.frame.repr (x j) i) ∈ LamHat V :=
      fun j => AddSubgroup.subset_closure
        ⟨1, fun w => by rw [map_one]; exact one_mem _, fun i => V.frame.repr (x j) i, by
          show ∑ i, V.frame.repr (x j) i • V.frame i ∈ V.L0
          rw [V.frame.sum_repr]
          exact hxL j, rfl⟩
    have := section_mem (v.adicCompletionIntegers D.host.F) π (fun a => finPart D (s a)) (finPart D e)
      (intAE D) (LamHat V) h1 h2 (fun x hx => (h3 x).2 hx) h4 _ hg (fun j => π (y j)) h
    simpa only [h2] using this

end GlobalTheory.SplitLatBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoordField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCoord

section General

variable {R T : Type} [CommRing R] [CommRing T] [Algebra R T]

theorem trace_mul_idem (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0) (x y : T) :
    Algebra.trace R T (e * (x * y)) = Algebra.trace R T (e * x) * Algebra.trace R T (e * y) := by
  apply hi
  have hc : c e * c e = c e := by rw [← map_mul, h1]
  rw [RingHom.map_mul, ht, ht, ht]
  simp only [map_mul]
  linear_combination (-(x * y)) * h1 - (c x * c y) * hc - (x * c y + c x * y) * h2

theorem idem_mul_trace (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) (x : T) :
    e * algebraMap R T (α * Algebra.trace R T (e * x)) = e * x := by
  rw [map_mul, ht, ← h3, map_mul]
  linear_combination ((e + 1) * x) * h1 + (e * x + e * c x + c e * c x) * h2

theorem trace_idem_mul (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T}
    {α : R} (h3 : e + c e = algebraMap R T α) (b : R) :
    Algebra.trace R T (e * algebraMap R T b) = b * α := by
  have : Algebra.trace R T e = α := hi (by rw [ht, h3])
  rw [mul_comm, ← Algebra.smul_def, map_smul, this, smul_eq_mul]

theorem exists_hom (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) {S K : Type} [CommRing S] [CommRing K] [Algebra S R] [Algebra S K]
    (φ : R →ₐ[S] K) (hα : φ α = 1) :
    ∃ π : T →+* K, ∀ x, π x = φ (Algebra.trace R T (e * x)) :=
  ⟨{ toFun := fun x => φ (Algebra.trace R T (e * x))
     map_one' := by
       have := trace_idem_mul hi c ht h3 1
       rw [RingHom.map_one, one_mul] at this
       rw [this, hα]
     map_mul' := fun x y => by rw [trace_mul_idem hi c ht h1 h2, map_mul]
     map_zero' := by rw [mul_zero, map_zero, map_zero]
     map_add' := fun x y => by rw [mul_add, map_add (f := _), map_add (f := _)] }, fun _ => rfl⟩

end General

section Single

variable {F : Type} [Field F] [NumberField F]

theorem evalV_single (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : evalV F v (singleV F v a) = a := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v a

theorem evalV_single_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (a : Fv F v) : evalV F w (singleV F v a) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) a h

theorem single_evalV {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → evalV F w α = 0) (b : Af F) : singleV F v (evalV F v b) = α * b := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (singleV F v (evalV F v b)) = evalV F w (α * b)
  by_cases hw : w = v
  · subst hw
    rw [evalV_single, map_mul, h1, one_mul]
  · rw [evalV_single_ne hw, map_mul, h2 w hw, zero_mul]

theorem single_mem {v : HeightOneSpectrum (𝓞 F)} {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    singleV F v a ∈ intAf F := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [evalV_single]; exact ha
  · rw [evalV_single_ne hw]; exact zero_mem _

end Single

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def finT : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom


variable (F E) in
def intT : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

theorem alg_inj (R : Type) [CommRing R] [Algebra F R] : Function.Injective (algebraMap R (R ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

theorem finT_sig (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : finT F E (sigR (AF F) σ z) = sigR (Af F) σ (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem finT_alg (a : AF F) : finT F E (algebraMap (AF F) _ a) = algebraMap (Af F) _ (sndA F a) := rfl

theorem mul_mem_intT {x y : Af F ⊗[F] E} (hx : x ∈ intT F E) (hy : y ∈ intT F E) : x * y ∈ intT F E := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intT F E) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem trace_mem (v : HeightOneSpectrum (𝓞 F)) {x : Af F ⊗[F] E} (hx : x ∈ intT F E) :
    evalV F v (Algebra.trace (Af F) (Af F ⊗[F] E) x) ∈ v.adicCompletionIntegers F := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    have h1 : a ⊗ₜ[F] (y : E) = a • ((1 : Af F) ⊗ₜ[F] (y : E)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace (Af F) (Af F ⊗[F] E) (a ⊗ₜ[F] (y : E)) = a * algebraMap F _ (Algebra.trace F E y) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    rw [h3, map_mul, AlgHom.commutes]
    refine mul_mem (ha v) ?_
    have hi : IsIntegral ℤ (Algebra.trace F E y) := Algebra.isIntegral_trace y.isIntegral_coe
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨_, hi⟩ : 𝓞 F)
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg, map_neg]; exact neg_mem h

theorem exists_coord_field (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (hI : ∀ z : Af F ⊗[F] E, z * z = z → z ∈ intT F E)
    (e : AF F ⊗[F] E) (h1 : e * e = e) (h2 : e * sigR (AF F) σ e = 0) (v : HeightOneSpectrum (𝓞 F)) (α : Af F)
    (hv : evalV F v α = 1) (hv' : ∀ w, w ≠ v → evalV F w α = 0)
    (h3 : e + sigR (AF F) σ e = algebraMap (AF F) _ (pairA F 0 α)) :
    ∃ (π : Af F ⊗[F] E →+* Fv F v) (s : Fv F v → AF F ⊗[F] E), (∀ x, s (π (finT F E x)) = e * x) ∧
      (∀ a, π (finT F E (s a)) = a) ∧ (∀ x, finT F E (s (π x)) = finT F E e * x) ∧
      (∀ x, finT F E e * x ∈ intT F E ↔ π x ∈ Formalism.UG.Ov F v) ∧
      ∀ x : F, π (finT F E (inclR (F := F) (AF F) (algebraMap F E x))) = algebraMap F (Fv F v) x := by
  have tA := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (AF F)
  have tf := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (Af F)
  have tt : ∀ z, Algebra.trace (Af F) (Af F ⊗[F] E) (finT F E z) = sndA F (Algebra.trace (AF F) _ z) := fun z => by
    apply alg_inj (F := F) (E := E)
    rw [tf, ← finT_alg, tA, RingHom.map_add (f := _), finT_sig]
  have g1 : finT F E e * finT F E e = finT F E e := by rw [← RingHom.map_mul, h1]
  have g2 : finT F E e * sigR (Af F) σ (finT F E e) = 0 := by
    rw [← finT_sig, ← RingHom.map_mul, h2, RingHom.map_zero]
  have g3 : finT F E e + sigR (Af F) σ (finT F E e) = algebraMap (Af F) _ α := by
    rw [← finT_sig, ← RingHom.map_add (f := _), h3]; rfl
  have k := fun b => trace_idem_mul (alg_inj _) _ tf g3 b
  obtain ⟨π, hπ⟩ := exists_hom (alg_inj _) _ tf g1 g2 g3 (evalV F v) hv
  have p3 : ∀ x, finT F E e * algebraMap (Af F) _ (singleV F v (π x)) = finT F E e * x := fun x => by
    rw [hπ, single_evalV hv hv']
    exact idem_mul_trace _ tf g1 g2 g3 x
  refine ⟨π, fun a => e * algebraMap (AF F) _ (pairA F 0 (singleV F v a)), fun x => ?_,
    fun a => ?_, fun x => ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · refine Eq.trans ?_ (idem_mul_trace _ tA h1 h2 h3 x)
    beta_reduce
    rw [hπ, single_evalV hv hv', ← RingHom.map_mul, tt]
    congr 2
    exact Prod.ext (zero_mul _).symm rfl
  · rw [hπ, RingHom.map_mul, ← mul_assoc, g1, finT_alg, k, map_mul, hv, mul_one]
    exact evalV_single v a
  · rw [RingHom.map_mul, finT_alg]
    exact p3 x
  · rw [hπ]; exact trace_mem v h
  · rw [← p3]
    exact mul_mem_intT (hI _ g1) (AddSubgroup.subset_closure ⟨_, single_mem h, 1, rfl⟩)
  · have : finT F E (inclR (F := F) (AF F) (algebraMap F E x)) = algebraMap (Af F) _ (algebraMap F (Af F) x) := by
      change (sndA F 1) ⊗ₜ[F] (algebraMap F E x) = (algebraMap F (Af F) x) ⊗ₜ 1
      rw [map_one, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [this, hπ, k, map_mul, hv, mul_one, AlgHom.commutes]

end Field

theorem exists_coord : ∀ {D : D7} (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v) (s : Fv D.host.F v → Formalism.L2.Theta.AE D), (∀ x, s (π (finPart D x)) = e * x) ∧ (∀ a, π (finPart D (s a)) = a) ∧ (∀ x, finPart D (s (π x)) = finPart D e * x) ∧ (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) ∧ ∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) = algebraMap D.host.F (Fv D.host.F v) x := by
  rintro D e ⟨h1, h2, v, ε, ⟨α, rfl, hv, hv'⟩, h3⟩
  exact ⟨v, exists_coord_field D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he)
    (GlobalTheory.AdIdem.idempotent_mem_intAE D) e h1 h2 v α hv hv' h3⟩

end GlobalTheory.SplitCoord

end
end

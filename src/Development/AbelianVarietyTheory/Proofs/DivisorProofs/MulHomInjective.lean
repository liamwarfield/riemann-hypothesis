module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

def crd (y : B.A) : Fin a → w.adicCompletion E := fun i => e (b.repr y i)

def ofCrd (v : Fin a → w.adicCompletion E) : B.A := b.equivFun.symm fun i => e.symm (v i)

def mulHom : B.A →+* Matrix (Fin a) (Fin a) (w.adicCompletion E) :=
  e.toRingHom.mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom

def mulGL : B.Aˣ →* GLw a w := Units.map (mulHom e b).toMonoidHom

theorem mulHom_eq (t : B.A) : mulHom e b t = GlobalTheory.TwLat.mulMat e b t := by
  ext i j
  simp [mulHom, GlobalTheory.TwLat.mulMat, Algebra.leftMulMatrix_apply]

theorem latOf_eq (q : GLw a w) :
    GlobalTheory.TwLat.lat e b q = Submodule.span K.O (Set.range fun j => ofCrd e b fun i => q.val i j) := by
  simp [GlobalTheory.TwLat.lat, ofCrd, Module.Basis.equivFun_symm_apply]

theorem crd_ofCrd (v : Fin a → w.adicCompletion E) : crd e b (ofCrd e b v) = v := by
  funext i
  simp only [crd, ofCrd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem ofCrd_crd (y : B.A) : ofCrd e b (crd e b y) = y := by
  simp [crd, ofCrd]

theorem mulHom_apply (t : B.A) (i j : Fin a) : mulHom e b t i j = e (b.repr (t * b j) i) := by
  simp [mulHom, Algebra.leftMulMatrix_eq_repr_mul]

theorem mulGL_val (t : B.Aˣ) : (mulGL e b t).val = GlobalTheory.TwLat.mulMat e b t := mulHom_eq e b t

theorem mulHom_injective : Function.Injective (mulHom e b) := by
  intro x y h
  apply Algebra.leftMulMatrix_injective b
  ext i j
  have := congrFun (congrFun h i) j
  exact e.injective (by simpa [mulHom] using this)

theorem mulGL_injective : Function.Injective (mulGL e b) := by
  intro x y h
  exact Units.ext (mulHom_injective e b (congrArg Units.val h))

theorem crd_injective : Function.Injective (crd e b) := fun x y h => by
  rw [← ofCrd_crd e b x, h, ofCrd_crd]

theorem crd_add (y z : B.A) : crd e b (y + z) = crd e b y + crd e b z := by
  funext i; simp [crd]

theorem crd_smul (c : K.E) (y : B.A) : crd e b (c • y) = e c • crd e b y := by
  funext i; simp [crd]

theorem crd_mul (t y : B.A) : crd e b (t * y) = mulHom e b t *ᵥ crd e b y := by
  funext i
  simp only [crd, mulHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← Algebra.leftMulMatrix_mulVec_repr]
  simp [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, crd]

theorem ofCrd_mulVec (t : B.A) (v : Fin a → w.adicCompletion E) :
    ofCrd e b (mulHom e b t *ᵥ v) = t * ofCrd e b v := by
  apply crd_injective e b
  rw [crd_mul, crd_ofCrd, crd_ofCrd]

theorem col_mul (M N : Matrix (Fin a) (Fin a) (w.adicCompletion E)) (j : Fin a) :
    (fun i => (M * N) i j) = M *ᵥ fun i => N i j := by
  funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem crd_sum (s : Finset (Fin a)) (f : Fin a → B.A) : crd e b (∑ j ∈ s, f j) = ∑ j ∈ s, crd e b (f j) := by
  induction s using Finset.induction_on with
  | empty => funext i; simp [crd]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, crd_add, ih]

theorem latOf_mul (t : B.Aˣ) (q : GLw a w) :
    GlobalTheory.TwLat.lat e b (mulGL e b t * q) = GlobalTheory.UnitLemma.mulLat K.O (t : B.A) (GlobalTheory.TwLat.lat e b q) := by
  rw [latOf_eq, latOf_eq]
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span K.O) (congrArg Set.range (funext fun j => ?_))
  simp only [Function.comp_apply, LinearMap.mulLeft_apply, Units.val_mul]
  change (ofCrd e b fun i => (mulHom e b (t : B.A) * q.val) i j) = _
  rw [col_mul (mulHom e b (t : B.A)) q.val j, ofCrd_mulVec]

theorem latOf_isLat (q : GLw a w) : GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b q) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [latOf_eq, Submodule.span_span_of_tower, eq_top_iff]
  intro z _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b z) j), ?_⟩
  apply crd_injective e b
  rw [crd_sum]
  have h1 : crd e b z = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  conv_rhs => rw [h1]
  funext i
  simp [crd_smul, crd_ofCrd, Finset.sum_apply, Matrix.mulVec, dotProduct, mul_comm]

end GlobalTheory.TwOrbLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
noncomputable section

open Matrix
open scoped Quaternion

namespace GlobalTheory.PlaneSU

open Formalism.UG

section Emb

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def emb (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) (X : Matrix (Fin 2) (Fin 2) R) : Matrix n n R :=
  1 + A * (X - 1) * B

theorem emb_one (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) : emb A B 1 = 1 := by
  simp [emb]

theorem emb_mul {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X Y : Matrix (Fin 2) (Fin 2) R) : emb A B (X * Y) = emb A B X * emb A B Y := by
  have e1 : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  have e2 : A * (X - 1) * B * (A * (Y - 1) * B) = A * ((X - 1) * (Y - 1)) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
  unfold emb
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, e2, e1,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem det_emb {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).det = X.det := by
  unfold emb
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hBA, Matrix.mul_one, add_sub_cancel]

theorem emb_map {S : Type} [CommRing S] (f : R →+* S) (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).map f = emb (A.map f) (B.map f) (X.map f) := by
  simp [emb, Matrix.map_mul, Matrix.map_add (f := _), Matrix.map_sub, Matrix.map_one]

theorem cT_add (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P + Q) = cT c P + cT c Q := by
  ext i j; simp [cT]

theorem cT_sub (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P - Q) = cT c P - cT c Q := by
  ext i j; simp [cT]

theorem emb_unitary (c : R →+* R) {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} {J : Matrix n n R}
    {H X : Matrix (Fin 2) (Fin 2) R} (hBA : B * A = 1) (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H)
    (hX : cT c X * H * X = H) : cT c (emb A B X) * J * emb A B X = J := by
  have hc : cT c (emb A B X) = 1 + cT c B * (cT c X - 1) * cT c A := by
    unfold emb
    rw [cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]
  set P := X - 1 with hP
  set P' := cT c X - 1 with hP'
  have key : H * P + P' * H + P' * H * P = 0 := by
    rw [hP, hP']
    calc H * (X - 1) + (cT c X - 1) * H + (cT c X - 1) * H * (X - 1) = cT c X * H * X - H := by noncomm_ring
      _ = 0 := by rw [hX, sub_self]
  have h1' : ∀ Z : Matrix n n R, cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h1'' : ∀ {k : Type} [Fintype k] (Z : Matrix n k R), cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h2' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), J * (A * Z) = cT c B * (H * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have hBA' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), B * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [hc]
  unfold emb
  rw [← hP]
  have e : (1 + cT c B * P' * cT c A) * J * (1 + A * P * B) =
      J + cT c B * ((H * P + P' * H + P' * H * P) * B) := by
    have hAB' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), cT c A * (cT c B * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, ← cT_mul, hBA, cT_one, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, h1, h1'', h2', hBA', hAB']
    abel
  rw [e, key, Matrix.zero_mul, Matrix.mul_zero, add_zero]

end Emb

section Quat

variable {S T : Type} [CommRing S] [CommRing T]

def qm (ι : S →+* T) (θ : T) {a b : S} (x : ℍ[S, a, b]) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * θ, ι b * (ι x.imJ + ι x.imK * θ); ι x.imJ - ι x.imK * θ, ι x.re - ι x.imI * θ]

variable (ι : S →+* T) (θ : T) {a b : S}

theorem qm_one : qm ι θ (1 : ℍ[S, a, b]) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm]

theorem qm_sub (x y : ℍ[S, a, b]) : qm ι θ (x - y) = qm ι θ x - qm ι θ y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_smul (r : S) (x : ℍ[S, a, b]) : qm ι θ (r • x) = ι r • qm ι θ x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_mul (hθ : θ * θ = ι a) (x y : ℍ[S, a, b]) : qm ι θ (x * y) = qm ι θ x * qm ι θ y := by
  ext i j
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  fin_cases i <;> fin_cases j <;> simp [qm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp only [hθ2] <;> ring

theorem det_qm (hθ : θ * θ = ι a) (x : ℍ[S, a, b]) : (qm ι θ x).det = ι (GlobalTheory.QSA.nrm x) := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  simp [qm, Matrix.det_fin_two, GlobalTheory.QSA.nrm]
  ring_nf
  simp only [hθ2]
  ring

theorem qm_unitary (c : T →+* T) (hc : ∀ s, c (ι s) = ι s) (hcθ : c θ = -θ) (hθ : θ * θ = ι a)
    {h₁ h₂ : T} (hb : ι b * h₁ = -h₂) {x : ℍ[S, a, b]} (hx : GlobalTheory.QSA.nrm x = 1) :
    cT c (qm ι θ x) * Matrix.diagonal ![h₁, h₂] * qm ι θ x = Matrix.diagonal ![h₁, h₂] := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  have hn : ι x.re ^ 2 - ι a * ι x.imI ^ 2 - ι b * ι x.imJ ^ 2 + ι a * ι b * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simp only [GlobalTheory.QSA.nrm, map_sub, map_add (f := _), map_mul, map_pow, map_one] at this
    exact this
  have hh2 : h₂ = -(ι b * h₁) := by rw [hb, neg_neg]
  subst hh2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination h₁ * hn
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination (-(ι b * h₁)) * hn

end Quat

section Plane

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

def planeA (e₁ e₂ : Fin M → E) : Matrix (Fin M) (Fin 2) E := Matrix.of fun i k => ![e₁, e₂] k i

def planeH (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin 2) E :=
  Matrix.diagonal ![hE σ J e₁ e₁, hE σ J e₂ e₂]

def planeB (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin M) E :=
  Matrix.diagonal ![(hE σ J e₁ e₁)⁻¹, (hE σ J e₂ e₂)⁻¹] * cT (σ : E →+* E) (planeA e₁ e₂) * J

end Plane

end GlobalTheory.PlaneSU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
set_option autoImplicit false

noncomputable section

open NumberField Module

namespace GlobalTheory

theorem exists_isShortGen_of_short_span : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) →
    (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L →
    Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) →
    ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧
      abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧
      n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  intro K V _ _ _ _ _ _ _ N L s A hLfg h0 hsm hadd hsL hsp hA
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  haveI : IsScalarTower ℚ K V := ⟨fun q a x => by
    show (q • a) • x = (algebraMap ℚ K q) • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hspL : Submodule.span K (L : Set V) = ⊤ := eq_top_iff.2 (hsp ▸ Submodule.span_mono hsL)
  have hrk : Formalism.HN.rkK L = Module.finrank K V := by
    rw [Formalism.HN.rkK, hspL, finrank_top]

  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent K s
  let vb : Basis t K V := Basis.mk hti (by rw [Subtype.range_coe, htsp, hsp])
  haveI : Finite t := Module.Finite.finite_basis vb
  haveI : Fintype t := Fintype.ofFinite t
  have hm : Fintype.card t = Formalism.HN.rkK L := by rw [hrk, finrank_eq_card_basis vb]

  obtain ⟨ω, hωi, hωb⟩ := exists_short_independent_integers K
  haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let ob : Basis (Fin (finrank ℚ K)) ℚ K := basisOfLinearIndependentOfCardEqFinrank hωi (by simp)
  have hob : ∀ k, ob k = (ω k : K) := fun k => by
    simp [ob, coe_basisOfLinearIndependentOfCardEqFinrank]
  let E : Basis (Fin (finrank ℚ K) × t) ℚ V := ob.smulTower vb
  have hE : ∀ p, E p = ω p.1 • (p.2 : V) := fun p => by
    rw [Basis.smulTower_apply, hob, Basis.mk_apply]
    exact algebraMap_smul K (ω p.1) (p.2 : V)

  have hN0 : ∀ σ, N σ 0 = 0 := fun σ => by simpa using hsm σ 0 0
  have hsum : ∀ σ {ι : Type} (S : Finset ι) (f : ι → V), N σ (∑ i ∈ S, f i) ≤ ∑ i ∈ S, N σ (f i) := by
    intro σ ι S f
    induction S using Finset.induction_on with
    | empty => simp [hN0]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hadd σ _ _).trans (add_le_add le_rfl ih)
  have hq : ∀ σ (q : ℚ) x, N σ (q • x) = |(q : ℝ)| * N σ x := fun σ q x => by
    have := hsm σ (algebraMap ℚ K q) x
    rw [eq_ratCast, map_ratCast, Complex.norm_ratCast] at this
    exact this

  set C : ℝ := (finrank ℚ K : ℝ) ^ 3 * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A with hC
  have hEle : ∀ σ p, N σ (E p) ≤ C := fun σ p => by
    rw [hE p, ← algebraMap_smul K (ω p.1) (p.2 : V), hsm]
    have h1 := hA _ (hts p.2.2) σ
    exact mul_le_mul (hωb σ p.1) h1 (h0 _ _) ((norm_nonneg _).trans (hωb σ p.1))

  let red : V → V := fun x => ∑ p, Int.fract (E.repr x p) • E p
  have hred_sub : ∀ x, x - red x ∈ Submodule.span ℤ (Set.range E) := fun x => by
    have hx : x - red x = ∑ p, (⌊E.repr x p⌋ : ℤ) • E p := by
      rw [sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
      conv_lhs => rw [← E.sum_repr x]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.floor_add_fract]
    rw [hx]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  have hred_le : ∀ σ x, N σ (red x) ≤ ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C := fun σ x => by
    refine (hsum σ _ _).trans ?_
    have hle : ∀ p ∈ (Finset.univ : Finset (Fin (finrank ℚ K) × t)),
        N σ (Int.fract (E.repr x p) • E p) ≤ C := fun p _ => by
      rw [hq]
      have h1 : |((Int.fract (E.repr x p) : ℚ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (Rat.cast_nonneg.2 (Int.fract_nonneg _))]
        exact_mod_cast (Int.fract_lt_one _).le
      exact (mul_le_of_le_one_left (h0 _ _) h1).trans (hEle σ p)
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hm]
    push_cast; ring

  haveI : NoZeroSMulDivisors ℤ V := ⟨fun {c x} h => by
    rw [← Int.cast_smul_eq_zsmul K] at h
    exact (smul_eq_zero.1 h).imp_left Int.cast_eq_zero.1⟩
  let Lz := L.restrictScalars ℤ
  haveI : Module.Finite ℤ Lz := Module.Finite.iff_fg.2 hLfg.restrictScalars
  haveI : Module.Free ℤ Lz := Module.free_of_finite_type_torsion_free'
  let ZB := Module.Free.chooseBasis ℤ Lz
  let bZ : Module.Free.ChooseBasisIndex ℤ Lz → V := fun j => (ZB j : V)
  have hZq : LinearIndependent ℚ bZ := (LinearIndependent.iff_fractionRing ℤ ℚ).1
    (ZB.linearIndependent.map' Lz.subtype (Submodule.ker_subtype _))
  haveI : Module.Finite ℚ V := Module.Finite.of_basis E
  have hcardZ : Fintype.card (Module.Free.ChooseBasisIndex ℤ Lz) ≤ Fintype.card (Fin (finrank ℚ K) × t) := by
    rw [← finrank_eq_card_basis E]; exact hZq.fintype_card_le_finrank
  have hLz : Lz = Submodule.span ℤ (Set.range bZ) := by
    rw [show Set.range bZ = Lz.subtype '' Set.range ZB from Set.range_comp _ _, ← Submodule.map_span,
      ZB.span_eq, Submodule.map_top, Submodule.range_subtype]

  let F : (Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz → V := Sum.elim E (fun j => red (bZ j))
  let e := Fintype.equivFin ((Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz)
  have hEL : ∀ p, E p ∈ L := fun p => by rw [hE]; exact L.smul_mem _ (hsL (hts p.2.2))
  have hspanE : Submodule.span ℤ (Set.range E) ≤ Lz :=
    Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hEL p)
  have hrng : Set.range (F ∘ e.symm) = Set.range F := e.symm.surjective.range_comp F
  have hbig : ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C ≤ max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _); rw [hC]; ring
  refine ⟨Fintype.card _, F ∘ e.symm, max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A),
    ⟨fun x => ?_, fun i σ => ?_, le_max_left _ _⟩, le_rfl, ?_⟩
  · rw [hrng]
    constructor
    · intro hx
      have hx' : x ∈ Lz := hx
      rw [hLz] at hx'
      refine (Submodule.span_le.2 ?_) hx'
      rintro _ ⟨j, rfl⟩
      have h1 : red (bZ j) ∈ Submodule.span ℤ (Set.range F) := Submodule.subset_span ⟨Sum.inr j, rfl⟩
      have h2 : bZ j - red (bZ j) ∈ Submodule.span ℤ (Set.range F) :=
        Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨Sum.inl p, rfl⟩) (hred_sub _)
      simpa using add_mem h2 h1
    · intro hx
      have : x ∈ Lz := (Submodule.span_le (p := Lz)).2 (by
        rintro _ ⟨q | j, rfl⟩
        · exact hEL q
        · have h1 : bZ j ∈ Lz := (ZB j).2
          have h2 := hspanE (hred_sub (bZ j))
          have e1 : red (bZ j) = bZ j - (bZ j - red (bZ j)) := by abel
          show red (bZ j) ∈ Lz
          rw [e1]; exact sub_mem h1 h2) hx
      exact this
  · refine le_trans ?_ hbig
    rw [Function.comp_apply]
    generalize e.symm i = q
    rcases q with q | j
    · have hC0 : 0 ≤ C := (h0 σ _).trans (hEle σ q)
      have hpos : 0 < Fintype.card t := Fintype.card_pos_iff.2 ⟨q.2⟩
      have h1 : (1 : ℝ) ≤ (finrank ℚ K : ℝ) * Formalism.HN.rkK L := by
        rw [← hm]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Module.finrank_pos.ne' hpos.ne')
      exact (hEle σ q).trans (le_mul_of_one_le_left hC0 h1)
    · exact hred_le σ _
  · rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hm]
    rw [Fintype.card_prod, Fintype.card_fin, hm] at hcardZ
    linarith

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamilyStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_generators_of_short_spanning_family : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) → (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L → Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) → ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧ abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧ n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  first | exact @GlobalTheory.exists_isShortGen_of_short_span | exact GlobalTheory.exists_isShortGen_of_short_span | (intros; apply GlobalTheory.exists_isShortGen_of_short_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocGlue

theorem entry_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {v : HeightOneSpectrum (𝓞 E)}
    {g : GL (Fin n) (v.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL v (n := n)) (i j : Fin n) :
    g.val i j ∈ v.adicCompletionIntegers E ∧ (g⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E := by
  obtain ⟨g0, rfl⟩ := hg
  refine ⟨(g0.val i j).2, ?_⟩
  rw [← map_inv]
  exact ((g0⁻¹).val i j).2

theorem glue : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)), (∀ᶠ v in cofinite, g v ∈ GlobalTheory.LFun.KGL v (n := n)) → ∃ k : GL (Fin n) (Af E), ∀ v, GeneralLinearGroup.map (pLoc E v) k = g v := by
  intro E _ _ n g hg
  have hent : ∀ i j, ∀ᶠ v in cofinite, (g v).val i j ∈ v.adicCompletionIntegers E ∧
      ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E :=
    fun i j => hg.mono fun v hv => entry_mem hv i j
  let M : Matrix (Fin n) (Fin n) (Af E) := fun i j => ⟨fun v => (g v).val i j, (hent i j).mono fun v h => h.1⟩
  let N : Matrix (Fin n) (Fin n) (Af E) := fun i j =>
    ⟨fun v => ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j, (hent i j).mono fun v h => h.2⟩
  have hM : ∀ v, RingHom.mapMatrix (pLoc E v) M = (g v).val := fun v => rfl
  have hN : ∀ v, RingHom.mapMatrix (pLoc E v) N = ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val := fun v => rfl
  have hMN : M * N = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.mul_inv]
  have hNM : N * M = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.inv_mul]
  exact ⟨⟨M, N, hMN, hNM⟩, fun v => Units.ext (hM v)⟩

theorem intst : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (v u : HeightOneSpectrum (𝓞 E)) (f : v.adicCompletion E →+* u.adicCompletion E), (∀ x, Valued.v (f x) = Valued.v x) → ∀ g ∈ GlobalTheory.LFun.KGL v (n := n), invT n _ (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL u (n := n) := by
  intro E _ _ n v u f hf g hg
  obtain ⟨g0, rfl⟩ := hg
  let r : Formalism.UG.Ov E v →+* Formalism.UG.Ov E u := f.restrict _ _ fun x hx => by
    change _ ∈ u.adicCompletionIntegers E
    change x ∈ v.adicCompletionIntegers E at hx
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
    rw [hf]
    exact hx
  refine ⟨invT n _ (GeneralLinearGroup.map r g0), ?_⟩
  apply Units.ext
  ext i j
  rfl

theorem ns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), ¬ IsSplitAt u → GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) u)) = GeneralLinearGroup.map (cj u) (Y u) := by
  intro E _ _ _ n Y u hu
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      GeneralLinearGroup.map f (Y v) = GeneralLinearGroup.map (cj u) (Y u) := by
    rintro v rfl f hf hext
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
    have hcj : cj v = hex.choose := by unfold cj; rw [dite_eq_left hex]
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = hex.choose :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
        (funext fun k => (hext k).trans (hex.choose_spec.2 k).symm)
    rw [hcj]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have hcu : conjSrc (GlobalTheory.SplitPts.conjE E) u = u := by
    by_contra h
    exact hu ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
  exact key _ hcu _ (conjLoc_spec _ u).1 (conjLoc_spec _ u).2.1

theorem twice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))) = Y u := by
  intro E _ _ _ n Y u
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → GeneralLinearGroup.map f (Y v) = Y u := by
    rintro v rfl f hf hext
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = id :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext fun k => hext k)
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have h := key _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm u)
    ((conjLoc (GlobalTheory.SplitPts.conjE E) u).comp (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))
    ((conjLoc_spec _ u).1.comp (conjLoc_spec _ _).1) fun k => by
      rw [RingHom.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
      exact congrArg _ (IsCMField.complexConj_apply_apply E k)
  rw [← h]
  rfl

end GlobalTheory.BCT.LocGlue

theorem GlobalTheory.BCT.exists_finU_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU (E := E) (n := n), ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  intro E _ _ _ _ n S hS y hy
  set c := GlobalTheory.SplitPts.conjE E with hc
  have hnotS : ∀ v, v ∉ S → conjSrc c v ∈ S := by
    intro v hv
    obtain ⟨s, ⟨hsS, hsv⟩, -⟩ := hS v
    have hne : v ≠ s := fun e => hv (e ▸ hsS)
    have hsp : IsSplitAt s := ⟨v, hne, hsv.symm⟩
    obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
    rcases hover v hsv.symm with h | h
    · exact absurd h hne
    · rw [h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]; exact hsS
  have hSsplit : ∀ v ∈ S, IsSplitAt v → conjSrc c v ∉ S := by
    intro v hv hsp h
    obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hsp
    exact hne ((hS v).unique ⟨h, hund⟩ ⟨hv, rfl⟩)
  let z : ∀ v : Pl E, GLw n v := fun v => if v ∈ S then (y v).1 else
    invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1)
  have hz_in : ∀ v ∈ S, z v = (y v).1 := fun v hv => if_pos hv
  have hz_out : ∀ v, v ∉ S → z v = invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1) :=
    fun v hv => if_neg hv
  have hint : ∀ᶠ v in cofinite, z v ∈ GlobalTheory.LFun.KGL v (n := n) := by
    have h1 : ∀ᶠ v in cofinite, (y v).1 ∈ GlobalTheory.LFun.KGL v (n := n) := hy.mono fun v hv => Subgroup.mem_subgroupOf.1 hv
    have h2 := (conjSrc_injective c).tendsto_cofinite.eventually h1
    filter_upwards [h1, h2] with v a1 a2
    by_cases hv : v ∈ S
    · rw [hz_in v hv]; exact a1
    · rw [hz_out v hv]; exact GlobalTheory.BCT.LocGlue.intst E n _ v (conjLoc c v) (conjLoc_spec c v).2.2 _ a2
  obtain ⟨k, hk⟩ := GlobalTheory.BCT.LocGlue.glue E n z hint
  have hk' : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc c u)) k).val.map (conjLoc c u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1 := by
    intro u
    rw [hk, hk]
    show ((GeneralLinearGroup.map (conjLoc c u) (z (conjSrc c u))).val)ᵀ * (z u).val = 1
    by_cases hu : u ∈ S
    · by_cases hsp : IsSplitAt u
      · rw [hz_out _ (hSsplit u hu hsp), hz_in u hu, GlobalTheory.SplitPts.invT_map,
          GlobalTheory.BCT.LocGlue.twice E n (fun v => (y v).1) u]
        change ((((y u).1)⁻¹ : GLw n u).val)ᵀᵀ * (y u).1.val = 1
        rw [Matrix.transpose_transpose, Units.inv_mul]
      · have hcu : conjSrc c u = u := by
          by_contra h
          exact hsp ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
            (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
            (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
        rw [hz_in _ (by rw [hcu]; exact hu), hz_in u hu, GlobalTheory.BCT.LocGlue.ns E n (fun v => (y v).1) u hsp]
        have key : ∀ g : GLw n u, g ∈ UL n u → g ∈ UJ (cj u) 1 := by
          intro g hg
          unfold UL at hg
          rwa [if_neg hsp] at hg
        have hUL : (y u).1 ∈ UJ (cj u) 1 := key _ (y u).2
        have h3 : cT (cj u) (y u).1.val * 1 * (y u).1.val = 1 := hUL
        rw [Matrix.mul_one] at h3
        exact h3
    · rw [hz_out u hu, hz_in _ (hnotS u hu)]
      change ((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1).val)ᵀ *
        (((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1)⁻¹ : GLw n u).val)ᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  let x : finU (E := E) (n := n) := ⟨⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩, MonoidHom.mem_ker.2 (pInf_finGL k)⟩
  refine ⟨x, fun w hw => ?_⟩
  show toSub (UL n w) (cLoc w ⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩) = y w
  rw [GlobalTheory.SplitPts.cLoc_finGL, hk, hz_in w hw]
  unfold toSub
  rw [dite_eq_left (y w).2]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamilyStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU (E := E) (n := n), ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  first | exact @GlobalTheory.BCT.exists_finU_of_loc | exact GlobalTheory.BCT.exists_finU_of_loc | (intros; apply GlobalTheory.BCT.exists_finU_of_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [CommRing K] [Algebra ℚ K]
    (x : K ⊗[ℚ] G.C) : (starT G.star K (starT G.star K x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

end GlobalTheory.FinClsLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.TwistInvol

theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (x : w.adicCompletion E) :
    cj w (cj w x) = x := by
  unfold cj
  split_ifs with h
  · obtain ⟨hc, he⟩ := h.choose_spec
    have hd : DenseRange (algebraMap E (w.adicCompletion E)) := HeightOneSpectrum.denseRange_algebraMap E w
    refine hd.induction_on (p := fun x => h.choose (h.choose x) = x) x
      (isClosed_eq (hc.comp hc) continuous_id) fun y => ?_
    rw [he, he, IsCMField.complexConj_apply_apply]
  · rfl

theorem thL_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    thL n w (thL n w g) = g := by
  intro E _ _ _ n w g
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj w) g

end GlobalTheory.BCT.TwistInvol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapOrb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsModelMap (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) : Prop :=
  (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧ (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧
    ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

theorem isModel_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : IsModel w e B u x γ ↔ ∃ ψ, IsModelMap w e B u x γ ψ := Iff.rfl

def pullLat (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : Submodule K.O B.A where
  carrier := {y | ∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E}
  zero_mem' := by
    intro c i
    simp
  add_mem' := by
    intro a b ha hb c i
    rw [smul_add, map_add (f := _), Matrix.mulVec_add, Pi.add_apply]
    exact add_mem (ha c i) (hb c i)
  smul_mem' := by
    intro c' a ha c i
    rw [smul_smul]
    exact ha (c * c') i

def torusOf (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : B.Aˣ :=
  if h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y then h.choose else 1

theorem torusOf_spec (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) (a : B.Aˣ)
    (ha : ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y) : torusOf w B ψ g = a := by
  have h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y := ⟨a, ha⟩
  unfold torusOf
  rw [dite_eq_left h]
  apply Units.ext
  have h1 := h.choose_spec 1
  have h2 := ha 1
  rw [mul_one] at h1 h2
  exact ψ.injective (h1.trans h2.symm)

end GlobalTheory.KapOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodInt

variable {E : Type} [Field E] [NumberField E]

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) x).compl_mem_cofinite] with w hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [h2]
  exact not_lt.mp hw

theorem mem_GLint {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL {n : ℕ} (g : GL (Fin n) E) : ∀ᶠ w : Pl E in cofinite,
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]; exact fun i j => eventually_int _
  filter_upwards [h g, h g⁻¹] with w a b
  exact mem_GLint _ _ a (by rw [← map_inv]; exact b)

theorem locPt_mem_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  intro E _ _ _ _ n γ _
  filter_upwards [eventually_mem_KGL (E := E) γ.1] with w hw
  unfold locPt toSub
  split_ifs with h
  · exact hw
  · exact one_mem _

end GlobalTheory.BCT.GoodInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompactStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodInt.locPt_mem_KL | exact GlobalTheory.BCT.GoodInt.locPt_mem_KL | (intros; apply GlobalTheory.BCT.GoodInt.locPt_mem_KL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.FODef

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem sqZero : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0 := by
  rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  change TrivSqZeroExt.fst r = 0 at hr
  change TrivSqZeroExt.fst s = 0 at hs
  rw [Submodule.mem_bot]
  ext
  · simp [hr, hs]
  · simp [hr, hs]

theorem constMorV (A₀ : Over (Sp k)) [GrpObj A₀] :
    GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ (sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
      (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
      congr 1) (𝟙 A₀)

variable {k V}

def IsFilLiftV {A₀ : Over (Sp k)} [GrpObj A₀] {A : Over (Sp (TrivSqZeroExt k V))} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) i)
    (x : HdR A₀) (y : primDR A₀ →ₗ[k] V) : Prop :=
  ∃ d ∈ liftFil (divided₂ (sqZero k V)) h, ∀ c : primDR A₀,
    d ((constMorV k V A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c)

end GlobalTheory.FODef

namespace GlobalTheory.HTUniv

theorem coord {k : Type} [Field k] {d : ℕ} (c : (Fin d → k) →ₗ[k] k) (v : Fin d → k) :
    c v = ∑ j, v j * c (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Pi.single j (v j) = v j • (Pi.single j (1 : k) : Fin d → k) := by
    ext i; simp [Pi.single_apply]
  rw [e, map_smul, smul_eq_mul]

theorem comp_pi {k : Type} [Field k] {d : ℕ} {P : Type*} [AddCommGroup P] [Module k P]
    (c : (Fin d → k) →ₗ[k] k) (y : Fin d → (P →ₗ[k] k)) :
    c ∘ₗ LinearMap.pi y = ∑ j, c (Pi.single j 1) • y j := by
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.comp_apply, coord c, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pi_apply, smul_eq_mul, mul_comm]

theorem sum_proj_single {k : Type} [Field k] {d : ℕ} (c₀ : Fin d → k) (j : Fin d) :
    (∑ i, c₀ i • LinearMap.proj (R := k) (φ := fun _ : Fin d => k) i) (Pi.single j 1) = c₀ j := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try exact mul_one _

end GlobalTheory.HTUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance borelSpace_adelicU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

end GlobalTheory.DefDoubling
end
end

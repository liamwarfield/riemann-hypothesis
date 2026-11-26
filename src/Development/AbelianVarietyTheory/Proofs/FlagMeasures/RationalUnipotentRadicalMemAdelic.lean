module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Proof.rational_unipotentRadical_mem_adelic

theorem sub_one_map {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) E) : g.map ι - 1 = (g - 1).map ι := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_mulVec_incl {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    M.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((M *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_span {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E)) (T : Submodule A (Fin n → A))
    (h : ∀ w ∈ S, (fun i => ι ((M *ᵥ w) i)) ∈ T) :
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S), M.map ι *ᵥ y ∈ T := by
  intro y hy
  have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) ≤
      T.comap (M.map ι).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    rw [map_mulVec_incl]
    exact h w hw
  exact this hy

theorem span_univ {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  refine ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j <;> simp [Pi.single_apply, h]

theorem inUnipRad_map (I : AutInst) {A : Type} [CommRing A] (σ : I.E →+* I.E) (s : A →+* A)
    (ι : I.E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) (W : Submodule I.E (Fin I.n → I.E))
    (g : Matrix (Fin I.n) (Fin I.n) I.E) (hg : I.InUnipRad σ I.J W g) :
    I.InUnipRad s (I.J.map ι)
      (Submodule.span A ((fun w : Fin I.n → I.E => fun i => ι (w i)) '' (W : Set _))) (g.map ι) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hp := GlobalTheory.PerpBaseChange.perpSet_baseChange I.E A σ s ι I.n I.J W hι
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [sub_one_map]
    have h0 : ∀ w ∈ (W : Set (Fin I.n → I.E)), (fun i => ι (((g - 1) *ᵥ w) i)) ∈ (⊥ : Submodule A (Fin I.n → A)) := by
      intro w hw
      rw [h1 w hw, Submodule.mem_bot]
      funext i
      exact map_zero ι
    have := map_mulVec_span ι (g - 1) (W : Set (Fin I.n → I.E)) ⊥ h0 x hx
    exact (Submodule.mem_bot A).1 this
  · intro y hy
    replace hy := (Set.ext_iff.1 hp y).1 hy
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) _ _ (fun w hw => ?_) y hy
    exact Submodule.subset_span ⟨_, h2 w hw, rfl⟩
  · intro y
    refine (Set.ext_iff.1 hp _).2 ?_
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) Set.univ _ (fun w _ => ?_) y (by rw [span_univ]; trivial)
    exact Submodule.subset_span ⟨_, h3 w, rfl⟩

theorem unitary_map {E A : Type} [CommRing E] [CommRing A] (σ : E →+* E) (s : A →+* A)
    (ι : E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map ι) * J.map ι * g.map ι = J.map ι := by
  have : Formalism.UG.cT s (g.map ι) = (Formalism.UG.cT σ g).map ι := by
    ext i j
    simp [Formalism.UG.cT, hι]
  rw [this, ← Matrix.map_mul, ← Matrix.map_mul, hg]

theorem rational_mem_adelic (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (hN : I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E)) :
    ∃ a ∈ I.GFset ∩ I.NA W,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
    fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm
  have hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  have hdet : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hdet v)
  let u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit
  have hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    change (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Jm (I.ε v) * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Jm (I.ε v)
    have h := unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp [Formalism.UG.cT]
    rw [hc] at h
    rw [← I.P_spec v]
    calc (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) *
          (u v : Matrix (Fin I.n) (Fin I.n) ℂ)
        = (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ))ᴴ * I.J.map (I.φ v) *
          (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
          rw [hPu]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hF : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    unitary_map _ _ _ hf I.J _ hγ
  refine ⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), ⟨⟨γ, hγ, hu, rfl⟩, fun v => ?_, ?_⟩, hu, rfl⟩
  · change I.InUnipRad _ _ _ (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) * (I.P v)⁻¹)
    rw [hPu, Matrix.mul_assoc, hPP, Matrix.mul_one]
    exact inUnipRad_map I _ _ _ (hφ v) W _ hN
  · exact inUnipRad_map I _ _ _ hf W _ hN

end GlobalTheory.Proof.rational_unipotentRadical_mem_adelic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelicStatement
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotentRadical_mem_adelic : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E) → ∃ a ∈ I.GFset ∩ I.NA W, (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧ I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  first | exact @GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | exact GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | (intros; apply GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTail
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTail
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerTail

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.triangle_succ, Nat.triangle_succ, ih]
    ring

variable {g : ℕ} [Fact g.Prime]

theorem entN_tl (m : ℕ) {n : ℕ} (M : Mt g n) {a b : ℕ} (ha : a < m) (hb : b < m) :
    entN (tl m M) a b = entN M a b := by
  rw [entN, dite_eq_left ⟨ha, hb⟩]; rfl

theorem entN_fin {n : ℕ} (M : Mt g n) (a b : Fin n) : entN M a b = M a b := by
  rw [entN, dite_eq_left ⟨a.2, b.2⟩]

theorem inR_iff (i : ℕ) {n : ℕ} (M : Mt g n) :
    InR i M ↔ ∀ a : ℕ, i ≤ a → a < n → (∀ b, b < a → entN M a b = 0) ∧ entN M a a = 1 := by
  constructor
  · rintro ⟨h1, h2⟩ a hia han
    refine ⟨fun b hb => ?_, ?_⟩
    · by_cases hbi : b < i
      · have := h1 ⟨a, han⟩ ⟨b, by omega⟩ hbi hia
        exact (entN_fin M ⟨a, han⟩ ⟨b, by omega⟩).trans this
      · have := (h2 ⟨a - i, by omega⟩ ⟨b - i, by omega⟩).1 (by simp only [Fin.mk_lt_mk]; omega)
        simp only [br] at this
        rwa [show i + (a - i) = a by omega, show i + (b - i) = b by omega] at this
    · have := (h2 ⟨a - i, by omega⟩ ⟨a - i, by omega⟩).2 rfl
      simp only [br] at this
      rwa [show i + (a - i) = a by omega] at this
  · intro h
    refine ⟨fun a b hb ha => ?_, fun a b => ⟨fun hab => ?_, fun hab => ?_⟩⟩
    · exact (entN_fin M a b).symm.trans ((h a ha a.2).1 b (by omega))
    · have := a.2
      have hab' : (b : ℕ) < a := hab
      exact (h (i + a) (by omega) (by omega)).1 (i + b) (by omega)
    · subst hab
      have := a.2
      exact (h (i + a) (by omega) (by omega)).2

theorem inR_split {i m n : ℕ} (him : i ≤ m) (hmn : m ≤ n) (M : Mt g n) :
    InR i M ↔ InR m M ∧ InR i (tl m M) := by
  simp only [inR_iff]
  constructor
  · intro h
    refine ⟨fun a ha han => h a (by omega) han, fun a ha ham => ⟨fun b hb => ?_, ?_⟩⟩
    · rw [entN_tl m M ham (by omega)]
      exact (h a ha (by omega)).1 b hb
    · rw [entN_tl m M ham ham]
      exact (h a ha (by omega)).2
  · rintro ⟨h1, h2⟩ a ha han
    by_cases ham : a < m
    · refine ⟨fun b hb => ?_, ?_⟩
      · rw [← entN_tl m M ham (by omega)]
        exact (h2 a ha ham).1 b hb
      · rw [← entN_tl m M ham ham]
        exact (h2 a ha ham).2
    · exact h1 a (by omega) han

theorem tl_tl {i m n : ℕ} (him : i ≤ m) (M : Mt g n) : tl i (tl m M) = tl i M := by
  funext a b
  have := a.2
  have := b.2
  exact entN_tl m M (by omega) (by omega)

theorem supFrom_split {i m n : ℕ} (him : i < m) (hmn : m ≤ n) (M : Mt g n) :
    supFrom i M = supFrom (m - 1) M + supFrom i (tl m M) := by
  unfold supFrom
  rw [add_comm, ← Finset.sum_Ico_consecutive _ (show i ≤ m - 1 by omega) (show m - 1 ≤ n - 1 by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact (entN_tl m M (by omega) (by omega)).symm

theorem der_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ),
    i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  intro g _ ψ i m n F him hmn
  funext h
  rw [GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i m _ h him.le, GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i n _ h (by omega)]
  have he : i * (n - i) + (n - i) * (n - i - 1) / 2 =
      (i * (m - i) + (m - i) * (m - i - 1) / 2) + (m * (n - m) + (n - m) * (n - m - 1) / 2) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le him.le
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [show i + a + b - i = a + b by omega, show i + a - i = a by omega, show i + a + b - (i + a) = b by omega,
      tri_add]
    ring
  rw [he, pow_add _ _ (m * (n - m) + (n - m) * (n - m - 1) / 2), mul_inv _ ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2)),
    mul_assoc]
  congr 1
  unfold tail
  set c : ℂ := ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹
  have h1 : ∀ p : Gn g m, (if InR i (p : Mt g m) ∧ tl i (p : Mt g m) = (h : Mt g i) then
      (c * ∑ x : Gn g n, if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
        F x * (ψ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0) * (ψ (supFrom i (p : Mt g m)))⁻¹ else 0) =
      c * ∑ x : Gn g n, if tl m (x : Mt g n) = (p : Mt g m) then
        (if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
          F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0) else 0 := by
    intro p
    split_ifs with hp
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx]
        rw [← hx] at hp
        rw [tl_tl him.le] at hp
        rw [inR_split him.le hmn (x : Mt g n), supFrom_split him hmn (x : Mt g n), AddChar.map_add_eq_mul, mul_inv,
          ← hx]
        by_cases hR : InR m (x : Mt g n)
        · rw [if_pos ⟨hR, rfl⟩, if_pos ⟨⟨hR, hp.1⟩, hp.2⟩, mul_assoc]
        · rw [if_neg (fun hh => hR hh.1), if_neg (fun hh => hR hh.1.1), zero_mul]
      · rw [if_neg hx, if_neg (fun hh => hx hh.2), zero_mul]
    · symm
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx, if_neg]
        rintro ⟨ha, hb⟩
        apply hp
        rw [← hx, tl_tl him.le]
        exact ⟨((inR_split him.le hmn _).1 ha).2, hb⟩
      · rw [if_neg hx]
  rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i)
  · have hu : IsUnit (tl m (x : Mt g n)) :=
      ((GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g m (n - m) n (by omega)).2.2.1 x ((inR_split him.le hmn _).1 hx.1).1.1).1
    obtain ⟨p, hp⟩ := hu
    rw [Finset.sum_eq_single p]
    · rw [if_pos hp.symm]
    · intro q _ hq
      rw [if_neg]
      intro hh
      exact hq (Units.ext (hp.trans hh).symm)
    · intro hh
      exact absurd (Finset.mem_univ p) hh
  · simp [hx]

end GlobalTheory.GLm.DerTail
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTailStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.der_tail_of_lt_of_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ), i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  first | exact @GlobalTheory.GLm.DerTail.der_tail | exact GlobalTheory.GLm.DerTail.der_tail | (intros; apply GlobalTheory.GLm.DerTail.der_tail <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCutoffFibreIntegralOneSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCutoffFibreIntegralOneSubgroup
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem exists_measurable_cutoff_fibre_integral_one (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure G)
    (_hN : IsClosed (N : Set G)) (hν : IsHaarSub (N : Set G) ν) :
    ∃ β : G → ENNReal, Measurable β ∧ (∀ y, β y ≠ ⊤) ∧ ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1 := by
  classical
  obtain ⟨hne, hfin, hcompl, hinv⟩ := hν

  have hae : ∀ᵐ m ∂ν, m ∈ (N : Set G) := by
    rw [ae_iff]; exact hcompl

  have horb : ∀ (h : G → ENNReal) (a : G), a ∈ N → ∀ y,
      ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν = ∫⁻ z, h (z⁻¹ * y) ∂ν := by
    intro h a ha y
    have hmap : ν.map (MeasurableEquiv.mulLeft a) = ν := hinv a ha
    calc ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν
        = ∫⁻ z, h ((MeasurableEquiv.mulLeft a z)⁻¹ * y) ∂ν := by
          congr 1; ext z; simp [_root_.mul_inv_rev, mul_assoc]
      _ = ∫⁻ z, h (z⁻¹ * y) ∂(ν.map (MeasurableEquiv.mulLeft a)) :=
          (lintegral_map_equiv (fun z => h (z⁻¹ * y)) _).symm
      _ = ∫⁻ z, h (z⁻¹ * y) ∂ν := by rw [hmap]

  have hpos : ∀ O : Set G, IsOpen O → ∀ x ∈ O, x ∈ N → 0 < ν O := by
    intro O hO x hxO hxN
    rw [pos_iff_ne_zero]
    intro h0
    apply hne
    set U : G → Set G := fun n => (fun z => (x * n⁻¹) * z) ⁻¹' O with hU
    have hUo : ∀ n ∈ (N : Set G), IsOpen (U n) := fun n _ =>
      hO.preimage (continuous_const.mul continuous_id)
    have hU0 : ∀ n ∈ (N : Set G), ν (U n) = 0 := by
      intro n hn
      have hxn : x * n⁻¹ ∈ N := N.mul_mem hxN (N.inv_mem hn)
      have := hinv _ hxn
      rw [← this] at h0
      rwa [Measure.map_apply (measurable_const_mul _) hO.measurableSet] at h0
    obtain ⟨T, hTN, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable (N : Set G) U hUo
    have hNsub : (N : Set G) ⊆ ⋃ n ∈ T, U n := by
      rw [hTU]
      intro n hn
      exact Set.mem_biUnion hn (by simpa [hU, mul_assoc] using hxO)
    have hN0 : ν (N : Set G) = 0 :=
      measure_mono_null hNsub ((measure_biUnion_null_iff hTc).2 fun n hn => hU0 n (hTN hn))
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self (N : Set G)]
    exact measure_union_null hN0 hcompl

  let E := CompactExhaustion.choice G
  let F : ℕ → G → ENNReal := fun k y => ∫⁻ m, (E k).indicator 1 (m⁻¹ * y) ∂ν
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    refine Measurable.lintegral_prod_right' (f := fun p : G × G => (E k).indicator 1 (p.2⁻¹ * p.1)) ?_
    exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
      (measurable_snd.inv.mul measurable_fst)
  have hFeq : ∀ k y, F k y = ν ((fun m => m⁻¹ * y) ⁻¹' E k) := by
    intro k y
    rw [← lintegral_indicator_one
      ((E.isCompact k).isClosed.measurableSet.preimage (measurable_inv.mul_const y))]
    rfl
  have hFtop : ∀ k y, F k y ≠ ⊤ := by
    intro k y
    rw [hFeq]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (((E.isCompact k).image (f := fun u : G => y * u⁻¹)
        (continuous_const.mul continuous_inv)).measure_lt_top (μ := ν)))
    intro m hm
    exact ⟨m⁻¹ * y, hm, by simp⟩
  have hFpos : ∀ y, ∃ k, 0 < F k y := by
    intro y
    obtain ⟨k, hk⟩ := E.exists_mem_nhds y
    refine ⟨k, ?_⟩
    rw [hFeq]
    refine lt_of_lt_of_le (hpos ((fun m => m⁻¹ * y) ⁻¹' interior (E k))
      (isOpen_interior.preimage (continuous_inv.mul continuous_const)) 1 ?_ N.one_mem)
      (measure_mono (Set.preimage_mono interior_subset))
    simpa [mem_interior_iff_mem_nhds] using hk
  have hFinv : ∀ k y, ∀ᵐ m ∂ν, F k (m⁻¹ * y) = F k y := by
    intro k y
    filter_upwards [hae] with m hm
    exact horb ((E k).indicator 1) m hm y

  let w : ℕ → G → ENNReal := fun k y => (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹
  have hwm : ∀ k, Measurable (w k) := fun k =>
    (measurable_const.mul (measurable_one.indicator (E.isCompact k).isClosed.measurableSet)).mul
      (measurable_const.add (hFm k)).inv
  let f : G → ENNReal := fun y => ∑' k, w k y
  have hfm : Measurable f := Measurable.tsum hwm
  let T : G → ENNReal := fun y => ∫⁻ m, f (m⁻¹ * y) ∂ν
  have hTm : Measurable T :=
    Measurable.lintegral_prod_right' (f := fun p : G × G => f (p.2⁻¹ * p.1))
      (hfm.comp (measurable_snd.inv.mul measurable_fst))
  have hTinv : ∀ y, ∀ᵐ m ∂ν, T (m⁻¹ * y) = T y := by
    intro y
    filter_upwards [hae] with m hm
    exact horb f m hm y
  have hTsum : ∀ y, T y = ∑' k, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
    intro y
    show ∫⁻ m, ∑' k, w k (m⁻¹ * y) ∂ν = _
    rw [lintegral_tsum (f := fun k m => w k (m⁻¹ * y)) fun k => ((hwm k).comp (measurable_inv.mul_const y)).aemeasurable]
    congr 1; ext k
    calc ∫⁻ m, w k (m⁻¹ * y) ∂ν
        = ∫⁻ m, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * (E k).indicator 1 (m⁻¹ * y) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hFinv k y] with m hm
          simp only [w, hm]
          ring
      _ = (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
          rw [lintegral_const_mul]
          exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
            (measurable_inv.mul_const y)
  have hgeom : ∑' k : ℕ, (2⁻¹ : ENNReal) ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    rw [ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hTtop : ∀ y, T y ≠ ⊤ := by
    intro y
    rw [hTsum]
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    rw [mul_comm, ← div_eq_mul_inv]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)
  have hT0 : ∀ y, T y ≠ 0 := by
    intro y
    obtain ⟨k, hk⟩ := hFpos y
    rw [hTsum]
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum k)).ne'
    rw [mul_assoc, mul_comm ((1 + F k y)⁻¹), ← div_eq_mul_inv]
    refine ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)) ?_
    exact (ENNReal.div_pos_iff.2 ⟨hk.ne', ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hFtop k y⟩⟩).ne'
  have hfle : ∀ y, f y ≠ ⊤ := by
    intro y
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    show (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹ ≤ _
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    refine mul_le_one' ?_ (ENNReal.inv_le_one.2 le_self_add)
    by_cases hy : y ∈ E k <;> simp [hy]
  refine ⟨fun y => f y * (T y)⁻¹, hfm.mul hTm.inv, fun y => ?_, fun y => ?_⟩
  · exact ENNReal.mul_ne_top (hfle y) (ENNReal.inv_ne_top.2 (hT0 y))
  · calc ∫⁻ m, f (m⁻¹ * y) * (T (m⁻¹ * y))⁻¹ ∂ν
        = ∫⁻ m, f (m⁻¹ * y) * (T y)⁻¹ ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hTinv y] with m hm
          rw [hm]
      _ = T y * (T y)⁻¹ := lintegral_mul_const _ (hfm.comp (measurable_inv.mul_const y))
      _ = 1 := ENNReal.mul_inv_cancel (hT0 y) (hTtop y)

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCutoffFibreIntegralOneSubgroupStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_cutoff_fibre_integral_one_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∃ β : G → ENNReal, Measurable β ∧ (∀ y, β y ≠ ⊤) ∧ ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1 := by
  first | exact @GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one | exact GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one | (intros; apply GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockDiagUnitaryProductHom
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockDiagUnitaryProductHom
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.BlockDiagEmb

section
variable {n : ℕ} {σ ι : Type} [Fintype σ] {π : σ → ι} {m : ι → ℕ}

def blk (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ) (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ s, T s * k (π s) * (T s)ᴴ

variable {T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ}

theorem frame_mul_blk (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) (s : σ) :
    (T s)ᴴ * blk T k = k (π s) * (T s)ᴴ := by
  unfold blk
  rw [Matrix.mul_sum, Finset.sum_eq_single s]
  · rw [Matrix.mul_assoc (T s), ← Matrix.mul_assoc, h1, Matrix.one_mul]
  · intro t _ hts
    rw [Matrix.mul_assoc (T t), ← Matrix.mul_assoc, h0 s t hts.symm, Matrix.zero_mul]
  · simp

theorem blk_mul (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k l : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    blk T k * blk T l = blk T (fun i => k i * l i) := by
  conv_lhs => rw [blk, Matrix.sum_mul]
  unfold blk
  refine Finset.sum_congr rfl fun s _ => ?_
  have := frame_mul_blk h1 h0 l s
  unfold blk at this
  rw [Matrix.mul_assoc, this]
  simp only [Matrix.mul_assoc]

theorem blk_one (hs : ∑ s, T s * (T s)ᴴ = 1) : blk T (fun _ => 1) = 1 := by
  simpa [blk] using hs

theorem blk_conjTranspose (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    (blk T k)ᴴ = blk T (fun i => (k i)ᴴ) := by
  simp [blk, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem blk_sub (k l : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    blk T k - blk T l = blk T (fun i => k i - l i) := by
  simp [blk, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem blk_trace (h1 : ∀ s, (T s)ᴴ * T s = 1) (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    (blk T k).trace = ∑ s, (k (π s)).trace := by
  unfold blk
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem hs_eq_trace {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    Formalism.REAL.hs X = (X * Xᴴ).trace.re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem blk_hs (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    Formalism.REAL.hs (blk T k) = ∑ s, Formalism.REAL.hs (k (π s)) := by
  rw [hs_eq_trace, blk_conjTranspose, blk_mul h1 h0, blk_trace h1, Complex.re_sum]
  simp only [hs_eq_trace]

theorem continuous_blk : Continuous (blk T) := by
  unfold blk
  refine continuous_finsetSum _ fun s _ => ?_
  exact (continuous_const.matrix_mul (continuous_apply (π s))).matrix_mul continuous_const

end

theorem unitary_of_allPos {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : (uMat g)ᴴ * uMat g = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  have hJ : Formalism.REAL.Jm (allPos N) = 1 := by simp [Formalism.REAL.Jm, allPos]
  simpa [hJ] using h

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one' {n : ℕ} {ε : Fin n → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem continuous_uMat {n : ℕ} {ε : Fin n → Bool} : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem exists_blockDiag_hom : ∀ (n : ℕ) (ε : Fin n → Bool) (σ ι : Type) [Fintype σ] [Fintype ι] (π : σ → ι) (m : ι → ℕ) (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ), Function.Surjective π → (∀ s, (T s)ᴴ * T s = 1) → (∀ s t, s ≠ t → (T s)ᴴ * T t = 0) → ∑ s, T s * (T s)ᴴ = 1 → (∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ, Formalism.REAL.Jm ε * ∑ s, T s * k (π s) * (T s)ᴴ = (∑ s, T s * k (π s) * (T s)ᴴ) * Formalism.REAL.Jm ε) → ∃ Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε, Continuous Φ ∧ Function.Injective Φ ∧ (∀ g, uMat (Φ g) = ∑ s, T s * uMat (g (π s)) * (T s)ᴴ) ∧ ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ s, Formalism.REAL.hs (uMat (g (π s)) - 1) := by
  intro n ε σ ι _ _ π m T hπ h1 h0 hs hJ
  let f : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => blk T (fun i => uMat (g i))
      map_one' := by simp only [Pi.one_apply, uMat_one']; exact blk_one hs
      map_mul' := fun g h => by simp only [Pi.mul_apply, uMat_mul']; exact (blk_mul h1 h0 _ _).symm }
  have hfe : ∀ g, f g = blk T (fun i => uMat (g i)) := fun g => rfl
  clear_value f
  have hf : Continuous f := by
    have h : Continuous (fun (g : ∀ i, Formalism.REAL.UJ (allPos (m i))) => fun i => uMat (g i)) :=
      continuous_pi fun i => continuous_uMat.comp (continuous_apply i)
    have h2 := (continuous_blk (T := T)).comp h
    exact h2.congr fun g => (hfe g).symm
  have hmem : ∀ g, f.toHomUnits g ∈ Formalism.REAL.UJ ε := by
    intro g
    show (f g)ᴴ * Formalism.REAL.Jm ε * f g = Formalism.REAL.Jm ε
    rw [hfe]
    have hJ' : ∀ k, Formalism.REAL.Jm ε * blk T k = blk T k * Formalism.REAL.Jm ε := hJ
    have := hJ' (fun i => uMat (g i))
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, blk_conjTranspose, blk_mul h1 h0]
    simp only [unitary_of_allPos]
    rw [blk_one hs, Matrix.one_mul]
  refine ⟨f.toHomUnits.codRestrict _ hmem, ?_, ?_, fun g => hfe g, fun g => ?_⟩
  · have hu : Continuous f.toHomUnits :=
      Units.continuous_iff.2 ⟨hf, hf.comp continuous_inv⟩
    exact hu.subtype_mk hmem
  · intro g h hgh
    have e : blk T (fun i => uMat (g i)) = blk T (fun i => uMat (h i)) := by
      rw [← hfe, ← hfe]
      exact congrArg (fun x : Formalism.REAL.UJ ε => uMat x) hgh
    funext i
    obtain ⟨s, rfl⟩ := hπ i
    have e2 := frame_mul_blk h1 h0 (fun i => uMat (g i)) s
    rw [e, frame_mul_blk h1 h0] at e2
    have e3 := congrArg (· * T s) e2
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at e3
    exact Subtype.ext (Units.ext e3.symm)
  · show Formalism.REAL.hs (f g - 1) = _
    rw [hfe, ← blk_one (T := T) hs, blk_sub, blk_hs h1 h0]

end GlobalTheory.BlockDiagEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockDiagUnitaryProductHomStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockDiag_unitary_product_hom : ∀ (n : ℕ) (ε : Fin n → Bool) (σ ι : Type) [Fintype σ] [Fintype ι] (π : σ → ι) (m : ι → ℕ) (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ), Function.Surjective π → (∀ s, (T s)ᴴ * T s = 1) → (∀ s t, s ≠ t → (T s)ᴴ * T t = 0) → ∑ s, T s * (T s)ᴴ = 1 → (∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ, Formalism.REAL.Jm ε * ∑ s, T s * k (π s) * (T s)ᴴ = (∑ s, T s * k (π s) * (T s)ᴴ) * Formalism.REAL.Jm ε) → ∃ Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε, Continuous Φ ∧ Function.Injective Φ ∧ (∀ g, uMat (Φ g) = ∑ s, T s * uMat (g (π s)) * (T s)ᴴ) ∧ ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ s, Formalism.REAL.hs (uMat (g (π s)) - 1) := by
  first | exact @GlobalTheory.BlockDiagEmb.exists_blockDiag_hom | exact GlobalTheory.BlockDiagEmb.exists_blockDiag_hom | (intros; apply GlobalTheory.BlockDiagEmb.exists_blockDiag_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompleteIsotropicFrameSignatureEigenvectors
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianIdempotentEqIsometryMulConjTranspose
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem hermitian_idempotent_eq_isometry_mul_conjTranspose :
    ∀ (n : ℕ) (R : Matrix (Fin n) (Fin n) ℂ), Rᴴ = R → R * R = R →
      ∃ (r : ℕ) (P : Matrix (Fin n) (Fin r) ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = R := by
  intro n R hH hI
  classical
  have hA : R.IsHermitian := hH
  have hev : ∀ i, hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
    intro i
    have hv := hA.mulVec_eigenvectorBasis i
    have hne : (⇑(hA.eigenvectorBasis i) : Fin n → ℂ) ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
    have h2 : R *ᵥ (R *ᵥ ⇑(hA.eigenvectorBasis i)) = R *ᵥ ⇑(hA.eigenvectorBasis i) := by
      rw [mulVec_mulVec, hI]
    rw [hv, mulVec_smul, hv, smul_smul] at h2
    have h3 : (hA.eigenvalues i * hA.eigenvalues i - hA.eigenvalues i) •
        (⇑(hA.eigenvectorBasis i) : Fin n → ℂ) = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · have h4 : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h4 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linarith)
    · exact absurd h hne
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  let e : Fin (Fintype.card {i // hA.eigenvalues i ≠ 0}) ≃ {i // hA.eigenvalues i ≠ 0} :=
    (Fintype.equivFin _).symm
  let f : Fin (Fintype.card {i // hA.eigenvalues i ≠ 0}) → Fin n := fun j => (e j).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let Q : Matrix (Fin n) (Fin (Fintype.card {i // hA.eigenvalues i ≠ 0})) ℂ :=
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id f
  have hQQ : Qᴴ * Q = 1 := by
    ext j k
    simp [Q, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hQ : Q * Qᴴ = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i k
    rw [Matrix.mul_apply, diagonal_apply]
    simp only [Q, conjTranspose_apply, submatrix_apply, id, Matrix.one_apply, Function.comp_apply]
    by_cases h0 : hA.eigenvalues i = 0
    · have hz : ∀ j, (if i = f j then (1 : ℂ) else 0) = 0 := by
        intro j
        refine if_neg (fun h => (e j).2 ?_)
        rw [show (e j).1 = i from h.symm]
        exact h0
      simp only [hz, zero_mul, Finset.sum_const_zero, h0]
      split_ifs <;> simp
    · have h1 : hA.eigenvalues i = 1 := (hev i).resolve_left h0
      have hj0 : f (e.symm ⟨i, h0⟩) = i := by simp [f]
      rw [Finset.sum_eq_single (e.symm ⟨i, h0⟩)]
      · rw [hj0, if_pos rfl, one_mul, h1]
        by_cases hik : i = k
        · subst hik
          simp
        · rw [if_neg (Ne.symm hik), if_neg hik]
          simp
      · intro b _ hb
        have hne : i ≠ f b := by
          intro h
          apply hb
          rw [Equiv.eq_symm_apply]
          exact Subtype.ext h.symm
        rw [if_neg hne, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
  refine ⟨Fintype.card {i // hA.eigenvalues i ≠ 0}, U * Q, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul, hQQ]
  · have hs := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ]
    conv_rhs => rw [hs]
    simp [U, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompleteIsotropicFrameSignatureEigenvectors
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IsoFrame

private theorem half_smul_sub_mul_mul_mul_self {n : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (hAA : A * A = A + A)
    (hSAS : S * A * S = S) :
    ((1 / 2 : ℂ) • (A - A * S * A)) * ((1 / 2 : ℂ) • (A - A * S * A)) =
      (1 / 2 : ℂ) • (A - A * S * A) := by
  have h5 : A * S * A * S * A = A * S * A := by
    rw [show A * S * A * S * A = A * (S * A * S) * A by noncomm_ring, hSAS]
  have key : (A - A * S * A) * (A - A * S * A) = (A - A * S * A) + (A - A * S * A) := by
    calc (A - A * S * A) * (A - A * S * A)
        = A * A - (A * A) * S * A - A * S * (A * A) + A * S * (A * A) * S * A := by noncomm_ring
      _ = (A + A) - (A + A) * S * A - A * S * (A + A) + A * S * (A + A) * S * A := by rw [hAA]
      _ = (A + A) - (A * S * A + A * S * A) - (A * S * A + A * S * A)
            + (A * S * A * S * A + A * S * A * S * A) := by noncomm_ring
      _ = (A - A * S * A) + (A - A * S * A) := by rw [h5]; abel
  rw [Matrix.smul_mul, Matrix.mul_smul, key, ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

theorem exists_eigenframe {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J) (p : ℕ)
    (hp : Matrix.trace (1 + J) = 2 * (p : ℂ)) {a : ℕ} (j : Fin a → ℕ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) :
    ∃ P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ, (∀ i, (T i)ᴴ * P = 0) ∧ Pᴴ * P = 1 ∧ J * P = P ∧
      P * Pᴴ = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by

  have hA : ∀ i k, (T i)ᴴ * (1 + J) * T k = (T i)ᴴ * T k := by
    intro i k
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h3, add_zero]
  have hTS : ∀ i, (T i)ᴴ * (1 + J) * (∑ k, T k * (T k)ᴴ) = (T i)ᴴ := by
    intro i
    rw [Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, hA, h1, Matrix.one_mul]
    · intro k _ hk
      rw [← Matrix.mul_assoc, hA, h2 i k (Ne.symm hk), Matrix.zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hSAS : (∑ k, T k * (T k)ᴴ) * (1 + J) * (∑ k, T k * (T k)ᴴ) = ∑ k, T k * (T k)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T k)ᴴ, hTS]
  have hAA : (1 + J) * (1 + J) = (1 + J) + (1 + J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJJ]; abel
  have hJA : J * (1 + J) = 1 + J := by
    rw [Matrix.mul_add, Matrix.mul_one, hJJ, add_comm]

  have hRR := half_smul_sub_mul_mul_mul_self (1 + J) (∑ k, T k * (T k)ᴴ) hAA hSAS
  have hAh : (1 + J)ᴴ = 1 + J := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hJh]
  have hSh : (∑ k, T k * (T k)ᴴ)ᴴ = ∑ k, T k * (T k)ᴴ := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hRh : ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))ᴴ
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hAh, hSh, ← Matrix.mul_assoc]
    congr 1
    simp

  have htrS : Matrix.trace ((1 + J) * (∑ k, T k * (T k)ᴴ)) = ∑ k, (j k : ℂ) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, h1, Matrix.trace_one,
      Fintype.card_fin]
  have htrR : Matrix.trace ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [Matrix.trace_smul, Matrix.trace_sub, hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAA,
      Matrix.add_mul, Matrix.trace_add, htrS]
    simp only [smul_eq_mul]; ring
  obtain ⟨r, P, hPP, hPR⟩ := GlobalTheory.hermitian_idempotent_eq_isometry_mul_conjTranspose n _ hRh hRR
  have hr : (r : ℂ) = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [← htrR, ← hPR, Matrix.trace_mul_comm, hPP, Matrix.trace_one, Fintype.card_fin]
  have hr' : r = p - ∑ i, j i := by
    have hc : ((r + ∑ i, j i : ℕ) : ℂ) = (p : ℂ) := by push_cast; rw [hr]; ring
    have h' : r + ∑ i, j i = p := by exact_mod_cast hc
    omega
  subst hr'
  have hRP : (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) * P = P := by
    rw [← hPR, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hTR : ∀ i, (T i)ᴴ * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))) = 0 := by
    intro i
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hTS, sub_self, smul_zero]
  have hJR : J * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hJA]
  refine ⟨P, fun i => ?_, hPP, ?_, hPR⟩
  · rw [← hRP, ← Matrix.mul_assoc, hTR i, Matrix.zero_mul]
  · rw [← hRP, ← Matrix.mul_assoc, hJR]

theorem complete_isotropic_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  intro n ε p q hp hq a j T h1 h2 h3

  have hJdef : Formalism.REAL.Jm ε = Matrix.diagonal (fun b => if ε b = true then (1 : ℂ) else -1) := by
    unfold Formalism.REAL.Jm
    try rfl
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [hJdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext b; split_ifs <;> norm_num
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [hJdef, Matrix.diagonal_conjTranspose]
    congr 1; funext b; simp only [Pi.star_apply]; split_ifs <;> simp
  have htp : Matrix.trace (1 + Formalism.REAL.Jm ε) = 2 * (p : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = true then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hp]; ring
  have htq : Matrix.trace (1 + -Formalism.REAL.Jm ε) = 2 * (q : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = false then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hq]; ring

  obtain ⟨P, hP0, hPP, hJP, hPR⟩ := exists_eigenframe _ hJJ hJh p htp j T h1 h2 h3
  have h3' : ∀ i k, (T i)ᴴ * (-Formalism.REAL.Jm ε) * T k = 0 := by
    intro i k; rw [Matrix.mul_neg, Matrix.neg_mul, h3, neg_zero]
  obtain ⟨Q, hQ0, hQQ, hJQ, hQR⟩ := exists_eigenframe (-Formalism.REAL.Jm ε)
    (by rw [neg_mul_neg, hJJ]) (by rw [Matrix.conjTranspose_neg, hJh]) q htq j T h1 h2 h3'
  refine ⟨P, Q, hP0, hQ0, hPP, hQQ, hJP, ?_, ?_⟩
  · rw [Matrix.neg_mul, neg_eq_iff_eq_neg] at hJQ; exact hJQ
  · have hsum : (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε))
        = (∑ i, T i * (T i)ᴴ) + Formalism.REAL.Jm ε * (∑ i, T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
      rw [Finset.sum_add_distrib, Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    rw [hsum, hPR, hQR]
    generalize (∑ i, T i * (T i)ᴴ) = S
    generalize Formalism.REAL.Jm ε = J

    have hX : ((1 + J) - (1 + J) * S * (1 + J)) + ((1 + -J) - (1 + -J) * S * (1 + -J))
        = (1 - S - J * S * J) + (1 - S - J * S * J) := by noncomm_ring
    rw [add_assoc (S + J * S * J), ← smul_add, hX, ← two_smul ℂ, smul_smul,
      show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
    abel

end GlobalTheory.IsoFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompleteIsotropicFrameSignatureEigenvectorsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_isotropicFrame_signature_eigenvectors : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  first | exact @GlobalTheory.IsoFrame.complete_isotropic_frame | exact GlobalTheory.IsoFrame.complete_isotropic_frame | (intros; apply GlobalTheory.IsoFrame.complete_isotropic_frame <;> assumption)
end
end

module

public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescent
public import Lemmata.GeneralBFactLeftSide.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.OddDualWeylFactorization

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OddDualWeyl
theorem oddDualWeyl {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    PI.OddDualWeyl.OddFact (K := K) O m lam :=
  PI.OddDualWeyl.odd_dual_weyl_factorization O m lam
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentOfIntegralModels
section -- merged from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.RowActWeylMemDescentLattice
section -- merged from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylEqSpanInt
open MvPolynomial Matrix Formalism.GradedWeylDivisibility

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

theorem prodSpan {O A I : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype I] [DecidableEq I]
    {B : I → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module O (B i)] (ε : ∀ i, B i →ₗ[O] A) (T : ∀ i, Set (B i)) :
    Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ Submodule.span O (T i)) ∧ X = ∏ i, ε i (F i)} =
      Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ T i) ∧ X = ∏ i, ε i (F i)} := by
  exact Bl.general_b_fact_left'''''.goal1 ..

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (F : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R g F) = rowAct S (g.map φ) (MvPolynomial.map φ F) := by
  have h : (MvPolynomial.map φ).comp (rowAct R (n := n) g).toRingHom =
      (rowAct S (n := n) (g.map φ)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro x
      simp [rowAct]
  exact RingHom.congr_fun h F

theorem rowAct_one {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) F = F := by
  have e : rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [rowAct, aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e]; rfl

theorem rowAct_cancel {R : Type} [CommRing R] {r n : ℕ} (g gi : Matrix (Fin r) (Fin r) R) (h : gi * g = 1)
    (F : MvPolynomial (Fin r × Fin n) R) : rowAct R g (rowAct R gi F) = F := by
  have h1 := rowActMul R r n g gi
  rw [h] at h1
  have h2 := congrArg (fun f => f F) h1
  simp only [AlgHom.comp_apply] at h2
  rw [h2, rowAct_one]

theorem map_mem_weyl {O : Type} [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    MvPolynomial.map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨w, by rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : MvPolynomial.map (Int.castRingHom O) (c • x) = (c : O) • MvPolynomial.map (Int.castRingHom O) x := by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]; rfl
    rw [e1]; exact Submodule.smul_mem _ _ hx

theorem weyl_eq_span_int (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    weyl O r n hn ν = Submodule.span O ((fun f => MvPolynomial.map (Int.castRingHom O) f) ''
      (weyl ℤ r n hn ν : Set (MvPolynomial (Fin r × Fin n) ℤ))) := by
  apply le_antisymm
  · show Submodule.span O (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord O w (hw O hn ν)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    exact ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, by
      show MvPolynomial.map (Int.castRingHom O) (applyWord ℤ w (hw ℤ hn ν)) = _
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact map_mem_weyl hn ν f hf

end Formalism.L2.G.RelativeIndexFlags.Core
end
end

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem int_comp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    φ.comp (Int.castRingHom A) = Int.castRingHom B := RingHom.ext_int _ _

theorem lamStar_anti {m : ℕ} (lam : Fin (m + 1) → ℤ) (hd : Antitone lam) : Antitone (lamStar lam) := by
  intro i j hij
  simp only [lamStar, neg_le_neg_iff]
  exact hd (Fin.rev_le_rev.2 hij)

theorem lamAt_odd {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (hs : ¬ Even s.val) :
    lamAt lam0 s = lamStar (lam0 s) := by
  unfold lamAt; rw [ite_eq_right hs]; rfl

theorem lamAt_even {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (hs : Even s.val) :
    lamAt lam0 s = lam0 s := by
  unfold lamAt; rw [ite_eq_left hs]

theorem lamAt_anti {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) (s : Fin n') :
    Antitone (lamAt lam0 s) := by
  by_cases hs : Even s.val
  · rw [lamAt_even lam0 s hs]; exact hd s
  · rw [lamAt_odd lam0 s hs]; exact lamStar_anti _ (hd s)

theorem rowAct_weyl_mem_span_integral {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (ν : Fin (m + 1) → ℕ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (a : Kf) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O)
    (hf : f ∈ weyl O (m + 1) (m + 1) le_rfl ν) :
    a • rowAct Kf g (map (algebraMap O Kf) f) ∈ Submodule.span O
      ((fun f0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ => a • rowAct Kf g (map (Int.castRingHom Kf) f0)) ''
        (weyl ℤ (m + 1) (m + 1) le_rfl ν : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ))) := by
  rw [weyl_eq_span_int] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f0, hf0, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨f0, hf0, ?_⟩
    show _ = a • rowAct Kf g (map (algebraMap O Kf) (map (Int.castRingHom O) f0))
    rw [MvPolynomial.map_map, int_comp]
  | zero => rw [map_zero, map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), smul_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : map (algebraMap O Kf) (c • x) = algebraMap O Kf c • map (algebraMap O Kf) x := by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    rw [e1, map_smul, smul_comm, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem rowAct_weyl_mem_descentLattice {O K : Type} [CommRing O] [Field K] [Algebra O K] (hinj : Function.Injective (algebraMap O K)) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det)
    (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O) (hf : f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam)) :
    (g.det ^ (-(lam (Fin.last m)))) • rowAct K g⁻¹ (map (algebraMap O K) f) ∈ Dl0 O m lam (colSpan O g) := by
  rw [dw_eq hinj m lam hlam g hg]
  refine ⟨rowAct K g⁻¹ (map (algebraMap O K) f), ⟨f, hf, ?_⟩, rfl⟩
  change map (algebraMap O K) f = rowAct K g (rowAct K g⁻¹ (map (algebraMap O K) f))
  rw [rowAct_cancel g g⁻¹ (Matrix.nonsing_inv_mul g hg)]

theorem descentLattice_eq_span_weyl {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    Dl0 O m lam (colSpan O g) = Submodule.span O
      ((fun f0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ =>
          (g.det ^ (-(lam (Fin.last m)))) • rowAct Kf g⁻¹ (map (Int.castRingHom Kf) f0)) ''
        (weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ))) := by
  apply le_antisymm
  · rw [dw_eq hinj m lam hlam g hg]
    rintro _ ⟨F0, ⟨f, hf, hfe⟩, rfl⟩
    have hfe' : map (algebraMap O Kf) f = rowAct Kf g F0 := hfe
    have hF0 : F0 = rowAct Kf g⁻¹ (map (algebraMap O Kf) f) := by
      rw [hfe', rowAct_cancel g⁻¹ g (Matrix.mul_nonsing_inv g hg)]
    show g.det ^ (-(lam (Fin.last m))) • F0 ∈ _
    rw [hF0]
    exact rowAct_weyl_mem_span_integral m _ g⁻¹ _ f hf
  · rw [Submodule.span_le]
    rintro _ ⟨f0, hf0, rfl⟩
    have h1 := rowAct_weyl_mem_descentLattice hinj m lam hlam g hg (map (Int.castRingHom O) f0) (map_mem_weyl le_rfl _ f0 hf0)
    rw [MvPolynomial.map_map, int_comp] at h1
    exact h1

theorem sub_rfl {k : ℕ} {R : Type} (h : k = k) (A : Matrix (Fin k) (Fin k) R) :
    A.submatrix (finCongr h) (finCongr h) = A := by
  ext i j; rfl

theorem gl_map_det {k : ℕ} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (A : GL (Fin k) R) :
    IsUnit ((A : Matrix (Fin k) (Fin k) R).map φ).det := by
  have h1 : ((A : Matrix (Fin k) (Fin k) R).map φ).det = φ (A : Matrix (Fin k) (Fin k) R).det :=
    (RingHom.map_det φ _).symm
  rw [h1]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).map φ

section Blocks

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]
  (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (N : Tau → GL (Fin n) LL)

def niAt (v : Fin P.nV) (s : Fin (P.n' v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL :=
  if Even s.val then (((N (pos ⟨v, s⟩))⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL).submatrix (finCongr h) (finCongr h)
  else (N (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) LL)ᵀ.submatrix (finCongr h) (finCongr h)

theorem niAt_mul_nAt (v : Fin P.nV) (s : Fin (P.n' v)) : niAt P h pos N v s * nAt P h pos N v s = 1 := by
  unfold niAt nAt
  split_ifs
  · rw [Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.submatrix_one_equiv]
  · rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.submatrix_one_equiv]

theorem niAt_map_mul {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v)) :
    (niAt P h pos N v s).map φ * (nAt P h pos N v s).map φ = 1 := by
  rw [← Matrix.map_mul, niAt_mul_nAt, Matrix.map_one φ φ.map_zero φ.map_one]

theorem nAt_map_inv {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v)) :
    ((nAt P h pos N v s).map φ)⁻¹ = (niAt P h pos N v s).map φ :=
  Matrix.inv_eq_left_inv (niAt_map_mul P h pos N φ v s)

theorem nAt_map_det {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v)) :
    IsUnit ((nAt P h pos N v s).map φ).det :=
  Matrix.isUnit_det_of_left_inverse (niAt_map_mul P h pos N φ v s)

def bl (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) LL :=
  ((nAt P h pos N v s).det ^ (-(eAt P v s))) • rowAct LL (niAt P h pos N v s) (map (Int.castRingHom LL) f)

theorem map_bl {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v))
    (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map φ (bl P h pos N v s f) = (((nAt P h pos N v s).map φ).det ^ (-(eAt P v s))) •
      rowAct R ((nAt P h pos N v s).map φ)⁻¹ (map (Int.castRingHom R) f) := by
  unfold bl
  rw [Cmp.map_smul', map_rowAct, MvPolynomial.map_map, int_comp, map_zpow₀, nAt_map_inv, RingHom.map_det]
  rfl

def gen (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) : XR P LL :=
  ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb LL s (bl P h pos N v s (f v s)))

def genSet : Set (XR P LL) :=
  {X | ∃ f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
    (∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧ X = gen P h pos N f}

theorem map_gen {R : Type} [Field R] (φ : LL →+* R)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map φ (gen P h pos N f) =
      ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb R s (map φ (bl P h pos N v s (f v s)))) := by
  unfold gen
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [MvPolynomial.map_rename, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  exact MvPolynomial.map_rename _ _ _

theorem htupW_eq (hinj : Function.Injective (algebraMap O Kf)) (e : LL →+* Kf) (L : P.Tup)
    (HL : ∀ v (s : Fin (P.n' v)), extO O (P.ι v) (P.σ v) s.val (L v) = colSpan O ((nAt P h pos N v s).map e)) :
    P.HtupW L = Submodule.span O ((fun q => map e q) '' genSet P h pos N) := by
  classical
  let Tb : ∀ v, ∀ _ : Fin (P.n' v), Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) := fun v s =>
    (fun f0 => map e (bl P h pos N v s f0)) ''
      (weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)) : Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ))
  have hD : ∀ v (s : Fin (P.n' v)), Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L v)) =
      Submodule.span O (Tb v s) := by
    intro v s
    rw [HL v s, descentLattice_eq_span_weyl hinj P.m _ (lamAt_anti _ (P.dom v) s) _ (nAt_map_det P h pos N e v s)]
    congr 1
    apply Set.image_congr
    intro f0 _
    exact (map_bl P h pos N e v s f0).symm
  let Tv : ∀ v, Set (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf) := fun v =>
    {X | ∃ F : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
      (∀ s, F s ∈ Tb v s) ∧ X = ∏ s, blockEmb Kf s (F s)}
  have hs : ∀ v, HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v)) = Submodule.span O (Tv v) := by
    intro v
    unfold HtenW tensorLat
    simp only [hD]
    exact prodSpan (O := O) (A := MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)
      (B := fun _ => MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
      (fun s => (blockEmb Kf s).toLinearMap.restrictScalars O) (Tb v)
  unfold Places.HtupW Places.tenV
  simp only [hs]
  refine (prodSpan (O := O) (A := P.Xsp)
    (B := fun v => MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)
    (fun v => (P.vEmb v).toLinearMap.restrictScalars O) Tv).trans ?_
  congr 1
  ext X
  constructor
  · rintro ⟨F, hF, rfl⟩
    choose F' hF' hFe using hF
    choose f hf hfe using hF'
    refine ⟨gen P h pos N f, ⟨f, hf, rfl⟩, ?_⟩
    show map e (gen P h pos N f) = _
    rw [map_gen]
    refine Finset.prod_congr rfl fun v _ => ?_
    show _ = P.vEmb v (F v)
    rw [hFe v]
    have e2 : ∀ s, map e (bl P h pos N v s (f v s)) = F' v s := fun s => hfe v s
    simp only [e2]
    rfl
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨fun v => ∏ s, blockEmb Kf s (map e (bl P h pos N v s (f v s))),
      fun v => ⟨fun s => map e (bl P h pos N v s (f v s)), fun s => ⟨f v s, hf v s, rfl⟩, rfl⟩,
      map_gen P h pos N e f⟩

theorem mem_htupW_iff (hD : DescVal) (hfr : IsFractionRing O Kf) (e : LL →+* Kf) (R0 : Subring LL)
    (hR0 : ∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap O Kf)) (L : P.Tup)
    (HL : ∀ v (s : Fin (P.n' v)), extO O (P.ι v) (P.σ v) s.val (L v) = colSpan O ((nAt P h pos N v s).map e))
    (Q : XR P LL) : map e Q ∈ P.HtupW L ↔ Q ∈ Submodule.span R0 (genSet P h pos N) := by
  rw [htupW_eq P h pos N (IsFractionRing.injective O Kf) e L HL]
  constructor
  · exact hD e R0 hR0 _ Q
  · intro hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨o, ho⟩ := (hR0 r.1).1 r.2
      have e1 : map e (r • x) = o • map e x := by
        rw [Subring.smul_def, Cmp.map_smul', ← ho, algebraMap_smul]
      rw [e1]; exact Submodule.smul_mem _ o hx

end Blocks

end Formalism.L2.G.RelativeIndexFlags.Core
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.CoreDesc
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

section Desc

variable {LL Kf ι : Type} [Field LL] [Field Kf] [Algebra LL Kf]

theorem desc_fun (ℓ : Kf →ₗ[LL] LL) (t : Finset (MvPolynomial ι LL)) (c : MvPolynomial ι LL → Kf) (c0 : Kf)
    (Q : MvPolynomial ι LL)
    (h : ∑ x ∈ t, C (c x) * map (algebraMap LL Kf) x = C c0 * map (algebraMap LL Kf) Q) :
    ∑ x ∈ t, ℓ (c x) • x = ℓ c0 • Q := by
  ext m
  have hm := congrArg (fun P => ℓ (AddMonoidAlgebra.coeff P m)) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_sum, coeff_C_mul, coeff_map, map_sum] at hm
  simp only [coeff_sum, coeff_smul, smul_eq_mul]
  have e : ∀ (a : Kf) (r : LL), ℓ (a * algebraMap LL Kf r) = ℓ a * r := by
    intro a r
    rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp only [e] at hm
  exact hm

theorem exists_pivot {α : Type} [DecidableEq α] (R0 : Subring LL) (hv : ∀ x : LL, x ∈ R0 ∨ x⁻¹ ∈ R0) (f : α → LL)
    (t : Finset α) : (∃ x ∈ t, f x ≠ 0) → ∃ j ∈ t, f j ≠ 0 ∧ ∀ x ∈ t, f x / f j ∈ R0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rintro ⟨x, hx, _⟩
    simp at hx
  | insert a t' ha ih =>
    rintro ⟨x, hx, hfx⟩
    by_cases hex : ∃ x ∈ t', f x ≠ 0
    · obtain ⟨j, hj, hfj, hall⟩ := ih hex
      by_cases hr : f a / f j ∈ R0
      · refine ⟨j, Finset.mem_insert_of_mem hj, hfj, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hr
        · exact hall y hy
      · have hinv : f j / f a ∈ R0 := by
          have h2 := (hv (f a / f j)).resolve_left hr
          rwa [inv_div] at h2
        have hfa : f a ≠ 0 := by
          intro h0
          apply hr
          rw [h0, zero_div]
          exact R0.zero_mem
        refine ⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · rw [div_self hfa]
          exact R0.one_mem
        · have h3 := R0.mul_mem (hall y hy) hinv
          have e : f y / f j * (f j / f a) = f y / f a := by
            field_simp
          rwa [e] at h3
    · push_neg at hex
      have hfa : f a ≠ 0 := by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hfx
        · exact absurd (hex x hx') hfx
      refine ⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [div_self hfa]
        exact R0.one_mem
      · rw [hex y hy, zero_div]
        exact R0.zero_mem

theorem exists_dual_ne {v : Kf} (hv : v ≠ 0) : ∃ ℓ : Kf →ₗ[LL] LL, ℓ v ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hv ((Module.forall_dual_apply_eq_zero_iff LL v).mp hc)

theorem desc_main (A : Subring Kf) (hA : ∀ x : Kf, x ∈ A ∨ x⁻¹ ∈ A) (R0 : Subring LL)
    (hR0 : ∀ x, x ∈ R0 ↔ algebraMap LL Kf x ∈ A) :
    ∀ (n : ℕ) (t : Finset (MvPolynomial ι LL)), t.card = n → ∀ c : MvPolynomial ι LL → Kf, (∀ x ∈ t, c x ∈ A) →
    ∀ Q : MvPolynomial ι LL, ∑ x ∈ t, C (c x) * map (algebraMap LL Kf) x = map (algebraMap LL Kf) Q →
    Q ∈ Submodule.span R0 (t : Set (MvPolynomial ι LL)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro t ht c _ Q hQ
    rw [Finset.card_eq_zero] at ht
    subst ht
    simp only [Finset.sum_empty] at hQ
    have hQ0 : Q = 0 := by
      apply MvPolynomial.map_injective _ (algebraMap LL Kf).injective
      rw [← hQ, map_zero]
    rw [hQ0]
    exact zero_mem _
  | succ k ih =>
    intro t ht c hc Q hQ
    by_cases hdep : LinearIndependent LL (fun x : t => (x : MvPolynomial ι LL))
    ·
      have hsum : ∀ ℓ : Kf →ₗ[LL] LL, ∑ x ∈ t, ℓ (c x) • x = ℓ 1 • Q := by
        intro ℓ
        apply desc_fun ℓ t c 1 Q
        rw [map_one, one_mul]
        exact hQ
      have hrange : ∀ x ∈ t, c x ∈ Set.range (algebraMap LL Kf) := by
        intro x0 hx0
        by_contra hnot
        have hmk : (Submodule.span LL {(1 : Kf)}).mkQ (c x0) ≠ 0 := by
          rw [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
          rintro ⟨a, ha⟩
          apply hnot
          exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩
        obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual LL (Kf ⧸ Submodule.span LL {(1 : Kf)}),
            φ ((Submodule.span LL {(1 : Kf)}).mkQ (c x0)) ≠ 0 := by
          by_contra hc'
          push_neg at hc'
          exact hmk ((Module.forall_dual_apply_eq_zero_iff LL _).mp hc')
        set ℓ : Kf →ₗ[LL] LL := φ.comp (Submodule.span LL {(1 : Kf)}).mkQ with hℓ
        have hℓ1 : ℓ 1 = 0 := by
          simp only [hℓ, LinearMap.comp_apply, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self 1), map_zero]
        have h0 := hsum ℓ
        rw [hℓ1, zero_smul, ← Finset.sum_coe_sort t] at h0
        have h1 := Fintype.linearIndependent_iff.mp hdep (fun x : t => ℓ (c x)) h0 ⟨x0, hx0⟩
        exact hφ h1
      choose d hd using fun x (hx : x ∈ t) => hrange x hx
      obtain ⟨ℓ0, hℓ0⟩ := exists_dual_ne (LL := LL) (Kf := Kf) (one_ne_zero : (1 : Kf) ≠ 0)
      set ℓ1 : Kf →ₗ[LL] LL := (ℓ0 1)⁻¹ • ℓ0 with hℓ1def
      have hℓ11 : ℓ1 1 = 1 := by
        simp only [hℓ1def, LinearMap.smul_apply, smul_eq_mul]
        exact inv_mul_cancel₀ hℓ0
      have h0 := hsum ℓ1
      rw [hℓ11, one_smul] at h0
      rw [← h0]
      refine Submodule.sum_mem _ fun x hx => ?_
      have hdx : ℓ1 (c x) = d x hx := by
        rw [← hd x hx, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, hℓ11, smul_eq_mul, mul_one]
      have hR : d x hx ∈ R0 := by
        rw [hR0, hd x hx]
        exact hc x hx
      rw [hdx]
      exact Submodule.smul_mem _ (⟨d x hx, hR⟩ : R0) (Submodule.subset_span hx)
    ·
      obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
      set f : MvPolynomial ι LL → LL := fun x => if h : x ∈ t then g ⟨x, h⟩ else 0 with hfdef
      have hfsum : ∑ x ∈ t, f x • x = 0 := by
        rw [← hg, ← Finset.sum_coe_sort t]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [hfdef, x.2]
      obtain ⟨j, hj, hfj, hpiv⟩ := exists_pivot R0
        (fun x => by
          by_cases hx : algebraMap LL Kf x ∈ A
          · exact Or.inl ((hR0 x).mpr hx)
          · right
            rw [hR0, map_inv₀]
            exact (hA _).resolve_left hx) f t ⟨i0, i0.2, by simpa [hfdef] using hi0⟩
      have hcard : (t.erase j).card = k := by
        rw [Finset.card_erase_of_mem hj, ht]
        simp
      set c' : MvPolynomial ι LL → Kf := fun x => c x - c j * algebraMap LL Kf (f x / f j) with hc'def
      have hc' : ∀ x ∈ (t.erase j), c' x ∈ A := by
        intro x hx
        have hx' := Finset.mem_of_mem_erase hx
        have hr : algebraMap LL Kf (f x / f j) ∈ A := (hR0 _).mp (hpiv x hx')
        exact A.sub_mem (hc x hx') (A.mul_mem (hc j hj) hr)
      have hrel : ∑ x ∈ t.erase j, (f x / f j) • x = -j := by
        have h1 := hfsum
        rw [← Finset.add_sum_erase t _ hj] at h1
        have h2 : ∑ x ∈ t.erase j, (f x / f j) • x = (f j)⁻¹ • ∑ x ∈ t.erase j, f x • x := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [smul_smul, div_eq_mul_inv, mul_comm]
        rw [h2, eq_neg_of_add_eq_zero_right h1, smul_neg, smul_smul, inv_mul_cancel₀ hfj, one_smul]
      have hQ' : ∑ x ∈ (t.erase j), C (c' x) * map (algebraMap LL Kf) x = map (algebraMap LL Kf) Q := by
        rw [← hQ, ← Finset.add_sum_erase t _ hj]
        simp only [hc'def, map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
        have e1 : ∑ x ∈ (t.erase j), C (c j) * C (algebraMap LL Kf (f x / f j)) * map (algebraMap LL Kf) x =
            C (c j) * map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, mul_assoc]
        rw [e1]
        have e2 : map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x) = -map (algebraMap LL Kf) j := by
          rw [hrel, map_neg]
        rw [e2]
        ring
      have hmem := ih (t.erase j) hcard c' hc' Q hQ'
      exact Submodule.span_mono (by
        intro x hx
        exact Finset.mem_of_mem_erase hx) hmem

end Desc

theorem descVal : DescVal := by
  intro LL Kf O ι _ _ _ _ _ _ _ e R0 hR0 S Q hQ
  classical
  letI : Algebra LL Kf := e.toAlgebra
  have he : ∀ x, algebraMap LL Kf x = e x := fun x => rfl
  let A : Subring Kf := (algebraMap O Kf).range
  have hA : ∀ x : Kf, x ∈ A ∨ x⁻¹ ∈ A := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger O x with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r, hr⟩
    · exact Or.inr ⟨r, hr⟩
  have hR0' : ∀ x, x ∈ R0 ↔ algebraMap LL Kf x ∈ A := by
    intro x
    rw [hR0 x, he]
    rfl
  obtain ⟨cc, hsupp, hsum⟩ := Submodule.mem_span_set.mp hQ
  have hpre : ∀ y ∈ cc.support, ∃ q ∈ S, MvPolynomial.map e q = y := fun y hy => hsupp hy
  choose! qof hqS hqy using hpre
  have htS : ((cc.support.image qof : Finset (MvPolynomial ι LL)) : Set (MvPolynomial ι LL)) ⊆ S := by
    intro q hq
    rw [Finset.coe_image] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    exact hqS y hy
  have hinjOn : Set.InjOn qof (cc.support : Set (MvPolynomial ι Kf)) := by
    intro y hy y' hy' h
    rw [← hqy y hy, ← hqy y' hy', h]
  let c' : MvPolynomial ι LL → Kf := fun q => algebraMap O Kf (cc (MvPolynomial.map e q))
  have hc' : ∀ q ∈ cc.support.image qof, c' q ∈ A := fun q _ => ⟨_, rfl⟩
  have hrel : ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map (algebraMap LL Kf) q =
      MvPolynomial.map (algebraMap LL Kf) Q := by
    show ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map e q = MvPolynomial.map e Q
    rw [Finset.sum_image hinjOn, ← hsum, Finsupp.sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [c', hqy y hy]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]
  exact Submodule.span_mono htS
    (desc_main A hA R0 hR0' (cc.support.image qof).card (cc.support.image qof) rfl c' hc' Q hrel)

end Formalism.L2.G.RelativeIndexFlags
end
end

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem int_inj : Function.Injective (algebraMap ℤ ℂ) := (algebraMap ℤ ℂ).injective_int

def OddId {m : ℕ} (lam : Fin (m + 1) → ℤ) (ft f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ) : Prop :=
  ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit z.det →
    z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) (map (Int.castRingHom ℂ) ft) =
      (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) *
        eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) (map (Int.castRingHom ℂ) f)

theorem oddZ (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (hodd : OddFact (K := ℂ) ℤ m lam) :
    (∀ f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      ∃ ft ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam), OddId lam ft f) ∧
    (∀ ft ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam),
      ∃ f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)), OddId lam ft f) := by
  have h1 : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det := by simp
  have hg' : IsUnit (((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹)ᵀ).det := by simp
  have hst := lamStar_anti lam hlam
  have hi1 : ∀ w : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹ * w = w := by
    intro w; simp
  have hi2 : ∀ w : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      (((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹)ᵀ)⁻¹ * w = w := by
    intro w; simp
  obtain ⟨hA, hB⟩ := hodd 1 h1
  constructor
  · intro f hf
    obtain ⟨F, hF, hev⟩ := hB _ (rowAct_weyl_mem_descentLattice int_inj m (lamStar lam) hst _ hg' f hf)
    obtain ⟨ft, hft, hev2⟩ := even_block_weyl_mem int_inj m lam hlam 1 h1 F hF
    refine ⟨ft, hft, fun z hz => ?_⟩
    have e1 := hev2 z
    rw [hi1] at e1
    have e3 := even_block_row_action_eval (((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹)ᵀ) (lamStar lam (Fin.last m))
      (map (algebraMap ℤ ℂ) f) (revCol (z⁻¹)ᵀ)
    rw [hi2] at e3
    exact e1.symm.trans ((hev z hz).trans e3)
  · intro ft hft
    obtain ⟨F', hF', hev⟩ := hA _ (rowAct_weyl_mem_descentLattice int_inj m lam hlam 1 h1 ft hft)
    obtain ⟨f, hf, hev2⟩ := even_block_weyl_mem int_inj m (lamStar lam) hst _ hg' F' hF'
    refine ⟨f, hf, fun z hz => ?_⟩
    have e0 := even_block_row_action_eval (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (lam (Fin.last m)) (map (algebraMap ℤ ℂ) ft) z
    rw [hi1] at e0
    have e4 := hev2 (revCol (z⁻¹)ᵀ)
    rw [hi2] at e4
    exact e0.symm.trans ((hev z hz).trans e4)

theorem detShift_eq {m : ℕ} (lam : DomWeight (m + 1)) : lam.detShift = lam.w (Fin.last m) := by
  unfold DomWeight.detShift
  rw [dite_eq_left (Nat.succ_pos m)]
  rfl

theorem natW_eq {m : ℕ} (lam : DomWeight (m + 1)) : lam.natW = nuOf lam.w := by
  funext i
  unfold DomWeight.natW nuOf
  rw [detShift_eq]

theorem core_intSpanG_smul {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL] (embLL : LL →+* ℂ) (R0 : Subring LL)
    (lam : Tau → DomWeight n) (a : LL) (ha : a ∈ R0) {Pp : MvPolynomial (Tau × Fin n × Fin n) ℂ}
    (hP : Pp ∈ IntSpanG embLL R0 lam) : embLL a • Pp ∈ IntSpanG embLL R0 lam := by
  unfold IntSpanG at hP ⊢
  induction hP using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hq
    exact AddSubgroup.subset_closure ⟨a * s, f, R0.mul_mem ha hs, hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

section Ev

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {LL : Type} [Field LL]
  (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (lam : Tau → DomWeight (P.m + 1))
  (M N : Tau → GL (Fin (P.m + 1)) LL) (embLL : LL →+* ℂ)

abbrev mcOf {k : ℕ} (M : Tau → GL (Fin k) LL) (embLL : LL →+* ℂ) : Tau → Matrix (Fin k) (Fin k) ℂ :=
  fun τ => (M τ : Matrix (Fin k) (Fin k) LL).map embLL

abbrev kcOf {k : ℕ} (M N : Tau → GL (Fin k) LL) (embLL : LL →+* ℂ) : Tau → Matrix (Fin k) (Fin k) ℂ :=
  fun τ => (((N τ)⁻¹ * M τ : GL (Fin k) LL) : Matrix (Fin k) (Fin k) LL).map embLL

def BlockRealisation (x : Σ v : Fin P.nV, Fin (P.n' v)) (f ft : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) : Prop :=
  ∀ y : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ, (∀ τ, IsUnit (y τ).det) →
    (zAt P rfl pos (mcOf M embLL) y x.1 x.2).det ^ (eAt P x.1 x.2) *
        eval (fun a => zAt P rfl pos (mcOf M embLL) y x.1 x.2 a.1 a.2) (map embLL (bl P rfl pos N x.1 x.2 f)) =
      (kcOf M N embLL (pos x) * y (pos x)).det ^ (lam (pos x)).detShift *
        eval (fun a => (kcOf M N embLL (pos x) * y (pos x)) a.1 a.2) (map (Int.castRingHom ℂ) ft)

theorem blk_lhs (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (zz : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) :
    zz.det ^ (eAt P v s) * eval (fun a => zz a.1 a.2) (map embLL (bl P rfl pos N v s f)) =
      ((niAt P rfl pos N v s).map embLL * zz).det ^ (eAt P v s) *
        eval (fun a => ((niAt P rfl pos N v s).map embLL * zz) a.1 a.2) (map (Int.castRingHom ℂ) f) := by
  rw [map_bl, even_block_row_action_eval, nAt_map_inv]

theorem even_mat (v : Fin P.nV) (s : Fin (P.n' v)) (hs : Even s.val)
    (y : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) :
    (niAt P rfl pos N v s).map embLL * zAt P rfl pos (mcOf M embLL) y v s =
      kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩) := by
  unfold niAt zAt reM
  rw [if_pos hs, if_pos hs, sub_rfl, sub_rfl]
  show _ = ((((N (pos ⟨v, s⟩))⁻¹ * M (pos ⟨v, s⟩) : GL (Fin (P.m + 1)) LL) :
    Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL) * _
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem odd_mat (v : Fin P.nV) (s : Fin (P.n' v)) (hs : ¬ Even s.val)
    (y : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) :
    (niAt P rfl pos N v s).map embLL * zAt P rfl pos (mcOf M embLL) y v s =
      revCol (((kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))⁻¹)ᵀ) := by
  have hN : ((((N (pos ⟨v, s⟩))⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL)⁻¹ =
      (N (pos ⟨v, s⟩) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one embLL embLL.map_zero embLL.map_one]
  have hK : (kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))⁻¹ =
      (mcOf M embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))⁻¹ *
        (N (pos ⟨v, s⟩) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL := by
    show (((((N (pos ⟨v, s⟩))⁻¹ * M (pos ⟨v, s⟩) : GL (Fin (P.m + 1)) LL) :
      Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL) * y (pos ⟨v, s⟩))⁻¹ = _
    rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_inv_rev, hN]
  unfold niAt zAt reM revCol
  rw [if_neg hs, if_neg hs, sub_rfl, sub_rfl, hK, Matrix.transpose_mul,
    Matrix.submatrix_mul _ _ id id Fin.rev Function.bijective_id, Matrix.submatrix_id_id, Matrix.transpose_map]

theorem blk_ev (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam)
    (hw : WtTie P rfl pos lam) (x : Σ v : Fin P.nV, Fin (P.n' v)) :
    (∀ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 x.1) x.2)),
      ∃ ft ∈ delSq ℤ (P.m + 1) (lam (pos x)), BlockRealisation P pos lam M N embLL x f ft) ∧
    (∀ ft ∈ delSq ℤ (P.m + 1) (lam (pos x)),
      ∃ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 x.1) x.2)), BlockRealisation P pos lam M N embLL x f ft) := by
  obtain ⟨v, s⟩ := x
  have hl0 : P.lam0 v s = (lam (pos ⟨v, s⟩)).w := funext fun i => hw v s i
  have hdel : delSq ℤ (P.m + 1) (lam (pos ⟨v, s⟩)) = weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (P.lam0 v s)) := by
    unfold delSq; rw [natW_eq, hl0]
  have hsh : (lam (pos ⟨v, s⟩)).detShift = P.lam0 v s (Fin.last P.m) := by rw [detShift_eq, hl0]
  show (∀ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)), _) ∧
    (∀ ft ∈ delSq ℤ (P.m + 1) (lam (pos ⟨v, s⟩)),
      ∃ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)), _)
  rw [hdel]
  by_cases hs : Even s.val
  · have hla := lamAt_even (P.lam0 v) s hs
    have hid : ∀ f, BlockRealisation P pos lam M N embLL ⟨v, s⟩ f f := by
      intro f y hy
      show (zAt P rfl pos (mcOf M embLL) y v s).det ^ (eAt P v s) *
        eval (fun a => zAt P rfl pos (mcOf M embLL) y v s a.1 a.2) (map embLL (bl P rfl pos N v s f)) = _
      rw [blk_lhs, even_mat P pos M N embLL v s hs y, hsh]
      unfold eAt
      rw [hla]
    rw [hla]
    exact ⟨fun f hf => ⟨f, hf, hid f⟩, fun f hf => ⟨f, hf, hid f⟩⟩
  · have hla := lamAt_odd (P.lam0 v) s hs
    obtain ⟨hA, hB⟩ := oddZ P.m (P.lam0 v s) (P.dom v s) (hodd _ _ (P.dom v s))
    have hid : ∀ f ft, OddId (P.lam0 v s) ft f → BlockRealisation P pos lam M N embLL ⟨v, s⟩ f ft := by
      intro f ft h y hy
      show (zAt P rfl pos (mcOf M embLL) y v s).det ^ (eAt P v s) *
        eval (fun a => zAt P rfl pos (mcOf M embLL) y v s a.1 a.2) (map embLL (bl P rfl pos N v s f)) = _
      rw [blk_lhs, odd_mat P pos M N embLL v s hs y, hsh]
      have hz : IsUnit (kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩)).det := by
        rw [Matrix.det_mul]; exact (gl_map_det embLL _).mul (hy _)
      have h2 := h _ hz
      unfold eAt
      rw [hla]
      exact h2.symm
    rw [hla]
    exact ⟨fun f hf => let ⟨ft, hft, h⟩ := hA f hf; ⟨ft, hft, hid f ft h⟩,
      fun ft hft => let ⟨f, hf, h⟩ := hB ft hft; ⟨f, hf, hid f ft h⟩⟩

theorem fnOf_ten (G K : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)
    (g : Tau → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ) (z : Frames G) :
    fnOf G (shiftOf lam) K (ten g) z =
      ∏ τ, ((K τ * z.1 τ).det ^ (lam τ).detShift * eval (fun a => (K τ * z.1 τ) a.1 a.2) (g τ)) := by
  rw [Finset.prod_mul_distrib]
  show (∏ τ, (K τ * z.1 τ).det ^ shiftOf lam τ) *
    eval (fun x : Tau × Fin (P.m + 1) × Fin (P.m + 1) => (K x.1 * z.1 x.1) x.2.1 x.2.2) (ten g) = _
  simp only [ten, map_prod, eval_rename, Function.comp_def, shiftOf]

theorem evC_gen (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (ft : Tau → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (hid : ∀ x : Σ v : Fin P.nV, Fin (P.n' v), BlockRealisation P pos lam M N embLL x (f x.1 x.2) (ft (pos x))) (z : Frames G) :
    evC P rfl pos G (mcOf M embLL) (map embLL (gen P rfl pos N f)) z =
      fnOf G (shiftOf lam) (kcOf M N embLL) (ten fun τ => map (Int.castRingHom ℂ) (ft τ)) z := by
  rw [map_gen, evC_prod, fnOf_ten, ← pos.prod_comp, Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => hid ⟨v, s⟩ z.1 z.2

theorem span_to_int (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam)
    (hw : WtTie P rfl pos lam) (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (R0 : Subring LL) (Q : XR P LL)
    (hQ : Q ∈ Submodule.span R0 (genSet P rfl pos N)) :
    ∃ Pp ∈ IntSpanG embLL R0 lam, ∀ z : Frames G,
      evC P rfl pos G (mcOf M embLL) (map embLL Q) z = fnOf G (shiftOf lam) (kcOf M N embLL) Pp z := by
  induction hQ using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨f, hf, rfl⟩ := hq
    choose ft0 hft0 hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
      (blk_ev P pos lam M N embLL hodd hw x).1 (f x.1 x.2) (hf x.1 x.2)
    refine ⟨embLL 1 • ten (fun τ => map (Int.castRingHom ℂ) (ft0 (pos.symm τ))),
      AddSubgroup.subset_closure ⟨1, fun τ => ft0 (pos.symm τ), R0.one_mem, fun τ => ?_, rfl⟩, fun z => ?_⟩
    · have h1 := hft0 (pos.symm τ)
      rwa [pos.apply_symm_apply] at h1
    · rw [map_one, one_smul]
      refine evC_gen P pos lam M N embLL G f (fun τ => ft0 (pos.symm τ)) (fun x => ?_) z
      show BlockRealisation P pos lam M N embLL x (f x.1 x.2) (ft0 (pos.symm (pos x)))
      rw [pos.symm_apply_apply]
      exact hev x
  | zero => exact ⟨0, zero_mem _, fun z => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA, e1⟩ := ha
    obtain ⟨B, hB, e2⟩ := hb
    exact ⟨A + B, add_mem hA hB, fun z => by
      rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, e1 z, e2 z]⟩
  | smul r a _ ha =>
    obtain ⟨A, hA, e1⟩ := ha
    refine ⟨embLL r.1 • A, core_intSpanG_smul embLL R0 lam r.1 r.2 hA, fun z => ?_⟩
    rw [Subring.smul_def, Cmp.map_smul', map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, e1 z]

theorem int_to_span (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam)
    (hw : WtTie P rfl pos lam) (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (R0 : Subring LL)
    (Pp : MvPolynomial (Tau × Fin (P.m + 1) × Fin (P.m + 1)) ℂ) (hP : Pp ∈ IntSpanG embLL R0 lam) :
    ∃ Q ∈ Submodule.span R0 (genSet P rfl pos N), ∀ z : Frames G,
      evC P rfl pos G (mcOf M embLL) (map embLL Q) z = fnOf G (shiftOf lam) (kcOf M N embLL) Pp z := by
  unfold IntSpanG at hP
  induction hP using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r, ft, hr, hft, rfl⟩ := hq
    choose f hf hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
      (blk_ev P pos lam M N embLL hodd hw x).2 (ft (pos x)) (hft (pos x))
    refine ⟨(⟨r, hr⟩ : R0) • gen P rfl pos N (fun v s => f ⟨v, s⟩),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun v s => f ⟨v, s⟩, fun v s => hf ⟨v, s⟩, rfl⟩), fun z => ?_⟩
    rw [Subring.smul_def, Cmp.map_smul', map_smul, map_smul, Pi.smul_apply, Pi.smul_apply]
    congr 1
    exact evC_gen P pos lam M N embLL G (fun v s => f ⟨v, s⟩) ft (fun x => hev x) z
  | zero => exact ⟨0, zero_mem _, fun z => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA, e1⟩ := ha
    obtain ⟨B, hB, e2⟩ := hb
    exact ⟨A + B, add_mem hA hB, fun z => by
      rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, e1 z, e2 z]⟩
  | neg a _ ha =>
    obtain ⟨A, hA, e1⟩ := ha
    exact ⟨-A, neg_mem hA, fun z => by
      rw [map_neg, map_neg, map_neg, Pi.neg_apply, Pi.neg_apply, e1 z]⟩

end Ev

end Formalism.L2.G.RelativeIndexFlags.Core

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags.Core

theorem weylLatticeDescent_of_valuation (hD : DescVal)
    (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam) : WeylLatticeDescent := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G embLL e R0 hfr hR0 lam hw M N L HL Q
  subst h
  unfold CoreAt
  rw [mem_htupW_iff P rfl pos N hD hfr e R0 hR0 L HL Q]
  constructor
  · intro hQ
    exact span_to_int P pos lam M N embLL hodd hw G R0 Q hQ
  · rintro ⟨Pp, hPp, hev⟩
    obtain ⟨Q', hQ', hev'⟩ := int_to_span P pos lam M N embLL hodd hw G R0 Pp hPp
    have h0 := Formalism.L2.G.evC_inj P rfl pos G (mcOf M embLL) (fun τ => gl_map_det embLL (M τ))
      (map embLL Q - map embLL Q') (by
        funext z
        rw [map_sub, Pi.sub_apply, hev z, hev' z, sub_self]
        rfl)
    have h1 : Q = Q' := map_injective embLL embLL.injective (sub_eq_zero.1 h0)
    rw [h1]; exact hQ'

theorem weylLatticeDescent_of_integral_models
    (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam) : WeylLatticeDescent :=
  weylLatticeDescent_of_valuation descVal hodd

end Formalism.L2.G.RelativeIndexFlags
end
end

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

theorem oddFact_pf {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    OddFact (K := K) O m lam := oddDualWeyl O m lam

theorem weylLatticeDescent_holds : WeylLatticeDescent := weylLatticeDescent_of_integral_models fun m lam _ => oddFact_pf ℤ m lam

end Formalism.L2.G.RelativeIndexFlags

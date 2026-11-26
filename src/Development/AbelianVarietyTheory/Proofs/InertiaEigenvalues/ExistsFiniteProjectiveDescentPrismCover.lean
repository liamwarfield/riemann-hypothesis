module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleDescentFiniteLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCover
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mem_span_range_of_isBaseChange {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (w : N) : w ∈ Submodule.span S (Set.range f) := by
  obtain ⟨y, rfl⟩ := hf.equiv.surjective w
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s x => rw [hf.equiv_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem le_of_span_eq_top_of_isBaseChange {R S N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (P Q : Submodule R N) (hPQ : P ≤ Q) (hQ : IsBaseChange S Q.subtype)
    (hP : Submodule.span S (P : Set N) = ⊤) : Q ≤ P := by
  let ι := Submodule.inclusion hPQ
  have hs : Function.Surjective (ι.lTensor S) := by
    intro y
    have hv : hQ.equiv y ∈ Submodule.span S (P : Set N) := hP ▸ Submodule.mem_top
    have key : ∀ v ∈ Submodule.span S (P : Set N), ∃ y' : S ⊗[R] P, hQ.equiv (ι.baseChange S y') = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp [ι, hQ.equiv_tmul]⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simp [ha, hb]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c • a, by simp [ha]⟩
    obtain ⟨y', hy'⟩ := key _ hv
    exact ⟨y', by rw [← LinearMap.baseChange_eq_ltensor]; exact hQ.equiv.injective hy'⟩
  have hι := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S ι).mp hs
  intro x hx
  obtain ⟨y, hy⟩ := hι ⟨x, hx⟩
  have hx' : (y : N) = x := congrArg Subtype.val hy
  exact hx' ▸ y.2

theorem lift_solution_succ_of_descent {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C)
    (p q : Hom C D) (hcomm : p.comp h = q.comp h) (m : ℕ) (hff : (qmap h m).FaithfullyFlat)
    (ε : Matrix (Fin d) (Fin d) D.A)
    (H : ∀ k : ℕ, letI := (qmap h k).toAlgebra
      ∃ N : Submodule (B.A ⧸ adI B ^ k) (Fin d → C.A ⧸ adI C ^ k),
        (∀ z, z ∈ N ↔ (fun i => qmap p k (z i)) =
          (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec fun i => qmap q k (z i)) ∧
        IsBaseChange (C.A ⧸ adI C ^ k) N.subtype)
    (z : Fin d → C.A) (hz : ∀ i, p.f (z i) - ε.mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧
      ∀ i, p.f (z' i) - ε.mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  have hmem : ∀ (k : ℕ) (w : Fin d → C.A),
      ((fun i => qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i))) =
        (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i)))) ↔
      ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ k := by
    intro k w
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    have e1 : qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i)) = Ideal.Quotient.mk (adI D ^ k) (p.f (w i)) :=
      qmap_mk p k _
    have e2 : (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec
        (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i))) i =
        Ideal.Quotient.mk (adI D ^ k) (ε.mulVec (fun j => q.f (w j)) i) := by
      simp only [qmap_mk]
      exact (RingHom.map_mulVec (Ideal.Quotient.mk (adI D ^ k)) ε (fun j => q.f (w j)) i).symm
    rw [e1, e2]
    exact Ideal.Quotient.eq
  letI alg0 : Algebra (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := (qmap h m).toAlgebra
  letI alg1 : Algebra (B.A ⧸ adI B ^ (m + 1)) (C.A ⧸ adI C ^ (m + 1)) := (qmap h (m + 1)).toAlgebra
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := hff
  obtain ⟨N, hN, hbN⟩ := H m
  obtain ⟨N', hN', hbN'⟩ := H (m + 1)
  have hpq : ∀ b : B.A, p.f (h.f b) = q.f (h.f b) := fun b => congrArg (fun g : Hom B D => g.f b) hcomm
  let P : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m) :=
    { carrier := {x | ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = x ∧
        ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ (m + 1)}
      zero_mem' := ⟨0, by funext i; simp, fun i => by
        have e : (fun j => q.f ((0 : Fin d → C.A) j)) = 0 := funext fun j => by simp
        rw [e, Matrix.mulVec_zero]
        simp⟩
      add_mem' := by
        rintro _ _ ⟨w₁, rfl, h₁⟩ ⟨w₂, rfl, h₂⟩
        refine ⟨w₁ + w₂, by funext i; simp, fun i => ?_⟩
        have := Ideal.add_mem _ (h₁ i) (h₂ i)
        convert this using 1
        have e : (fun j => q.f ((w₁ + w₂) j)) = (fun j => q.f (w₁ j)) + (fun j => q.f (w₂ j)) := by
          funext j; simp
        rw [e, Matrix.mulVec_add]
        simp only [Pi.add_apply, map_add (f := _)]
        ring
      smul_mem' := by
        rintro c _ ⟨w, rfl, hw⟩
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        refine ⟨fun i => h.f b * w i, ?_, fun i => ?_⟩
        · funext i
          simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, qmap_mk]
        · have := Ideal.mul_mem_left _ (q.f (h.f b)) (hw i)
          convert this using 1
          have e : (fun j => q.f (h.f b * w j)) = q.f (h.f b) • (fun j => q.f (w j)) := by
            funext j; simp
          rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, hpq, mul_sub] }
  have hPN : P ≤ N := by
    rintro _ ⟨w, rfl, hw⟩
    exact (hN _).2 ((hmem m w).2 fun i => Ideal.pow_le_pow_right (Nat.le_succ m) (hw i))
  have hspan : Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    let πC := Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m) : adI C ^ (m + 1) ≤ adI C ^ m)
    let r : (Fin d → C.A ⧸ adI C ^ (m + 1)) → (Fin d → C.A ⧸ adI C ^ m) := fun y i => πC (y i)
    have hr : ∀ y ∈ Submodule.span (C.A ⧸ adI C ^ (m + 1)) (Set.range N'.subtype),
        r y ∈ Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨x, hxN⟩, rfl⟩ := hx
        apply Submodule.subset_span
        obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk _ (w i)) = x :=
          ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
            funext fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec⟩
        exact ⟨w, by funext i; simp [r, πC], (hmem (m + 1) w).1 ((hN' _).1 hxN)⟩
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i; simp [r]
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy using 1
        funext i; simp [r]
      | smul c x _ hx =>
        convert Submodule.smul_mem _ (πC c) hx using 1
        funext i; simp [r]
    obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = v :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    have := hr (fun i => Ideal.Quotient.mk _ (w i)) (mem_span_range_of_isBaseChange hbN' _)
    convert this using 1
    funext i; simp [r, πC]
  have hNP : N ≤ P := le_of_span_eq_top_of_isBaseChange P N hPN hbN hspan
  have hzN : (fun i => Ideal.Quotient.mk (adI C ^ m) (z i)) ∈ N := (hN _).2 ((hmem m z).2 hz)
  obtain ⟨w, hw, hwE⟩ := hNP hzN
  exact ⟨w, fun i => Ideal.Quotient.eq.1 (congrFun hw i), hwE⟩

theorem lift_solution_succ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  intro l _ K bk d S B C D h f p q hcov hpo m z hz
  refine lift_solution_succ_of_descent h p q hpo.comm m (hcov.ff m) _ (fun k => ?_) z hz
  exact (GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p q hcov hpo k).imp fun N hN => ⟨hN.1, hN.2.2.2⟩

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_stratifiedSolution_succ_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  first | exact @GlobalTheory.BSP.lift_solution_succ | exact GlobalTheory.BSP.lift_solution_succ | (intros; apply GlobalTheory.BSP.lift_solution_succ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdeal
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_smul_top_eq {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A A)) = I ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem mulVec_mem_of_mem {B : Type} [CommRing B] {d : ℕ} (E : Matrix (Fin d) (Fin d) B) (J : Ideal B)
    (v : Fin d → B) (hv : ∀ j, v j ∈ J) (i : Fin d) : E.mulVec v i ∈ J := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)

theorem lift_solution_of_step {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (hA : IsPrecomplete I A) (hB : IsHausdorff J B) {d : ℕ} (p q : A →+* B)
    (hp : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap p) (hq : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap q)
    (E : Matrix (Fin d) (Fin d) B)
    (step : ∀ (m : ℕ) (z : Fin d → A), (∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ m) →
      ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ m) ∧
        ∀ i, p (z' i) - E.mulVec (fun j => q (z' j)) i ∈ J ^ (m + 1))
    (z : Fin d → A) (hz : ∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ 1) :
    ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ 1) ∧
      (fun i => p (z' i)) = E.mulVec (fun j => q (z' j)) := by

  let res : (Fin d → A) → Fin d → B := fun w i => p (w i) - E.mulVec (fun j => q (w j)) i
  have hres_sub : ∀ (w w' : Fin d → A) (i : Fin d),
      res w i - res w' i = p (w i - w' i) - E.mulVec (fun j => q (w j - w' j)) i := by
    intro w w' i
    have : (fun j => q (w j - w' j)) = (fun j => q (w j)) - (fun j => q (w' j)) := by
      funext j; simp
    show p (w i) - E.mulVec (fun j => q (w j)) i - (p (w' i) - E.mulVec (fun j => q (w' j)) i) = _
    rw [this, Matrix.mulVec_sub, Pi.sub_apply, map_sub]
    ring

  have hseq : ∃ g : ℕ → (Fin d → A), g 0 = z ∧ (∀ k i, res (g k) i ∈ J ^ (k + 1)) ∧
      ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := by
    let G : (k : ℕ) → {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)} := fun k =>
      Nat.rec (motive := fun k => {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}) ⟨z, hz⟩
        (fun k w => ⟨Classical.choose (step (k + 1) w.1 w.2),
          (Classical.choose_spec (step (k + 1) w.1 w.2)).2⟩) k
    refine ⟨fun k => (G k).1, rfl, fun k => (G k).2, fun k i => ?_⟩
    exact (Classical.choose_spec (step (k + 1) (G k).1 (G k).2)).1 i
  let g := Classical.choose hseq
  have hg0 : g 0 = z := (Classical.choose_spec hseq).1
  have hgres : ∀ k i, res (g k) i ∈ J ^ (k + 1) := (Classical.choose_spec hseq).2.1
  have hgd : ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := (Classical.choose_spec hseq).2.2

  have hcau : ∀ i {m n : ℕ}, m ≤ n → g n i - g m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : g (n + 1) i - g n i ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (hgd n i)
      have := Ideal.add_mem _ h1 ih
      simpa using this

  have hlim : ∀ i, ∃ L : A, ∀ n, g n i - L ∈ I ^ n := by
    intro i
    have h := @IsPrecomplete.prec' A _ I A _ _ hA (fun k => g k i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, pow_smul_top_eq]
      have := hcau i hmn
      rw [← neg_mem_iff, neg_sub] at this
      exact this)
    refine ⟨Classical.choose h, fun n => ?_⟩
    have := Classical.choose_spec h n
    rw [SModEq.sub_mem, pow_smul_top_eq] at this
    exact this
  let z' : Fin d → A := fun i => Classical.choose (hlim i)
  have hz' : ∀ i n, g n i - z' i ∈ I ^ n := fun i => Classical.choose_spec (hlim i)
  refine ⟨z', fun i => ?_, ?_⟩
  · have h1 : g 1 i - z' i ∈ I ^ 1 := hz' i 1
    have h2 : g 1 i - g 0 i ∈ I ^ 1 := hgd 0 i
    rw [hg0] at h2
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  · funext i
    rw [← sub_eq_zero]
    refine hB.haus' _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
    have hd : res (g k) i - res z' i ∈ J ^ k := by
      rw [hres_sub]
      refine Ideal.sub_mem _ (hp k (hz' i k)) ?_
      exact mulVec_mem_of_mem E _ _ (fun j => hq k (hz' j k)) i
    have hr : res (g k) i ∈ J ^ k := Ideal.pow_le_pow_right (by omega) (hgres k i)
    have := Ideal.sub_mem _ hr hd
    simpa [res] using this

theorem lift_solution (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hh : Cover h)
    (hpo : IsPO h h p q) (z : Fin d → C.A)
    (hz : ∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧
      (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) :=
  lift_solution_of_step (adI C) (adI D) C.complete.toIsPrecomplete D.complete.toIsHausdorff p.f q.f
    (adI_pow_le p) (adI_pow_le q) _ (GlobalTheory.T.lift_stratifiedSolution_succ_of_cover l K bk d S B C D h f p q hh hpo) z hz

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdealStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ z : Fin d → C.A, (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧ (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) := by
  first | exact @GlobalTheory.BSP.lift_solution | exact GlobalTheory.BSP.lift_solution | (intros; apply GlobalTheory.BSP.lift_solution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeOfIsBaseChangeQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeOfIsBaseChangeQuotient
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isBaseChange_of_isBaseChange_quotient :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (𝔞 : Ideal S), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] (V : Type) [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V] [Module.Finite S V] [Module.Projective S V] (W : Type) [AddCommGroup W] [Module (S ⧸ 𝔞) W] [Module S W] [Module R W] [IsScalarTower S (S ⧸ 𝔞) W] [IsScalarTower R (S ⧸ 𝔞) W] [IsScalarTower R S W] (u : P →ₗ[R] V) (g : V →ₗ[S] W), IsBaseChange (S ⧸ 𝔞) g → IsBaseChange (S ⧸ 𝔞) (g.restrictScalars R ∘ₗ u) → IsBaseChange S u := by
  intro R S _ _ _ 𝔞 h𝔞 P _ _ _ V _ _ _ _ _ _ W _ _ _ _ _ _ _ u g hg hgu
  have hF : IsBaseChange S (TensorProduct.mk R S P 1) := TensorProduct.isBaseChange R P S
  let w : S ⊗[R] P →ₗ[S] V := hF.lift u
  have hw : ∀ x : P, w (1 ⊗ₜ[R] x) = u x := fun x => hF.lift_eq u x
  have hcomp : (g ∘ₗ w).restrictScalars R ∘ₗ TensorProduct.mk R S P 1 = g.restrictScalars R ∘ₗ u := by
    ext x
    simp [hw]
  have hgw : IsBaseChange (S ⧸ 𝔞) (g ∘ₗ w) := hF.of_comp (hcomp ▸ hgu)
  have heq : ∀ z, hg.equiv (w.baseChange (S ⧸ 𝔞) z) = hgw.equiv z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  have hfun : ⇑(w.baseChange (S ⧸ 𝔞)) = hg.equiv.symm ∘ hgw.equiv := by
    funext z
    simp [← heq z]
  have hbij : Function.Bijective (w.baseChange (S ⧸ 𝔞)) := by
    rw [hfun]
    exact hg.equiv.symm.bijective.comp hgw.equiv.bijective
  have hwb : Function.Bijective w := GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient S 𝔞 h𝔞 (S ⊗[R] P) V w hbij
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective w hwb) (fun x => hw x)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeOfIsBaseChangeQuotientStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_of_isBaseChange_quotient_comp : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (𝔞 : Ideal S), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] (V : Type) [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V] [Module.Finite S V] [Module.Projective S V] (W : Type) [AddCommGroup W] [Module (S ⧸ 𝔞) W] [Module S W] [Module R W] [IsScalarTower S (S ⧸ 𝔞) W] [IsScalarTower R (S ⧸ 𝔞) W] [IsScalarTower R S W] (u : P →ₗ[R] V) (g : V →ₗ[S] W), IsBaseChange (S ⧸ 𝔞) g → IsBaseChange (S ⧸ 𝔞) (g.restrictScalars R ∘ₗ u) → IsBaseChange S u := by
  first | exact @GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient | exact GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient | (intros; apply GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveLiftOfIsAdicComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveLiftOfIsAdicComplete
open GlobalTheory.Prism

namespace GlobalTheory.BSP.LiftProj

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_mem {I J : Ideal A} {x y : Matrix n n A} (hx : ∀ i j, x i j ∈ I) (hy : ∀ i j, y i j ∈ J)
    (i j : n) : (x * y) i j ∈ I * J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hx i k) (hy k j)

theorem mul_mem_right {I : Ideal A} {x : Matrix n n A} (y : Matrix n n A) (hx : ∀ i j, x i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

theorem mul_mem_left {I : Ideal A} {y : Matrix n n A} (x : Matrix n n A) (hy : ∀ i j, y i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k j)

theorem exists_idem (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (x : Matrix n n A)
    (hx : ∀ i j, (x * x - x) i j ∈ 𝔞) :
    ∃ e : Matrix n n A, e * e = e ∧ ∀ i j, (e - x) i j ∈ 𝔞 := by
  let f : ℕ → Matrix n n A := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k i j, (f k * f k - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      intro i j
      rw [e]
      refine mul_mem_right _ (fun i j => ?_) i j
      have := mul_mem ih ih i j
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
  have h2 : ∀ k i j, (f (k + 1) - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k i j
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k) i j
  have h3 : ∀ k m, k ≤ m → ∀ i j, (f m - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro i j; simp
    | succ m hkm ih =>
      intro i j
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e, Matrix.add_apply]
      exact add_mem (Ideal.pow_le_pow_right (by omega) (h2 m i j)) (ih i j)
  have h4 : ∀ i j, ∃ L : A, ∀ k, f k i j - L ∈ 𝔞 ^ k := by
    intro i j
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔞) (fun k => f k i j) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (h3 k m hkm i j))
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Matrix n n A := Matrix.of L
  have hL' : ∀ k i j, (f k - e) i j ∈ 𝔞 ^ k := fun k i j => hL i j k
  refine ⟨e, ?_, fun i j => ?_⟩
  · rw [← sub_eq_zero]
    ext i j
    refine IsHausdorff.haus' (I := 𝔞) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1, Matrix.sub_apply, Matrix.add_apply]
    exact sub_mem (Ideal.pow_le_pow_right (Nat.le_succ k) (h1 k i j))
      (add_mem (mul_mem_right _ (hL' k) i j) (mul_mem_left _ (hL' k) i j))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1, Matrix.sub_apply]
    have a := h2 0 i j
    have b := hL' 1 i j
    rw [zero_add, pow_one] at a
    rw [pow_one] at b
    exact sub_mem a b

theorem exists_idem_lift (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (y : Matrix n n (A ⧸ 𝔞))
    (hy : y * y = y) :
    ∃ e : Matrix n n A, e * e = e ∧ e.map (Ideal.Quotient.mk 𝔞) = y := by
  choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
  have hxy : (y.map g).map (Ideal.Quotient.mk 𝔞) = y := by
    ext i j; simp [hg]
  obtain ⟨e, he, hex⟩ := exists_idem 𝔞 (y.map g) fun i j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : (Ideal.Quotient.mk 𝔞).mapMatrix (y.map g * y.map g - y.map g) = 0 := by
      rw [map_sub, map_mul, RingHom.mapMatrix_apply, hxy, hy, sub_self]
    exact congrFun (congrFun this i) j
  refine ⟨e, he, ?_⟩
  ext i j
  have := (Ideal.Quotient.eq).2 (hex i j)
  simpa [hg] using this

theorem exists_lift : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (N : Type)
    [AddCommGroup N] [Module (A ⧸ 𝔞) N] [Module.Finite (A ⧸ 𝔞) N] [Module.Projective (A ⧸ 𝔞) N],
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module A P) (_ : Module.Finite A P)
      (_ : Module.Projective A P) (u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N), SemiBC u := by
  intro A _ 𝔞 _ N _ _ _ _
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' (A ⧸ 𝔞) N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hs' : ∀ z, p (s z) = z := fun z => LinearMap.congr_fun hs z
  obtain ⟨e, he, hey⟩ := exists_idem_lift 𝔞 (LinearMap.toMatrix' (s ∘ₗ p)) (by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    ext1 z
    ext1
    simp [hs'])
  let red : (Fin n → A) →ₛₗ[Ideal.Quotient.mk 𝔞] (Fin n → A ⧸ 𝔞) :=
    { toFun := fun z i => Ideal.Quotient.mk 𝔞 (z i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun a b => by ext i; simp }
  have red_surj : Function.Surjective red := fun z => by
    choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
    exact ⟨fun i => g (z i), funext fun i => hg (z i)⟩
  let E : (Fin n → A) →ₗ[A] (Fin n → A) := Matrix.toLin' e
  have hEE : ∀ z, E (E z) = E z := fun z => by
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec_mulVec, he]
  have hred : ∀ z, red (E z) = s (p (red z)) := fun z => by
    have h1 : s (p (red z)) = Matrix.toLin' (LinearMap.toMatrix' (s ∘ₗ p)) (red z) := by
      rw [Matrix.toLin'_toMatrix']; rfl
    rw [h1, ← hey]
    ext i
    simp [red, E, Matrix.mulVec, dotProduct]
  let P := LinearMap.range E
  let q : (Fin n → A) →ₗ[A] P := E.rangeRestrict
  have hq : ∀ y : P, q y = y := by
    rintro ⟨_, z, rfl⟩
    exact Subtype.ext (hEE z)
  have hproj : Module.Projective A P := Module.Projective.of_split P.subtype q (LinearMap.ext hq)
  let u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N := p.comp (red.comp P.subtype)
  have hu : ∀ y : P, u y = p (red y) := fun y => rfl
  have u_surj : Function.Surjective u := fun z => by
    obtain ⟨t, ht⟩ := red_surj (s z)
    refine ⟨q t, ?_⟩
    rw [hu]
    change p (red (E t)) = z
    rw [hred, ht, hs', hs']
  refine ⟨P, inferInstance, inferInstance, inferInstance, hproj, u, ?_⟩
  intro Q _ _ v
  let w0 : (Fin n → A ⧸ 𝔞) →ₗ[A ⧸ 𝔞] Q :=
    (Pi.basisFun (A ⧸ 𝔞) (Fin n)).constr ℕ fun i => v (q (Pi.single i 1))
  have hw0 : w0.comp red = v.comp q := by
    refine (Pi.basisFun A (Fin n)).ext fun i => ?_
    have : red (Pi.basisFun A (Fin n) i) = Pi.basisFun (A ⧸ 𝔞) (Fin n) i := by
      ext j
      by_cases h : j = i
      · subst h; simp [red]
      · simp [red, h]
    rw [LinearMap.comp_apply, this, LinearMap.comp_apply, Pi.basisFun_apply A]
    exact Module.Basis.constr_basis _ _ _ _
  have key : ∀ y : P, (w0 ∘ₗ s) (u y) = v y := fun y => by
    have h1 : E y = y := congrArg Subtype.val (hq y)
    rw [hu, LinearMap.comp_apply, ← hred, h1]
    have := LinearMap.congr_fun hw0 (y : Fin n → A)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq] at this
    exact this
  refine ⟨w0 ∘ₗ s, key, fun w hw => ?_⟩
  ext z
  obtain ⟨y, rfl⟩ := u_surj z
  rw [hw, key]

end GlobalTheory.BSP.LiftProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveLiftOfIsAdicCompleteStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_projective_lift_of_isAdicComplete : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (N : Type) [AddCommGroup N] [Module (A ⧸ 𝔞) N] [Module.Finite (A ⧸ 𝔞) N] [Module.Projective (A ⧸ 𝔞) N], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module A P) (_ : Module.Finite A P) (_ : Module.Projective A P) (u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N), SemiBC u := by
  first | exact @GlobalTheory.BSP.LiftProj.exists_lift | exact GlobalTheory.BSP.LiftProj.exists_lift | (intros; apply GlobalTheory.BSP.LiftProj.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveDescentPrismCover
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoverDesc

def solSub {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C) (p q : Hom C D)
    (hpq : p.comp h = q.comp h) (E : Matrix (Fin d) (Fin d) D.A) :
    letI := h.f.toAlgebra; Submodule B.A (Fin d → C.A) :=
  letI := h.f.toAlgebra
  { carrier := {z | (fun i => p.f (z i)) = E.mulVec fun i => q.f (z i)}
    add_mem' := by
      intro a b ha hb
      change (fun i => p.f (a i + b i)) = E.mulVec fun i => q.f (a i + b i)
      have e1 : (fun i => p.f (a i + b i)) = (fun i => p.f (a i)) + fun i => p.f (b i) := by
        funext i; exact map_add _ _ _
      have e2 : (fun i => q.f (a i + b i)) = (fun i => q.f (a i)) + fun i => q.f (b i) := by
        funext i; exact map_add _ _ _
      rw [e1, e2, Matrix.mulVec_add]
      exact congrArg₂ (· + ·) ha hb
    zero_mem' := by
      change (fun i => p.f 0) = E.mulVec fun i => q.f 0
      simp only [map_zero]
      exact (Matrix.mulVec_zero _).symm
    smul_mem' := by
      intro b z hz
      change (fun i => p.f (h.f b * z i)) = E.mulVec fun i => q.f (h.f b * z i)
      have hc : p.f (h.f b) = q.f (h.f b) := congrArg (fun k : Hom B D => k.f b) hpq
      have e1 : (fun i => p.f (h.f b * z i)) = p.f (h.f b) • fun i => p.f (z i) := by
        funext i; exact map_mul _ _ _
      have e2 : (fun i => q.f (h.f b * z i)) = p.f (h.f b) • fun i => q.f (z i) := by
        funext i; rw [map_mul, ← hc]; rfl
      rw [e1, e2, Matrix.mulVec_smul]
      exact congrArg _ hz }

theorem lift_mod {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B C D : Obj l ↥(OL K)}
    (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (v : Fin d → C.A ⧸ adI C ^ 1)
    (hv : (fun i => qmap p 1 (v i)) =
      ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ 1))).mulVec fun i => qmap q 1 (v i)) :
    ∃ z : Fin d → C.A, (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) ∧
      ∀ i, Ideal.Quotient.mk (adI C ^ 1) (z i) = v i := by
  choose z₀ hz₀ using fun i => Ideal.Quotient.mk_surjective (I := adI C ^ 1) (v i)
  obtain rfl : (fun i => Ideal.Quotient.mk (adI C ^ 1) (z₀ i)) = v := funext hz₀
  have hyp : ∀ i, p.f (z₀ i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z₀ j)) i ∈ adI D ^ 1 := by
    intro i
    rw [← Ideal.Quotient.eq]
    have e := congrFun hv i
    simp only [qmap_mk] at e
    exact e.trans (RingHom.map_mulVec _ _ _ i).symm
  have H := GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal l K bk d S B C D h f p q hc hpo z₀ hyp
  exact ⟨H.choose, H.choose_spec.2, fun i => Ideal.Quotient.eq.2 (H.choose_spec.1 i)⟩


set_option maxHeartbeats 1600000 in
theorem exists_descent : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B.A P) (_ : Module.Finite B.A P) (_ : Module.Projective B.A P) (u : P →ₛₗ[h.f] (Fin d → C.A)), SemiBC u ∧ ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i) := by
  intro l _ K bk d S B C h f hc
  obtain ⟨D, p₀, q₀, hpo⟩ := hc.stable.po C h
  have hcomm : ∀ b, p₀.f (h.f b) = q₀.f (h.f b) := fun b => congrArg (fun k : Hom B D => k.f b) hpo.comm
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  obtain ⟨N₁, hN₁, hfin, hproj, hbc⟩ := GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p₀ q₀ hc hpo 1
  haveI hcB : IsAdicComplete (adI B ^ 1) B.A := by rw [pow_one]; exact B.complete
  obtain ⟨P, _, _, _, _, u₁, hu₁⟩ := GlobalTheory.T.exists_finite_projective_lift_of_isAdicComplete B.A (adI B ^ 1) ↥N₁
  letI : Algebra B.A C.A := h.f.toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq (fun b => rfl)
  have hs : ∀ (b : B.A) (y : ↥N₁), (Ideal.Quotient.mk (adI B ^ 1) b) • y = b • y := fun b y => Subtype.ext rfl
  let u₁' : P →ₗ[B.A] ↥N₁ := { toFun := fun x => u₁ x, map_add' := fun x y => u₁.map_add x y, map_smul' := fun b x => (u₁.map_smulₛₗ b x).trans (hs b (u₁ x)) }
  have hb1 : IsBaseChange (B.A ⧸ adI B ^ 1) u₁' := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A (B.A ⧸ adI B ^ 1) P ↥N₁ u₁ u₁' (fun x => rfl)).1 hu₁
  have hb2 := hb1.comp hbc
  let M := solSub h p₀ q₀ hpo.comm (S.ε (p₀.comp f) (q₀.comp f))
  have memM : ∀ z, z ∈ M ↔ (fun i => p₀.f (z i)) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec fun i => q₀.f (z i) := fun z => Iff.rfl
  have memN : ∀ z : Fin d → C.A, z ∈ M → (fun i => Ideal.Quotient.mk (adI C ^ 1) (z i)) ∈ N₁ := by
    intro z hz
    rw [hN₁]
    funext i
    simp only [qmap_mk]
    have e : p₀.f (z i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (z j)) i := congrFun ((memM z).1 hz) i
    exact (congrArg (Ideal.Quotient.mk (adI D ^ 1)) e).trans (RingHom.map_mulVec _ _ _ i)
  let π : M →ₗ[B.A] ↥N₁ :=
    { toFun := fun z => ⟨fun i => Ideal.Quotient.mk (adI C ^ 1) (z.1 i), memN z.1 z.2⟩
      map_add' := fun a b => Subtype.ext (funext fun i => map_add _ _ _)
      map_smul' := fun b z => Subtype.ext (funext fun i => map_mul _ _ _) }
  have hπ : Function.Surjective π := by
    intro n
    have H := lift_mod S h f p₀ q₀ hc hpo n.1 ((hN₁ n.1).1 n.2)
    exact ⟨⟨H.choose, (memM _).2 H.choose_spec.1⟩, Subtype.ext (funext H.choose_spec.2)⟩
  have HG := Module.projective_lifting_property π u₁' hπ
  let g := HG.choose
  have hg : π ∘ₗ g = u₁' := HG.choose_spec
  let u' : P →ₗ[B.A] (Fin d → C.A) := M.subtype ∘ₗ g
  let u : P →ₛₗ[h.f] (Fin d → C.A) :=
    { toFun := fun x => u' x, map_add' := fun x y => u'.map_add x y, map_smul' := fun b x => u'.map_smul b x }
  have huM : ∀ x, u x ∈ M := fun x => (g x).2
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, u, ?_, ?_⟩
  · haveI := C.complete
    have hV : IsBaseChange C.A u' := by
      have hgq := (IsBaseChange.linearMap C.A (C.A ⧸ adI C ^ 1)).finitePow (Fin d)
      refine GlobalTheory.T.isBaseChange_of_isBaseChange_quotient_comp B.A C.A (adI C ^ 1) ?_ P (Fin d → C.A) _ u' _ hgq ?_
      · exact le_trans (Ideal.pow_le_self one_ne_zero) (IsAdicComplete.le_jacobson_bot _)
      · have heq : ((Algebra.linearMap C.A (C.A ⧸ adI C ^ 1)).compLeft (Fin d)).restrictScalars B.A ∘ₗ u' =
            (N₁.subtype.restrictScalars B.A).comp u₁' := by
          refine LinearMap.ext fun x => funext fun i => ?_
          exact congrArg (fun y : ↥N₁ => y.1 i) (LinearMap.congr_fun hg x)
        rw [heq]; exact hb2
    exact (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A C.A P (Fin d → C.A) u u' (fun x => rfl)).2 hV
  · intro Q p q hpq x
    have HC := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C C D h h p₀ q₀ hpo Q p q hpq
    obtain ⟨c, ⟨hcp, hcq⟩, -⟩ := HC
    subst hcp hcq
    have hx := (memM _).1 (huM x)
    rw [show (c.comp p₀).comp f = c.comp (p₀.comp f) from rfl, show (c.comp q₀).comp f = c.comp (q₀.comp f) from rfl,
      ← S.ε_nat c]
    funext i
    change c.f (p₀.f (u x i)) = _
    have e : p₀.f (u x i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (u x j)) i := congrFun hx i
    rw [e, RingHom.map_mulVec]
    rfl

end GlobalTheory.BSP.CoverDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveDescentPrismCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteProjective_descent_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B.A P) (_ : Module.Finite B.A P) (_ : Module.Projective B.A P) (u : P →ₛₗ[h.f] (Fin d → C.A)), SemiBC u ∧ ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i) := by
  first | exact @GlobalTheory.BSP.CoverDesc.exists_descent | exact GlobalTheory.BSP.CoverDesc.exists_descent | (intros; apply GlobalTheory.BSP.CoverDesc.exists_descent <;> assumption)
end

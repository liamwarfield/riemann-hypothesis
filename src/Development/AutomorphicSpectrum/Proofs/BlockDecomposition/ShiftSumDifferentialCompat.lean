module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBOfSub

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomology
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomology
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShiftCoh

variable {K : Type} [Field K]

def ev (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m where
  toFun y := y ⟨m, h⟩
  invFun x := fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext ⟨m', h'⟩
    obtain rfl : m' = m := by omega
    rfl
  right_inv _ := rfl

theorem ev_apply (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    ev ς k C h y = y ⟨m, h⟩ := rfl

theorem d_apply_succ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) (h' : m + 1 + k = n + 1) :
    (Sh ς k C).d n y ⟨m + 1, h'⟩ = (ς : ℤ) • C.d m (y ⟨m, h⟩) := rfl

theorem d_apply_zero (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {n : ℕ} (y : (Sh ς k C).X n) (h' : 0 + k = n + 1) :
    (Sh ς k C).d n y ⟨0, h'⟩ = 0 := rfl

theorem unit_smul_eq_zero (ς : ℤˣ) {M : Type*} [AddCommGroup M] {x : M} : (ς : ℤ) • x = 0 ↔ x = 0 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem unit_smul_smul (ς : ℤˣ) {M : Type*} [AddCommGroup M] (x : M) : (ς : ℤ) • (ς : ℤ) • x = x := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem ext_at (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) {y z : (Sh ς k C).X n}
    (e : y ⟨m, h⟩ = z ⟨m, h⟩) : y = z :=
  (ev ς k C h).injective e

theorem mem_Z_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    (Sh ς k C).d n y = 0 ↔ C.d m (y ⟨m, h⟩) = 0 := by
  have h' : m + 1 + k = n + 1 := by omega
  constructor
  · intro e
    have := congrFun e ⟨m + 1, h'⟩
    rw [d_apply_succ ς k C h y h'] at this
    exact (unit_smul_eq_zero ς).1 this
  · intro e
    refine ext_at ς k C h' ?_
    rw [d_apply_succ ς k C h y h', e, smul_zero]
    rfl

theorem mem_B_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    y ∈ (Sh ς k C).B n ↔ y ⟨m, h⟩ ∈ C.B m := by
  cases n with
  | zero =>
    obtain rfl : m = 0 := by omega
    constructor
    · intro e
      have e' : y = 0 := e
      rw [e']
      exact Submodule.zero_mem _
    · intro e
      have e' : y ⟨0, h⟩ = 0 := e
      have : y = 0 := ext_at ς k C h e'
      rw [this]
      exact Submodule.zero_mem _
  | succ n =>
    cases m with
    | zero =>
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_zero ς k C x h]
        exact Submodule.zero_mem _
      · intro e
        have e' : y ⟨0, h⟩ = 0 := e
        have : y = 0 := ext_at ς k C h e'
        rw [this]
        exact Submodule.zero_mem _
    | succ m =>
      have h0 : m + k = n := by omega
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_succ ς k C h0 x h]
        exact ⟨(ς : ℤ) • x ⟨m, h0⟩, by rw [map_zsmul]⟩
      · rintro ⟨z, hz⟩
        refine ⟨(ev ς k C h0).symm ((ς : ℤ) • z), ext_at ς k C h ?_⟩
        rw [d_apply_succ ς k C h0 _ h]
        change (ς : ℤ) • C.d m ((ev ς k C h0) ((ev ς k C h0).symm ((ς : ℤ) • z))) = _
        rw [LinearEquiv.apply_symm_apply, map_zsmul, unit_smul_smul, hz]

def evZ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.Z m ≃ₗ[K] (Sh ς k C).Z n :=
  LinearEquiv.ofSubmodules (ev ς k C h).symm (C.Z m) ((Sh ς k C).Z n) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine (mem_Z_iff ς k C h _).2 ?_
      change C.d m ((ev ς k C h) ((ev ς k C h).symm x)) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hx
    · intro hy
      exact ⟨ev ς k C h y, (mem_Z_iff ς k C h y).1 hy, (ev ς k C h).symm_apply_apply y⟩)

theorem evZ_coe (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.Z m) :
    ev ς k C h (evZ ς k C h x).1 = x.1 :=
  (ev ς k C h).apply_symm_apply x.1

def evH (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Submodule.Quotient.equiv _ _ (evZ ς k C h) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x.1 ∈ C.B m := hx
      change (evZ ς k C h x).1 ∈ (Sh ς k C).B n
      refine (mem_B_iff ς k C h _).2 ?_
      have := evZ_coe ς k C h x
      rw [ev_apply] at this
      rw [this]
      exact hx'
    · intro hy
      have hy' : y.1 ∈ (Sh ς k C).B n := hy
      refine ⟨(evZ ς k C h).symm y, ?_, (evZ ς k C h).apply_symm_apply y⟩
      change ((evZ ς k C h).symm y).1 ∈ C.B m
      have := evZ_coe ς k C h ((evZ ς k C h).symm y)
      rw [LinearEquiv.apply_symm_apply, ev_apply] at this
      rw [← this]
      exact (mem_B_iff ς k C h _).1 hy')

theorem main : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  intro K _ ς k C n
  refine ⟨fun hn => ?_, fun m h => ⟨evH ς k C h, fun y hy hy' => ?_⟩⟩
  · have : IsEmpty {m : ℕ // m + k = n} := ⟨fun x => by have := x.2; omega⟩
    have hX : Subsingleton ((Sh ς k C).X n) :=
      inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, C.X m.1))
    have hZ : Subsingleton ((Sh ς k C).Z n) := ⟨fun a b => Subtype.ext (hX.elim _ _)⟩
    exact Quotient.instSubsingletonQuotient _
  · refine congrArg (Submodule.Quotient.mk (p := ((Sh ς k C).B n).submoduleOf ((Sh ς k C).Z n))) (Subtype.ext ?_)
    exact (ev ς k C h).symm_apply_apply y

end GlobalTheory.CompanionTheory.KunGlue.ShiftCoh
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomologyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_complex_cohomology : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main | exact GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescends
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescends
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShDesc

universe w

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

def cechMap (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S) (n : ℕ) : P.cech.X n →ₗ[R] Q.cech.X n :=
  LinearMap.pi fun i => (e (ent i)).comp (LinearMap.proj i)

theorem cechMap_d (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (n : ℕ) (x : P.cech.X n) :
    Q.cech.d n (cechMap P Q e n x) = cechMap P Q e (n + 1) (P.cech.d n x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (hn _ _).symm

theorem cechMap_aug (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (x : P.M ∅) :
    Q.aug (e ∅ x) = cechMap P Q e 0 (P.aug x) := by
  funext t
  exact (hn _ _).symm

theorem ex_of_equiv (P Q : PM.{w} R ι) (e : ∀ S, Q.M S ≃ₗ[R] P.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (Q.res h x) = P.res h (e S x)) (hP : P.Ex) : Q.Ex := by
  have hn' : ∀ {S T : Finset ι} (h : S ⊆ T) x, (e T).symm (P.res h x) = Q.res h ((e S).symm x) := by
    intro S T h x
    apply (e T).injective
    rw [hn]
    simp
  let f : ∀ S, P.M S →ₗ[R] Q.M S := fun S => ((e S).symm : P.M S →ₗ[R] Q.M S)
  let g : ∀ S, Q.M S →ₗ[R] P.M S := fun S => ((e S) : Q.M S →ₗ[R] P.M S)
  have hf : ∀ {S T : Finset ι} (h : S ⊆ T) x, f T (P.res h x) = Q.res h (f S x) := hn'
  have hg : ∀ {S T : Finset ι} (h : S ⊆ T) x, g T (Q.res h x) = P.res h (g S x) := hn
  have fg : ∀ n (y : Q.cech.X n), cechMap P Q f n (cechMap Q P g n y) = y := by
    intro n y
    funext t
    exact (e _).symm_apply_apply _
  have gf0 : ∀ n (y : P.cech.X n), cechMap Q P g n (cechMap P Q f n y) = y := by
    intro n y
    funext t
    exact (e _).apply_symm_apply _
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · have : Q.aug y = cechMap P Q f 0 (P.aug (g ∅ y)) := by
      rw [← cechMap_aug P Q f hf]
      congr 1
      exact ((e ∅).symm_apply_apply y).symm
    change Q.cech.d 0 (Q.aug y) = 0
    rw [this, cechMap_d P Q f hf, show P.cech.d 0 (P.aug (g ∅ y)) = 0 from h0 _, map_zero]
  · have h := h1 (g ∅ y) (by
      have := cechMap_aug Q P g hg y
      rw [this]
      change cechMap Q P g 0 (Q.aug y) = 0 at *
      rw [hy, map_zero])
    rw [one_smul] at h ⊢
    exact (e ∅).injective (by rw [map_zero]; exact h)
  · obtain ⟨x, hx⟩ := h2 (cechMap Q P g 0 y) (by
      change P.cech.d 0 _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d 0 y = 0 := hy
      rw [hy', map_zero])
    refine ⟨f ∅ x, ?_⟩
    rw [one_smul] at hx ⊢
    rw [cechMap_aug P Q f hf]
    have hx' : P.aug x = cechMap Q P g 0 y := hx
    rw [hx', fg]
  · obtain ⟨x, hx⟩ := h3 n (cechMap Q P g (n + 1) y) (by
      change P.cech.d (n + 1) _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d (n + 1) y = 0 := hy
      rw [hy', map_zero])
    refine ⟨cechMap P Q f n x, ?_⟩
    rw [one_smul] at hx ⊢
    change Q.cech.d n _ = y
    rw [cechMap_d P Q f hf]
    have hx' : P.cech.d n x = cechMap Q P g (n + 1) y := hx
    rw [hx', fg]

theorem ex_of_subsingleton (P : PM.{w} R ι) (h : ∀ S, Subsingleton (P.M S)) : P.Ex := by
  have hX : ∀ n, Subsingleton (P.cech.X n) := fun n =>
    inferInstanceAs (Subsingleton (∀ i : Fin (n + 1) → ι, P.M (ent i)))
  refine ⟨fun x => Subsingleton.elim (α := P.cech.X 1) _ _, fun x _ => Subsingleton.elim _ _,
    fun y _ => ⟨0, Subsingleton.elim (α := P.cech.X 0) _ _⟩, fun n y _ => ⟨0, Subsingleton.elim (α := P.cech.X (n + 1)) _ _⟩⟩

variable {K : Type} [Field K]

def shEv (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m :=
  LinearEquiv.ofBijective
    (LinearMap.proj (φ := fun p : {p : ℕ // p + k = n} => C.X p.1) ⟨m, h⟩) (by
    constructor
    · intro y y' hyy
      funext ⟨p, hp⟩
      obtain rfl : p = m := by omega
      exact hyy
    · intro x
      refine ⟨fun p => (show m = p.1 by have := p.2; omega) ▸ x, rfl⟩)

theorem shSy_desc {ς : ℤˣ} {k : ℕ} {A : Sy.{w} K ι} (hA : A.Desc) : (shSy ς k A).Desc := by
  intro n
  by_cases hk : k ≤ n
  · have h : n - k + k = n := by omega
    exact ex_of_equiv (A.term (n - k)) ((shSy ς k A).term n) (fun S => shEv ς k (A.K S) h)
      (fun _ _ => rfl) (hA (n - k))
  · refine ex_of_subsingleton _ fun S => ?_
    have : IsEmpty {m : ℕ // m + k = n} := ⟨fun p => hk (by have := p.2; omega)⟩
    exact inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, (A.K S).X m.1))

theorem sh_desc : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι),
    A.Desc → (shSy ς k A).Desc :=
  fun _ _ _ h => shSy_desc h

end GlobalTheory.CompanionTheory.KunGlue.ShDesc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescendsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι), A.Desc → (shSy ς k A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | exact GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomology
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomology
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.DsumCoh

variable {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K)

def inj (i : I) : Cx.Hom (E i) (Dsum E) (RingHom.id K) where
  f n := DirectSum.lof K I (fun i => (E i).X n) i
  comm n x := by
    change DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x) = _
    rw [DirectSum.lmap_lof]
    rfl

def prj (i : I) : Cx.Hom (Dsum E) (E i) (RingHom.id K) where
  f n := DirectSum.component K I (fun i => (E i).X n) i
  comm n x := by
    change (E i).d n (DirectSum.component K I (fun i => (E i).X n) i x) =
      DirectSum.component K I (fun i => (E i).X (n + 1)) i (DirectSum.lmap (fun i => (E i).d n) x)
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
      by_cases h : j = i
      · subst h
        simp only [DirectSum.component.lof_self]
      · rw [DirectSum.component.of, DirectSum.component.of, dite_eq_right h, dite_eq_right h, map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

def toH (n : ℕ) : (⨁ i, (E i).H n) →ₗ[K] (Dsum E).H n :=
  DirectSum.toModule K I _ fun i => (inj E i).mapH n

theorem prj_toH (n : ℕ) (i : I) (y : ⨁ i, (E i).H n) :
    (prj E i).mapH n (toH E n y) = DirectSum.component K I (fun i => (E i).H n) i y := by
  have hcl : ∀ (x y : (E i).X n) (hx : (E i).d n x = 0) (hy : (E i).d n y = 0), x = y →
      (E i).cls x hx = (E i).cls y hy := by
    rintro x _ _ _ rfl
    rfl
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j z =>
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
    have h1 : (Dsum E).d n ((inj E j).f n a) = 0 := CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E j) a ha
    rw [← DirectSum.lof_eq_of K, toH, DirectSum.toModule_lof, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E j) a ha h1,
      CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (prj E i) _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) _ h1)]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.component.lof_self]
      exact hcl _ _ _ _ (DirectSum.component.lof_self K _ _)
    · rw [DirectSum.component.of, dite_eq_right hji]
      rw [← CrystallineSemistableComparison.CechClassBoundaries.cls_zero' (K := E i) (n := n) (map_zero _)]
      refine hcl _ _ _ _ ?_
      show DirectSum.component K I (fun i ↦ (E i).X n) i (DirectSum.lof K I (fun i ↦ (E i).X n) j a) = 0
      rw [DirectSum.component.of, dite_eq_right hji]
  | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]

theorem toH_injective (n : ℕ) : Function.Injective (toH E n) := by
  refine (injective_iff_map_eq_zero (toH E n)).2 fun y hy ↦ ?_
  refine DirectSum.ext fun i ↦ ?_
  have h := prj_toH E n i y
  rw [hy, map_zero] at h
  rw [DirectSum.apply_eq_component K, ← h]
  rfl

theorem toH_surjective (n : ℕ) : Function.Surjective (toH E n) := by
  classical
  intro z
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
  have hc : ∀ i, (E i).d n ((prj E i).f n x) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) x hx
  have hci : ∀ i, (Dsum E).d n ((inj E i).f n ((prj E i).f n x)) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E i) _ (hc i)
  have hsum : ∀ S : Finset I, ∀ h : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0,
      (Dsum E).cls (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) h =
        ∑ i ∈ S, (Dsum E).cls ((inj E i).f n ((prj E i).f n x)) (hci i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact CrystallineSemistableComparison.CechClassBoundaries.cls_zero' h
    | insert j S hj ih =>
      intro h
      have hS : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_eq_zero fun i _ ↦ hci i
      simp only [Finset.sum_insert hj]
      rw [CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ (hci j) hS, ih hS]
  have hx_eq : ∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x) = x := by
    conv_rhs => rw [← DirectSum.sum_support_of x]
    rfl
  refine ⟨∑ i ∈ DFinsupp.support x, DirectSum.lof K I (fun i ↦ (E i).H n) i ((E i).cls _ (hc i)), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [toH, DirectSum.toModule_lof]
  have hx' : (Dsum E).d n (∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x)) = 0 := by
    rw [hx_eq]
    exact hx
  rw [Finset.sum_congr rfl fun i _ ↦ CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E i) _ (hc i) (hci i), ← hsum _ hx']
  exact (CrystallineSemistableComparison.CechClassBoundaries.cls_eq _ _ _ _).2 (by rw [hx_eq, sub_self]; exact zero_mem _)

end GlobalTheory.CompanionTheory.KunGlue.DsumCoh

theorem GlobalTheory.CompanionTheory.KunGlue.dsum_coh : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ),
    ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0)
      (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0),
      e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) =
        (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  intro K _ I _ E n
  refine ⟨LinearEquiv.ofBijective (DsumCoh.toH E n) ⟨DsumCoh.toH_injective E n, DsumCoh.toH_surjective E n⟩,
    fun i x hx hx' ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, DsumCoh.toH, DirectSum.toModule_lof]
  exact CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (DsumCoh.inj E i) x hx hx'
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomologyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.direct_sum_complex_cohomology : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ), ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0) (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0), e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) = (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.dsum_coh | exact GlobalTheory.CompanionTheory.KunGlue.dsum_coh | (intros; apply GlobalTheory.CompanionTheory.KunGlue.dsum_coh <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescends
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescends
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.SumDesc

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {I : Type 1} [DecidableEq I]

def sumPM (P : I → PM.{1} K ι) : PM.{1} K ι where
  M S := ⨁ i, (P i).M S
  res h := DirectSum.lmap fun i => (P i).res h
  res_id S h x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ _ = _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_id]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  res_comp h h' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_comp]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (P : I → PM.{1} K ι)

def pr (i : I) (m : ℕ) : (sumPM P).cech.X m →ₗ[K] (P i).cech.X m :=
  LinearMap.pi fun t => (DirectSum.component K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

def inc (i : I) (m : ℕ) : (P i).cech.X m →ₗ[K] (sumPM P).cech.X m :=
  LinearMap.pi fun t => (DirectSum.lof K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

theorem component_res {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (sumPM P).M S) :
    DirectSum.component K I (fun j => (P j).M T) i ((sumPM P).res h x) =
      (P i).res h (DirectSum.component K I (fun j => (P j).M S) i x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    change DirectSum.component K I _ i (DirectSum.lmap _ _) = _
    rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
    by_cases e : j = i
    · subst e
      simp
    · simp [DirectSum.component.of, e]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem res_lof {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (P i).M S) :
    (sumPM P).res h (DirectSum.lof K I (fun j => (P j).M S) i x) =
      DirectSum.lof K I (fun j => (P j).M T) i ((P i).res h x) := DirectSum.lmap_lof _ _ _

theorem pr_d (i : I) (m : ℕ) (z : (sumPM P).cech.X m) :
    pr P i (m + 1) ((sumPM P).cech.d m z) = (P i).cech.d m (pr P i m z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1

theorem inc_d (i : I) (m : ℕ) (y : (P i).cech.X m) :
    inc P i (m + 1) ((P i).cech.d m y) = (sumPM P).cech.d m (inc P i m y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (res_lof P _ i _).symm

theorem cochain_ext {m : ℕ} {z : (sumPM P).cech.X m} (h : ∀ i, pr P i m z = 0) : z = 0 := by
  funext t
  refine DFinsupp.ext fun i => ?_
  exact congrFun (h i) t

theorem pr_aug (i : I) (x : (sumPM P).M ∅) :
    pr P i 0 ((sumPM P).aug x) = (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) := by
  funext t
  exact component_res P _ i _

theorem aug_lof (i : I) (x : (P i).M ∅) :
    (sumPM P).aug (DirectSum.lof K I (fun j => (P j).M ∅) i x) = inc P i 0 ((P i).aug x) := by
  funext t
  exact res_lof P _ i _

theorem pr_inc_self (i : I) (m : ℕ) (y : (P i).cech.X m) : pr P i m (inc P i m y) = y := by
  funext t
  exact DirectSum.component.lof_self (M := fun j => (P j).M (ent t)) K i (y t)

theorem pr_inc_ne {i j : I} (e : j ≠ i) (m : ℕ) (y : (P j).cech.X m) : pr P i m (inc P j m y) = 0 := by
  funext t
  change DirectSum.component K I (fun j => (P j).M (ent t)) i (DirectSum.lof K I (fun j => (P j).M (ent t)) j (y t)) = 0
  rw [DirectSum.component.of, dite_eq_right e]

open Classical in
theorem decomp [Fintype ι] {m : ℕ} (z : (sumPM P).cech.X m) :
    ∃ F : Finset I, z = ∑ i ∈ F, inc P i m (pr P i m z) := by
  refine ⟨Finset.univ.biUnion fun t => DFinsupp.support (z t), sub_eq_zero.1 (cochain_ext P fun i => ?_)⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  by_cases hi : i ∈ Finset.univ.biUnion fun t => DFinsupp.support (z t)
  · rw [Finset.sum_eq_single_of_mem i hi (fun j _ e => pr_inc_ne P e _ _), pr_inc_self, sub_self]
  · have hz : pr P i m z = 0 := by
      funext t
      by_contra hne
      exact hi (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, DFinsupp.mem_support_iff.2 hne⟩)
    rw [hz, Finset.sum_eq_zero (fun j hj => pr_inc_ne P (ne_of_mem_of_not_mem hj hi) _ _), sub_zero]

theorem sum_ex [Fintype ι] (h : ∀ i, (P i).Ex) : (sumPM P).Ex := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · refine cochain_ext P fun i => ?_
    change pr P i 1 ((sumPM P).cech.d 0 ((sumPM P).aug x)) = 0
    rw [pr_d, pr_aug]
    exact (h i).1 _
  · rw [one_smul]
    refine DFinsupp.ext fun i => ?_
    have h0 : (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) = 0 := by
      rw [← pr_aug, hx, map_zero]
    have h1 := (h i).2.1 _ h0
    rw [one_smul] at h1
    exact h1
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d 0 (pr P i 0 y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i 1) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.1 _ (hc i)
    refine ⟨∑ i ∈ F, DirectSum.lof K I (fun j => (P j).M ∅) i (c i), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [one_smul, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [aug_lof, hc', one_smul]
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d (m + 1) (pr P i (m + 1) y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i (m + 2)) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.2 m _ (hc i)
    refine ⟨∑ i ∈ F, inc P i m (c i), ?_⟩
    rw [one_smul]
    change (sumPM P).cech.d m _ = y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [← inc_d]
    have h2 := hc' i
    rw [one_smul] at h2
    exact congrArg (inc P i (m + 1)) h2

theorem sum_desc {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I]
    (A : I → Sy.{1} K ι) (h : ∀ i, (A i).Desc) : (sumSy A).Desc :=
  fun n => sum_ex (fun i => (A i).term n) fun i => h i n

end GlobalTheory.CompanionTheory.KunGlue.SumDesc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescendsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.direct_sum_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (A : I → Sy.{1} K ι), (∀ i, (A i).Desc) → (sumSy A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | exact GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftSumDifferentialCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.MvSum

variable {K : Type} [Field K]

def shIn (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.X m) : (Sh ς k C).X n :=
  show ∀ m' : {m' : ℕ // m' + k = n}, C.X m'.1 from
    fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x

theorem shIn_d (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.X m) (hx : C.d m x = 0) :
    (Sh ς k C).d n (shIn ς C h x) = 0 := by
  funext ⟨m', h'⟩
  cases m' with
  | zero => rfl
  | succ m' =>
    obtain rfl : m' = m := by omega
    change (ς : ℤ) • C.d m' x = 0
    rw [hx, smul_zero]

section Psi

variable {k : ℕ} {C D : Cx.{1} K} (ς : ℤˣ) (g : ∀ {m n : ℕ}, m + k = n → C.X m →ₗ[K] D.X n)

def psi (n : ℕ) : (Sh ς k C).X n →ₗ[K] D.X n where
  toFun w := if h : k ≤ n then g (m := n - k) (by omega) (w ⟨n - k, by omega⟩) else 0
  map_add' x y := by
    split_ifs with h
    · exact map_add _ _ _
    · simp
  map_smul' r x := by
    split_ifs with h
    · exact map_smul _ _ _
    · simp

theorem psi_eq {m n : ℕ} (h : m + k = n) (w : (Sh ς k C).X n) : psi ς g n w = g h (w ⟨m, h⟩) := by
  obtain rfl : m = n - k := by omega
  have hk : k ≤ n := by omega
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hk]

theorem psi_zero {n : ℕ} (h : n < k) (w : (Sh ς k C).X n) : psi ς g n w = 0 := by
  have hk : ¬ k ≤ n := by omega
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hk]

theorem psi_comm
    (hg : ∀ {m n : ℕ} (h : m + k = n) (h' : m + 1 + k = n + 1) (x : C.X m),
      D.d n (g h x) = (ς : ℤ) • g h' (C.d m x))
    (n : ℕ) (w : (Sh ς k C).X n) : D.d n (psi ς g n w) = psi ς g (n + 1) ((Sh ς k C).d n w) := by
  by_cases h : k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    have h' : m + 1 + k = m + k + 1 := by omega
    rw [psi_eq ς g rfl, psi_eq ς g h', hg rfl h']
    change _ = g h' ((ς : ℤ) • C.d m (w ⟨m, _⟩))
    rw [map_zsmul]
  · rw [psi_zero ς g (by omega), map_zero]
    by_cases h2 : k = n + 1
    · have h0 : 0 + k = n + 1 := by omega
      rw [psi_eq ς g h0]
      change 0 = g h0 0
      rw [map_zero]
    · rw [psi_zero ς g (by omega)]

def shHom
    (hg : ∀ {m n : ℕ} (h : m + k = n) (h' : m + 1 + k = n + 1) (x : C.X m),
      D.d n (g h x) = (ς : ℤ) • g h' (C.d m x)) : Cx.Hom (Sh ς k C) D (RingHom.id K) where
  f n := psi ς g n
  comm n x := psi_comm ς g hg n x

end Psi

theorem psi_nat {k : ℕ} {C C' D D' : Cx.{1} K} (ς : ℤˣ) (g : ∀ {m n : ℕ}, m + k = n → C.X m →ₗ[K] D.X n)
    (g' : ∀ {m n : ℕ}, m + k = n → C'.X m →ₗ[K] D'.X n) (f : Cx.Hom C C' (RingHom.id K))
    (f' : Cx.Hom D D' (RingHom.id K))
    (hn : ∀ {m n : ℕ} (h : m + k = n) (x : C.X m), f'.f n (g h x) = g' h (f.f m x))
    (n : ℕ) (w : (Sh ς k C).X n) : psi ς g' n ((Sh.map ς k f).f n w) = f'.f n (psi ς g n w) := by
  by_cases h : k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    rw [psi_eq ς g rfl, psi_eq ς g' rfl, hn]
    rfl
  · rw [psi_zero ς g (by omega), psi_zero ς g' (by omega), map_zero]

section Sum

variable {I : Type 1} [DecidableEq I]

def sumHom {E : I → Cx.{1} K} {D : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K)) :
    Cx.Hom (Dsum E) D (RingHom.id K) where
  f n := DirectSum.toModule K I _ fun i => (φ i).f n
  comm n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change D.d n (DirectSum.toModule K I _ (fun i => (φ i).f n) (DirectSum.lof K I (fun i => (E i).X n) i x)) =
        DirectSum.toModule K I _ (fun i => (φ i).f (n + 1))
          (DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x))
      rw [DirectSum.lmap_lof, DirectSum.toModule_lof, DirectSum.toModule_lof, (φ i).comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sumHom_lof {E : I → Cx.{1} K} {D : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K)) (n : ℕ) (i : I)
    (x : (E i).X n) : (sumHom φ).f n (DirectSum.lof K I (fun i => (E i).X n) i x) = (φ i).f n x :=
  DirectSum.toModule_lof _ _ _

theorem sumHom_nat {E E' : I → Cx.{1} K} {D D' : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K))
    (φ' : ∀ i, Cx.Hom (E' i) D' (RingHom.id K)) (a : ∀ i, Cx.Hom (E i) (E' i) (RingHom.id K))
    (b : Cx.Hom D D' (RingHom.id K)) (h : ∀ i n x, (φ' i).f n ((a i).f n x) = b.f n ((φ i).f n x)) (n : ℕ)
    (x : (Dsum E).X n) : (sumHom φ').f n ((Dsum.map a).f n x) = b.f n ((sumHom φ).f n x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    have e : (Dsum.map a).f n (DirectSum.lof K I (fun i => (E i).X n) i x) =
        DirectSum.lof K I (fun i => (E' i).X n) i ((a i).f n x) := DirectSum.lmap_lof _ _ _
    change (sumHom φ').f n ((Dsum.map a).f n (DirectSum.lof K I (fun i => (E i).X n) i x)) =
      b.f n ((sumHom φ).f n (DirectSum.lof K I (fun i => (E i).X n) i x))
    rw [e, sumHom_lof, sumHom_lof, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def eSh (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Classical.choose ((GlobalTheory.T.shifted_complex_cohomology ς k C n).2 m h)

theorem eSh_cls (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n)
    (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0) :
    eSh ς C h (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy :=
  Classical.choose_spec ((GlobalTheory.T.shifted_complex_cohomology ς k C n).2 m h) y hy hy'

variable (k : I → ℕ) (ς : I → ℤˣ) (C : I → Cx.{1} K) (n : ℕ)

abbrev Ix : Type 1 := {v : I × ℕ // v.2 + k v.1 = n}

def reF : (⨁ v : Ix k n, (C v.1.1).H v.1.2) →ₗ[K] ⨁ u, (Sh (ς u) (k u) (C u)).H n :=
  DirectSum.toModule K _ _ fun v =>
    (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).H n) v.1.1) ∘ₗ (eSh (ς v.1.1) (C v.1.1) v.2).toLinearMap

def reG : (⨁ u, (Sh (ς u) (k u) (C u)).H n) →ₗ[K] ⨁ v : Ix k n, (C v.1.1).H v.1.2 :=
  DirectSum.toModule K I _ fun u =>
    if h : k u ≤ n then
      (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) ⟨(u, n - k u), by change n - k u + k u = n; omega⟩) ∘ₗ
        (eSh (ς u) (C u) (m := n - k u) (n := n) (by omega)).symm.toLinearMap
    else 0

theorem reG_reF : reG k ς C n ∘ₗ reF k ς C n = LinearMap.id := by
  refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun y => ?_
  obtain ⟨⟨u, m⟩, h⟩ := v
  have h' : m + k u = n := h
  obtain rfl : m = n - k u := by omega
  have hk : k u ≤ n := by omega
  simp only [reF, reG, LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe, dif_pos hk,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

theorem reF_reG : reF k ς C n ∘ₗ reG k ς C n = LinearMap.id := by
  refine DirectSum.linearMap_ext K fun u => LinearMap.ext fun y => ?_
  by_cases hk : k u ≤ n
  · simp only [reF, reG, LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe, dif_pos hk,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · have : Subsingleton ((Sh (ς u) (k u) (C u)).H n) := (GlobalTheory.T.shifted_complex_cohomology (ς u) (k u) (C u) n).1 (by omega)
    rw [Subsingleton.elim y 0, map_zero, map_zero]

def reE : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] ⨁ u, (Sh (ς u) (k u) (C u)).H n :=
  LinearEquiv.ofLinear (reF k ς C n) (reG k ς C n) (reF_reG k ς C n) (reG_reF k ς C n)

theorem exists_P : ∃ P : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] (Dsum fun u => Sh (ς u) (k u) (C u)).H n,
    ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
      (hw : (Dsum fun u => Sh (ς u) (k u) (C u)).d n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) = 0),
      P (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
        (Dsum fun u => Sh (ς u) (k u) (C u)).cls
          (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) hw := by
  obtain ⟨e1, he1⟩ := GlobalTheory.T.direct_sum_complex_cohomology (fun u => Sh (ς u) (k u) (C u)) n
  refine ⟨(reE k ς C n).trans e1, ?_⟩
  intro v x hx hw
  have hy := shIn_d (ς v.1.1) (C v.1.1) v.2 x hx
  rw [LinearEquiv.trans_apply]
  have h1 : reE k ς C n (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
      DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).H n) v.1.1
        ((Sh (ς v.1.1) (k v.1.1) (C v.1.1)).cls (shIn (ς v.1.1) (C v.1.1) v.2 x) hy) := by
    change reF k ς C n _ = _
    rw [reF, DirectSum.toModule_lof]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← eSh_cls (ς v.1.1) (C v.1.1) v.2 _ hy hx]
    rfl
  rw [h1]
  exact he1 v.1.1 _ hy hw

variable {D : Cx.{1} K} (g : ∀ (u : I) {m n : ℕ}, m + k u = n → (C u).X m →ₗ[K] D.X n)
  (hg : ∀ (u : I) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : (C u).X m),
    D.d n (g u h x) = (ς u : ℤ) • g u h' ((C u).d m x))

include hg in
theorem g_cocycle (u : I) {m n : ℕ} (h : m + k u = n) (x : (C u).X m) (hx : (C u).d m x = 0) :
    D.d n (g u h x) = 0 := by
  rw [hg u h (by omega), hx, map_zero, smul_zero]

theorem bij_iff : Function.Bijective ((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ↔
    ∃ e : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] D.H n,
      ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
        (hz : D.d n (g v.1.1 v.2 x) = 0),
        e (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
          D.cls (g v.1.1 v.2 x) hz := by
  obtain ⟨P, hP⟩ := exists_P k ς C n
  have key : ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
      (hz : D.d n (g v.1.1 v.2 x) = 0),
      (sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n
        (P (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx))) =
        D.cls (g v.1.1 v.2 x) hz := by
    intro v x hx hz
    have hw : (Dsum fun u => Sh (ς u) (k u) (C u)).d n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) = 0 := by
      change DirectSum.lmap _ _ = 0
      rw [DirectSum.lmap_lof, shIn_d _ _ _ _ hx, map_zero]
    have hf : (sumHom fun u => shHom (ς u) (g u) (hg u)).f n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) =
        g v.1.1 v.2 x := by
      rw [sumHom_lof]
      exact psi_eq (ς v.1.1) (g v.1.1) v.2 _
    rw [hP v x hx hw, CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (by rw [hf]; exact hz)]
    exact GlobalTheory.CompanionTheory.ConeKillC.cls_congr _ hf _ _
  constructor
  · intro hb
    refine ⟨P.trans (LinearEquiv.ofBijective _ hb), fun v x hx hz => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply]
    exact key v x hx hz
  · rintro ⟨e, he⟩
    have hEq : ((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ₗ P.toLinearMap = e.toLinearMap := by
      refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun y => ?_
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.CompanionTheory.ConeKillC.cls_surj _ _ y
      have hz := g_cocycle k ς C g hg v.1.1 v.2 x hx
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [key v x hx hz, he v x hx hz]
    have hb : Function.Bijective (((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ P) := by
      have : (((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ P) = e := by
        funext y
        exact LinearMap.congr_fun hEq y
      rw [this]
      exact e.bijective
    exact (Function.Bijective.of_comp_iff _ P.bijective).1 hb

end Sum

variable {ι : Type} [DecidableEq ι] {I : Type 1} [DecidableEq I]

def mvHom (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι)
    (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n)
    (hd : ∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m),
      (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x))
    (hn : ∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m),
      (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) :
    (sumSy fun u => shSy (ς u) (k u) (A u)).Hom T where
  φ S := sumHom (E := fun u => Sh (ς u) (k u) ((A u).K S)) fun u => shHom (ς u) (g u S) (hd u S)
  nat {S S'} h n x :=
    sumHom_nat (E := fun u => Sh (ς u) (k u) ((A u).K S)) (E' := fun u => Sh (ς u) (k u) ((A u).K S'))
      (fun u => shHom (ς u) (g u S) (hd u S)) (fun u => shHom (ς u) (g u S') (hd u S'))
      (fun u => Sh.map (ς u) (k u) ((A u).res h)) (T.res h)
      (fun u n x => psi_nat (ς u) (g u S) (g u S') ((A u).res h) (T.res h) (fun h' x => hn u h h' x) n x) n x

theorem mvSum : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι) (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n), (∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m), (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x)) → (∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m), (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) → (∀ u, (A u).Desc) → T.Desc → (∀ S : Finset ι, S.Nonempty → ∀ n, MvE k A T g S n) → ∀ n, MvE k A T g ∅ n := by
  intro hMV K _ ι _ _ I _ k ς A T g hd hn hA hT hE n
  have hiff : ∀ (S : Finset ι) (n : ℕ), Function.Bijective (((mvHom k ς A T g hd hn).φ S).mapH n) ↔ MvE k A T g S n :=
    fun S n => bij_iff k ς (fun u => (A u).K S) n (fun u => g u S) (fun u => hd u S)
  exact (hiff ∅ n).1 (hMV K ι _ T (mvHom k ς A T g hd hn)
    (GlobalTheory.T.direct_sum_system_descends _ fun u => GlobalTheory.T.shifted_system_descends _ _ _ (hA u)) hT (fun S hS n => (hiff S n).2 (hE S hS n)) n)

end GlobalTheory.CompanionTheory.KunGlue.MvSum
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftSumDifferentialCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvE_empty_of_mvE_nonempty : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι) (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n), (∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m), (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x)) → (∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m), (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) → (∀ u, (A u).Desc) → T.Desc → (∀ S : Finset ι, S.Nonempty → ∀ n, MvE k A T g S n) → ∀ n, MvE k A T g ∅ n := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum | exact GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum | (intros; apply GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum <;> assumption)
end

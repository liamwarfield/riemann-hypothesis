module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ValuationUnitNeZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LeftMultiplication.Lmul
noncomputable section

namespace UpperTheory.V.ZK.PM

variable (A : Type) [CommRing A] {G : Type} [Group G]

def cone (a : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G (m + 1) :=
  Finsupp.lmapDomain A A fun x => Fin.cons (α := fun _ => G) a x

def rmul (k : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G m := Finsupp.lmapDomain A A fun x i => x i * k

def lmul (h : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G m := Finsupp.lmapDomain A A fun x i => h * x i

def hbd (G : Type) [Group G] : ∀ m : ℕ, Ch A G (m + 1) →ₗ[A] Ch A G m
  | 0 => Finsupp.linearCombination A fun x => Finsupp.single (Fin.tail (α := fun _ => G) x) 1
  | m + 1 => Finsupp.linearCombination A fun x => Finsupp.single (Fin.tail (α := fun _ => G) x) 1 -
      cone A (x 0) m (hbd G m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def hp (k : G) : ∀ m : ℕ, Ch A G m →ₗ[A] Ch A G (m + 1)
  | 0 => 0
  | m + 1 => Finsupp.linearCombination A fun x => cone A (x 0) (m + 1)
      (rmul A k (m + 1) (Finsupp.single x 1) - hp k m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def hd (k k' : G) : ∀ m : ℕ, Ch A G m →ₗ[A] Ch A G (m + 2)
  | 0 => 0
  | m + 1 => Finsupp.linearCombination A fun x => cone A (x 0) (m + 2)
      (hp A k' (m + 1) (rmul A k (m + 1) (Finsupp.single x 1)) +
        hd k k' m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def pr (G : Type) [Group G] (m : ℕ) : Ch A G (m + 1) →ₗ[A] Ch A G m :=
  Finsupp.lmapDomain A A fun x i => (x i.castSucc)⁻¹ * x i.succ

end UpperTheory.V.ZK.PM

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TupleChainBoundaryFormula
open UpperTheory.V.ZK UpperTheory.V.ZK.PM

private theorem hbd_eq (A : Type) [CommRing A] (G : Type) [Group G] :
    ∀ (m : ℕ) (z : Ch A G (m + 1)), PM.hbd A G m z = UpperTheory.V.ZK.hbd A G m z
  | 0, z => ch_ext A (fun x => by
      have h := hbd_cone_zero A (x 0) (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul]) z
  | m + 1, z => ch_ext A (fun x => by
      have h := hbd_cone A (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul, hbd_eq A G m]
      rfl) z

theorem UpperTheory.tupleChain_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 2)), bd A G m (pr A G (m + 1) z) = pr A G m (PM.hbd A G (m + 1) z) := by
  intro A _ G _ m z
  rw [hbd_eq]
  exact bd_toInh A m z
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LeftMulChainChainHomotopic
open UpperTheory.V.ZK UpperTheory.V.ZK.PM

section
variable (A : Type) [CommRing A] {G : Type} [Group G]

private theorem lmul_single (h : G) (m : ℕ) (x : Fin m → G) (a : A) :
    lmul A h m (Finsupp.single x a) = Finsupp.single (fun i => h * x i) a := by
  simp [lmul]

private theorem lmul_cone (h a : G) (m : ℕ) (y : Ch A G m) :
    lmul A h (m + 1) (PM.cone A a m y) = PM.cone A (h * a) m (lmul A h m y) := by
  simp only [lmul, PM.cone, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem lmul_rmul (h k : G) (m : ℕ) (y : Ch A G m) :
    lmul A h m (rmul A k m y) = rmul A k m (lmul A h m y) := by
  simp only [lmul, rmul, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  simp [mul_assoc]

private theorem pr_lmul (h : G) (m : ℕ) (y : Ch A G (m + 1)) :
    pr A G m (lmul A h (m + 1) y) = pr A G m y := by
  simp only [lmul, pr, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  simp [mul_assoc]

private theorem lmul_hp (h k : G) : ∀ (m : ℕ) (y : Ch A G m),
    lmul A h (m + 1) (hp A k m y) = hp A k m (lmul A h m y)
  | 0, y => by simp [hp]
  | m + 1, y => by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | single x a =>
      rw [lmul_single]
      simp only [hp, Finsupp.linearCombination_single, map_smul]
      rw [lmul_cone, map_sub, lmul_rmul, lmul_hp h k m, lmul_single, lmul_single]
      rfl

private theorem lmul_hd (h k k' : G) : ∀ (m : ℕ) (y : Ch A G m),
    lmul A h (m + 2) (hd A k k' m y) = hd A k k' m (lmul A h m y)
  | 0, y => by simp [hd]
  | m + 1, y => by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | single x a =>
      rw [lmul_single]
      simp only [hd, Finsupp.linearCombination_single, map_smul]
      rw [lmul_cone, map_add (f := _), lmul_hp, lmul_rmul, lmul_hd h k k' m, lmul_single, lmul_single]
      rfl

end

theorem UpperTheory.leftMulChain_chainHomotopic :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k k' h : G) (m : ℕ) (z : Ch A G (m + 1)), pr A G (m + 2) (hd A k k' (m + 1) (lmul A h (m + 1) z)) = pr A G (m + 2) (hd A k k' (m + 1) z) := by
  intro A _ G _ k k' h m z
  rw [← lmul_hd]
  exact pr_lmul A h (m + 2) _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.ConeHomotopyBoundaryFormula
open UpperTheory.V.ZK UpperTheory.V.ZK.PM

private theorem hp_eq (A : Type) [CommRing A] (G : Type) [Group G] (k : G) :
    ∀ (m : ℕ) (z : Ch A G m), hp A k m z = hprism A (· * k) m z
  | 0, z => by rw [hprism_zero]; rfl
  | m + 1, z => ch_ext A (fun x => by
      have h := hprism_cone A (· * k) (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [← hmap_cone A (· * k), cone_single, Fin.cons_self_tail] at h
      rw [h, hp, Finsupp.linearCombination_single, one_smul, hp_eq A G k m, map_sub]
      rfl) z

theorem UpperTheory.coneHomotopy_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k : G) (m : ℕ) (z : Ch A G (m + 1)), pr A G (m + 1) (hp A k (m + 1) z) = prism A k m (pr A G m z) := by
  intro A _ G _ k m z
  rw [hp_eq]
  exact (prism_toInh A k m z).symm
end

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

namespace UpperTheory.V.ZK.PM

variable (A : Type) [CommRing A] {G : Type} [Group G]

private theorem single_eq_cone (m : ℕ) (x : Fin (m + 1) → G) :
    (Finsupp.single x 1 : Ch A G (m + 1)) =
      cone A (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1) := by
  simp [cone, Finsupp.mapDomain_single]

private theorem ext_cone {m : ℕ} {B : Type} [AddCommGroup B] [Module A B] (f g : Ch A G (m + 1) →ₗ[A] B)
    (h : ∀ a y, f (cone A a m y) = g (cone A a m y)) : f = g := by
  refine Finsupp.lhom_ext fun x b => ?_
  rw [← Finsupp.smul_single_one, map_smul, map_smul, single_eq_cone, h]

private theorem hbd_cone_zero (a : G) (y : Ch A G 0) : hbd A G 0 (cone A a 0 y) = y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2]
  | single x b =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul]
    congr 1
    simp [cone, hbd.eq_1, Finsupp.mapDomain_single, Finsupp.linearCombination_single]

private theorem hbd_cone (a : G) (m : ℕ) (y : Ch A G (m + 1)) :
    hbd A G (m + 1) (cone A a (m + 1) y) = y - cone A a m (hbd A G m y) := by
  have e2 : hbd A G (m + 1) = Finsupp.linearCombination A fun x =>
      (Finsupp.single (Fin.tail x) 1 : Ch A G (m + 1)) - cone A (x 0) m (hbd A G m (Finsupp.single (Fin.tail x) 1)) :=
    hbd.eq_2 A G m
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), h1, h2] <;> abel
  | single x b =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, ← smul_sub]
    congr 1
    rw [e2]
    simp [cone, Finsupp.mapDomain_single, Finsupp.linearCombination_single]

private theorem hp_cone (k a : G) (m : ℕ) (y : Ch A G m) :
    hp A k (m + 1) (cone A a m y) = cone A a (m + 1) (rmul A k (m + 1) (cone A a m y) - hp A k m y) := by
  have e : hp A k (m + 1) = Finsupp.linearCombination A fun x =>
      cone A (x 0) (m + 1) (rmul A k (m + 1) (Finsupp.single x 1) - hp A k m (Finsupp.single (Fin.tail x) 1)) :=
    hp.eq_2 A k m
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), map_sub, h1, h2] <;> abel
  | single x b =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, ← smul_sub]
    congr 1
    have hc : cone A a m (Finsupp.single x 1) = Finsupp.single (Fin.cons a x) 1 := by
      simp [cone, Finsupp.mapDomain_single]
    rw [hc, e, Finsupp.linearCombination_single, one_smul, Fin.cons_zero, Fin.tail_cons]

private theorem hd_cone (k k' a : G) (m : ℕ) (y : Ch A G m) :
    hd A k k' (m + 1) (cone A a m y) =
      cone A a (m + 2) (hp A k' (m + 1) (rmul A k (m + 1) (cone A a m y)) + hd A k k' m y) := by
  have e : hd A k k' (m + 1) = Finsupp.linearCombination A fun x =>
      cone A (x 0) (m + 2) (hp A k' (m + 1) (rmul A k (m + 1) (Finsupp.single x 1)) +
        hd A k k' m (Finsupp.single (Fin.tail x) 1)) :=
    hd.eq_2 A k k' m
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), h1, h2] <;> abel
  | single x b =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, ← smul_add]
    congr 1
    have hc : cone A a m (Finsupp.single x 1) = Finsupp.single (Fin.cons a x) 1 := by
      simp [cone, Finsupp.mapDomain_single]
    rw [hc, e, Finsupp.linearCombination_single, one_smul, Fin.cons_zero, Fin.tail_cons]

private theorem rmul_cone (k a : G) (m : ℕ) (y : Ch A G m) :
    rmul A k (m + 1) (cone A a m y) = cone A (a * k) m (rmul A k m y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), h1, h2]
  | single x b =>
    simp only [rmul, cone, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem rmul_rmul (k k' : G) (m : ℕ) (y : Ch A G m) :
    rmul A k' m (rmul A k m y) = rmul A (k * k') m y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), h1, h2]
  | single x b => simp [rmul, Finsupp.mapDomain_single, mul_assoc]

private theorem hbd_rmul (k : G) (m : ℕ) (y : Ch A G (m + 1)) :
    hbd A G m (rmul A k (m + 1) y) = rmul A k m (hbd A G m y) := by
  induction m with
  | zero =>
    refine LinearMap.congr_fun (ext_cone A ((hbd A G 0).comp (rmul A k 1))
      ((rmul A k 0).comp (hbd A G 0)) fun a w => ?_) y
    simp only [LinearMap.comp_apply]
    rw [rmul_cone, hbd_cone_zero, hbd_cone_zero]
  | succ m ih =>
    refine LinearMap.congr_fun (ext_cone A ((hbd A G (m + 1)).comp (rmul A k (m + 1 + 1)))
      ((rmul A k (m + 1)).comp (hbd A G (m + 1))) fun a w => ?_) y
    simp only [LinearMap.comp_apply]
    rw [rmul_cone, hbd_cone, hbd_cone, ih, map_sub, rmul_cone]

private theorem hbd_hp (k : G) (m : ℕ) (y : Ch A G (m + 1)) :
    hbd A G (m + 1) (hp A k (m + 1) y) = rmul A k (m + 1) y - y - hp A k m (hbd A G m y) := by
  induction m with
  | zero =>
    have r0 : ∀ w : Ch A G 0, rmul A k 0 w = w := fun w => by
      simp only [rmul, Finsupp.lmapDomain_apply]
      rw [show (fun (x : Fin 0 → G) (i : Fin 0) => x i * k) = id from funext fun x => funext fun i => i.elim0,
        Finsupp.mapDomain_id]
    refine LinearMap.congr_fun (ext_cone A ((hbd A G 1).comp (hp A k 1))
      (rmul A k 1 - LinearMap.id - (hp A k 0).comp (hbd A G 0)) fun a w => ?_) y
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hp_cone, hbd_cone, hp.eq_1, LinearMap.zero_apply, LinearMap.zero_apply, sub_zero, sub_zero,
      rmul_cone, hbd_cone_zero, r0]
  | succ m ih =>
    refine LinearMap.congr_fun (ext_cone A ((hbd A G (m + 1 + 1)).comp (hp A k (m + 1 + 1)))
      (rmul A k (m + 1 + 1) - LinearMap.id - (hp A k (m + 1)).comp (hbd A G (m + 1))) fun a w => ?_) y
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hp_cone, hbd_cone, map_sub, map_sub, hbd_rmul, hbd_cone, ih]
    simp only [map_sub, hp_cone]
    abel

private theorem hbd_hd (k k' : G) (m : ℕ) (y : Ch A G (m + 1)) :
    hbd A G (m + 2) (hd A k k' (m + 1) y) = hd A k k' m (hbd A G m y) -
      (hp A (k * k') (m + 1) y - hp A k (m + 1) y - hp A k' (m + 1) (rmul A k (m + 1) y)) := by
  induction m with
  | zero =>
    refine LinearMap.congr_fun (ext_cone A ((hbd A G (0 + 2)).comp (hd A k k' (0 + 1)))
      ((hd A k k' 0).comp (hbd A G 0) - (hp A (k * k') (0 + 1) - hp A k (0 + 1) - (hp A k' (0 + 1)).comp (rmul A k (0 + 1))))
      fun a w => ?_) y
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    simp only [hd_cone, hbd_cone, map_add (f := _), map_sub, hbd_hp, rmul_rmul, hbd_rmul, hbd_cone_zero, hd.eq_1, hp.eq_1,
      LinearMap.zero_apply, hp_cone, sub_zero, map_zero, add_zero]
    abel
  | succ m ih =>
    refine LinearMap.congr_fun (ext_cone A ((hbd A G (m + 1 + 2)).comp (hd A k k' (m + 1 + 1)))
      ((hd A k k' (m + 1)).comp (hbd A G (m + 1)) - (hp A (k * k') (m + 1 + 1) - hp A k (m + 1 + 1) -
        (hp A k' (m + 1 + 1)).comp (rmul A k (m + 1 + 1)))) fun a w => ?_) y
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    simp only [hd_cone, hbd_cone, map_add (f := _), map_sub, hbd_hp, rmul_rmul, hbd_rmul, ih, hp_cone]
    abel

private theorem pr_rmul (k : G) (m : ℕ) (y : Ch A G (m + 1)) :
    pr A G m (rmul A k (m + 1) y) = cm A (MulAut.conj k⁻¹).toMonoidHom m (pr A G m y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), h1, h2]
  | single x b =>
    simp only [pr, rmul, cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    congr 1
    funext i
    simp [MulAut.conj_apply, mul_assoc]

private noncomputable def sec (G : Type) [Group G] (m : ℕ) : Ch A G m →ₗ[A] Ch A G (m + 1) :=
  Finsupp.lmapDomain A A fun g => Fin.partialProd g

private theorem pr_sec (m : ℕ) (z : Ch A G m) : pr A G m (sec A G m z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), h1, h2]
  | single x b =>
    simp only [pr, sec, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Fin.partialProd_right_inv]

private theorem hd_sec_pr (k k' : G) (m : ℕ) (y : Ch A G (m + 1)) :
    pr A G (m + 2) (hd A k k' (m + 1) (sec A G m (pr A G m y))) = pr A G (m + 2) (hd A k k' (m + 1) y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y1 y2 h1 h2 => simp only [map_add (f := _), h1, h2]
  | single x b =>
    have hs : sec A G m (pr A G m (Finsupp.single x b)) = lmul A (x 0)⁻¹ (m + 1) (Finsupp.single x b) := by
      simp only [pr, sec, lmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      congr 1
      funext i
      have h := congrFun (Fin.partialProd_left_inv x) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [eq_inv_mul_iff_mul_eq]
      exact h
    rw [hs, UpperTheory.leftMulChain_chainHomotopic]

end UpperTheory.V.ZK.PM

open UpperTheory.V.ZK.PM in
theorem UpperTheory.V.ZK.sPrismMul :
    UpperTheory.V.ZK.SPrismMul := by
  intro A _ G _ k k' m z hz
  have hz' : pr A G (m + 1) (sec A G (m + 1) z) = z := pr_sec A (m + 1) z
  set y := sec A G (m + 1) z
  have h0 : pr A G (m + 1 + 1) (hd A k k' (m + 1) (PM.hbd A G (m + 1) y)) = 0 := by
    rw [← hd_sec_pr, ← UpperTheory.tupleChain_boundary_formula, hz', hz, map_zero, map_zero, map_zero]
  have hX := hbd_hd A k k' (m + 1) y
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at hX
  refine LinearMap.mem_range.mpr ⟨-(pr A G (m + 1 + 2) (hd A k k' (m + 1 + 1) y)), ?_⟩
  rw [← hz', ← pr_rmul, ← UpperTheory.coneHomotopy_boundary_formula, ← UpperTheory.coneHomotopy_boundary_formula, ← UpperTheory.coneHomotopy_boundary_formula, ← map_sub, ← map_sub, hX,
    map_sub, h0, ← UpperTheory.tupleChain_boundary_formula, zero_sub, map_neg]

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToOmegaSpanModMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegenerates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneDiagSumEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnectingSumMultDiag
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  [IsCocomm R A] [IsCocomm R B]


variable (R A) in
abbrev multDiag (i : ℕ) : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (mulBy R A i : A →ₐ[R] A) (AlgHom.id R _) (fun _ _ ↦ Commute.all _ _)


variable (R A) in
abbrev valZero : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (counitAlgHom R A) (counitAlgHom R A) (fun _ _ ↦ Commute.all _ _)


theorem pullTwo_mulBy_eq (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) (k : ℕ) :
    pullbackTwo (mulBy R A k) c = algebraMap R _ (valZero R A c) + k • c +
      cobOne R A (∑ i ∈ Finset.range k, multDiag R A i c) := by
  induction k with
  | zero =>
    have h0 : ∀ a : A, mulBy R A 0 a = algebraMap R A (counit a) := fun _ => rfl
    rw [Finset.sum_range_zero, map_zero, zero_smul, add_zero, add_zero]
    generalize c = t
    induction t with
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
    | tmul a b =>
      simp [h0, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
        smul_smul, mul_comm]
  | succ k ih =>
    have h := pullTwo_convMul (mulBy R A k) (BialgHom.id R A) c hc
    have e : (toConv (mulBy R A k) * toConv (BialgHom.id R A)).ofConv = mulBy R A (k + 1) := by
      rw [mulBy, mulBy, pow_succ]
    have e2 : ∀ t : A ⊗[R] A, LinearMap.mul' R A (TensorProduct.map (mulBy R A k : A →ₗ[R] A)
        (BialgHom.id R A : A →ₗ[R] A) t) = multDiag R A k t := fun t => by
      induction t with
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
      | tmul a b => simp
    rw [e, e2, pullTwo_id, ih] at h
    rw [h, Finset.sum_range_succ, map_add (f := _), succ_nsmul]
    abel

end PDiv

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem cobOne_diagSum_eq (p : ℕ) (R : Type) [CommRing R] (G : PDivGroup p R) (n m : ℕ) (hm : (m : R) = 0) :
    ∀ c ∈ symCocycles R (G.A n), cobOne R (G.A n) (diagSum R (G.A n) m c) = pullbackTwo (mulBy R (G.A n) m) c -
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
        (fun _ _ ↦ Commute.all _ _) c) • (1 : G.A n ⊗[R] G.A n) := by
  intro c hc
  have hd : diagSum R (G.A n) m c = ∑ i ∈ Finset.range m, multDiag R (G.A n) i c := by
    simp [diagSum, LinearMap.sum_apply]
  have hz : m • c = 0 := by rw [← Nat.cast_smul_eq_nsmul R, hm, zero_smul]
  rw [pullTwo_mulBy_eq c hc m, hz, add_zero, hd, Algebra.algebraMap_eq_smul_one]
  abel

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamClassOfRigidifiedExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclesOmega
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.exists_cocycles_omega : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
    ∃ (z : G.cocycles) (w : G.omega), (∀ n, z.1 n = d.coc n) ∧ ∀ n, w.1 n = d.om n := by
  intro R _ A _ hA p G t c d
  have hs : IsSymCoc d.g := isSymCoc_of_isAdd R A hA _ _ d.add
  refine ⟨⟨fun n => d.coc n, fun n => ⟨coc_mem_symCocycles R A p G t c d hs n,
    Dat.pullTwo_res_coc R A p G t c d n⟩⟩, ⟨fun n => d.om n, fun n => OmRes.cotMap_res_om R A p G t c d n⟩,
    fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupCocycleMemCobRangeOfDiagonalSumZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumPullTwo
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem diagSum_pullTwo : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] [CommRing D'] [Bialgebra R D'] [Coalgebra.IsCocomm R D'] (f : D →ₐc[R] D')
    (m : ℕ) (c : D ⊗[R] D), f (diagSum R D m c) = diagSum R D' m (pullbackTwo f c) := by
  intro R _ D D' _ _ _ _ _ _ f m c
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [diagSum_tmul, pullbackTwo, TensorProduct.map_tmul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mulBy]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleMemRangeCobOfPullbackMulByPow
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_injective_mulBy_pow_eq_comp_resOne (n : ℕ) : ∃ q : G.A 1 →ₐc[R] G.A (n + 1),
    Function.Injective q ∧ ∀ a, mulBy R _ (p ^ n) a = q (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R _, Function.injective_id, fun a => ?_⟩
    simp only [pow_zero, mulBy, pow_one, ofConv_toConv, BialgHom.coe_id, id_eq, resOne_zero]
  | succ n ih =>
    obtain ⟨q, hq, hq'⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp q, (Test.mulP_injective G (n + 1)).comp hq, fun a => ?_⟩
    rw [pow_succ', ← mulBy_mulBy, ← mulP_res, map_mulBy, hq', BialgHom.comp_apply,
      resOne_succ]

theorem mulBy_pow_zero_eq_id (n : ℕ) : mulBy R (G.A n) (p ^ 0) = BialgHom.id R _ := by
  rw [pow_zero, mulBy, pow_one]

theorem exists_cob_eq_mulBy_eq (c : G.cocycles) (B : G.funs)
    (hB : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n)) (h1 : B.1 1 = 0) :
    ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ p (e.1 n) = B.1 n := by
  have hlev : ∀ n, cobOne R _ (B.1 (n + 1)) = pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    rw [hB, ← mulP_comp_res, pullTwo_comp, (c.2 n).2]
  have hinv : ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ 1 := fun n =>
    G.transl_eq_of_cobOne_eq_pullTwo n _ _ (hlev n) (by rw [resOne_funs, h1])
  choose e he using fun n => G.exists_mulP_eq_of_transl_eq n (B.1 (n + 1)) (hinv n)
  have hres : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply Test.mulP_injective G n
    rw [mulP_res, he n, ← B.2 (n + 1), ← he (n + 1), res_mulP]
  refine ⟨⟨e, hres⟩, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
  · change cobOne R _ (e n) = c.1 n
    apply G.pullbackTwo_mulP_injective n
    rw [pullTwo_cobOne, he n, hlev n]
  · change mulBy R _ p (e n) = B.1 n
    rw [← res_mulP, he n, B.2 n]

theorem exists_cob_eq_mulBy_pow_eq [Fact p.Prime] (N : ℕ) : ∀ (c : G.cocycles) (B : G.funs),
    (∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B.1 N = 0 →
      ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ (p ^ N) (e.1 n) = B.1 n := by
  induction N with
  | zero =>
    intro c B hB _
    refine ⟨B, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
    · change cobOne R _ (B.1 n) = c.1 n
      rw [hB n, mulBy_pow_zero_eq_id, pullTwo_id]
    · rw [mulBy_pow_zero_eq_id]
      rfl
  | succ N ih =>
    intro c B hB hN
    let c' : G.cocycles := cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c
    have hc' : ∀ n, c'.1 n = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n => by
      change pullbackTwo (Hom.app ((p : ℤ_[p]) • 𝟙 G) n) (c.1 n) = _
      rw [natCast_smul_id_app]
    have hB' : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c'.1 n) := fun n => by
      rw [hB n, hc' n, ← pullTwo_comp, pow_succ,
        show (mulBy R (G.A n) (p ^ N)).comp (mulBy R _ p) = mulBy R _ (p ^ N * p) from
          BialgHom.ext fun a => mulBy_mulBy _ _ a]
    obtain ⟨e', he', hm'⟩ := ih c' B hB' ((B.2 N).symm.trans (by rw [hN, map_zero]))
    have h1 : e'.1 1 = 0 := by
      obtain ⟨q, hq, hq'⟩ := G.exists_injective_mulBy_pow_eq_comp_resOne N
      apply hq
      rw [map_zero, ← G.resOne_funs e' N, ← hq', hm', hN]
    have hA : ∀ n, cobOne R _ (e'.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n =>
      (congrArg (fun d : G.cocycles => d.1 n) he').trans (hc' n)
    obtain ⟨e, he, hm⟩ := G.exists_cob_eq_mulBy_eq c e' hA h1
    refine ⟨e, he, fun n => ?_⟩
    rw [pow_succ, ← mulBy_mulBy, hm, hm']

end PDivGroup

theorem cocycle_mem_range_cob_of_pullback_mulBy_pow :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (G : PDivGroup p R) (N : ℕ) (c : G.cocycles)
      (B : ∀ n, G.A n), (∀ n, G.res n (B (n + 1)) = B n) →
      (∀ n, cobOne R (G.A n) (B n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B N = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G N c B hB hc hN
  obtain ⟨e, he, -⟩ := G.exists_cob_eq_mulBy_pow_eq N c ⟨B, hB⟩ hc hN
  exact ⟨e, he⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupCocycleMemCobRangeOfDiagonalSumZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lift_counit_pullTwo {R D D' : Type} [CommRing R] [CommRing D] [Bialgebra R D] [CommRing D']
    [Bialgebra R D'] (f : D →ₐc[R] D') (c : D ⊗[R] D) :
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D') (Bialgebra.counitAlgHom R D')
        (fun _ _ ↦ Commute.all _ _) (pullbackTwo f c) =
      Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D) (Bialgebra.counitAlgHom R D)
        (fun _ _ ↦ Commute.all _ _) c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem diagSum_one (R D : Type) [CommRing R] [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) :
    diagSum R D m 1 = (m : D) := by
  rw [Algebra.TensorProduct.one_def, diagSum_tmul]
  simp

theorem cocycle_mem_range_cob_of_diagSum_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
      ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 →
        z ∈ LinearMap.range G.cob := by
  intro p _ R _ N hp G z hz
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow, hp]
  let ε : ∀ n, G.A n ⊗[R] G.A n →ₐ[R] R := fun n =>
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
      (fun _ _ ↦ Commute.all _ _)
  have hr : ∀ n, ε n (z.1 n) = ε 0 (z.1 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← (z.2 n).2]; exact (lift_counit_pullTwo _ _).symm
  let o : G.funs := ⟨fun _ => 1, fun n => map_one (G.res n)⟩
  let z' : G.cocycles := z + ε 0 (z.1 0) • G.cob o
  have hz' : ∀ n, z'.1 n = z.1 n - ε 0 (z.1 0) • (1 : G.A n ⊗[R] G.A n) := by
    intro n
    change z.1 n + ε 0 (z.1 0) • cobOne R (G.A n) 1 = _
    rw [cobOne_apply, Bialgebra.comul_one, ← Algebra.TensorProduct.one_def, sub_self, zero_sub, smul_neg,
      sub_eq_add_neg]
  have h0 : ∀ n, ε n (z'.1 n) = 0 := by
    intro n
    rw [hz', map_sub, map_smul, map_one, hr, smul_eq_mul, _root_.mul_one, sub_self]
  have hmem : z' ∈ LinearMap.range G.cob := by
    refine cocycle_mem_range_cob_of_pullback_mulBy_pow p R G N z'
      (fun n => diagSum R (G.A n) (p ^ N) (z'.1 n)) (fun n => ?_) (fun n => ?_) ?_
    · rw [diagSum_pullTwo, (z'.2 n).2]
    · rw [cobOne_diagSum_eq p R G n (p ^ N) hq _ (z'.2 n).1]
      have := h0 n
      simp only [ε] at this
      rw [this, zero_smul, sub_zero]
    · change diagSum R (G.A N) (p ^ N) (z'.1 N) = 0
      rw [hz', map_sub, map_smul, hz, diagSum_one, ← map_natCast (algebraMap R (G.A N)), hq, map_zero,
        smul_zero, sub_zero]
  have : z = z' - ε 0 (z.1 0) • G.cob o := by simp [z']
  rw [this]
  exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ ⟨o, rfl⟩)

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupCocycleMemCobRangeOfDiagonalSumZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_cocycle_mem_cob_range_of_diagonalSum_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 → z ∈ LinearMap.range G.cob := by
  first | exact @GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero | exact GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero | (intros; apply GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsCharTorsVal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {p : ℕ} {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {G : PDivGroup p R}
  (t : PDivGroup.TorsionTower G A) (N : ℕ)


open Classical in
def torsVal (b : G.A N) : Fn0 A := fun _ _ _ x ↦
  if h : x ^ p ^ N = 1 then t.lift N x h b else 0

theorem lift_spOver {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (w : Pt A D) (hw : w ^ p ^ N = 1) (hw' : (spOver φ ≫ w) ^ p ^ N = 1) :
    t.lift N (spOver φ ≫ w) hw' = φ.comp (t.lift N w hw) :=
  t.inj N D' _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.lift_y])

theorem lift_mul {D : Type} [CommRing D] [Algebra R D] (w w' : Pt A D) (hw : w ^ p ^ N = 1)
    (hw' : w' ^ p ^ N = 1) (h : (w * w') ^ p ^ N = 1) :
    t.lift N (w * w') h = (toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv :=
  t.inj N D _ _ (by rw [t.lift_y, t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y])

theorem isTorsChar_torsVal (b : G.A N) (hb : cobOne R (G.A N) b = 0) :
    IsTorsChar (p ^ N) (torsVal t N b) := by
  have hc : Coalgebra.comul (R := R) b = b ⊗ₜ 1 + 1 ⊗ₜ b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb; exact hb
  refine ⟨fun D _ _ D' _ _ φ w hw ↦ ?_, fun D _ _ w w' hw hw' ↦ ?_⟩
  · have hw2 : (spOver φ ≫ w) ^ p ^ N = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    simp only [torsVal, dite_eq_left hw, dite_eq_left hw2, lift_spOver t N φ w hw hw2,
      AlgHom.comp_apply]
  · have h : (w * w') ^ p ^ N = 1 := (t.exists_iff N _).1
      ⟨(toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv, by
        rw [t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y]⟩
    simp only [torsVal, dite_eq_left hw, dite_eq_left hw', dite_eq_left h, lift_mul t N w w' hw hw' h]
    change (toConv (t.lift N w hw) * toConv (t.lift N w' hw')) b = _
    simp only [AlgHom.convMul_apply, hc, map_add, Algebra.TensorProduct.lift_tmul, map_one,
      _root_.mul_one, _root_.one_mul]

theorem exists_isTorsChar :
    ∀ (p : ℕ) (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (G : PDivGroup p R)
      (t : PDivGroup.TorsionTower G A) (N : ℕ) (b : G.A N),
      cobOne R (G.A N) b = 0 → ∃ β : Fn0 A, IsTorsChar (p ^ N) β ∧
        ∀ (D : Type) [CommRing D] [Algebra R D] (φ : G.A N →ₐ[R] D), β D (spOver φ ≫ t.y N) = φ b := by
  intro p R _ A _ G t N b hb
  refine ⟨torsVal t N b, isTorsChar_torsVal t N b hb, fun D _ _ φ ↦ ?_⟩
  have h : (spOver φ ≫ t.y N) ^ p ^ N = 1 := (t.exists_iff N _).1 ⟨φ, rfl⟩
  have e : t.lift N (spOver φ ≫ t.y N) h = φ := t.inj N D _ _ (t.lift_y N _ h)
  simp only [torsVal, dite_eq_left h, e]

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamClassOfRigidifiedExtension
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem pullTwo_mulBy_pow_self (p : ℕ) (R : Type) [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) :
    pullbackTwo (PDiv.mulBy (R := R) (A := G.A n) (p ^ n)) c =
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
        (fun _ _ ↦ Commute.all _ _) c) • (1 : G.A n ⊗[R] G.A n) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have ha := G.mulBy_pow_self n a
    have hb := G.mulBy_pow_self n b
    simp only [pullbackTwo, TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
    change PDiv.mulBy (R := R) (A := G.A n) (p ^ n) a ⊗ₜ[R]
      PDiv.mulBy (R := R) (A := G.A n) (p ^ n) b = _
    rw [ha, hb]
    simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_smul,
      TensorProduct.tmul_smul, mul_comm]
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), add_smul]

theorem exists_isCan_rigToExt_eq : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → AllPrim (dp0 R) (𝟙 _) A →
    Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A) (x : G.RigExt),
      ∃ (c : primDR A) (x' : G.RigExt), IsCan t c x' ∧ G.rigToExt x' = G.rigToExt x := by
  intro p _ R _ N hN A _ hA hP hS G t x
  obtain ⟨⟨z, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow, hN]
  have hcob : cobOne R (G.A N) (diagSum R (G.A N) (p ^ N) (z.1 N)) = 0 := by
    rw [cobOne_diagSum_eq p R G N (p ^ N) hq _ (z.2 N).1, pullTwo_mulBy_pow_self, sub_self]
  obtain ⟨β, hβ, hβy⟩ := exists_isTorsChar p R A G t N _ hcob
  obtain ⟨c, d, hd⟩ := GlobalTheory.T.exists_primitive_deRham_class_torsion_character p R N hN A hA hP hS G t β hβ
  obtain ⟨z', w', hz', hw'⟩ := Dat.exists_cocycles_omega R A hA p G t c d
  refine ⟨c, G.rigMk (z', w'), ⟨d, z', w', hz', hw', rfl⟩, ?_⟩
  have h1 : diagSum R (G.A N) (p ^ N) (z'.1 N) = diagSum R (G.A N) (p ^ N) (z.1 N) := by
    rw [hz', Dat.diagSum_coc R A p G t c d N hN, hd _ _ (t.y_pow N)]
    have h2 := hβy (G.A N) (AlgHom.id R (G.A N))
    rwa [spOver_id, Category.id_comp] at h2
  have hdiag : diagSum R (G.A N) (p ^ N) ((z' - z).1 N) = 0 := by
    rw [Submodule.coe_sub, Pi.sub_apply, map_sub, h1, sub_self]
  have hmem := GlobalTheory.T.pDivGroup_cocycle_mem_cob_range_of_diagonalSum_zero p R N hN G (z' - z) hdiag
  show G.rigToExt (Submodule.Quotient.mk (z', w')) = G.rigToExt (Submodule.Quotient.mk (z, w))
  simp only [PDivGroup.rigToExt, Submodule.mapQ_apply, LinearMap.fst_apply]
  exact (Submodule.Quotient.eq _).2 hmem

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamClassOfRigidifiedExtensionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRham_class_of_rigidified_extension :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → AllPrim (dp0 R) (𝟙 _) A →
    Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A) (x : G.RigExt),
      ∃ (c : primDR A) (x' : G.RigExt), IsCan t c x' ∧ G.rigToExt x' = G.rigToExt x :=
  GlobalTheory.PtExt.exists_isCan_rigToExt_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCompHodgeToOmegaEqLinearForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCompHodgeToOmegaEqLinearForm
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_lie_comp_psi_eq :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    (∃ N' : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N') →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ l : Module.Dual R (PrimitiveSubmodule A), ∃ x : G.Lie, ∀ c, x (ψ c) = l c := by
  intro p _ R _ N hN A _ hab hLE hN' G t ψ hψ l
  obtain ⟨N', hc⟩ := hN'
  let h : HdR A := l ∘ₗ Submodule.projectionOnto (PrimitiveSubmodule A) N' hc
  obtain ⟨v, hv, -⟩ := hLE.1 h
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨x, hx, -⟩ := t.existsUnique_lieCorr hv.1
  refine ⟨x, fun c => ?_⟩
  obtain ⟨⟨c, hc1⟩, hc2⟩ := c
  have hc3 : c ∈ F1 (A.hom ≫ 𝟙 _) := hc2
  rw [hodgeFiltration_eq_range] at hc3
  obtain ⟨β, rfl⟩ := hc3
  rw [GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent p R N hN A hab G t ψ hψ β hc1 hc2 x v hx, ← hv.2 β hc1]
  change l (Submodule.projectionOnto (PrimitiveSubmodule A) N' hc ⟨_, hc1⟩) = _
  exact congrArg l (Submodule.projectionOnto_apply_left hc ⟨⟨_, hc1⟩, hc2⟩)

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCompHodgeToOmegaEqLinearFormStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_comp_hodgeToOmega_eq_linearForm :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    (∃ N' : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N') →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ l : Module.Dual R (PrimitiveSubmodule A), ∃ x : G.Lie, ∀ c, x (ψ c) = l c :=
  @GlobalTheory.PtExt.exists_lie_comp_psi_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfDualMapSurjectiveOfProjective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem injective_of_dualMap_surjective_of_projective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Projective R M]
      (N : Type) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
      Function.Surjective f.dualMap → Function.Injective f := by
  intro R _ M _ _ _ N _ _ f hf
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  refine (Module.forall_dual_apply_eq_zero_iff R m).mp fun φ => ?_
  obtain ⟨ψ, rfl⟩ := hf φ
  simp [LinearMap.dualMap_apply, hm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotent
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem bijective_of_isCan_of_isNilpotent_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  intro hH p _ R _ hnil A _ g hA hg G t L hL
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hF, hHo, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hH
  obtain ⟨hAll, -⟩ := hF R A g hA hg
  obtain ⟨hLie, hCompl, hFfin, hFproj, -⟩ := hHo R A g hA hg
  have hO : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) :=
    GlobalTheory.PtExt.toH1O_surjective_of_abelian hH R A g hA hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t

  haveI : Module.Finite R (Cot R (G.A N)) := .of_surjective _ (AugCot.d_surjective _)
  haveI : Module.Finite R G.omega :=
    .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
  haveI : Module.Projective R (PrimitiveSubmodule A) := hFproj

  have hψs : Function.Surjective ψ :=
    GlobalTheory.surjective_of_range_sup_smul_top_eq_top R _ G.omega ψ
      (GlobalTheory.T.primitive_hodge_to_omega_span_mod_maximal hH p R N hN A g hA hg G t ψ hψ)
  have hψi : Function.Injective ψ := by
    refine GlobalTheory.injective_of_dualMap_surjective_of_projective R _ G.omega ψ fun l => ?_
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_lie_comp_hodgeToOmega_eq_linearForm p R N hN A hA hLie hCompl G t ψ hψ l
    exact ⟨x, LinearMap.ext fun c => hx c⟩

  have hLF : ∀ c : PrimitiveSubmodule A, L c.1 = G.rigOfOmega (ψ c) := fun c =>
    GlobalTheory.PtExt.isCan_unique R A p G t c.1 hA _ _ (hL c.1) (hψ c)
  refine ⟨(injective_iff_map_eq_zero L).2 fun c hc => ?_, fun x => ?_⟩
  · have hcF : c ∈ PrimitiveSubmodule A :=
      GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hL c) (by rw [hc]; exact G.rigToExt.map_zero)
    have h1 : G.rigOfOmega (ψ ⟨c, hcF⟩) = 0 := by rw [← hLF ⟨c, hcF⟩]; exact hc
    have h2 : ψ ⟨c, hcF⟩ = 0 :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (by rw [h1, map_zero])
    have h3 : (⟨c, hcF⟩ : PrimitiveSubmodule A) = 0 := hψi (by rw [h2, map_zero])
    exact congrArg Subtype.val h3
  · obtain ⟨c, x', hcx', hx'⟩ := GlobalTheory.T.exists_deRham_class_of_rigidified_extension p R N hN A hA hAll hO G t x
    have hx'L : x' = L c := GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ hcx' (hL c)
    have hd : G.rigToExt (x - L c) = 0 := by
      exact (G.rigToExt.map_sub x (L c)).trans (sub_eq_zero.mpr (hx'L ▸ hx'.symm))
    obtain ⟨w, hw⟩ := (G.exact_rigOfOmega_rigToExt (x - L c)).1 hd
    obtain ⟨c₁, rfl⟩ := hψs w
    refine ⟨c + c₁.1, ?_⟩
    rw [map_add (f := _), hLF c₁, hw, add_sub_cancel]

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotentStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  first | exact @GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | exact GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtensionIsoOfHodgeDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalDeRhamRigidExtensionFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTower
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TowerDim

theorem exists_smoothOfRelativeDimension_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ G : PDivGroup p R, G.TorsionTower A → ∃ g, SmoothOfRelativeDimension g A.hom := by
  intro hH p _ R _ hp A _ hA G t
  have hF : GlobalTheory.Published.AbelianDeRham.Free := (GlobalTheory.abelianDeRham_free_baseChange_rigid hH).1
  have hs := hA.smooth
  refine ⟨G.height / 2, GlobalTheory.FibreDim.smoothOfRelativeDimension_of_forall_field R A _ hs fun k _ _ ↦ ?_⟩
  have hk : IsNilpotent (p : k) := by simpa using hp.map (algebraMap R k)
  have hk0 : (p : k) = 0 := hk.eq_zero
  letI : GrpObj ((Over.pullback (spMap (algebraMap R k))).obj A) := Functor.grpObjObj
  have h := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R k))
  have hAk : IsAbelianScheme ((Over.pullback (spMap (algebraMap R k))).obj A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  obtain ⟨gk, hgk⟩ := GlobalTheory.AbelianDim.exists_relDim k ((Over.pullback (spMap (algebraMap R k))).obj A) hAk
  let tk := t.baseChange h
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap k ((Over.pullback (spMap (algebraMap R k))).obj A) p
    (G.baseChange k) tk hAk
  have hbij : Function.Bijective L :=
    GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent hH p k hk _ gk hAk hgk (G.baseChange k) tk L fun c ↦ (hL c (L c)).2 rfl
  obtain ⟨hfin, hprj, hrk⟩ := hF.prim hAk hgk
  have h1 : Module.finrank k (primDR ((Over.pullback (spMap (algebraMap R k))).obj A)) = 2 * gk := by
    have := hrk ⊥
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (G.baseChange k).RigExt = G.height :=
    (GlobalTheory.PDivGroup.finrank_rigExt_omega p k hk0 (G.baseChange k)).2.2.1
  have h3 : 2 * gk = G.height := by
    rw [← h1, ← h2]; exact (LinearEquiv.ofBijective L hbij).finrank_eq
  have h4 : G.height / 2 = gk := by omega
  rw [h4]
  exact hgk

end GlobalTheory.TowerDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTowerStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relativeDimension_abelian_torsionTower : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ G : PDivGroup p R, G.TorsionTower A → ∃ g, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | exact GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | (intros; apply GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtension
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt


set_option maxHeartbeats 1000000 in
theorem isLieImage_iff_lieCorr : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (E : primDR A ≃ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (E c)) → ∀ (h : HdR A) (v : epsR R ⟶ A), IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie (E.symm.dualMap h)) v := by
  intro hHdR p _ R _ hnil A _ g hA hsm G t E hE h v
  obtain ⟨N, hN⟩ := hnil
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩

  have key : ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) (w : G.omega),
      IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) → G.lieUnivToLie (E.symm.dualMap h) w = h ⟨_, hβ⟩ := by
    intro β hβ w hw
    have e : E ⟨_, hβ⟩ = G.rigOfOmega w := isCan_unique R A p G t _ hA _ _ (hE _) hw
    change (E.symm.dualMap h) (G.rigOfOmega w) = _
    change h (E.symm (G.rigOfOmega w)) = _
    rw [← e, LinearEquiv.symm_apply_apply]
  constructor
  · rintro ⟨hv, hh⟩
    obtain ⟨x', hx', -⟩ := t.existsUnique_lieCorr hv
    obtain ⟨ψ, hψ⟩ := T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
    haveI : Module.Finite R G.omega := .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
    have hs := surjective_of_range_sup_smul_top_eq_top R _ _ ψ
      (T.primitive_hodge_to_omega_span_mod_maximal hHdR p R N hN A g hA hsm G t ψ hψ)
    suffices e : x' = G.lieUnivToLie (E.symm.dualMap h) by rw [← e]; exact hx'
    refine LinearMap.ext fun w => ?_
    obtain ⟨c, rfl⟩ := hs w
    obtain ⟨c, hF⟩ := c
    have hF' := hF
    change c.1 ∈ F1 _ at hF'
    rw [hodgeFiltration_eq_range] at hF'
    obtain ⟨c, hc⟩ := c
    obtain ⟨β, rfl⟩ := hF'
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hc
    have hw : ψ ⟨_, hF⟩ = w :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (isCan_unique R A p G t _ hA _ _ (hψ _) hw2)
    rw [key β hc _ (hψ ⟨_, hF⟩), hw, lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x' v hx', hh β hc]
  · intro hx
    refine ⟨hx.1, fun β hβ => ?_⟩
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
    rw [← key β hβ w hw2]
    exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 _ v hx

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtensionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_image_iff_lie_correspondence_deRham_extension : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (E : primDR A ≃ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (E c)) → ∀ (h : HdR A) (v : epsR R ⟶ A), IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie (E.symm.dualMap h)) v := by
  first | exact @GlobalTheory.PtExt.isLieImage_iff_lieCorr | exact GlobalTheory.PtExt.isLieImage_iff_lieCorr | (intros; apply GlobalTheory.PtExt.isLieImage_iff_lieCorr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantForms
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem map_F1prim_eq_range_rigOfOmega (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))))
    (hL : Function.Surjective L) (hc : ∀ c, IsCan t c (L c)) :
    (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
  apply le_antisymm
  · rintro _ ⟨c, hcF, rfl⟩
    refine ⟨ψ ⟨c, hcF⟩, ?_⟩
    exact GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ (hψ ⟨c, hcF⟩) (hc c)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨c, hcw⟩ := hL (G.rigOfOmega w)
    refine ⟨c, GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hc c) ?_, hcw⟩
    rw [hcw]
    exact G.exact_rigOfOmega_rigToExt.apply_apply_eq_zero w

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantFormsStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), Function.Surjective L → (∀ c, IsCan t c (L c)) → (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  first | exact @GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | exact GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | (intros; apply GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalDeRhamRigidExtensionFamily
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DeRhamExt

def canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) :=
  Classical.choose (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA)

theorem isCan_iff_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A)
    (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) : IsCan t c x ↔ canMap p hA t c = x :=
  Classical.choose_spec (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA) c x

theorem isCan_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A) :
    IsCan t c (canMap p hA t c) :=
  (isCan_iff_canMap p hA t c _).2 rfl

theorem canMap_bijective (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] {R : Type}
    [CommRing R] (hR : IsNilpotent (p : R)) {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : Function.Bijective (canMap p hA t) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
  exact GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent hP p R hR A g hA hg G t _ (isCan_canMap p hA t)

def canFamily (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] :
    GlobalTheory.Published.DeRhamVectorExtension.Family p :=
  fun _ _ hR _ _ hA _ t => LinearEquiv.ofBijective (canMap p hA t) (canMap_bijective hP p hR hA t)

theorem exists_canonical_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime],
    ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧
      ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
        (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A),
        IsCan t c (e hR hA t c) := by
  intro hP p _
  refine ⟨canFamily hP p, ?_, ?_, ?_, ?_⟩
  · intro R R' _ _ hR hR' A _ A' _ hA hA' G G' t t' σ φ m c
    exact ((isCan_iff_canMap p hA' t' _ _).1
      (GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality p R R' A A' G G' t t' σ φ m c _ (isCan_canMap p hA t c)))
  · intro R _ hR A _ hA G t
    obtain ⟨N, hN⟩ := hR
    exact GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms p R N hN A hA G t (canMap p hA t)
      (canMap_bijective hP p ⟨N, hN⟩ hA t).2 (isCan_canMap p hA t)
  · intro R _ hR A _ hA G t h v
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
    exact GlobalTheory.T.lie_image_iff_lie_correspondence_deRham_extension hP p R hR A g hA hg G t (canFamily hP p hR hA t)
      (isCan_canMap p hA t) h v
  · intro R _ hR A _ hA G t c
    exact isCan_canMap p hA t c

end GlobalTheory.DeRhamExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalDeRhamRigidExtensionFamilyStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_deRham_rigidExtension_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime], ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧ ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A] (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A), IsCan t c (e hR hA t c) := by
  first | exact @GlobalTheory.DeRhamExt.exists_canonical_family | exact GlobalTheory.DeRhamExt.exists_canonical_family | (intros; apply GlobalTheory.DeRhamExt.exists_canonical_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtensionIsoOfHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem deRhamVectorExtension_of_abelianHodgeDeRham :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DeRhamVectorExtension := by
  intro hHdR p _
  obtain ⟨e, hN, hF, hT, -⟩ := GlobalTheory.T.exists_canonical_deRham_rigidExtension_family hHdR p
  exact ⟨e, hN, hF, hT⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtensionIsoOfHodgeDeRhamStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamVectorExtensionIso_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DeRhamVectorExtension := by
  first | exact @GlobalTheory.deRhamVectorExtension_of_abelianHodgeDeRham | exact GlobalTheory.deRhamVectorExtension_of_abelianHodgeDeRham | (intros; apply GlobalTheory.deRhamVectorExtension_of_abelianHodgeDeRham <;> assumption)
end
end

namespace GlobalTheory

theorem deRhamVectorExtension : GlobalTheory.Published.DeRhamVectorExtension :=
  GlobalTheory.T.deRhamVectorExtensionIso_of_hodgeDeRham GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates

end GlobalTheory

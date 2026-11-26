module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory

namespace GlobalTheory

namespace PDiv

section Lift

variable {R R' M N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R' N]

def liftSemi (f : M →ₛₗ[algebraMap R R'] N) : R' ⊗[R] M →ₗ[R'] N :=
  letI : Module R N := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' N := ⟨fun a b w => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange R'
    { toFun := f, map_add' := map_add f, map_smul' := fun r m => map_smulₛₗ f r m }

@[simp] theorem liftSemi_tmul (f : M →ₛₗ[algebraMap R R'] N) (r : R') (m : M) :
    liftSemi f (r ⊗ₜ m) = r • f m := rfl

end Lift

section Level

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']

def SemiBialgHom.prim (f : SemiBialgHom σ A A') :
    LinearMap.ker (cobOne R A) →ₛₗ[σ] LinearMap.ker (cobOne R' A') where
  toFun b := ⟨f b.1, by
    have hb : cobOne R A b.1 = 0 := b.2
    have hone : SemiBialgHom.lin f 1 = 1 := f.toRingHom.map_one
    have h := congrArg (SemiBialgHom.two f) hb
    simpa only [LinearMap.mem_ker, cobOne_apply, map_sub, SemiBialgHom.two_comul,
      TensorProduct.map_tmul, hone, SemiBialgHom.lin_apply, map_zero] using h⟩
  map_add' _ _ := Subtype.ext (f.toRingHom.map_add _ _)
  map_smul' _ _ := Subtype.ext (f.smul_map _ _)

@[simp] theorem SemiBialgHom.prim_val (f : SemiBialgHom σ A A') (b : LinearMap.ker (cobOne R A)) :
    (f.prim b).1 = f b.1 := rfl

theorem isPrimitiveElem_of_mem_ker {b : A} (hb : b ∈ LinearMap.ker (cobOne R A)) :
    IsPrimitiveElem R b := by
  rw [LinearMap.mem_ker, cobOne_apply, sub_sub, sub_eq_zero] at hb
  exact hb

theorem evalAt_mul [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ ψ : CartierDual R A) :
    CartierDual.evalAt R A b.1 (φ * ψ) =
      counitAlgHom R (CartierDual R A) φ • CartierDual.evalAt R A b.1 ψ +
        counitAlgHom R (CartierDual R A) ψ • CartierDual.evalAt R A b.1 φ :=
  (CartierDual.isPrimitiveElem_iff_mul b.1).1 (isPrimitiveElem_of_mem_ker b.2) φ ψ


variable (R A) in
def primTangent [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    LinearMap.ker (cobOne R A) →ₗ[R] Module.Dual R (Cot R (CartierDual R A)) where
  toFun b := AugCot.lift _ (CartierDual.evalAt R A b.1) (evalAt_mul b)
  map_add' b b' := AugCot.hom_ext fun φ => by simp
  map_smul' r b := AugCot.hom_ext fun φ => by simp

@[simp] theorem primTangent_d [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ : CartierDual R A) :
    primTangent R A b (dUnit (R := R) φ) = φ b.1 := AugCot.lift_d _ _ (evalAt_mul b) φ

variable [IsCocomm R A] [IsCocomm R' A']




end Level

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

def resOne (n : ℕ) : G.A (n + 1) →ₐc[R] G.A 1 :=
  Nat.rec (motive := fun n => G.A (n + 1) →ₐc[R] G.A 1) (BialgHom.id R _)
    (fun n f => f.comp (G.res (n + 1))) n

@[simp] theorem resOne_zero (a : G.A 1) : G.resOne 0 a = a := rfl

@[simp] theorem resOne_succ (n : ℕ) (a : G.A (n + 2)) :
    G.resOne (n + 1) a = G.resOne n (G.res (n + 1) a) := rfl

theorem resOne_surjective (n : ℕ) : Function.Surjective (G.resOne n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp (G.res_surjective (n + 1))

theorem resOne_funs (B : G.funs) (n : ℕ) : G.resOne n (B.1 (n + 1)) = B.1 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [resOne_succ, B.2, ih]

theorem resOne_mulBy (n : ℕ) (a : G.A (n + 1)) :
    G.resOne n (mulBy R _ p a) = algebraMap R _ (counit a) := by
  have h := G.mulBy_pow_self 1 (G.resOne n a)
  rw [pow_one, CoalgHomClass.counit_comp_apply] at h
  rw [map_mulBy, h]

theorem resOne_mulP (n : ℕ) (a : G.A n) :
    G.resOne n (G.mulP n a) = algebraMap R _ (counit a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, resOne_mulBy, CoalgHomClass.counit_comp_apply]

def transl (n : ℕ) : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1 :=
  (Algebra.TensorProduct.map (AlgHom.id R _) (G.resOne n : G.A (n + 1) →ₐ[R] G.A 1)).comp
    (comulAlgHom R _)

theorem transl_apply (n : ℕ) (a : G.A (n + 1)) :
    G.transl n a = (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ (comul a) := rfl

theorem transl_res (n : ℕ) (a : G.A (n + 2)) :
    G.transl n (G.res (n + 1) a) =
      (G.res (n + 1) : G.A (n + 2) →ₗ[R] G.A (n + 1)).rTensor _ (G.transl (n + 1) a) := by
  rw [transl_apply, transl_apply, ← pullTwo_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x y => simp

theorem transl_mulP (n : ℕ) (a : G.A n) : G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ 1 := by
  rw [transl_apply, ← pullTwo_comul]
  conv_rhs => rw [← (TensorProduct.rid R _).apply_symm_apply a, TensorProduct.rid_symm_apply,
    ← Coalgebra.lTensor_counit_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]
  | tmul x y => simp [resOne_mulP, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem pullbackTwo_mulP_injective (n : ℕ) : Function.Injective (pullbackTwo (G.mulP n)) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n) (Test.mulP_injective G n)

theorem res_eq_zero_of_cobOne_eq_zero (hp : (p : R) = 0) (n : ℕ) {b : G.A (n + 1)}
    (hb : cobOne R _ b = 0) : G.res n b = 0 :=
  Test.mulP_injective G n (by
    rw [mulP_res, (mulBy_of_cobOne_eq_zero hb p).1, ← Nat.cast_smul_eq_nsmul R, hp, zero_smul,
      map_zero])

theorem eq_zero_of_cob_eq_zero (hp : (p : R) = 0) {B : G.funs} (hB : G.cob B = 0) : B = 0 :=
  Subtype.ext (funext fun n => (B.2 n).symm.trans (G.res_eq_zero_of_cobOne_eq_zero hp n
    (congrArg (fun c : G.cocycles => c.1 (n + 1)) hB)))

theorem rigOfOmega_injective_of_eq_zero (hp : (p : R) = 0) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero hp (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

theorem omegaLevel_one_bijective (hp : (p : R) = 0) : Function.Bijective (G.omegaLevel 1) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, G.omegaLevel_surjective 1⟩
  obtain ⟨v, rfl⟩ := (G.omega_val_eq_zero_iff 1 w).1 hw
  rw [pow_one, hp, zero_smul]

def primLie : LinearMap.ker (cobOne R (G.A 1)) →ₗ[R] G.dual.Lie :=
  (G.dual.omegaLevel 1).dualMap ∘ₗ primTangent R (G.A 1)

theorem primLie_apply (b : LinearMap.ker (cobOne R (G.A 1))) (w : G.dual.omega)
    (φ : CartierDual R (G.A 1)) (h : w.1 1 = dUnit (R := R) φ) : G.primLie b w = φ b.1 :=
  (congrArg (primTangent R (G.A 1) b) h).trans (primTangent_d b φ)

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

namespace CupSpec

variable {R : Type} [CommRing R]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g :=
  ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x

section Cup
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc}

def awF {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U) : Sec (K.X w) U :=
  ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev a p _ rfl U (x.sub 0 p (by omega))) (ev b (N - p) _ rfl U (x.sub p (N - p) (by omega)))

theorem awF_res {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) :
    Sec.res g (awF μ hk a b N w h U x) = awF μ hk a b N w h V (x.res g) := by
  unfold awF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Sec.res, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, sub_res, sub_res, ← ev_res, ← ev_res, ← μ.nat]

theorem isAW_exists {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) :
    ∃ c, μ.IsAW hk a b c := by
  obtain ⟨c, hc⟩ := ev_exists (awF μ hk a b) (fun N w h V U g x => awF_res μ hk a b N w h g x)
  exact ⟨c, hc⟩

theorem isAW_unique {n m k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b c') : c = c' :=
  ev_ext c c' fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm

theorem isAW_add_left {n m k : ℤ} (hk : n + m = k) {a a' : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a' b c') : μ.IsAW hk (a + a') b (c + c') := by
  intro N w hw U x
  rw [ev_add, h N w hw U x, h' N w hw U x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_add, map_add (f := _), LinearMap.add_apply, smul_add]

theorem isAW_add_right {n m k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b b' : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b' c') : μ.IsAW hk a (b + b') (c + c') := by
  intro N w hw U x
  rw [ev_add, h N w hw U x, h' N w hw U x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_add, map_add (f := _), smul_add]

theorem isAW_zero_left {n m k : ℤ} (hk : n + m = k) (b : Cochain ((chains R).obj E) J m) : μ.IsAW hk 0 b 0 := by
  intro N w hw U x
  simp [ev_zero]

theorem isAW_zero_right {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) : μ.IsAW hk a 0 0 := by
  intro N w hw U x
  simp [ev_zero]

theorem aw_cocycle {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (c : Cochain ((chains R).obj E) K k) (hc : μ.IsAW hk α.1 β.1 c) : δ k (k + 1) c = 0 := by
  have h₁ : μ.IsAW (by omega : (n + 1) + m = k + 1) (δ n (n + 1) α.1) β.1 0 := by
    rw [Cocycle.δ_eq_zero]; exact isAW_zero_left μ _ _
  have h₂ : μ.IsAW (by omega : n + (m + 1) = k + 1) α.1 (δ m (m + 1) β.1) 0 := by
    rw [Cocycle.δ_eq_zero]; exact isAW_zero_right μ _ _
  rw [aw_leibniz μ rfl rfl rfl hc h₁ h₂]
  simp

def awc {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Cocycle.mk (isAW_exists μ hk α.1 β.1).choose (k + 1) rfl (aw_cocycle μ hk α β _ (isAW_exists μ hk α.1 β.1).choose_spec)

theorem awc_spec {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (awc μ hk α β).1 := (isAW_exists μ hk α.1 β.1).choose_spec

theorem awc_eq {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : awc μ hk α β = γ :=
  Cocycle.ext (isAW_unique μ hk (awc_spec μ hk α β) h)

def cupL {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) :
    CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun β => CohomologyClass.mk (awc μ hk α β)) (fun β β' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact awc_eq μ hk _ _ _ (isAW_add_right μ hk (awc_spec μ hk α β) (awc_spec μ hk α β'))))
    (by
      rintro ⟨b, hb⟩ ⟨m', hm', b', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨c₀, hc₀⟩ := isAW_exists μ (rfl : n + m' = n + m') α.1 b'
      have h₁ : μ.IsAW (by omega : (n + 1) + m' = k) (δ n (n + 1) α.1) b' 0 := by
        rw [Cocycle.δ_eq_zero]; exact isAW_zero_left μ _ _
      have hL := aw_leibniz μ rfl hm' (by omega) hc₀ h₁ (awc_spec μ hk α ⟨_, hb⟩)
      refine ⟨n + m', by omega, n.negOnePow • c₀, ?_⟩
      rw [δ_units_smul, hL, zero_add, smul_smul, Int.units_mul_self, one_smul])

theorem cupL_mk {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    cupL μ hk α (CohomologyClass.mk β) = CohomologyClass.mk (awc μ hk α β) := rfl

def cupMap {n m k : ℤ} (hk : n + m = k) :
    CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => cupL μ hk α) (fun α α' => by
      ext y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      rw [AddMonoidHom.add_apply, cupL_mk, cupL_mk, cupL_mk, ← CohomologyClass.mk_add]; congr 1
      exact awc_eq μ hk _ _ _ (isAW_add_left μ hk (awc_spec μ hk α β) (awc_spec μ hk α' β))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      ext y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨c₀, hc₀⟩ := isAW_exists μ (rfl : n' + m = n' + m) a' β.1
      have h₂ : μ.IsAW (by omega : n' + (m + 1) = k) a' (δ m (m + 1) β.1) 0 := by
        rw [Cocycle.δ_eq_zero]; exact isAW_zero_right μ _ _
      have hL := aw_leibniz μ hn' rfl (by omega) hc₀ (awc_spec μ hk ⟨_, ha⟩ β) h₂
      refine ⟨n' + m, by omega, c₀, ?_⟩
      rw [hL, smul_zero, add_zero])

end Cup

section Op
variable {S : Type} [CommRing S] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) {E : Spc} {n : ℤ}

theorem image_cochain_exists (a : Cochain ((chains S).obj E) I n) : ∃ b, ρ.IsImage a b :=
  ev_exists (fun p s h U x => ρ.app U s (ev a p s h U x)) (fun p s h V U g x => by rw [ρ.nat, ev_res])

theorem image_unique {a : Cochain ((chains S).obj E) I n} {b b' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) (h' : ρ.IsImage a b') : b = b' :=
  ev_ext b b' fun p s hs U x => (h p s hs U x).trans (h' p s hs U x).symm

theorem image_add {a a' : Cochain ((chains S).obj E) I n} {b b' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) (h' : ρ.IsImage a' b') : ρ.IsImage (a + a') (b + b') := fun p s hs U x => by
  rw [ev_add, ev_add, map_add (f := _), h p s hs, h' p s hs]

theorem image_zero : ρ.IsImage (0 : Cochain ((chains S).obj E) I n) 0 := fun p s hs U x => by
  rw [ev_zero, ev_zero, map_zero]

theorem image_δ {m : ℤ} (hm : n + 1 = m) {a : Cochain ((chains S).obj E) I n} {b : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) : ρ.IsImage (δ n m a) (δ n m b) := by
  intro p t ht U x
  cases p with
  | zero => rw [ev_δ_zero hm b U _ t rfl, ev_δ_zero hm a U _ t rfl, h, ρ.comm]
  | succ p =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ev_δ_succ hm b U p _ t rfl, ev_δ_succ hm a U p _ t rfl, h, ρ.comm, map_add (f := _), sg_smul, sg_smul, map_zsmul, map_sum]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, h]

theorem image_pull {E' : Spc} (f : E' ⟶ E) {a : Cochain ((chains S).obj E) I n} {b : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) : ρ.IsImage ((Cochain.ofHom ((chains S).map f)).comp a (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp b (zero_add n)) := fun p s hs U x => by
  rw [ev_pull, ev_pull, h]

def imgc (α : Cocycle ((chains S).obj E) I n) : Cocycle ((chains R).obj E) J n :=
  Cocycle.mk (image_cochain_exists ρ α.1).choose (n + 1) rfl (by
    have h := image_δ ρ rfl (image_cochain_exists ρ α.1).choose_spec
    rw [Cocycle.δ_eq_zero] at h
    exact image_unique ρ h (image_zero ρ))

theorem imgc_spec (α : Cocycle ((chains S).obj E) I n) : ρ.IsImage α.1 (imgc ρ α).1 :=
  (image_cochain_exists ρ α.1).choose_spec

theorem imgc_eq (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n) (h : ρ.IsImage α.1 β.1) :
    imgc ρ α = β := Cocycle.ext (image_unique ρ (imgc_spec ρ α) h)

def opMap : NatOp I J where
  app E n := CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => CohomologyClass.mk (imgc ρ α)) (fun α α' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact imgc_eq ρ _ _ (image_add ρ (imgc_spec ρ α) (imgc_spec ρ α'))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨b, hb⟩ := image_cochain_exists ρ a'
      exact ⟨n', hn', b, image_unique ρ (image_δ ρ hn' hb) (imgc_spec ρ ⟨_, ha⟩)⟩)
  nat f n x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (imgc_eq ρ (zcomp (Cocycle.ofHom ((chains S).map f)) x (zero_add n))
      (zcomp (Cocycle.ofHom ((chains R).map f)) (imgc ρ x) (zero_add n)) (image_pull ρ f (imgc_spec ρ x))).symm

end Op

end CupSpec

open CupSpec

theorem Pair.cup_spec {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k) :
    μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  intro h
  have hP : ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
      CohomologyClass ((chains R).obj E) K k, ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k),
        μ.IsAW hk α.1 β.1 γ.1 → c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    ⟨cupMap μ hk, fun α β γ h => by
      change CohomologyClass.mk (awc μ hk α β) = _
      rw [awc_eq μ hk α β γ h]⟩
  exact pick_spec hP α β γ h

theorem Pair.aw_exists {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) : ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 :=
  ⟨awc μ hk α β, awc_spec μ hk α β⟩

theorem SemiMap.op_spec {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
    (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n) :
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) →
    ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  pick_spec (P := fun c : NatOp I J => ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n)
    (β : Cocycle ((chains R).obj E) J n),
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U),
      ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) → c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β)
    ⟨opMap ρ, fun _ _ α β h => congrArg CohomologyClass.mk (imgc_eq ρ α β h)⟩ E n α β

theorem SemiMap.image_exists {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
    (α : Cocycle ((chains S).obj E) I n) : ∃ β : Cocycle ((chains R).obj E) J n,
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x) :=
  ⟨imgc ρ α, imgc_spec ρ α⟩

theorem cup_op_spec :
    (∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      (∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ γ : Cocycle ((chains R).obj E) K k,
        μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ) ∧
    ∀ {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
      (α : Cocycle ((chains S).obj E) I n),
      (∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧ ∀ β : Cocycle ((chains R).obj E) J n,
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  ⟨fun μ E _ _ _ hk α β => ⟨μ.aw_exists E hk α β, μ.cup_spec E hk α β⟩,
    fun ρ E n α => ⟨ρ.image_exists E n α, ρ.op_spec E n α⟩⟩

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ V g, P V g → Q V g) (hP : Loc U P) : Loc U Q := by
  obtain ⟨S, hS, h1⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h1 V g hg)⟩

lemma appTop_comp {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

lemma isUnit_prod' {R : Type*} [CommRing R] (S : Finset ℕ) (f : ℕ → R) (h : ∀ a ∈ S, IsUnit (f a)) :
    IsUnit (∏ a ∈ S, f a) := by
  exact IsUnit.prod_iff.mpr h

lemma loc_of_prod_eq_zero {U : Scheme.{0}} (y : Γ(U, ⊤)) (z : ℕ → Γ(U, ⊤)) (S : Finset ℕ)
    (hprod : ∏ a ∈ S, (y - z a) = 0) (hu : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsUnit (z a - z b)) :
    Loc U fun _ g => ∃ a ∈ S, g.appTop.hom y = g.appTop.hom (z a) := by
  classical
  rw [loc_iff_etale_affine_points U _ (by
    rintro V W g k ⟨a, ha, h⟩
    exact ⟨a, ha, by rw [appTop_comp, appTop_comp, h]⟩)]
  intro x
  let γ := (U.presheaf.germ ⊤ x trivial).hom
  have hex : ∃ a ∈ S, ¬ IsUnit (γ (y - z a)) := by
    by_contra hc
    push_neg at hc
    have h1 : IsUnit (γ (∏ a ∈ S, (y - z a))) := by
      rw [map_prod]; exact isUnit_prod' S _ hc
    rw [hprod, map_zero] at h1
    exact not_isUnit_zero h1
  obtain ⟨a0, ha0, hna⟩ := hex
  set s := ∏ b ∈ S.erase a0, (y - z b) with hs
  have hsu : IsUnit (γ s) := by
    rw [hs, map_prod]
    apply isUnit_prod'
    intro b hb
    obtain ⟨hba, hbS⟩ := Finset.mem_erase.1 hb
    by_contra hnb
    have hun : IsUnit (γ (z a0 - z b)) := (hu a0 ha0 b hbS (Ne.symm hba)).map γ
    have e : γ (z a0 - z b) = γ (y - z b) + -(γ (y - z a0)) := by
      rw [← map_neg, ← map_add (f := _)]; congr 1; ring
    rw [e] at hun
    exact (IsLocalRing.nonunits_add ((mem_nonunits_iff).2 hnb)
      ((mem_nonunits_iff).2 (fun h => hna (by simpa using h.neg)))) hun
  have hxs : x ∈ U.basicOpen s := (Scheme.mem_basicOpen_top U s x).2 hsu
  let W := U.basicOpen s
  let xW : W.toScheme := ⟨x, hxs⟩
  obtain ⟨w, hw⟩ := W.toScheme.affineCover.covers xW
  refine ⟨_, W.toScheme.affineCover.f (W.toScheme.affineCover.idx xW) ≫ W.ι, inferInstance, inferInstance, ⟨w, ?_⟩, a0, ha0, ?_⟩
  · simp [hw, xW]
  · set k := W.toScheme.affineCover.f (W.toScheme.affineCover.idx xW)
    have hsW : IsUnit (W.ι.appTop.hom s) := by
      rw [Scheme.Opens.ι_appTop]
      have h0 : IsUnit ((U.presheaf.map (homOfLE (U.basicOpen_le s)).op).hom s) := U.toRingedSpace.isUnit_res_basicOpen s
      have hle : W.ι ''ᵁ ⊤ ≤ W := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have e : (homOfLE le_top : W.ι ''ᵁ ⊤ ⟶ ⊤) = homOfLE hle ≫ homOfLE (U.basicOpen_le s) := Subsingleton.elim _ _
      rw [e, op_comp, Functor.map_comp]
      exact h0.map (U.presheaf.map (homOfLE hle).op).hom
    have hk : IsUnit ((k ≫ W.ι).appTop.hom s) := by
      rw [appTop_comp]; exact hsW.map _
    have hm : (y - z a0) * s = 0 := by rw [hs, Finset.mul_prod_erase S (fun b => y - z b) ha0, hprod]
    have h2 := congrArg (k ≫ W.ι).appTop.hom hm
    rw [map_mul, map_zero, hk.mul_left_eq_zero, map_sub, sub_eq_zero] at h2
    exact h2

end GlobalTheory.EtC.PrimLoc

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

lemma specMap_algebraMap_comp_apply_primeSpectrum {U : Scheme.{0}} {A : CommRingCat.{0}} {B : Type} [CommRing B] [Algebra A B] (f : Spec A ⟶ U)
    (z : PrimeSpectrum B) :
    (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f) z = f (PrimeSpectrum.comap (algebraMap A B) z) := rfl

lemma loc_of_alg {U : Scheme.{0}} (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ (A : CommRingCat.{0}) (f : Spec A ⟶ U), Nontrivial A → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B),
      Algebra.Etale A B ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) ∧
      P (Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f)) : Loc U P := by
  rw [loc_iff_etale_affine_points U P hP]
  intro x
  obtain ⟨y, hy⟩ := U.affineOpenCover.covers x
  have hA : Nontrivial (U.affineOpenCover.X (U.affineOpenCover.idx x)) :=
    nontrivial_of_ne 0 1 (fun h => y.2.ne_top ((Ideal.eq_top_iff_one _).2 (h ▸ y.asIdeal.zero_mem)))
  obtain ⟨B, _, _, hE, hS, hPB⟩ := h _ (U.affineOpenCover.f (U.affineOpenCover.idx x)) hA
  obtain ⟨z, hz⟩ := hS y
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap (U.affineOpenCover.X (U.affineOpenCover.idx x)) B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hE)
  refine ⟨_, _, inferInstance, inferInstance, ⟨z, ?_⟩, hPB⟩
  rw [specMap_algebraMap_comp_apply_primeSpectrum, hz, hy]

lemma adjoinRoot_surj {A : Type} [CommRing A] [Nontrivial A] (f : A[X]) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot f))) := by
  haveI : Module.Free A (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Nontrivial (AdjoinRoot f) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    exact hd (by rw [hf.isUnit_iff.1 h, natDegree_one]))
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

lemma etale_of_unit {A : Type} [CommRing A] (f : A[X]) (hm : f.Monic) (h : IsUnit (AdjoinRoot.mk f (derivative f))) :
    Algebra.Etale A (AdjoinRoot f) := by
  let P : StandardEtalePair A := ⟨f, hm, derivative f, 1, 0, 1, by simp⟩
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk f (derivative f))) _
      h).symm.restrictScalars A))

lemma cyc_etale {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  apply etale_of_unit _ (cyclotomic.monic q A)
  obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q A
  have hx : AdjoinRoot.root (cyclotomic q A) ^ q = 1 := by
    have := congrArg (AdjoinRoot.mk (cyclotomic q A)) hG
    rw [map_mul, AdjoinRoot.mk_self, zero_mul, map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at this
    exact this
  have hd := congrArg (fun p => AdjoinRoot.mk (cyclotomic q A) (derivative p)) hG
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_add (f := _), map_mul,
    AdjoinRoot.mk_self, zero_mul, add_zero] at hd
  have hu : IsUnit (AdjoinRoot.mk (cyclotomic q A) (C (q : A)) * AdjoinRoot.mk (cyclotomic q A) (X ^ (q - 1))) := by
    rw [map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    refine (hq.map _).mul (IsUnit.pow _ ?_)
    exact (isUnit_pow_iff (NeZero.ne q)).1 (hx ▸ isUnit_one)
  rw [hd] at hu
  exact isUnit_of_mul_isUnit_left hu

def cyc_root {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) : Prim q (AdjoinRoot (cyclotomic q A)) :=
  ⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), by
    rw [PrimBasic.aeval_cyc, ← map_cyclotomic q (AdjoinRoot.of (cyclotomic q A)), Polynomial.eval_map]
    exact AdjoinRoot.eval₂_root _⟩

lemma kummer_root {A : Type} [CommRing A] (q : ℕ) (hq0 : q ≠ 0) (u : Aˣ) :
    ∃ v : (AdjoinRoot (X ^ q - C (u : A)))ˣ, (v : AdjoinRoot (X ^ q - C (u : A))) ^ q = algebraMap A _ u := by
  have h1 : AdjoinRoot.root (X ^ q - C (u : A)) ^ q = algebraMap A _ u := by
    have := AdjoinRoot.eval₂_root (X ^ q - C (u : A))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ q - C (u : A))) := (isUnit_pow_iff hq0).1 (h1 ▸ u.isUnit.map _)
  exact ⟨hr.unit, by simpa using h1⟩

lemma spec_appTop {A B : CommRingCat.{0}} (ψ : A ⟶ B) (t : Γ(Spec A, ⊤)) :
    (Spec.map ψ).appTop.hom t = (Scheme.ΓSpecIso B).inv.hom (ψ.hom ((Scheme.ΓSpecIso A).hom.hom t)) := by
  have e := congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_naturality ψ)
  simp only [CommRingCat.comp_apply] at e
  rw [← e]
  simp

end GlobalTheory.EtC.PrimLoc

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

theorem prim_loc : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  intro q _ U
  obtain ⟨-, -, h3, h4, h5, -⟩ := PrimBasic.prim_basic q Γ(U, ⊤)
  have hmod : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q, a ≠ b → ¬ a ≡ b [MOD q] := by
    intro a ha b hb hab h
    apply hab
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hq
    refine loc_of_alg (fun V _ => Nonempty (Prim q Γ(V, ⊤))) (fun V W g k ⟨ζ⟩ => ⟨ζ.map k.appTop.hom⟩) ?_
    intro A f hA
    have hqA : IsUnit (q : A) := by
      simpa using hq.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom
    refine ⟨AdjoinRoot (cyclotomic q A), inferInstance, inferInstance, cyc_etale q hqA,
      adjoinRoot_surj _ (cyclotomic.monic q A) ?_, ⟨(cyc_root q hqA).map (Scheme.ΓSpecIso _).inv.hom⟩⟩
    rw [natDegree_cyclotomic]
    exact (Nat.totient_pos.2 (NeZero.pos q)).ne'
  · intro ζ ξ
    refine loc_mono ?_ (loc_of_prod_eq_zero ξ.1 (fun a => ζ.1 ^ a) _ (h5 ζ ξ) ?_)
    · rintro V g ⟨a, ha, h⟩
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      refine ⟨ZMod.unitOfCoprime a ha2, ?_⟩
      rw [h, map_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 ha1)]
    · intro a ha b hb hab
      exact h3 ζ a b (hmod a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 hab)
  · intro ζ x hx
    refine loc_mono ?_ (loc_of_prod_eq_zero x (fun a => ζ.1 ^ a) _ (h4 ζ x hx) ?_)
    · rintro V g ⟨a, -, h⟩
      exact ⟨a, by rw [h, map_pow]⟩
    · intro a ha b hb hab
      exact h3 ζ a b (hmod a ha b hb hab)
  · intro hq u
    refine loc_of_alg (fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) ?_ ?_
    · rintro V W g k ⟨v, hv⟩
      refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
      rw [← map_pow, hv]
      ext
      rfl
    intro A f hA
    have hqA : IsUnit (q : A) := by
      simpa using hq.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom
    obtain ⟨uA, huA⟩ : ∃ uA : (A : Type)ˣ, uA = Units.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom.toMonoidHom u :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := kummer_root q (NeZero.ne q) uA
    refine ⟨AdjoinRoot (X ^ q - C (uA : A)), inferInstance, inferInstance,
      GlobalTheory.etale_adjoinRoot_X_pow_sub_C A q uA hqA uA.isUnit,
      adjoinRoot_surj _ (monic_X_pow_sub_C _ (NeZero.ne q)) ?_,
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (X ^ q - C (uA : A))))).inv.hom.toMonoidHom v, ?_⟩⟩
    · rw [natDegree_X_pow_sub_C _]
      exact NeZero.ne q
    · ext
      have hu' : (uA : A) = (Scheme.ΓSpecIso A).hom.hom (f.appTop.hom (u : Γ(U, ⊤))) := by rw [huA]; rfl
      rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map]
      show (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (X ^ q - C (uA : A))))).inv.hom (v : AdjoinRoot (X ^ q - C (uA : A))) ^ q =
        (Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot (X ^ q - C (uA : A))))) ≫ f).appTop.hom (u : Γ(U, ⊤))
      rw [appTop_comp, spec_appTop, ← map_pow, hv]
      congr 1
      exact congrArg (algebraMap A (AdjoinRoot (X ^ q - C (uA : A)))) hu'

end GlobalTheory.EtC.PrimLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  first | (exact @GlobalTheory.EtC.PrimLoc.prim_loc) | (exact GlobalTheory.EtC.PrimLoc.prim_loc) | (intros; apply GlobalTheory.EtC.PrimLoc.prim_loc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.BZBridge

section Transport

variable {H G V : Type} [Group H] [Group G] [TopologicalSpace H] [TopologicalSpace G]
  [AddCommGroup V] [Module ℂ V]

def subrepCompEquiv (π : Representation ℂ G V) (Φ : H ≃* G) :
    Subrepresentation (π.comp Φ.toMonoidHom : Representation ℂ H V) ≃o Subrepresentation π where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (Φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (Φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp (π : Representation ℂ G V) (Φ : H ≃* G) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp Φ.toMonoidHom : Representation ℂ H V) := by
  have := h
  exact (subrepCompEquiv π Φ).isSimpleOrder

theorem isSmooth_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (h : IsSmooth π) :
    IsSmooth (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V) := by
  intro v
  exact (h v).preimage (map_continuous Φ)

theorem isAdmissible_of_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (hs : IsSmooth π)
    (h : IsAdmissible (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V)) : IsAdmissible π := by
  refine ⟨hs, fun K hKo hKc => ?_⟩

  set K' : Subgroup H := K.comap Φ.toMulEquiv.toMonoidHom with hK'
  have hset : (K' : Set H) = Φ.symm '' (K : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨Φ x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      show Φ (Φ.symm y) ∈ K
      simpa using hy
  have hK'o : IsOpen (K' : Set H) := hKo.preimage (map_continuous Φ)
  have hK'c : IsCompact (K' : Set H) := by
    rw [hset]
    exact hKc.image (map_continuous Φ.symm)
  have := h.2 K' hK'o hK'c
  refine Submodule.finiteDimensional_of_le (S₂ := fixed (π.comp Φ.toMulEquiv.toMonoidHom) K') ?_
  intro v hv
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hv ⊢
  intro x
  have h1 := hv ⟨Φ x, x.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  exact h1

end Transport

def glReindex (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ε : ι ≃ κ) : GL ι K ≃ₜ* GL κ K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem irreducibleAdmissible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : IrreducibleAdmissible k := by
  intro n _ _ V _ _ π hs hi
  let Φ := glReindex k (Fintype.equivFin n).symm
  exact isAdmissible_of_comp π Φ hs
    (hA k (Fintype.card n) V _ (isSmooth_comp π Φ hs) (isIrreducible_comp π Φ.toMulEquiv hi))

end GlobalTheory.BZBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ZcFun

variable {R : Type} [CommRing R]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_cpush {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  change CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • z.comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp z x.1 (by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp [zcomp, hz, Cochain.add_comp, smul_smul]

theorem main : ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n) := by
  intro R _
  refine ⟨fun K I n x => ⟨cpull_id K I n x, InjResCmp.cpush_id K I n x⟩, fun f g I n x => cpull_comp f g I n x,
    fun K _ _ _ f g n x => InjResCmp.cpush_comp K f g n x, fun f g n x => cpull_cpush f g n x, ?_⟩
  rintro K L f g ⟨h⟩ I n
  exact ⟨AddMonoidHom.ext fun x => cpull_homotopy h I n x, AddMonoidHom.ext fun x => InjResCmp.cpush_homotopy I h n x⟩

end GlobalTheory.EtC.ZcFun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullbackPushforward_functorial : ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n) := by
  first | (exact @GlobalTheory.EtC.ZcFun.main) | (exact GlobalTheory.EtC.ZcFun.main) | (intros; apply GlobalTheory.EtC.ZcFun.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def trivV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (show Fin (n.unop.len + 1) ⥤ (glCat N).obj (Scheme.Γ.obj U) from
          (CategoryTheory.Functor.const _).obj (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))))
      naturality := fun U U' f => by
        ext x
        exact CategoryTheory.Functor.hext (fun _ => rfl)
          (fun _ _ _ => heq_of_eq (map_one (Matrix.GeneralLinearGroup.map _)).symm) }
  naturality n m f := by
    ext U x
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f →
      ConnectedSpace X → IrreducibleSpace X := by
  intro k _ X f hf hc
  haveI := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace f
  infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f → ConnectedSpace X → IrreducibleSpace X := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace <;> assumption)
end
end

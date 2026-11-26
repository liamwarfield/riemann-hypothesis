module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqMulSecOfEqZpowSec
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory

namespace Twist

variable {X : Scheme.{0}} {F : X.Modules} {L : LB X} {m n : ℤ}

def zpowSec (σ : LB.Sec (lbZPow L m)) (k : ℕ) : LB.Sec (lbZPow L (k * m)) :=
  zmkGlobal (fun i => zfun σ i ^ k) fun i j => by
    have e : res (le_refl (L.U i ⊓ L.U j)) (L.g i j) = L.g i j := Units.ext (resG_self _ _)
    rw [map_pow, map_pow, zfun_rel σ i j _ inf_le_right le_rfl, e, mul_pow, mul_comm (k : ℤ),
      zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]

@[simp] theorem zfun_zpowSec (σ : LB.Sec (lbZPow L m)) (k : ℕ) (i : L.ι) :
    zfun (zpowSec σ k) i = zfun σ i ^ k := zfun_zmkGlobal _ _ i

theorem basicOpen_resG_zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i) :
    X.basicOpen (resG X h (zfun σ i)) = W ⊓ Out.nonzeroLocus σ := by
  rw [zfun, resG_resG]
  refine (X.basicOpen_res _ (homOfLE (h.trans (le_zidx_U m i))).op).trans ?_
  rw [← nonzeroLocus_inf_chart σ (zidx L m i), inf_comm (Out.nonzeroLocus σ), ← inf_assoc]
  exact congrArg (· ⊓ _) (inf_eq_left.2 (h.trans (le_zidx_U m i)))

theorem basicOpen_zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) :
    X.basicOpen (zfun σ i) = L.U i ⊓ Out.nonzeroLocus σ := by
  rw [← basicOpen_resG_zfun σ i le_rfl, resG_self]

theorem nonzeroLocus_eq_of_zfun (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) {V : X.Opens}
    (h : ∀ i, X.basicOpen (zfun σ i) = L.U i ⊓ V) : Out.nonzeroLocus σ = V := by
  ext x
  obtain ⟨i, hi⟩ := exists_chart hL x
  have e := (basicOpen_zfun σ i).symm.trans (h i)
  exact ⟨fun hx => (e.le ⟨hi, hx⟩).2, fun hx => (e.ge ⟨hi, hx⟩).2⟩

theorem nonzeroLocus_zofSec (hL : L.IsLB) (s : LB.Sec L) :
    Out.nonzeroLocus (zofSec s) = Out.nonzeroLocus s :=
  nonzeroLocus_eq_of_zfun hL _ fun i => by rw [zfun_zofSec, ← nonzeroLocus_inf_chart, inf_comm]

theorem nonzeroLocus_le_zpowSec (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) (k : ℕ) :
    Out.nonzeroLocus σ ≤ Out.nonzeroLocus (zpowSec σ k) := fun x hx => by
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine ((basicOpen_zfun (zpowSec σ k) i).le ?_).2
  rw [zfun_zpowSec]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Scheme.basicOpen_one]
    exact hi
  · rw [Scheme.basicOpen_pow _ _ hk, basicOpen_zfun]
    exact ⟨hi, hx⟩

theorem exists_finite_affine_chart_cover (hL : L.IsLB) {W : X.Opens} (hW : IsCompact (W : Set X)) :
    ∃ (κ : Type) (_ : Finite κ) (T : κ → X.Opens) (c : κ → L.ι),
      (∀ a, IsAffineOpen (T a)) ∧ (∀ a, T a ≤ W) ∧ (∀ a, T a ≤ L.U (c a)) ∧ W ≤ iSup T := by
  have h : ∀ x : W, ∃ (T : X.Opens) (c : L.ι), IsAffineOpen T ∧ x.1 ∈ T ∧ T ≤ W ⊓ L.U c := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hL x.1
    obtain ⟨T, hT, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := W ⊓ L.U i) (x := x.1) ⟨x.2, hi⟩
    exact ⟨T, i, hT, hx, hle⟩
  choose T c hT hx hle using h
  obtain ⟨S, hS⟩ := hW.elim_finite_subcover (fun x => (T x : Set X)) (fun x => (T x).isOpen)
    fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hx _⟩
  refine ⟨S, inferInstance, fun a => T a, fun a => c a, fun a => hT a,
    fun a => (hle a).trans inf_le_left, fun a => (hle a).trans inf_le_right, fun y hy => ?_⟩
  obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (hS hy)
  exact Opens.mem_iSup.2 ⟨⟨a, ha⟩, h⟩

theorem mulSecOfEq_zpowSec_app (σ : LB.Sec (lbZPow L m)) {a b c : ℕ} (hc : c = a + b) {d e : ℤ}
    (h₁ : n + a * m = d) (h₂ : d + b * m = e) (h₃ : n + c * m = e) {V : X.Opens}
    (t : Γ(twistZ F L n, V)) :
    (mulSecOfEq F (zpowSec σ b) h₂).app V ((mulSecOfEq F (zpowSec σ a) h₁).app V t) =
      (mulSecOfEq F (zpowSec σ c) h₃).app V t :=
  zsec_ext fun i => by
    simp only [zcoord_mulSecOfEq_app, zfun_zpowSec, hc, smul_smul, pow_add, map_mul, mul_comm]

variable [F.IsQuasicoherent]

theorem eventually_mulSecOfEq_zpowSec_eq_zero (hL : L.IsLB) (σ : LB.Sec (lbZPow L m))
    {W V : X.Opens} (hW : IsCompact (W : Set X)) (h : V ≤ W) (hV : W ⊓ Out.nonzeroLocus σ ≤ V)
    (a : Γ(twistZ F L n, W)) (ha : resM _ h a = 0) :
    ∀ᶠ k : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m = d),
      (mulSecOfEq F (zpowSec σ k) hd).app W a = 0 := by
  obtain ⟨κ, _, T, c, hT, hTW, hTc, hc⟩ := exists_finite_affine_chart_cover hL hW
  have key : ∀ α, ∀ᶠ k : ℕ in atTop,
      resG X (hTc α) (zfun σ (c α)) ^ k • zchartEquiv hL n (c α) (hTc α) (resM _ (hTW α) a) = 0 := by
    intro α
    obtain ⟨k, hk⟩ := QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact F (hT α).isCompact
      (resG X (hTc α) (zfun σ (c α))) inf_le_left (basicOpen_resG_zfun σ _ (hTc α)).symm
      (zchartEquiv hL n (c α) (hTc α) (resM _ (hTW α) a)) (by
        have hle : T α ⊓ Out.nonzeroLocus σ ≤ V := (inf_le_inf_right _ (hTW α)).trans hV
        refine (zchartEquiv_resM hL (c α) (hTc α) inf_le_left _).symm.trans ?_
        rw [resM_resM, ← resM_resM h hle, ha, map_zero, map_zero])
    refine eventually_atTop.2 ⟨k, fun j hj => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
    rw [pow_add, mul_smul, hk, smul_zero]
  refine (eventually_all.2 key).mono fun k hk d hd => sec_ext_of_cover T hTW hc fun α => ?_
  apply (zchartEquiv hL d (c α) (hTc α)).injective
  rw [← app_resM, zchartEquiv_mulSecOfEq_app, zfun_zpowSec, map_pow, hk, map_zero, map_zero]

theorem eventually_exists_resM_eq_mulSecOfEq_zpowSec (hL : L.IsLB) (σ : LB.Sec (lbZPow L m))
    {W V : X.Opens} (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) (h : V ≤ W)
    (hV : V = W ⊓ Out.nonzeroLocus σ) (b : Γ(twistZ F L n, V)) :
    ∀ᶠ k : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m = d), ∃ a : Γ(twistZ F L d, W),
      resM _ h a = (mulSecOfEq F (zpowSec σ k) hd).app V b := by
  obtain ⟨κ, _, T, c, hT, hTW, hTc, hc⟩ := exists_finite_affine_chart_cover hL hW
  have hTV : ∀ α, T α ⊓ V = T α ⊓ Out.nonzeroLocus σ := fun α => by
    rw [hV, ← inf_assoc, inf_eq_left.2 (hTW α)]
  have key : ∀ α, ∀ᶠ k : ℕ in atTop, ∃ a : Γ(twistZ F L (n + k * m), T α),
      resM _ (inf_le_left : T α ⊓ V ≤ T α) a =
        (mulSec F (zpowSec σ k) n).app _ (resM _ inf_le_right b) := by
    intro α
    have hc' : T α ⊓ V ≤ L.U (c α) := inf_le_left.trans (hTc α)
    obtain ⟨k, t, hk⟩ := QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs F (hT α).isCompact
      (hT α).isQuasiSeparated (resG X (hTc α) (zfun σ (c α))) (V := T α ⊓ V) inf_le_left
      ((hTV α).trans (basicOpen_resG_zfun σ _ (hTc α)).symm)
      (zchartEquiv hL n (c α) hc' (resM _ inf_le_right b))
    have hk' : resG X hc' (zfun σ (c α)) ^ k • zchartEquiv hL n (c α) hc' (resM _ inf_le_right b) =
        resM F inf_le_left t := by
      rw [← resG_resG (hTc α) inf_le_left]
      exact hk
    refine eventually_atTop.2 ⟨k, fun j hj => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
    refine ⟨(zchartEquiv hL _ (c α) (hTc α)).symm (resG X (hTc α) (zfun σ (c α)) ^ j • t), ?_⟩
    apply (zchartEquiv hL _ (c α) hc').injective
    rw [zchartEquiv_resM hL (c α) (hTc α), LinearEquiv.apply_symm_apply, zchartEquiv_mulSecOfEq_app,
      zfun_zpowSec, resM_smul, map_pow, map_pow, resG_resG, pow_add, mul_smul, hk']
  obtain ⟨k, hk⟩ := (eventually_all.2 key).exists
  choose a ha using hk
  have key₂ : ∀ p : κ × κ, ∀ᶠ j : ℕ in atTop, ∀ (d : ℤ) (hd : n + k * m + j * m = d),
      (mulSecOfEq F (zpowSec σ j) hd).app (T p.1 ⊓ T p.2)
        (resM _ inf_le_left (a p.1) - resM _ inf_le_right (a p.2)) = 0 := fun p => by
    refine eventually_mulSecOfEq_zpowSec_eq_zero hL σ
      (hW' _ _ (hTW p.1) (T p.1).isOpen (hT p.1).isCompact (hTW p.2) (T p.2).isOpen
        (hT p.2).isCompact) (V := T p.1 ⊓ T p.2 ⊓ V) inf_le_left
      (le_inf inf_le_left (hV.ge.trans' (inf_le_inf_right _ (inf_le_left.trans (hTW p.1))))) _ ?_
    have h₁ : T p.1 ⊓ T p.2 ⊓ V ≤ T p.1 ⊓ V := inf_le_inf_right _ inf_le_left
    have h₂ : T p.1 ⊓ T p.2 ⊓ V ≤ T p.2 ⊓ V := inf_le_inf_right _ inf_le_right
    rw [map_sub, resM_resM, resM_resM, ← resM_resM inf_le_left h₁, ← resM_resM inf_le_left h₂,
      ha, ha, ← app_resM, ← app_resM, resM_resM, resM_resM, sub_self]
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (eventually_all.2 key₂)
  refine eventually_atTop.2 ⟨k + j₀, fun l hl d hd => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (le_of_add_le_left hl)
  have hd' : n + k * m + j * m = d := by rw [← hd]; push_cast; ring
  obtain ⟨t, ht⟩ := exists_sec_of_cover T hTW hc
    (fun α => (mulSecOfEq F (zpowSec σ j) hd').app _ (a α)) fun α β => by
      have := hj₀ j (by omega) (α, β) d hd'
      rw [map_sub, sub_eq_zero] at this
      rw [← app_resM, ← app_resM]
      exact this
  refine ⟨t, sec_ext_of_cover (fun α => T α ⊓ V) (fun _ => inf_le_right)
    ((le_inf (h.trans hc) le_rfl).trans (iSup_inf_eq _ _).le) fun α => ?_⟩
  rw [resM_resM, ← resM_resM (hTW α) inf_le_left, ht, ← app_resM, ha, ← app_resM,
    mulSecOfEq_zpowSec_app σ rfl]

end Twist

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSection
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemSpanOfSaturatingOfLe
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem mem_span_of_saturating_of_le : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) → (∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g)) → (∀ y : M, (∀ i : ι, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) → y = 0) → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ y ∈ ℳ n, y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ r d g hg hsat hinj
  set K := Submodule.span (MvPolynomial ι R) (Set.range g) with hK
  have hhom : K.IsHomogeneous ℳ := isHomogeneous_span_gr ℳ (by
    rintro _ ⟨l, rfl⟩
    exact ⟨d l, hg l⟩)
  letI : Decomposition (grSub ℳ K) := grSubDecomposition ℳ hhom
  have hfin : Module.Finite (MvPolynomial ι R) K :=
    Module.Finite.span_of_finite _ (Set.finite_range g)
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.cubeComplex_gradedModule_exactAt_of_large_degree ι R K (grSub ℳ K) hfin
  refine ⟨n₀, fun n hn y hy => ?_⟩
  have hf := isGradedMap_subtype ℳ K
  have hb := (grAug_bijective_iff (ι := ι) (grSub ℳ K) n).2 ⟨hn₀ n hn 0, hn₀ n hn 1⟩
  haveI : IsIso (grCechMap hf n) := isIso_grCechMap hf
    (fun i m hm => ⟨0, by rw [(map_eq_zero_iff _ K.injective_subtype).1 hm, smul_zero]⟩)
    (fun i y => by simpa using hsat i y) n
  have hs : Function.Surjective (grHMap hf n 0).hom :=
    ((ConcreteCategory.isIso_iff_bijective (grHMap hf n 0)).1 inferInstance).2
  obtain ⟨z, hz⟩ := hs (grAug ι ℳ n ⟨y, hy⟩)
  obtain ⟨y₀, rfl⟩ := hb.2 z
  rw [grHMap_grAug] at hz
  have h0 : y - (y₀.1 : M) = 0 := hinj _ fun i => by
    have e : toHomLoc ℳ {i} n ⟨y, hy⟩ = toHomLoc ℳ {i} n (hf.piece n y₀) := by
      rw [← cechHomologyZeroIso_grAug ℳ n ⟨y, hy⟩ ⟨{i}, rfl⟩,
        ← cechHomologyZeroIso_grAug ℳ n (hf.piece n y₀) ⟨{i}, rfl⟩, hz]
    have e' : awayFrac M (xProd R {i}) 0 y = awayFrac M (xProd R {i}) 0 (y₀.1 : M) :=
      congrArg Subtype.val e
    rw [← sub_eq_zero, ← map_sub, awayFrac_eq_zero_iff] at e'
    simpa using e'
  rw [sub_eq_zero.1 h0]
  exact y₀.1.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSection
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory

theorem exists_X_pow_smul_mem_span_of_dehomogenisation {ι : Type} {R : Type} [CommRing R]
    {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (i : ι) {B N : Type} [CommRing B] [AddCommGroup N] [Module B N]
    {π : MvPolynomial ι R →+* B} (hπ : Function.Surjective π) (hi : π (MvPolynomial.X i) = 1)
    (ε : G →ₛₗ[π] N)
    (hker : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
      ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    {g : G} (hg : g ∈ 𝒢 0) (hgen : ∀ z : N, ∃ b : B, z = b • ε g)
    (K : Submodule (MvPolynomial ι R) G) (hK : g ∈ K) (y : G) :
    ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y ∈ K := by
  induction y using Decomposition.inductionOn 𝒢 with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    refine ⟨p + q, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact K.smul_mem _ hp
    · rw [pow_add, mul_smul]
      exact K.smul_mem _ hq
  | @homogeneous n y =>
    obtain ⟨b, hb⟩ := hgen (ε y)
    obtain ⟨F, rfl⟩ := hπ b
    obtain ⟨n₀, hn₀⟩ := exists_homogeneous_add_X_sub_one_smul (polyGrading ι R) i F
    obtain ⟨F', hF', w, e⟩ := hn₀ (n + ((n₀ - n).toNat : ℕ)) (by omega)
    have hX : (MvPolynomial.X i : MvPolynomial ι R) ^ (n₀ - n).toNat ∈
        polyGrading ι R ((n₀ - n).toNat : ℕ) :=
      mem_polyGrading_natCast.2 (MvPolynomial.isHomogeneous_X_pow i _)
    have h₁ := grSMul_mem 𝒢 hX y.2
    have h₂ := grSMul_mem 𝒢 hF' hg
    rw [zero_add] at h₂
    have hFF : π F = π F' := by
      rw [e, map_add (f := _), smul_eq_mul, map_mul, map_sub, hi, map_one, sub_self, zero_mul, add_zero]
    obtain ⟨k, hk⟩ := hker _ _ (sub_mem h₁ h₂) (by
      rw [map_sub, map_smulₛₗ, map_smulₛₗ, map_pow, hi, one_pow, one_smul, hb, hFF, sub_self])
    refine ⟨k + (n₀ - n).toNat, ?_⟩
    rw [smul_sub, sub_eq_zero] at hk
    rw [pow_add, mul_smul, hk]
    exact K.smul_mem _ (K.smul_mem _ hK)

namespace AbLaw

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {H : LB Y}
  {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (M : LB Y)

theorem operatorsCommute_mulSec (V : Y.Opens) :
    OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V)
      fun i t => SecOnR.mulSec f M t (s i) V :=
  fun i j _ a => SecOn.mulSec_comm (s i) (s j) a

theorem restrict_eq_zero_of_X_pow_smul (i : Fin (m + 1)) (k : ℕ) : ∀ (n : ℤ)
    (a : SecOnR f (tw M H n) ⊤), (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k •
      GrSum.of (operatorsCommute_mulSec f s M ⊤) n a = 0 →
    SecOnR.restrict f _ (le_top : nonzeroLocus (s i) ≤ ⊤) a = 0 := by
  induction k with
  | zero =>
    intro n a h
    rw [pow_zero, one_smul, map_eq_zero_iff _ (GrSum.of_injective _ n)] at h
    rw [h, map_zero]
  | succ k ih =>
    intro n a h
    rw [pow_succ, mul_smul, GrSum.X_smul_of] at h
    have e := ih _ _ h
    refine (map_eq_zero_iff _ (SecOnR.mulSec_bijective f (M := M) n (s i) le_rfl).1).1 ?_
    exact (SecOn.mulSec_restrict (s i) le_top a).trans e

theorem grSum_eq_zero_of_X_pow_smul (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (y : GrSum (operatorsCommute_mulSec f s M ⊤))
    (h : ∀ i, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • y = 0) : y = 0 := by
  obtain ⟨T, hT⟩ := exists_sum_grProj (GrSum.grading _) y
  rw [← hT]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [GrSum.proj_grading, map_eq_zero_iff _ (GrSum.of_injective _ n)]
  refine SecOnR.ext_of_cover f (fun i => nonzeroLocus (s i)) (fun _ => le_top) hs.ge fun i => ?_
  obtain ⟨k, hk⟩ := h i
  rw [map_zero]
  refine restrict_eq_zero_of_X_pow_smul f s M i k n _ ?_
  have hX : (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k ∈ polyGrading _ R (k : ℕ) :=
    mem_polyGrading_natCast.2 (MvPolynomial.isHomogeneous_X_pow i _)
  rw [← GrSum.proj_grading, ← proj_smul_of_mem (GrSum.grading _) hX, hk, map_zero]

def twZeroTrivEquiv (hH : H.IsLB) (V : Y.Opens) :
    Γ(Y, V) ≃ₗ[Γ(Y, V)] SecOn (tw (Inh.trivLB Y) H 0) V :=
  (secOnTrivEquiv V).symm ≪≫ₗ SecOn.twZeroEquiv (Inh.trivLB_isLB Y) hH V

theorem twCoord_twZeroTrivEquiv_one (hH : H.IsLB) (V : Y.Opens) (p : (Inh.trivLB Y).ι) (k : H.ι) :
    SecOn.twCoord (twZeroTrivEquiv hH V 1) p k = 1 := by
  refine (SecOn.twCoord_twZeroEquiv (Inh.trivLB_isLB Y) hH _ p k).trans ?_
  have e := SecOn.coord_chart_symm (Inh.trivLB_isLB Y) PUnit.unit p (le_top : V ≤ ⊤) 1
  have e₂ : rs Y (inf_le_left : V ⊓ ⊤ ≤ V) 1 *
      rs Y (le_inf le_top le_top : V ⊓ ⊤ ≤ ⊤ ⊓ ⊤) 1 = 1 := by
    rw [map_one, map_one, _root_.one_mul]
  exact (congrArg _ (e.trans e₂)).trans (map_one _)

theorem exists_eq_smul_restrict_one (hH : H.IsLB) (V : Y.Opens)
    (z : SecOn (tw (Inh.trivLB Y) H 0) V) :
    ∃ b : Γ(Y, V), z = b • SecOn.restrict _ (le_top : V ≤ ⊤) (twZeroTrivEquiv hH ⊤ 1) := by
  have e : SecOn.restrict _ (le_top : V ≤ ⊤) (twZeroTrivEquiv hH ⊤ 1) = twZeroTrivEquiv hH V 1 :=
    SecOn.tw_ext fun p k => by
      rw [SecOn.twCoord_restrict, twCoord_twZeroTrivEquiv_one, twCoord_twZeroTrivEquiv_one, map_one]
  obtain ⟨b, rfl⟩ := (twZeroTrivEquiv hH V).surjective z
  exact ⟨b, by rw [e, ← map_smul, smul_eq_mul, _root_.mul_one]⟩

def twTrivOfSec {t : ℤ} (σ : LB.Sec (pw H t)) : SecOn (tw (Inh.trivLB Y) H t) ⊤ :=
  SecOn.twMk t (fun _ k => rs Y (inf_le_right.trans inf_le_right) (σ.f k))
    fun p q k l O hp hq hM hH => by
      have e := (congrArg (rs Y hH) (σ.compat k l)).trans (map_mul (rs Y hH) _ _)
      have e₁ : res hM ((Inh.trivLB Y).g p q) = 1 := map_one _
      rw [e₁, _root_.one_mul, ← map_zpow]
      exact ((rs_rs _ _ _).trans (rs_rs _ _ _).symm).trans
        (e.trans (congrArg₂ (· * ·) rfl ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)))

theorem exists_form_eq_sec_pw : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F := by
  intro R _ Y f _ H m s hH hs
  let hx := operatorsCommute_mulSec f s (Inh.trivLB Y)
  let g : GrSum (hx ⊤) := GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ (twZeroTrivEquiv hH ⊤ 1))
  have hg : g ∈ GrSum.grading (hx ⊤) 0 := GrSum.of_mem_grading _ _ _
  obtain ⟨n₀, hn₀⟩ := mem_span_of_saturating_of_le (Fin (m + 1)) R (GrSum (hx ⊤))
    (GrSum.grading (hx ⊤)) 1 (fun _ => 0) (fun _ => g) (fun _ => hg)
    (fun i y => by
      obtain ⟨-, r, hr, hπ⟩ := hs.2 i
      obtain ⟨hi, ε, -, hker, hε⟩ :=
        GlobalTheory.T.exists_dehomogenisation_twisted_chart R Y f H m s _ hH (Inh.trivLB_isLB Y) hs hx i r hr
      exact exists_X_pow_smul_mem_span_of_dehomogenisation (GrSum.grading (hx ⊤)) i hπ
        ((MvPolynomial.eval₂Hom_X' _ _ i).trans hi) ε hker hg
        (fun z => by rw [hε]; exact exists_eq_smul_restrict_one hH _ z) _
        (Submodule.subset_span (Set.mem_range_self (f := fun _ : Fin 1 => g) 0)) y)
    (grSum_eq_zero_of_X_pow_smul f s _ hs.1)
  refine ⟨n₀.toNat, fun t ht σ => ?_⟩
  have hσ := GrSum.of_mem_grading (hx ⊤) t (SecOnR.of f _ ⊤ (twTrivOfSec σ))
  have hm := hn₀ t (by omega) _ hσ
  rw [Set.range_const, LinearMap.span_singleton_eq_range] at hm
  have hgr : IsGradedMap (polyGrading (Fin (m + 1)) R) (GrSum.grading (hx ⊤))
      (LinearMap.toSpanSingleton (MvPolynomial (Fin (m + 1)) R) _ g) := fun n p hp => by
    have := grSMul_mem (GrSum.grading (hx ⊤)) hp hg
    rwa [zero_add] at this
  obtain ⟨F, hF, e⟩ := hgr.exists_mem_of_mem_range hσ hm
  refine ⟨F, mem_polyGrading_natCast.1 hF, fun k => ?_⟩
  obtain ⟨y', hy', hc⟩ := exists_smul_of_twCoord R Y f H m s _ hx ⊤ F t 0 t
    (twZeroTrivEquiv hH ⊤ 1) hF (zero_add _).symm
  have hyy : twTrivOfSec σ = y' := GrSum.of_injective (hx ⊤) t (e.symm.trans hy')
  have h := hc PUnit.unit k
  rw [← hyy, twCoord_twZeroTrivEquiv_one hH ⊤ PUnit.unit k, _root_.mul_one] at h
  have h' := congrArg (rs Y (le_inf le_top (le_inf le_top le_rfl) : H.U k ≤ ⊤ ⊓ (⊤ ⊓ H.U k))) h
  exact ((rs_rs _ _ _).trans (rs_self _ _)).symm.trans (h'.trans ((rs_rs _ _ _).trans (rs_self _ _)))

end AbLaw

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSectionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F := by
  first | exact @GlobalTheory.AbLaw.exists_form_eq_sec_pw | exact GlobalTheory.AbLaw.exists_form_eq_sec_pw | (intros; apply GlobalTheory.AbLaw.exists_form_eq_sec_pw <;> assumption)
end
end

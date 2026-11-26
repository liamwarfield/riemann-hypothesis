module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValAtSpecMap
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyIdempotent

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CubNMulOfPow
noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor PositivityTheory.HtPt.Weilfun

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

private theorem cubN_succ_chow_mahler_families (k : ℕ) (a m x : A) :
    cubN θ (k + 1) a m x = cubN θ k a m x * θ (a * m ^ k) m x := by
  simp only [cubN, Finset.prod_range_succ]

theorem cubN_add (h : IsCub θ) (a b : ℕ) (y x : A) :
    cubN θ (a + b) 1 y x = cubN θ a 1 y x * (θ (y ^ a) (y ^ b) x * cubN θ b 1 y x) := by
  induction b with
  | zero =>
    have e : θ (y ^ a) 1 x = 1 := by rw [h.s01, h.face]
    simp [cubN, e]
  | succ b ih =>
    rw [← Nat.add_assoc, cubN_succ_chow_mahler_families (a + b), cubN_succ_chow_mahler_families b, ih, _root_.one_mul, _root_.one_mul]
    have c := h.coc (y ^ a) (y ^ b) y x
    rw [← pow_add, ← pow_succ] at c
    calc cubN θ a 1 y x * (θ (y ^ a) (y ^ b) x * cubN θ b 1 y x) * θ (y ^ (a + b)) y x
        = cubN θ a 1 y x * cubN θ b 1 y x * (θ (y ^ (a + b)) y x * θ (y ^ a) (y ^ b) x) := by ac_rfl
      _ = cubN θ a 1 y x * cubN θ b 1 y x * (θ (y ^ a) (y ^ (b + 1)) x * θ (y ^ b) y x) := by rw [c]
      _ = _ := by ac_rfl

theorem cubN_mul (h : IsCub θ) (N M : ℕ) (y x : A) :
    cubN θ (N * M) 1 y x = cubN θ N 1 (y ^ M) x * cubN θ M 1 y x ^ N := by
  induction N with
  | zero => simp [cubN]
  | succ N ih =>
    rw [Nat.succ_mul, cubN_add h (N * M) M y x, ih, cubN_succ_chow_mahler_families N, pow_succ (cubN θ M 1 y x) N,
      _root_.one_mul, show (y ^ M) ^ N = y ^ (N * M) by rw [← pow_mul, mul_comm]]
    ac_rfl

theorem cubN_mul_of_pow (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    cubN θ (N * M) 1 x y = cubN θ N 1 x y ^ M := by
  rw [show N * M = M * N from Nat.mul_comm N M, cubN_mul h M N x y, hx]
  have e : cubN θ M 1 1 y = 1 := by
    unfold cubN
    exact Finset.prod_eq_one fun i _ => by rw [one_pow, _root_.one_mul, h.face]
  rw [e, _root_.one_mul]

private theorem cubN_eq_theta_pow_mul_cubN_one (h : IsCub θ) (k : ℕ) (a x z : A) :
    cubN θ k a x z = θ a (x ^ k) z * cubN θ k 1 x z := by
  induction k with
  | zero =>
    have e : θ a 1 z = 1 := by rw [h.s01, h.face]
    simp [cubN, e]
  | succ k ih =>
    rw [cubN_succ_chow_mahler_families k a, cubN_succ_chow_mahler_families k 1, ih, _root_.one_mul]
    have c := h.coc a (x ^ k) x z
    rw [← pow_succ] at c
    calc θ a (x ^ k) z * cubN θ k 1 x z * θ (a * x ^ k) x z
        = cubN θ k 1 x z * (θ (a * x ^ k) x z * θ a (x ^ k) z) := by ac_rfl
      _ = cubN θ k 1 x z * (θ a (x ^ (k + 1)) z * θ (x ^ k) x z) := by rw [c]
      _ = _ := by ac_rfl

private theorem theta_pow_mul_prod_range_eq_prod (h : IsCub θ) (a x y : A) (M : ℕ) :
    θ a x (y ^ M) * ∏ j ∈ Finset.range M, θ (y ^ j) x y = ∏ j ∈ Finset.range M, θ (a * y ^ j) x y := by
  induction M with
  | zero =>
    rw [pow_zero, Finset.prod_range_zero, Finset.prod_range_zero, _root_.mul_one, h.s12, h.s01, h.face]
  | succ M ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih]
    have c := h.coc a (y ^ M) y x
    rw [← pow_succ, h.s12 (a * y ^ M) y x, h.s12 a (y ^ M) x, h.s12 a (y ^ (M + 1)) x,
      h.s12 (y ^ M) y x] at c
    calc θ a x (y ^ (M + 1)) * ((∏ j ∈ Finset.range M, θ (y ^ j) x y) * θ (y ^ M) x y)
        = (∏ j ∈ Finset.range M, θ (y ^ j) x y) * (θ a x (y ^ (M + 1)) * θ (y ^ M) x y) := by ac_rfl
      _ = (∏ j ∈ Finset.range M, θ (y ^ j) x y) * (θ (a * y ^ M) x y * θ a x (y ^ M)) := by rw [c]
      _ = _ := by ac_rfl

theorem cubN_pow (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    cubN θ N 1 x (y ^ M) * cubN θ M 1 y x ^ N = cubN θ N 1 x y ^ M := by
  have hD : cubN θ M 1 y x = ∏ j ∈ Finset.range M, θ (y ^ j) x y := by
    unfold cubN
    exact Finset.prod_congr rfl fun j _ => by rw [_root_.one_mul, h.s12]
  have hC : cubN θ N 1 x (y ^ M) * cubN θ M 1 y x ^ N =
      ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range M, θ (x ^ i * y ^ j) x y := by
    rw [hD, show (∏ j ∈ Finset.range M, θ (y ^ j) x y) ^ N =
        ∏ _i ∈ Finset.range N, ∏ j ∈ Finset.range M, θ (y ^ j) x y by
      rw [Finset.prod_const, Finset.card_range]]
    unfold cubN
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [_root_.one_mul, theta_pow_mul_prod_range_eq_prod h]
  rw [hC, Finset.prod_comm,
    show cubN θ N 1 x y ^ M = ∏ _j ∈ Finset.range M, cubN θ N 1 x y by
      rw [Finset.prod_const, Finset.card_range]]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e := cubN_eq_theta_pow_mul_cubN_one h N (y ^ j) x y
  rw [hx, h.s01 (y ^ j) 1 y, h.face, _root_.one_mul] at e
  rw [← e]
  unfold cubN
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

theorem wq_level (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    wq θ (N * M) x y = wq θ N x (y ^ M) := by
  unfold wq
  rw [cubN_mul h N M y x, cubN_mul_of_pow h N M hx y, ← cubN_pow h N M hx y,
    mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

end Alg

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

theorem weilUnit_level (c : CubicalStr G L) (N M n : ℕ) (hn : n = N * M) {T : Over S} {x y x' y' : T ⟶ G}
    (hx : x ^ N = 1) (hy : y ^ N = 1) (hx' : x' ^ n = 1) (hy' : y' ^ n = 1) (e₁ : x = x') (e₂ : y = y' ^ M) :
    weilUnit c N T x y hx hy = weilUnit c n T x' y' hx' hy' := by
  subst hn e₁ e₂
  apply Units.ext
  apply fn_ext
  intro z _
  obtain ⟨J, hJ⟩ := exists_good_at L z
  have h1 := gm_id_weilUnit c N hx hy z hJ
  have h2 := gm_id_weilUnit c (N * M) hx' hy' z hJ
  rw [wq_level (isCub_cubV c hJ) N M hx] at h2
  have h3 := congrArg Units.val (h1.trans h2.symm)
  simp only [gm_val (𝟙 T.left) z ⊤ trivial] at h3
  simp only [gs, dif_pos (show (𝟙 T.left : T.left ⟶ T.left) z ∈ (⊤ : T.left.Opens) from trivial)]
  exact h3

end PositivityTheory.Xgn.TestGroupPoint
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDerGen
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem exists_der_gen {R RC C N L U : Type} [CommRing R] [IsDomain R] [CommRing RC] [IsDomain RC] [Field C]
    [Algebra RC C] [AddCommGroup N] [Finite N] [AddCommGroup L] [Module R L] [AddCommGroup U] [Module R U]
    (σ : R →+* RC) (h1 : Function.Injective σ) (h2 : Function.Injective (algebraMap RC C))
    (φ : R →+* C) (hφ : ∀ r, algebraMap RC C (σ r) = φ r)
    {A : Subalgebra R (Multiplicative N → R)} (hA : IsHopfOrder A) (p : ℕ) {g : ℕ} (θ : L →ₗ[R] omega A)
    (hθs : Function.Surjective θ) (hθk : ∀ w, θ w = 0 → ∃ u, w = p • u) (j : L →ₗ[R] U)
    (io : U →ₛₗ[σ] (Fin g → RC)) (M : Submodule RC (N → C))
    (hM : M = Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}) :
    ∃ Dv : M →ₗ[RC] ReciprocityTheory.PGsh.Up.LieDualModP p RC g, IsDerAt0 M Dv ∧
      ∀ (a : A) (f : M) (w : L), (∀ x, f.1 x = φ (a.1 (Multiplicative.ofAdd x))) → cotMap A a = θ w →
        Dv f = Submodule.Quotient.mk (io (j w)) := by
  letI : Algebra R RC := σ.toAlgebra
  let k₀ : L →ₗ[R] ReciprocityTheory.PGsh.Up.LieDualModP p RC g :=
    { toFun := fun w => Submodule.Quotient.mk (io (j w))
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _), Submodule.Quotient.mk_add]
      map_smul' := fun r a => by
        rw [map_smul, io.map_smulₛₗ, Submodule.Quotient.mk_smul]
        exact algebraMap_smul RC r _ }
  have hk : LinearMap.ker θ ≤ LinearMap.ker k₀ := by
    intro w hw
    obtain ⟨u, rfl⟩ := hθk w hw
    change Submodule.Quotient.mk (io (j (p • u))) = 0
    rw [map_nsmul, map_nsmul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul RC]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  let d₀ : omega A →ₗ[R] ReciprocityTheory.PGsh.Up.LieDualModP p RC g :=
    ((LinearMap.ker θ).liftQ k₀ hk) ∘ₗ (θ.quotKerEquivOfSurjective hθs).symm.toLinearMap
  have hd₀ : ∀ w, d₀ (θ w) = k₀ w := fun w => by
    have : (θ.quotKerEquivOfSurjective hθs).symm (θ w) = Submodule.Quotient.mk w :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [d₀, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨Dv, hD1, hD2⟩ := exists_der_ext h1 h2 φ hφ hA (d₀ ∘ₗ cotMap A)
    (fun a b => by simp only [LinearMap.comp_apply, cotMap_mul, map_add (f := _), map_smul]) M hM
  refine ⟨Dv, hD1, fun a f w hf hw => ?_⟩
  rw [hD2 a f hf, LinearMap.comp_apply, hw, hd₀]
  rfl

theorem cotMap_aug {R T : Type} [CommRing R] [CommGroup T] (A : Subalgebra R (T → R)) (a : augIdeal A) :
    cotMap A a.1 = (augIdeal A).toCotangent a := by
  have ha1 : a.1.1 1 = 0 := a.2
  exact cotMap_apply _ _ a (by rw [ha1, map_zero, sub_zero])

theorem cotMap_char {R T : Type} [CommRing R] [CommGroup T] (A : Subalgebra R (T → R)) (χ : T →* Rˣ)
    (hm : (fun t => ((χ t : Rˣ) : R)) ∈ A) : cotMap A ⟨_, hm⟩ = dlogChar A χ := by
  rw [OrderApi.dlogChar_of_mem _ _ hm]
  refine cotMap_apply _ _ _ ?_
  simp

end PositivityTheory.Xgn.TestGroupPoint
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TensOfBc
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem bichar_mem {C RC : Type} [Field C] [IsAlgClosed C] [CommRing RC] [IsDomain RC] [Algebra RC C]
    {v : Valuation C NNReal} (hv : v.Integers RC) {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup RC T)
    (β : T →* T →* RCˣ) (s : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hs : ∀ a b, valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s = algebraMap RC _ ((β a b : RCˣ) : RC)) :
    (fun z : T × T => ((β z.1 z.2 : RCˣ) : RC)) ∈ prodSpan (Γ.btOrder ⊤) := by
  haveI : ValuationRing RC := ValuationRing.of_integers v hv
  exact PositivityTheory.HtPt.Twpair.bichar_mem_prodSpan (PositivityTheory.HtPt.Twpair.henselian hv)
    (fun P => (PositivityTheory.HtPt.Twpair.prime_eq_bot_or_maximal hv P.asIdeal).imp id fun h => PrimeSpectrum.ext h)
    Γ β s hs

theorem tens_of_bc {R RC C N : Type} [CommRing R] [CommRing RC] [Field C] [Algebra R RC] [Algebra RC C]
    [AddCommGroup N] (φ : R →+* C) (hφ : ∀ r, algebraMap RC C (algebraMap R RC r) = φ r)
    {A : Subalgebra R (Multiplicative N → R)} {A' : Subalgebra RC (Multiplicative N → RC)}
    (ee : RC ⊗[R] A ≃ₐ[RC] A') (hee : ∀ (a : A) t, (ee (1 ⊗ₜ a)).1 t = algebraMap R RC (a.1 t))
    (M : Submodule RC (N → C))
    (hM : M = Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}) :
    ∀ g ∈ prodSpan A', (fun z : N × N =>
      algebraMap RC C (g (Multiplicative.ofAdd z.1, Multiplicative.ofAdd z.2))) ∈ GR.tens M M := by
  have lem : ∀ x : RC ⊗[R] A, (fun y => algebraMap RC C ((ee x).1 (Multiplicative.ofAdd y))) ∈ M := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      convert M.zero_mem using 1
      ext y
      simp
    | tmul r a =>
      have e1 : r ⊗ₜ[R] a = r • ((1 : RC) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e2 : (fun y => algebraMap RC C ((ee (r ⊗ₜ[R] a)).1 (Multiplicative.ofAdd y))) =
          r • fun y => φ (a.1 (Multiplicative.ofAdd y)) := by
        funext y
        rw [e1, map_smul]
        simp [hee, hφ, Algebra.smul_def]
      rw [e2, hM]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a.1, a.2, rfl⟩)
    | add x y hx hy =>
      have e2 : (fun t => algebraMap RC C ((ee (x + y)).1 (Multiplicative.ofAdd t))) =
          (fun t => algebraMap RC C ((ee x).1 (Multiplicative.ofAdd t))) +
            (fun t => algebraMap RC C ((ee y).1 (Multiplicative.ofAdd t))) := by
        funext t
        simp
      rw [e2]
      exact M.add_mem hx hy
  have lem' : ∀ a ∈ A', (fun y => algebraMap RC C (a (Multiplicative.ofAdd y))) ∈ M := by
    intro a ha
    obtain ⟨x, hx⟩ := ee.surjective ⟨a, ha⟩
    have k := lem x
    rw [hx] at k
    exact k
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    refine Submodule.subset_span ⟨_, lem' a ha, _, lem' b hb, ?_⟩
    funext z
    simp
  | zero =>
    convert (GR.tens M M).zero_mem using 1
    ext z
    simp
  | add g₁ g₂ _ _ h₁ h₂ =>
    convert (GR.tens M M).add_mem h₁ h₂ using 1
    ext z
    simp
  | smul r g _ h =>
    convert (GR.tens M M).smul_mem r h using 1
    funext z
    simp [Algebra.smul_def]

end PositivityTheory.Xgn.TestGroupPoint
end
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}
  {C : Type} [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] {RC : Subalgebra O C}


set_option maxHeartbeats 800000 in
theorem kernel_mem [Fact p.Prime] (hpS : p ∈ S) [CharZero Ω] [IsLocallyNoetherian 𝔐.X]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (hT : IsTestPt p (CR O y c') RC) :
    ∃ Kf ∈ GR.tens (TestPt.testOrd P RC) (TestPt.testOrd P RC), ∀ x x' : Fin (D.p + D.q) → 𝓞 E,
      Kf (mkN p x, mkN p x') = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x x').val := by
  obtain ⟨halg, ⟨v, hv, hvp⟩, -, hR⟩ := hT
  have hp : p.Prime := Fact.out
  have hR1 : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hpow : p ^ 𝔐.R p = p * p ^ (𝔐.R p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hR1]
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hvI : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv x).1 x.2, fun r hr => ⟨⟨r, (hv r).2 hr⟩, rfl⟩⟩
  haveI : IsFractionRing RC C := hvI.isFractionRing
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  letI : Algebra (CR O y c') RC := (toRC _ RC hR).toAlgebra
  have hφ : Function.Injective (algebraMap (CR O y c') RC) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  let κ : FractionRing RC ≃+* C := (FractionRing.algEquiv RC C).toRingEquiv
  have hκ : ∀ r : RC, κ (algebraMap RC _ r) = r := (FractionRing.algEquiv RC C).commutes
  haveI : IsAlgClosed (FractionRing RC) := IsAlgClosed.of_ringEquiv C _ κ.symm
  let ik : Ω →+* FractionRing RC := κ.symm.toRingHom.comp (algebraMap Ω C)
  have hik : ∀ r : CR O y c', ik r = algebraMap RC _ (algebraMap (CR O y c') RC r) := fun r =>
    (RingEquiv.symm_apply_eq κ).2 (hκ (algebraMap (CR O y c') RC r)).symm
  have hfr : ik.comp (fracToField (CR O y c')) = PositivityTheory.UnitarySelfGeneration.fracMap hφ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))
    rw [PositivityTheory.UnitarySelfGeneration.fracMap_comp]
    ext r
    exact (congrArg ik (IsFractionRing.lift_algebraMap _ r)).trans (hik r)
  let Γ' := PositivityTheory.UnitarySelfGeneration.bcGroup P.Γ₁ hφ
  let F : Γ'.G.left ⟶ P.Γ₁.G.left := pullback.fst P.Γ₁.G.hom (spMap (algebraMap (CR O y c') RC))
  have hF : F ≫ P.Γ₁.G.hom = Γ'.G.hom ≫ spMap (algebraMap (CR O y c') RC) := pullback.condition
  have hbc : Γ'.IsBaseChange P.Γ₁ (algebraMap (CR O y c') RC) F := by
    have h := isGrpPullback_pullback P.Γ₁.G (spMap (algebraMap (CR O y c') RC))
    refine ⟨h.1, h.2, FractionRing (CR O y c'), inferInstance, algebraMap _ _,
      RingHom.id _, PositivityTheory.UnitarySelfGeneration.fracMap hφ, fun t => (P.Γ₁.pt t).left, Function.injective_id, rfl,
      PositivityTheory.UnitarySelfGeneration.fracMap_comp hφ, fun t => Over.w (P.Γ₁.pt t), fun t => ?_,
      fun t => (PositivityTheory.UnitarySelfGeneration.bcPt_fst P.Γ₁ hφ t).symm⟩
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hpt : ∀ t, (Γ'.pt t).left ≫ F ≫ P.i₁ = spMap ik ≫ (G.t₁.pt t).left := fun t => by
    rw [P.pts₁, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfr]
    exact congrArg (· ≫ P.i₁) (PositivityTheory.UnitarySelfGeneration.bcPt_fst P.Γ₁ hφ t)
  let ζ' : RCˣ := Units.map (algebraMap (CR O y c') RC).toMonoidHom (P.ζ ^ p ^ (𝔐.R p - 1))
  have hζ' : ((ζ' : RC) : C) = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) := by
    rw [← P.ζ_eq]; rfl
  have hζp : ζ' ^ p = 1 := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', ← map_pow, ← pow_mul, mul_comm, ← hpow,
      G.ζ_prim.pow_eq_one, map_one]; rfl))
  obtain ⟨bi, hbi⟩ := exists_bichar (D.p + D.q) p (p ^ 𝔐.R p) (dvd_pow_self p (by omega)) ζ' hζp G.e
  let Z : Over 𝔐.X := Over.mk ((Γ'.G ⊗ Γ'.G).hom ≫ spMap (algebraMap (CR O y c') RC) ≫ P.x)
  have hw : ∀ u : Γ'.G ⊗ Γ'.G ⟶ Γ'.G, (u.left ≫ F ≫ P.i₁) ≫ 𝔐.t.G.hom = Z.hom := fun u => by
    rw [Category.assoc, Category.assoc, P.tors₁.isOver, ← Category.assoc F, hF, Category.assoc,
      ← Category.assoc u.left, Over.w u]
    rfl
  let X : (Γ'.G ⊗ Γ'.G ⟶ Γ'.G) → (Z ⟶ 𝔐.t.G) := fun u => Over.homMk (u.left ≫ F ≫ P.i₁) (hw u)
  have hX : ∀ u, X u ^ p = 1 := fun u =>
    PositivityTheory.HtPt.Htat.tors_of_pt P.tors₁ (u.left ≫ F) (X u) (Category.assoc _ _ _).symm
  have hs : ∀ a b, valAt (lift (Γ'.pt a) (Γ'.pt b)).left ⊤ le_top
      (PositivityTheory.HtPt.Weilfun.weilUnit 𝔐.t.cub p Z (X (fst _ _)) (X (snd _ _)) (hX _) (hX _)).val =
      algebraMap RC _ ((bi a b : RCˣ) : RC) := by
    intro a b
    obtain ⟨x, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p a
    obtain ⟨x', rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p b
    let f₀ := lift (Γ'.pt (qmk p x)) (Γ'.pt (qmk p x'))
    have hf₀ : f₀.left ≫ Z.hom = spMap ik ≫ 𝔐.ξ := by
      rw [← hw (fst _ _), ← Category.assoc, ← Category.assoc, ← Over.comp_left, lift_fst, hpt, Category.assoc,
        Over.w]
      rfl
    let f : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Z := Over.homMk f₀.left hf₀
    let ψ : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Over.mk 𝔐.ξ := Over.homMk (spMap ik) rfl
    have e1 : f ≫ X (fst _ _) = ψ ≫ G.t₂.pt (qmk _ (p ^ (𝔐.R p - 1) • x)) := by
      rw [G.compat]
      refine Over.OverMorphism.ext ?_
      change f₀.left ≫ (fst Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _
      rw [← Category.assoc, ← Over.comp_left, lift_fst, hpt]
    have e2 : f ≫ X (snd _ _) = (ψ ≫ G.t₂.pt (qmk _ x')) ^ p ^ (𝔐.R p - 1) := by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, ← map_pow]
      have : (qmk (p ^ 𝔐.R p) x') ^ p ^ (𝔐.R p - 1) = qmk _ (p ^ (𝔐.R p - 1) • x') :=
        ((qhom _ (p ^ 𝔐.R p)).map_pow (Multiplicative.ofAdd x') _).symm
      rw [this, G.compat]
      refine Over.OverMorphism.ext ?_
      change f₀.left ≫ (snd Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _
      rw [← Category.assoc, ← Over.comp_left, lift_snd, hpt]
    have t1 : ∀ u, (f ≫ X u) ^ p = 1 := fun u => by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, hX, MonObj.comp_one]
    have t2 : ∀ z, (ψ ≫ G.t₂.pt z) ^ p ^ 𝔐.R p = 1 := fun z => by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, (G.t₂.onto _).2 ⟨z, rfl⟩, MonObj.comp_one]
    have k1 := PositivityTheory.HtPt.Weilfun.weilUnit_comp 𝔐.t.cub p f (hX (fst _ _)) (hX (snd _ _)) (t1 _) (t1 _)
    let u : (FractionRing RC)ˣ := Units.map (algebraMap RC _).toMonoidHom (bi (qmk p x) (qmk p x'))
    have hu : (u : FractionRing RC) = ik (G.ζ ^ (G.e (p ^ (𝔐.R p - 1) • x) x').val) := by
      rw [map_nsmul, AddMonoidHom.nsmul_apply, pow_val_nsmul G.ζ_prim.pow_eq_one]
      refine ((RingEquiv.symm_apply_eq κ).2 ?_).symm
      change _ = κ (algebraMap RC _ ((bi (qmk p x) (qmk p x') : RCˣ) : RC))
      rw [hκ, hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', map_pow]
    have k2 := (G.weil (p ^ (𝔐.R p - 1) • x) x' _ ik (ψ ≫ G.t₂.pt (qmk _ _)) (ψ ≫ G.t₂.pt (qmk _ _)) u rfl rfl).2 hu
    haveI : Subsingleton (Over.mk (spMap ik ≫ 𝔐.ξ)).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing RC)))
    have k3 := PositivityTheory.HtPt.Weilfun.weilUnit_eq_of_weilIs 𝔐.t.cub (p ^ 𝔐.R p) (t2 _) (t2 _) (unitOn u)
      (by rw [Nat.cast_pow]; exact k2)
    rw [weilUnit_level 𝔐.t.cub p (p ^ (𝔐.R p - 1)) _ hpow (t1 _) (t1 _) (t2 _) (t2 _) e1 e2, k3] at k1
    rw [PositivityTheory.HtPt.Weilreg.valAt_top]
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing RC))).hom.hom k1.symm).trans ?_
    exact PositivityTheory.HtPt.Weilreg.val_unitOn _
  have hmem := bichar_mem hvI Γ' bi _ hs
  obtain ⟨ee, hee⟩ := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.2.1 RC Γ' F hbc
  refine ⟨_, tens_of_bc (N := TestPt.NAdd E (D.p + D.q) p) (C := C) (RC := RC)
    ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) ee hee (TestPt.testOrd P RC) rfl _ hmem,
    fun x x' => ?_⟩
  change (((bi (qmk p x) (qmk p x') : RCˣ) : RC) : C) = _
  rw [hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ']


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem exists_der [Fact p.Prime] (hpS : p ∈ S) [CharZero Ω]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (hR : ∀ a ∈ CR O y c', algebraMap Ω C a ∈ RC) {g : ℕ}
    (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hR] (Fin g → RC)) :
    ∃ Dv : TestPt.testOrd P RC →ₗ[RC] ReciprocityTheory.PGsh.Up.LieDualModP p RC g, IsDerAt0 _ Dv ∧
      (∀ u : P.Dh.om, ∃ f : TestPt.testOrd P RC, f.1 0 = 0 ∧ Dv f = Submodule.Quotient.mk (io u)) ∧
      ∀ (x : Fin (D.p + D.q) → 𝓞 E) (f : TestPt.testOrd P RC),
        (∀ x', f.1 (mkN p x') = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x x').val) →
        Dv f = Submodule.Quotient.mk (io ⟨P.Dh.h x, P.Dh.h_mem x⟩) := by
  have hp : p.Prime := Fact.out
  have hR1 : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  haveI : Finite (TestPt.NAdd E (D.p + D.q) p) := this
  haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')
  have hφ : Function.Injective (toRC (CR O y c') RC hR) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  have hBT := GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁ 𝔐.t.semi.smooth
  obtain ⟨θ, ⟨hθs, -⟩, hθk, hθc⟩ := hBT.2.2.2.2.2 P.L P.M
  have hom : P.Dh.om = LinearMap.range P.j := P.isHT.1
  have hj : ∀ w, P.j w ∈ P.Dh.om := fun w => by rw [hom]; exact ⟨w, rfl⟩
  obtain ⟨Dv, hD1, hD2⟩ := exists_der_gen (N := TestPt.NAdd E (D.p + D.q) p) (C := C) _ hφ Subtype.val_injective
    ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) hBT.1 p θ hθs (fun w => (hθk w).1)
    (P.j.codRestrict _ hj) io (TestPt.testOrd P RC) rfl
  refine ⟨Dv, hD1, fun u => ?_, fun x f hf => ?_⟩
  · obtain ⟨w, hw⟩ : u.1 ∈ LinearMap.range P.j := by rw [← hom]; exact u.2
    obtain ⟨a, ha⟩ := (augIdeal (P.Γ₁.btOrder ⊤)).toCotangent_surjective (θ w)
    have ha1 : a.1.1 1 = 0 := a.2
    refine ⟨⟨_, Submodule.subset_span ⟨a.1.1, a.1.2, rfl⟩⟩, ?_, ?_⟩
    · change algebraMap Ω C ((a.1.1 1 : CR O y c') : Ω) = 0
      rw [ha1]; simp
    · refine (hD2 a.1 _ w (fun _ => rfl) ((cotMap_aug _ a).trans ha)).trans ?_
      exact congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw)
  · obtain ⟨χ, w, hχ, hw, hHT⟩ := P.isHT.2.2 x
    obtain ⟨α, hα⟩ := exists_alpha (E := E) (D.p + D.q) p (𝔐.R p) hR1
    have h1 := isHT_res P.Γ₁ P.Γ₂ (dvd_pow_self p (by omega)) P.tors₁ P.tors₂ P.M α (fun t => by
      obtain ⟨z, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p t
      rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, ← P.pts₂, hα, G.compat]) χ w hHT
    have hval : ∀ z, ((((χ.comp α) (qmk p z) : (CR O y c')ˣ) : CR O y c') : Ω) =
        (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x z).val := fun z => by
      rw [MonoidHom.comp_apply, hα]
      have : χ (qmk _ (p ^ (𝔐.R p - 1) • z)) = P.ζ ^ (P.Dh.e x (p ^ (𝔐.R p - 1) • z)).val := hχ _
      rw [this, P.Dh_e, map_nsmul, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, P.ζ_eq,
        pow_val_nsmul G.ζ_prim.pow_eq_one]
    have hm : (fun t => (((χ.comp α) t : (CR O y c')ˣ) : CR O y c')) ∈ P.Γ₁.btOrder ⊤ := by
      obtain ⟨s, hs, -⟩ := h1
      exact char_mem _ _ s hs
    refine (hD2 ⟨_, hm⟩ f w (fun z => ?_) ((cotMap_char _ _ hm).trans (hθc _ _ h1).symm)).trans
      (congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw.symm))
    obtain ⟨z', hz'⟩ := FunctionFamilyIdempotent.qmk_surj _ p (Multiplicative.ofAdd z)
    have : z = mkN p z' := (congrArg Multiplicative.toAdd hz').symm
    subst this
    rw [hf]
    exact ((congrArg (algebraMap Ω C) (hval z')).trans (map_pow _ _ _)).symm

theorem act_mem [Fact p.Prime]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (a : 𝓞 E) (f : TestPt.NAdd E (D.p + D.q) p → C) (hf : f ∈ TestPt.testOrd P RC) :
    (fun x : TestPt.NAdd E (D.p + D.q) p => f fun i => Ideal.Quotient.mk _ a * x i) ∈ TestPt.testOrd P RC := by
  have hp : p.Prime := Fact.out
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')
  haveI := 𝔐.t.act.hom a
  have h4 := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.1 (𝔐.t.act.act a) (FunctionFamilyIdempotent.mulT _ p a) (by
      intro t
      obtain ⟨x, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p t
      rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, FunctionFamilyIdempotent.mulT_qmk,
        G.t₁.lin, Over.comp_left, P.pts₁]
      simp only [Category.assoc])
  have : TestPt.testOrd P RC ≤ (TestPt.testOrd P RC).comap (LinearMap.funLeft RC C
      fun (x : TestPt.NAdd E (D.p + D.q) p) i => Ideal.Quotient.mk _ a * x i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, h4 g hg, rfl⟩
  exact this hf

end PositivityTheory.Xgn.TestGroupPoint

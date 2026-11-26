module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameAfterExtIffAnd
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.AlgLawsCompare

open NumberField IsDedekindDomain IsLocalRing AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

section Valuations

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem valV_le_one (v : V) : valV V (algebraMap V K' v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v

theorem valV_lt_one_iff (v : V) : valV V (algebraMap V K' v) < 1 ↔ v ∈ maximalIdeal V :=
  HeightOneSpectrum.valuation_lt_one_iff_mem _ v

theorem valV_eq_one_iff_isUnit (v : V) : valV V (algebraMap V K' v) = 1 ↔ IsUnit v := by
  rw [← notMem_maximalIdeal, ← valV_lt_one_iff (K' := K'), not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (valV_le_one v) h⟩

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K' v) := by
  have h1 : algebraMap V K' v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K')).2 h0
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 ((valV_lt_one_iff v).2 h)
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

end Valuations

theorem exists_overLa {K : Type} [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr) (hT : T.FinRes) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la T.V io e := by
  have hint : ∀ a : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = io a := fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := T.V) (K := T.Fr)
      (IsIntegral.map_of_comp_eq (Int.castRingHom T.V) io (RingHom.ext_int _ _) a.isIntegral_coe)
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective T.V T.Fr
  let g : 𝓞 K →+* T.V :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap T.V T.Fr (g a) = io (algebraMap (𝓞 K) K a) := hg0
  have hne : (maximalIdeal T.V).comap g ≠ ⊥ := by
    have : Finite (ResidueField T.V) := hT
    have hc : Nat.card (ResidueField T.V) ≠ 0 := Nat.card_pos.ne'
    intro h
    have h1 : ((Nat.card (ResidueField T.V) : ℕ) : 𝓞 K) ∈ (maximalIdeal T.V).comap g := by
      rw [Ideal.mem_comap, map_natCast, ← residue_eq_zero_iff, map_natCast, ← nsmul_one]
      exact card_nsmul_eq_zero'
    rw [h, Ideal.mem_bot] at h1
    exact hc (by exact_mod_cast h1)
  let la : HeightOneSpectrum (𝓞 K) := ⟨(maximalIdeal T.V).comap g, Ideal.comap_isPrime _ _, hne⟩
  have hun : ∀ a : 𝓞 K, a ∉ la.asIdeal → valV T.V (io (algebraMap (𝓞 K) K a)) = 1 := fun a ha => by
    rw [← hg, valV_eq_one_iff_isUnit]
    exact notMem_maximalIdeal.1 ha
  have hone : ∀ x : K, la.valuation K x = 1 → valV T.V (io x) = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
    have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
    have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
    rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  have hπK : la.valuation K (algebraMap (𝓞 K) K π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
  have hπm : π ∈ la.asIdeal := by
    rw [← la.valuation_lt_one_iff_mem (K := K), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hpos : 0 < vV T.V (io (algebraMap (𝓞 K) K π)) := by
    rw [← hg]
    refine vV_pos (fun h => ?_) hπm
    have := hg π
    rw [h, map_zero] at this
    exact (map_ne_zero io).2 hπ0 this.symm
  refine ⟨la, (vV T.V (io (algebraMap (𝓞 K) K π))).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha, vV, vLa]
  have hva : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 := hone (a * (algebraMap (𝓞 K) K π) ^ (-vLa la a)) (by
    rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
    simp [vLa])
  have h2 := congrArg WithZero.log h1
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
    (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
  simp only [vV, smul_eq_mul] at h2 ⊢
  linarith

theorem exists_testRing_factor {K : Type} [Field K] (p : TRing K) {S : Type} [Field S] [Algebra K S]
    (φ : p.R →ₐ[K] S) {J : Type} [Fintype J] (g : J → S) :
    ∃ (r : TRing K) (α : p.R →ₐ[K] r.R) (χ : r.R →ₐ[K] S) (gr : J → r.R),
      Function.Injective χ ∧ χ.comp α = φ ∧ ∀ j, χ (gr j) = g j := by
  classical
  let e := Fintype.equivFin J
  let v : Fin (p.n + Fintype.card J) → S :=
    Fin.append (fun i => φ (Ideal.Quotient.mk p.I (MvPolynomial.X i))) (fun k => g (e.symm k))
  let Φ : MvPolynomial (Fin (p.n + Fintype.card J)) K →ₐ[K] S := MvPolynomial.aeval v
  let r : TRing K := ⟨p.n + Fintype.card J, RingHom.ker Φ, (RingHom.ker_isPrime Φ).isRadical⟩
  have hΦ : Φ.comp (MvPolynomial.rename (Fin.castAdd (Fintype.card J))) =
      φ.comp (Ideal.Quotient.mkₐ K p.I) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Φ, v, Fin.append_left]
  let α₀ : MvPolynomial (Fin p.n) K →ₐ[K] r.R :=
    (Ideal.Quotient.mkₐ K (RingHom.ker Φ)).comp (MvPolynomial.rename (Fin.castAdd (Fintype.card J)))
  have hα₀ : ∀ a ∈ p.I, α₀ a = 0 := by
    intro a ha
    show Ideal.Quotient.mk _ _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]
    have h1 : Φ (MvPolynomial.rename (Fin.castAdd (Fintype.card J)) a) = φ (Ideal.Quotient.mk p.I a) :=
      congrArg (fun F => F a) hΦ
    exact h1.trans (by rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
  let α : p.R →ₐ[K] r.R := Ideal.Quotient.liftₐ p.I α₀ hα₀
  let χ : r.R →ₐ[K] S := Ideal.kerLiftAlg Φ
  refine ⟨r, α, χ, fun j => Ideal.Quotient.mk _ (MvPolynomial.X (Fin.natAdd p.n (e j))),
    Ideal.kerLiftAlg_injective Φ, ?_, ?_⟩
  · apply Ideal.Quotient.algHom_ext
    rw [← hΦ]
    apply MvPolynomial.algHom_ext
    intro i
    rfl
  · intro j
    show Φ _ = g j
    simp [Φ, v, Fin.append_right]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z : FrPt Xo c T, FrMap φ y z :=
  FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c S T φ y

theorem fromTest_of_same_point {S : Type} [Field S] [Algebra c.F S] {y y' : FrPt Xo c S} (hx : y'.x = y.x)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y' := by
  classical
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c S y y').1 hx
  obtain ⟨r, α, χ, gr, hχ, hα, hgr⟩ := exists_testRing_factor p φ
    (J := (Σ τ : E →+* ℂ, Option (Fin (Dw.mult τ) × Fin (Dw.mult τ))) ⊕ Bool)
    (Sum.elim (fun q => q.2.elim (g q.1).det⁻¹ fun ij => g q.1 ij.1 ij.2) fun b => cond b (a : S) (a⁻¹ : Sˣ))
  let g₀ : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) r.R :=
    fun τ => Matrix.of fun i j => gr (.inl ⟨τ, some (i, j)⟩)
  have hg₀ : ∀ τ, (g₀ τ).map χ = g τ := fun τ => Matrix.ext fun i j => hgr (.inl ⟨τ, some (i, j)⟩)
  have hd : ∀ τ, IsUnit (g₀ τ).det := fun τ => by
    refine IsUnit.of_mul_eq_one (gr (.inl ⟨τ, none⟩)) (hχ ?_)
    rw [map_mul, map_one, hgr, AlgHom.map_det, AlgHom.mapMatrix_apply, hg₀]
    exact mul_inv_cancel₀ (hg τ).ne_zero
  have h1 : gr (.inr true) * gr (.inr false) = 1 := hχ (by rw [map_mul, map_one, hgr, hgr]; simp)
  let a₀ : r.Rˣ := ⟨gr (.inr true), gr (.inr false), h1, (mul_comm _ _).trans h1⟩
  obtain ⟨z, hz⟩ := exists_baseChange α y₀
  have hzy : FrMap χ z y := frMap_cancel (Xo := Xo) (c := c) _ _ _ α χ y₀ z y hz (hα ▸ h₀)
  obtain ⟨z', hz', -⟩ := existsUnique_frChg E H Dw l Xo c r.R z g₀ a₀ hd
  refine ⟨r, χ, z', (ChgBC.frChg_baseChange E H Dw l Xo c r.R S χ z z' y y' g₀ a₀ hz' hzy).2 ?_⟩
  have ha : χ (a₀ : r.R) = (a : S) := hgr (.inr true)
  simp only [hg₀, ha]
  exact hc

theorem reFrame : Formalism.L2.PjFree.ReFrame Xo c := by
  refine Formalism.L2.PjFree.reFrame_of
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw') ?_
  intro T io
  let _ := io.toAlgebra
  intro y0 z hx k hk
  have hK : ∀ τ, IsUnit ((k τ).map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk τ).map _
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  simp only at hx
  subst hx
  obtain ⟨u0, hu0⟩ := IntRebase.gen_unit' (x := y0.1.x) zs y0.1.s zg y0.1.gen
  refine ⟨⟨IntRebase.rebase₂ y0.1 _ hK, fromTest_of_same_point (y := y0.1) rfl y0.2.1,
    IntRebase.integral_reb T io y0.1 y0.2.2 k hk hK⟩, u0, rfl, fun τ i => ?_,
    𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · exact (IntRebase.isCombAtG_iff Xo.univ.t y0.1.x
      (fun j => IntRebase.ovT (t := Xo.univ.t) (y0.1.tan τ j)) _ _).2 rfl
  · intro i h
    show ((𝟙 _ : Gx y0.1.x ⟶ Gx y0.1.x).appLE _ _ h).hom (scal y0.1.x (u0 : T.Fr) i * zs.f i) = y0.1.s.f i
    rw [← hu0 i]
    exact IntRebase.id_appLE_apply _ _ h _

variable (Xo c)

end GlobalTheory.AlgLawsCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameRingSubalgebraEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameRingSubalgebraEqTop
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem frameRing_subalgebra_eq_top : ∀ (K : Type) [Field K] (J : Type) (m : J → ℕ) (R A : Type) [CommRing R] [Algebra K R] [CommRing A] [Algebra K A] (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), FrameRing m π X s → ∀ A' : Subalgebra K A, (∀ t, π t ∈ A') → (∀ τ i j, X τ i j ∈ A') → (s : A) ∈ A' → ((s⁻¹ : Aˣ) : A) ∈ A' → (∀ τ, ∃ d ∈ A', d * (X τ).det = 1) → A' = ⊤ := by
  intro K _ J m R A _ _ _ _ π X s hF A' hπ hX hs hsi hd
  obtain ⟨hdet, huniv⟩ := hF
  let ψ : R →ₐ[K] A' := π.codRestrict A' hπ
  let g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A' := fun τ => Matrix.of fun i j => ⟨X τ i j, hX τ i j⟩
  have hg : ∀ τ, (g τ).map A'.val = X τ := fun τ => by ext i j; rfl
  let a : (A')ˣ := ⟨⟨s, hs⟩, ⟨_, hsi⟩, Subtype.ext s.mul_inv, Subtype.ext s.inv_mul⟩
  have hgu : ∀ τ, IsUnit (g τ).det := by
    intro τ
    obtain ⟨d, hdA, hd1⟩ := hd τ
    refine IsUnit.of_mul_eq_one_right (⟨d, hdA⟩ : A') ?_
    apply Subtype.ext
    have h1 : A'.val (g τ).det = (X τ).det := by
      rw [← hg τ]
      exact AlgHom.map_det A'.val (g τ)
    change d * A'.val (g τ).det = 1
    rw [h1, hd1]
  obtain ⟨k, ⟨hk1, hk2, hk3⟩, -⟩ := huniv A' ψ g a hgu
  obtain ⟨k₀, -, huq⟩ := huniv A π X s hdet
  have e1 : A'.val.comp k = k₀ := by
    apply huq
    refine ⟨?_, fun τ => ?_, ?_⟩
    · rw [AlgHom.comp_assoc, hk1]; ext t; rfl
    · rw [← hg τ, ← hk2 τ]
      conv_lhs => rw [hk2 τ, hg τ]
      ext i j; rfl
    · change A'.val (k s) = s
      rw [hk3]; rfl
  have e2 : AlgHom.id K A = k₀ := by
    apply huq
    refine ⟨by ext t; rfl, fun τ => by ext i j; rfl, rfl⟩
  rw [eq_top_iff]
  intro x _
  have : A'.val (k x) = x := by
    have := DFunLike.congr_fun (e1.trans e2.symm) x
    simpa using this
  rw [← this]
  exact (k x).2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameRingSubalgebraEqTopStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalFrameRing_subalgebra_eq_top : ∀ (K : Type) [Field K] (J : Type) (m : J → ℕ) (R A : Type) [CommRing R] [Algebra K R] [CommRing A] [Algebra K A] (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), FrameRing m π X s → ∀ A' : Subalgebra K A, (∀ t, π t ∈ A') → (∀ τ i j, X τ i j ∈ A') → (s : A) ∈ A' → ((s⁻¹ : Aˣ) : A) ∈ A' → (∀ τ, ∃ d ∈ A', d * (X τ).det = 1) → A' = ⊤ := by
  first | exact @GlobalTheory.frameRing_subalgebra_eq_top | exact GlobalTheory.frameRing_subalgebra_eq_top | (intros; apply GlobalTheory.frameRing_subalgebra_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFrames
noncomputable section

namespace GlobalTheory.HolEval

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

section Ring

variable {K : Type} [Field K] {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {A : Type} [CommRing A] [Algebra K A]

theorem toC_mul (x y : CAt σ) : toC (x * y) = toC x * toC y := rfl
theorem toC_add (x y : CAt σ) : toC (x + y) = toC x + toC y := rfl
theorem toC_one : toC (1 : CAt σ) = 1 := rfl

def holSub (B : Set V) (k : V → (A →ₐ[K] CAt σ)) : Subalgebra K A where
  carrier := {t | DifferentiableOn ℂ (fun b => toC (k b t)) B}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_mul, toC_mul] at *
    exact hx.mul hy
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_add (f := _), toC_add] at *
    exact hx.add hy
  algebraMap_mem' := fun r => by
    simp only [Set.mem_setOf_eq, AlgHom.commutes]
    exact differentiableOn_const _

theorem mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {t : A} :
    t ∈ holSub B k ↔ DifferentiableOn ℂ (fun b => toC (k b t)) B := Iff.rfl

theorem inv_mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {d x : A} (hx : x ∈ holSub B k)
    (h : d * x = 1) : d ∈ holSub B k := by
  rw [mem_holSub] at hx ⊢
  have key : ∀ b, toC (k b d) * toC (k b x) = 1 := fun b => by
    rw [← toC_mul, ← map_mul, h, map_one, toC_one]
  have hne : ∀ b, toC (k b x) ≠ 0 := fun b hb => by
    have h1 := key b
    rw [hb, mul_zero] at h1
    exact zero_ne_one h1
  have heq : (fun b => toC (k b d)) = fun b => (toC (k b x))⁻¹ :=
    funext fun b => eq_inv_of_mul_eq_one_left (key b)
  rw [heq]
  exact hx.inv fun b _ => hne b

theorem det_mem {n : ℕ} (A' : Subalgebra K A) (X : Matrix (Fin n) (Fin n) A) (h : ∀ i j, X i j ∈ A') :
    X.det ∈ A' := by
  rw [Matrix.det_apply]
  refine sum_mem fun e _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

private theorem evR_eq_of_frMap {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hS : Out.SecBaseChangeSt) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c w n)
    {S : Type} [CommRing S] [Algebra c.F S] (q : TRing c.F) (κ : q.R →ₐ[c.F] S) (u : FrPt Xo c q.R)
    (x : FrPt Xo c S) (h : FrMap κ u x) : evR Xo c f x = κ (f q u) := by
  have hW := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
  unfold sec secW at hf
  obtain ⟨hn, -⟩ := hf
  unfold evR evalAt
  split_ifs with hT
  · exact hW f hn S _ q _ κ _ u x hT.choose_spec.choose_spec.choose_spec h
  · exact absurd ⟨q, κ, u, h⟩ hT

end Ring

theorem differentiableOn_evR : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (p : TRing c.F) (y₀ : FrPt Xo c p.R) (ψ : V → (p.R →ₐ[c.F] CAt σ)) (z y : V → FrPt Xo c (CAt σ)) (G : V → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : V → CAt σ), (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b)) → (∀ t, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B) → DifferentiableOn ℂ (fun b => toC (a b)) B → ∀ w n, ∀ f ∈ sec Xo c w n, DifferentiableOn ℂ (fun b => toC (evR Xo c f (y b))) B := by
  intro hS E _ _ _ H Dw l Xo c σ V _ _ B p y₀ ψ z y G a hzy hψ hG ha w n f hf
  obtain ⟨A, π, X, s, u, hU⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨hFR, u₀, hπ, hch⟩ := hU
  have hk : ∀ b ∈ B, ∃ kk : A.R →ₐ[c.F] CAt σ,
      kk.comp π = ψ b ∧ (∀ τ, (X τ).map kk = G b τ) ∧ kk (s : A.R) = a b := by
    intro b hb
    obtain ⟨-, hc⟩ := hzy b hb
    obtain ⟨hex, huniq⟩ := GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)
    obtain ⟨g, a', hdet, hc'⟩ := hex hc.1
    obtain ⟨hg, ha'⟩ := huniq _ _ _ _ hc hc'
    obtain ⟨kk, ⟨h1, h2, h3⟩, -⟩ := hFR.2 (CAt σ) (ψ b) g a' hdet
    exact ⟨kk, h1, fun τ => (h2 τ).trans (congrFun hg τ).symm, h3.trans ha'.symm⟩
  rcases B.eq_empty_or_nonempty with hB | ⟨b₀, hb₀⟩
  · rw [hB]
    exact differentiableOn_empty
  have : Nonempty (A.R →ₐ[c.F] CAt σ) := ⟨(hk b₀ hb₀).choose⟩
  choose! kk hkk using hk
  have hX : ∀ τ i j, X τ i j ∈ holSub B kk := by
    intro τ i j
    rw [mem_holSub]
    refine (hG τ i j).congr fun b hb => ?_
    show toC (kk b (X τ i j)) = toC (G b τ i j)
    rw [← (hkk b hb).2.1 τ]
    rfl
  have hs : (s : A.R) ∈ holSub B kk := by
    rw [mem_holSub]
    refine ha.congr fun b hb => ?_
    show toC (kk b (s : A.R)) = toC (a b)
    rw [(hkk b hb).2.2]
  have hA' := GlobalTheory.T.universalFrameRing_subalgebra_eq_top c.F (E →+* ℂ) (fun τ => Dw.mult τ) p.R A.R π X s hFR (holSub B kk)
    (fun t => by
      rw [mem_holSub]
      refine (hψ t).congr fun b hb => ?_
      show toC (kk b (π t)) = toC (ψ b t)
      rw [← (hkk b hb).1]
      rfl)
    hX hs (inv_mem_holSub hs (Units.inv_mul s))
    (fun τ => by
      obtain ⟨v, hv⟩ := hFR.1 τ
      refine ⟨((v⁻¹ : (A.R)ˣ) : A.R), inv_mem_holSub (det_mem _ (X τ) (hX τ)) ?_, ?_⟩ <;>
        · rw [← hv]
          exact Units.inv_mul v)
  have he : f A u ∈ holSub B kk := by
    rw [hA']
    exact Algebra.mem_top
  rw [mem_holSub] at he
  refine he.congr fun b hb => ?_
  show toC (evR Xo c f (y b)) = toC (kk b (f A u))
  congr 1
  apply evR_eq_of_frMap hS hf A (kk b) u (y b)
  obtain ⟨hm, hc⟩ := hzy b hb
  have hb1 : FrMap (kk b) u₀ (z b) :=
    ((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 p.R A.R (CAt σ) π (kk b) y₀ u₀ (z b) hπ).2
      (by rw [(hkk b hb).1]; exact hm)
  apply (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A.R (CAt σ) (kk b) u₀ u (z b) (y b) X s hch hb1).2
  have e1 : (fun τ => (X τ).map (kk b)) = G b := funext (hkk b hb).2.1
  rw [e1, (hkk b hb).2.2]
  exact hc

end GlobalTheory.HolEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFramesStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_natural_rule_holomorphic_frames : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (p : TRing c.F) (y₀ : FrPt Xo c p.R) (ψ : V → (p.R →ₐ[c.F] CAt σ)) (z y : V → FrPt Xo c (CAt σ)) (G : V → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : V → CAt σ), (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b)) → (∀ t, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B) → DifferentiableOn ℂ (fun b => toC (a b)) B → ∀ w n, ∀ f ∈ sec Xo c w n, DifferentiableOn ℂ (fun b => toC (evR Xo c f (y b))) B := by
  first | exact @GlobalTheory.HolEval.differentiableOn_evR | exact GlobalTheory.HolEval.differentiableOn_evR | (intros; apply GlobalTheory.HolEval.differentiableOn_evR <;> assumption)
end
end

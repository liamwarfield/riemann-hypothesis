module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicitySubquotientLatticeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

abbrev Var (ι : Type) (d a : ℕ) : Type := ι × Fin d × Fin a

abbrev Pol (ι : Type) (d a : ℕ) : Type := MvPolynomial (Var ι d a) ℂ

abbrev Tup (ι : Type) (a d : ℕ) (n : ι → ℕ) : Type := ∀ τ, Fin (n τ) → {s : Fin a → Fin d // StrictMono s}

variable {ι : Type}

def minorAt (τ : ι) {a d : ℕ} (s : Fin a → Fin d) : Pol ι d a :=
  (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)).det

variable [Fintype ι]

def prodMinors {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : Pol ι d a := ∏ τ, ∏ j, minorAt τ (T τ j).1

def rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ i' : Fin d, C (κ y.1 i' y.2.1) * X (y.1, i', y.2.2)

def colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ j' : Fin a, C (g y.1 j' y.2.2) * X (y.1, y.2.1, j')

def detChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) : ℂ := ∏ τ, (g τ).det ^ n τ

def inv (a d : ℕ) (n : ι → ℕ) : Submodule ℂ (Pol ι d a) where
  carrier := {P | ∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
    colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P = detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • P}
  add_mem' := by
    intro P Q hP hQ g
    simp only [Set.mem_setOf_eq] at *
    rw [map_add (f := _), hP g, hQ g, smul_add]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c P hP g
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hP g, smul_comm]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem colSub_minorAt {a d : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (s : Fin a → Fin d) :
    colSub g (minorAt τ s) = (g τ).det • minorAt τ s := by
  unfold minorAt
  rw [AlgHom.map_det]
  have hM : (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).mapMatrix (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) =
      (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) * (g τ).map C := by
    ext i i'
    simp [colSub, Matrix.mul_apply, mul_comm]
  rw [hM, Matrix.det_mul, show ((g τ).map C).det = C (g τ).det from ((C : ℂ →+* Pol ι d a).map_det (g τ)).symm, smul_eq_C_mul, mul_comm]

theorem colSub_prodMinors {a d : ℕ} {n : ι → ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (T : Tup ι a d n) :
    colSub g (prodMinors T) = detChar n g • prodMinors T := by
  unfold prodMinors detChar
  simp only [map_prod, colSub_minorAt, smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, map_prod, map_pow]

theorem prodMinors_mem_inv {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : prodMinors T ∈ inv a d n :=
  fun g => colSub_prodMinors _ T

theorem colSub_rowSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    colSub g (rowSub κ P) = rowSub κ (colSub g P) := by
  have : (colSub g).comp (rowSub κ) = (rowSub κ).comp (colSub g) := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowSub, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_mem_inv {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) {P : Pol ι d a} (hP : P ∈ inv a d n) :
    rowSub κ P ∈ inv a d n := by
  intro g
  rw [colSub_rowSub, hP g, map_smul]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

open Classical

variable {ι : Type} [Fintype ι]

theorem fockS_conj {σ : Type} (f g : MvPolynomial σ ℂ) :
    Formalism.L2.DIV.fockS f g = starRingEnd ℂ (Formalism.L2.DIV.fockS g f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.L2.DIV.fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, RCLike.star_def, Complex.conj_conj]
  ring

theorem fockS_self_re_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.L2.DIV.fockS f f).re := by
  unfold Formalism.L2.DIV.fockS
  rw [Complex.re_sum]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hf
  have hms : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have key : ∀ k ∈ f.support, (star (f.coeff k) * f.coeff k * (Formalism.L2.DIV.mfact k : ℂ)).re =
      ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ) := by
    intro k _
    rw [RCLike.star_def, mul_comm (starRingEnd ℂ _), Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl key]
  have hpos : 0 < ‖f.coeff m‖ ^ 2 * (Formalism.L2.DIV.mfact m : ℝ) := by
    have : (0 : ℝ) < Formalism.L2.DIV.mfact m := by
      unfold Formalism.L2.DIV.mfact; exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ))
    (fun k _ => by positivity) hms)

end GlobalTheory.MinorFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaNoPTorsionOfCotangentInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaNoPTorsionOfCotangentInjective
open scoped TensorProduct

namespace GlobalTheory

open PDiv

theorem omega_eq_zero_of_p_smul_eq_zero :
    ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R),
      (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) →
        ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  intro p R _ G hinj w hw
  refine Subtype.ext (funext fun n => ?_)
  have hp : (p : R) • w.1 (n + 1) = 0 := congrArg (fun v : G.omega => v.1 (n + 1)) hw
  apply hinj n
  change cotMap (G.mulP n) (w.1 n) = cotMap (G.mulP n) 0
  rw [map_zero, ← w.2 n, ← LinearMap.comp_apply, ← cotMap_comp, G.mulP_comp_res,
    cotMap_mulBy, hp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R), (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) → ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  first | exact @GlobalTheory.omega_eq_zero_of_p_smul_eq_zero | exact GlobalTheory.omega_eq_zero_of_p_smul_eq_zero | (intros; apply GlobalTheory.omega_eq_zero_of_p_smul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomCotangentPullbackInjectiveOfSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomCotangentPullbackInjectiveOfSq
open scoped TensorProduct

namespace GlobalTheory

namespace PDiv

theorem cotMap_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A]
    [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A),
    (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 →
      b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) →
    Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  intro R C A _ _ _ _ _ f h
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, rfl⟩ := AugCot.d_surjective _ w
  have hw' : dUnit (R := R) (f c) = 0 := (cotMap_d f c).symm.trans hw
  rw [dUnit, AugCot.d_eq_zero_iff] at hw'
  change AugCot.d _ c = 0
  rw [AugCot.d_eq_zero_iff]
  apply h
  have e : Bialgebra.counitAlgHom R A (f c) = Bialgebra.counitAlgHom R C c :=
    AlgHom.congr_fun (BialgHomClass.counitAlgHom_comp f) c
  have e2 : f (c - algebraMap R C (Bialgebra.counitAlgHom R C c)) =
      f c - algebraMap R A (Bialgebra.counitAlgHom R A (f c)) := by
    rw [map_sub, e]
    congr 1
    exact AlgHom.commutes (f : C →ₐ[R] A) _
  rw [e2]
  exact hw'

end PDiv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomCotangentPullbackInjectiveOfSqStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A] [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A), (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) → Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  first | exact @GlobalTheory.PDiv.cotMap_injective_of_sq | exact GlobalTheory.PDiv.cotMap_injective_of_sq | (intros; apply GlobalTheory.PDiv.cotMap_injective_of_sq <;> assumption)
end
end

set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_pow_eq_of_integers {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {n : ℕ} (hn : 0 < n) (a : O) : ∃ b : O, b ^ n = a := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) hn
  have h1 : v c ^ n ≤ 1 := by
    rw [← map_pow, hc]
    exact hv.map_le_one a
  obtain ⟨b, rfl⟩ := hv.exists_of_le_one ((pow_le_one_iff hn.ne').1 h1)
  exact ⟨b, hv.hom_inj (by rw [map_pow, hc])⟩

theorem omega_finite_projective (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) :
    Module.Finite O G.omega ∧ Module.Projective O G.omega := by
  have : IsDomain O := hv.hom_inj.isDomain _
  have : ValuationRing O := ValuationRing.of_integers v hv
  have hp : (p : O) ≠ 0 := fun h => by
    have := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 this)
  have htf : ∀ w : G.omega, (p : O) • w = 0 → w = 0 :=
    GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective p O G fun n => GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq O _ _ (G.mulP n)
      (GlobalTheory.T.mulP_mem_sq_counit_ker p O hp Fact.out (exists_pow_eq_of_integers hv (Fact.out : p.Prime).pos) G n)
  have htfk : ∀ (k : ℕ) (w : G.omega), (p : O) ^ k • w = 0 → w = 0 := fun k => by
    induction k with
    | zero => intro w hw; rwa [pow_zero, one_smul] at hw
    | succ k ih => intro w hw; exact htf w (ih _ (by rw [← mul_smul, ← pow_succ, hw]))
  have : Module.Finite O G.omega := by
    have h := Module.Finite.equiv (G.omegaQuotEquiv 1).symm
    rw [pow_one] at h
    exact GlobalTheory.finite_of_isHausdorff_of_finite_quotient (Ideal.span {(p : O)}) _
  have : Module.Flat O G.omega := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro w ⟨⟨a, ha⟩, hw⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have : ∃ k, a ∣ (p : O) ^ k := by
      by_contra! hk
      refine ha0 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) a fun k => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact (ValuationRing.dvd_total _ _).resolve_left (hk k)
    obtain ⟨k, c, hc⟩ := this
    have hw' : a • w = 0 := hw
    exact htfk k w (by rw [hc, mul_comm, mul_smul, hw', smul_zero])
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.PDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
open IsLocalRing

namespace GlobalTheory.EtaleHensel

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem algHom_eq_of_residue_eq [Algebra.Etale R A] [IsLocalRing B] {φ₁ φ₂ : A →ₐ[R] B}
    (h : ∀ a, residue B (φ₁ a) = residue B (φ₂ a)) : φ₁ = φ₂ := by

  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let ψ : TensorProduct R A A →ₐ[R] B := Algebra.TensorProduct.productMap φ₁ φ₂
  let ρ : B →ₐ[R] ResidueField B := IsScalarTower.toAlgHom R B (ResidueField B)
  have hρ : ∀ b, ρ b = residue B b := fun _ => rfl
  have key : ρ.comp ψ = (ρ.comp φ₁).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, ψ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, hρ, h b]
  have hres : residue B (ψ t) = 1 := by
    have := congrArg (fun f : TensorProduct R A A →ₐ[R] ResidueField B => f t) key
    simpa only [AlgHom.comp_apply, ht1, map_one, hρ] using this
  have hu : IsUnit (ψ t) := by
    by_contra hn
    have h0 : residue B (ψ t) = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)
    exact one_ne_zero (hres.symm.trans h0)
  ext a
  have hz := congrArg ψ (ht a)
  simp only [map_mul, map_sub, map_zero, ψ, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, one_mul, mul_one] at hz
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

theorem bijective_residue_comp : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B],
    Function.Bijective
      (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  intro R A B _ _ _ _ _ _ _
  refine ⟨fun φ₁ φ₂ he => algHom_eq_of_residue_eq fun a => ?_, fun φ => ?_⟩
  · exact DFunLike.congr_fun he a
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal B)
      (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective
      (fun b => (residue_eq_zero_iff b).symm) φ
    exact ⟨ψ, hψ⟩

end GlobalTheory.EtaleHensel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselianStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_residue_comp_etale_henselian : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B], Function.Bijective (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  first | exact @GlobalTheory.EtaleHensel.bijective_residue_comp | exact GlobalTheory.EtaleHensel.bijective_residue_comp | (intros; apply GlobalTheory.EtaleHensel.bijective_residue_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.AxesPull

variable {R : Type} [CommRing R]

theorem isAffine_unit : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))

theorem pO1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pO1 g (pO1 f a) = pO1 (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).1 a)

theorem pF_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pF g (pF f a) = pF (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.1 a)

theorem pH1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : deRhamH1Pullback g (deRhamH1Pullback f a) = deRhamH1Pullback (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.2.1 a)

theorem pO1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pO1 (u ≫ f) a = 0 := by
  rw [← pO1_comp]
  haveI := ((GlobalTheory.AbCoh.Vanish.main.1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom isAffine_unit).1)
  rw [Subsingleton.elim (pO1 f a) 0, map_zero]

theorem pF_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pF (u ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem pH1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    deRhamH1Pullback (u ≫ f) a = 0 := by
  rw [← pH1_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).2
  rw [Subsingleton.elim (deRhamH1Pullback f a) 0, map_zero]

theorem main : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], (∀ a, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (fst A A) a) = a ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (snd A A) a) = 0 ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 μ[A] a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (fst A A) a) = 0 ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (snd A A) a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 μ[A] a) = a) ∧ (∀ a, pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) a) = a ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (snd A A) a) = 0 ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF μ[A] a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) a) = 0 ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (snd A A) a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF μ[A] a) = a) ∧ (∀ a, deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (fst A A) a) = a ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (snd A A) a) = 0 ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback μ[A] a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (fst A A) a) = 0 ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (snd A A) a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback μ[A] a) = a) := by
  intro R _ A _
  have hid := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 R A)
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · simp only [pO1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pO1_unit, hid.1, and_self]
  · simp only [pF_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pF_unit, hid.2.2.1, and_self]
  · simp only [pH1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pH1_unit, hid.2.2.2.1, and_self]

end GlobalTheory.AbCoh.AxesPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_pullback_axes_cohomology_projections : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], (∀ a, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (fst A A) a) = a ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (snd A A) a) = 0 ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 μ[A] a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (fst A A) a) = 0 ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (snd A A) a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 μ[A] a) = a) ∧ (∀ a, pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) a) = a ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (snd A A) a) = 0 ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF μ[A] a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) a) = 0 ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (snd A A) a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF μ[A] a) = a) ∧ (∀ a, deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (fst A A) a) = a ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (snd A A) a) = 0 ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback μ[A] a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (fst A A) a) = 0 ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (snd A A) a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback μ[A] a) = a) := by
  first | exact @GlobalTheory.AbCoh.AxesPull.main | exact GlobalTheory.AbCoh.AxesPull.main | (intros; apply GlobalTheory.AbCoh.AxesPull.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPart
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem lintegral_nsq_chart_part : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (i : ι) (W : Set (V n)) (D : ι → Y → ℂ), MeasurableSet W → W ⊆ (A.chart i).target → (∀ y ∈ (A.chart i).source, A.chart i y ∈ W → D (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D i y) → AEMeasurable (D i ∘ (A.chart i).symm) (volume.restrict W) → ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu = ∫⁻ v in W, ENNReal.ofReal (‖D i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A la i W D hW hWt hD hae
  classical
  set e := A.chart i with he
  have hS : MeasurableSet e.source := e.open_source.measurableSet
  have hT : MeasurableSet e.target := e.open_target.measurableSet

  set c : Y → V n := e.source.piecewise e (fun _ => 0) with hc
  have hcm : Measurable c :=
    ContinuousOn.measurable_piecewise e.continuousOn continuousOn_const hS
  set P : V n → ℝ := e.target.piecewise (fun v => A.ph (A.kap + la) i (e.symm v)) (fun _ => 0) with hP
  have hPm : Measurable P :=
    ContinuousOn.measurable_piecewise (A.smooth_ph (A.kap + la) i).continuousOn continuousOn_const hT
  set D' : V n → ℂ := hae.mk _ with hD'
  have hD'm : Measurable D' := hae.measurable_mk
  have hDD' : (D i ∘ e.symm) =ᵐ[volume.restrict W] D' := hae.ae_eq_mk
  have hcs : ∀ y ∈ e.source, c y = e y := fun y hy => by simp [hc, hy]
  have hPt : ∀ v ∈ e.target, P v = A.ph (A.kap + la) i (e.symm v) := fun v hv => by simp [hP, hv]
  set S : Set Y := e.source ∩ c ⁻¹' W with hSdef
  have hSm : MeasurableSet S := hS.inter (hcm hW)
  have hSeq : e.source ∩ e ⁻¹' W = S := by
    ext y; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
  set G : Y → ℝ≥0∞ := S.indicator (fun y => ENNReal.ofReal (‖D' (c y)‖ ^ 2 * Real.exp (-P (c y))))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hSm
    exact ENNReal.measurable_ofReal.comp
      (((hD'm.comp hcm).norm.pow_const 2).mul ((hPm.comp hcm).neg.exp))

  set T : Set (V n) := toMeasurable (volume.restrict W) {v | ¬ (D i ∘ e.symm) v = D' v}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : volume.restrict W T = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hDD'
  set E : Set Y := e.source ∩ c ⁻¹' (T ∩ W)
  have hEm : MeasurableSet E := hS.inter (hcm (hTm.inter hW))
  have hE0 : A.mu E = 0 := by
    rw [A.mu_chart i E hEm Set.inter_subset_left]
    apply setLIntegral_measure_zero
    refine measure_mono_null ?_ (show volume (T ∩ W) = 0 by
      rwa [Measure.restrict_apply hTm] at hT0)
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    simpa [hcs y hy1] using hy2

  have hL : ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
      ∫⁻ y in e.source, G y ∂A.mu := by
    rw [hSeq]
    have h1 : ∫⁻ y in S, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
        ∫⁻ y in e.source, S.indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y)) y ∂A.mu := by
      rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_eq_left.mpr Set.inter_subset_left]
    rw [h1]
    apply lintegral_congr_ae
    have hnE : ∀ᵐ y ∂A.mu, y ∉ E := measure_eq_zero_iff_ae_notMem.mp hE0
    filter_upwards [ae_restrict_of_ae hnE, ae_restrict_mem hS] with y hyE hys
    by_cases hyS : y ∈ S
    · simp only [G, Set.indicator_of_mem hyS]
      congr 1
      have hyW : e y ∈ W := by simpa [hcs y hys] using hyS.2
      have hyT : e y ∉ T := fun h => hyE ⟨hys, by simp [hcs y hys, h, hyW]⟩
      have hDy : D i y = D' (c y) := by
        rw [hcs y hys]
        have : (D i ∘ e.symm) (e y) = D' (e y) := by
          by_contra hne
          exact hyT (subset_toMeasurable _ _ hne)
        simpa [e.left_inv hys] using this
      have hPy : P (c y) = A.ph (A.kap + la) i y := by
        rw [hcs y hys, hPt _ (e.map_source hys), e.left_inv hys]
      rw [← hDy, hPy]

      unfold WeightedAtlas.nsq
      have hp := A.mem_pick y
      have hg := A.g_ne (A.kap + la) (A.pick y) i y hp hys
      have hg2 : 0 < ‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2 := by positivity
      have ht := A.ph_trans (A.kap + la) (A.pick y) i y hp hys
      rw [hD y hys hyW, norm_mul, mul_pow]
      have : A.ph (A.kap + la) (A.pick y) y =
          A.ph (A.kap + la) i y + Real.log (‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2) := by linarith
      rw [this, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hg2]
      field_simp
    · simp [G, Set.indicator_of_notMem hyS]

  rw [hL, ap_lintegral_chart A i G hGm]
  have h2 : ∫⁻ v in e.target, G (e.symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v))) =
      ∫⁻ v in e.target, W.indicator (fun v => ENNReal.ofReal (‖D' v‖ ^ 2 * Real.exp (-P v)) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))) v := by
    refine setLIntegral_congr_fun hT fun v hv => ?_
    have hs := e.map_target hv
    have hcv : c (e.symm v) = v := by rw [hcs _ hs, e.right_inv hv]
    by_cases hvW : v ∈ W
    · have : e.symm v ∈ S := ⟨hs, by simpa [hcv] using hvW⟩
      simp only [G, Set.indicator_of_mem this, Set.indicator_of_mem hvW, hcv]
    · have : e.symm v ∉ S := fun h => hvW (by simpa [hcv] using h.2)
      simp [G, Set.indicator_of_notMem this, Set.indicator_of_notMem hvW]
  rw [h2, lintegral_indicator hW, Measure.restrict_restrict hW, Set.inter_eq_left.mpr hWt]
  apply lintegral_congr_ae
  filter_upwards [hDD', ae_restrict_mem hW] with v hv hvW
  have hvt := hWt hvW
  have hs := e.map_target hvt
  simp only [Function.comp_apply] at hv
  rw [← hv, hPt v hvt, A.ph_add A.kap la i _ hs, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [neg_add, Real.exp_add]
  have := Real.exp_pos (A.ph A.kap i (e.symm v))
  rw [Real.exp_neg (A.ph A.kap i _)]
  field_simp

end GlobalTheory.OTY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPartStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_nsq_canonical_add_chart_part : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (i : ι) (W : Set (V n)) (D : ι → Y → ℂ), MeasurableSet W → W ⊆ (A.chart i).target → (∀ y ∈ (A.chart i).source, A.chart i y ∈ W → D (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D i y) → AEMeasurable (D i ∘ (A.chart i).symm) (volume.restrict W) → ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu = ∫⁻ v in W, ENNReal.ofReal (‖D i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm v))) := by
  first | exact @GlobalTheory.OTY.lintegral_nsq_chart_part | exact GlobalTheory.OTY.lintegral_nsq_chart_part | (intros; apply GlobalTheory.OTY.lintegral_nsq_chart_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorph
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_isLocalHomeomorph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → IsLocalHomeomorph (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  apply IsLocalHomeomorph.mk
  intro y
  set i := A.pick y
  set e := A.chart i
  set S : Set (V n) := e.target ∩ e.symm ⁻¹' U with hSdef
  have hS : IsOpen S := e.isOpen_inter_preimage_symm hE.isOpen
  have hyU : (y : Y) ∈ U := y.2
  have hys : (y : Y) ∈ e.source := A.mem_pick y
  have hxS : e y ∈ S := ⟨e.map_source hys, by simp [e.left_inv hys, hyU]⟩
  have hd : DifferentiableOn ℂ (z ∘ e.symm) S := hE.holo i
  have hcd : ContDiffOn ℂ ∞ (z ∘ e.symm) S :=
    contDiffOn_piLp' 2 (fun k => contDiffOn_of_differentiableOn n _ S hS
      ((differentiableOn_piLp 2).1 hd k))
  have hca : ContDiffAt ℂ ∞ (z ∘ e.symm) (e y) := hcd.contDiffAt (hS.mem_nhds hxS)
  have hst := hca.hasStrictFDerivAt_fderiv (by simp)
  have hdet : (fderiv ℂ (z ∘ e.symm) (e y)).det ≠ 0 := hE.det_ne i y hyU hys
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero ((fderiv ℂ (z ∘ e.symm) (e y)) : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hL : ((L : V n →L[ℂ] V n)) = fderiv ℂ (z ∘ e.symm) (e y) := by
    ext v; rfl
  have hst' : HasStrictFDerivAt (z ∘ e.symm) (L : V n →L[ℂ] V n) (e y) := hL ▸ hst
  let h := hst'.toOpenPartialHomeomorph (z ∘ e.symm)
  let P := e.trans (h.restrOpen S hS)
  have hyP : (y : Y) ∈ P.source := by
    simp only [P, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hys, hst'.mem_toOpenPartialHomeomorph_source, hxS⟩
  have hPz : ∀ w ∈ P.source, P w = z w := by
    intro w hw
    have hw1 : w ∈ e.source := by
      simp only [P, OpenPartialHomeomorph.trans_source] at hw; exact hw.1
    have hh : ∀ v, h v = (z ∘ e.symm) v := fun v => by
      simp only [h, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    change (h.restrOpen S hS) (e w) = z w
    change h (e w) = z w
    rw [hh, Function.comp_apply, e.left_inv hw1]
  have hne : Nonempty (⟨U, hE.isOpen⟩ : TopologicalSpace.Opens Y) := ⟨y⟩
  let Q := P.subtypeRestr hne
  refine ⟨Q, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hyP
  · intro w hw
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hw
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    exact (hPz w hw).symm

end GlobalTheory.OTY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeight
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem jdet_isFrameOn_kap : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → A.IsFrameOn A.kap U (jdet A z) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz
  refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => hz.det_ne _ y hy (A.mem_pick y)⟩
  · set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U with hS
    have hSo : IsOpen S := (A.chart i).isOpen_inter_preimage_symm hz.isOpen
    have hk : ∀ k, ContDiffOn ℂ ∞ (fun v => (z ((A.chart i).symm v)) k) S := fun k =>
      contDiffOn_of_differentiableOn n _ S hSo (fun v hv =>
        (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt v
          (hz.holo i v hv))
    have hpi := contDiffOn_pi.mpr hk
    have h1 : ContDiffOn ℂ ∞ (z ∘ (A.chart i).symm) S :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.comp_contDiffOn hpi
    have h2 : ContDiffOn ℂ ∞ (fderiv ℂ (z ∘ (A.chart i).symm)) S :=
      h1.fderiv_of_isOpen hSo (by simp)
    have h3 : DifferentiableOn ℂ (fun v => (fderiv ℂ (z ∘ (A.chart i).symm) v).det) S := by
      intro v hv
      exact ((flL_det_contDiffAt ((h2 v hv).contDiffAt (hSo.mem_nhds hv))).differentiableAt
        (by simp)).differentiableWithinAt
    refine h3.congr fun v hv => ?_
    simp only [Function.comp_apply, jdet, jz, (A.chart i).right_inv hv.1]
  · have hyt : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
    have hov : IsOpen (ovl A.chart i j) :=
      (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
    have hmov : A.chart i y ∈ ovl A.chart i j := ⟨hyt, by simp [(A.chart i).left_inv hi, hj]⟩
    have hτ : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_trans i j).differentiableAt (hov.mem_nhds hmov)
    have hτy : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp [(A.chart i).left_inv hi]
    have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
      (A.chart j).isOpen_inter_preimage_symm hz.isOpen
    have hmj : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
      ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hy]⟩
    have hzj : DifferentiableAt ℂ (z ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hτy]; exact (hz.holo j).differentiableAt (hSo.mem_nhds hmj)
    have hev : z ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        (z ∘ (A.chart j).symm) ∘ (A.chart j ∘ (A.chart i).symm) := by
      filter_upwards [hov.mem_nhds hmov] with v hv
      simp only [Function.comp_apply, (A.chart j).left_inv hv.2]
    have hjz : jz A z i y = (jz A z j y).comp (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      unfold jz
      rw [hev.fderiv_eq, fderiv_comp _ hzj hτ, hτy]
    simp only [jdet]
    rw [hjz, A.g_kap i j y hi hj]
    exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

end GlobalTheory.OTY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeightStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → A.IsFrameOn A.kap U (jdet A z) := by
  first | exact @GlobalTheory.OTY.jdet_isFrameOn_kap | exact GlobalTheory.OTY.jdet_isFrameOn_kap | (intros; apply GlobalTheory.OTY.jdet_isFrameOn_kap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelf
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem trace_pi_eq_sum (n : ℕ) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    LinearMap.trace ℂ (Fin n → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

theorem kills_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  intro G _ _ Y hY V _ _ _ ρ h
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, σ, hσ⟩ := hY
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h
  rw [finsum_eq_sum_of_fintype]
  simp only [hst] at h ⊢

  have hinv : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne')
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  have h' : ∑ g : G, σ.character g⁻¹ * ρ.character g = 0 := h
  rw [h', mul_zero] at hfr
  have hbot : (Representation.linHom σ ρ).invariants = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm

  have hsum : ∀ f : (Fin n → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom σ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom σ ρ g f ∈ (Representation.linHom σ ρ).invariants := by
      intro h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin n, ∑ g : G, (σ g⁻¹ (Pi.single i 1)) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin n → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum ((LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [Representation.character, trace_pi_eq_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelfStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  first | (exact @GlobalTheory.Shin.kills_self) | (exact GlobalTheory.Shin.kills_self) | (intros; apply GlobalTheory.Shin.kills_self  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHom
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Pre

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]

def preToPair : AffOp X ⥤ (Pair φ)ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ prePair φ U) fun _ _ h ↦
    (show prePair φ _ ≤ prePair φ _ from ⟨preU_mono φ h, h⟩)).op

def pairToPre (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPair φ s') (OPre φ s') where
  G := preToPair φ
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def preToPairRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPre φ s') (OPair φ s') where
  G := pairSnd φ
  α p := (Sec.res s' p.unop.2 : Sec s' (preU φ p.unop.1.2).1 →ₐ[R'] Sec s' p.unop.1.1.1).toRingHom
  naturality {p q} a b := by
    exact (Sec.res_res s' (U := (preU φ p.unop.1.2).1) _ _ b).symm.trans (Sec.res_res s' _ _ b)
  smul p r b := map_smul (Sec.res s' p.unop.2) r b

end Pre

section Lemmas

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {φ : X' ⟶ X} [IsAffineHom φ]
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}

theorem pairToPre_pull1_pairRes (x : HO1 s') :
    (pairToPre φ s').pull1 ((pairRes φ s').pull1 x) = (preRes φ s').pull1 x := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s') _ b) x

theorem pairToPre_pull2_pairRes (x : HO2 s') :
    (pairToPre φ s').pull2 ((pairRes φ s').pull2 x) = (preRes φ s').pull2 x := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s') _ b) x

def preIncl : pairSnd φ ⋙ preAff φ ⟶ pairFst φ where
  app p := (homOfLE p.unop.2).op

theorem preToPairRes_pull1_preRes (x : HO1 s') :
    (preToPairRes φ s').pull1 ((preRes φ s').pull1 x) = (pairRes φ s').pull1 x := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ preIncl (fun _ _ ↦ rfl) x

theorem preToPairRes_pull2_preRes (x : HO2 s') :
    (preToPairRes φ s').pull2 ((preRes φ s').pull2 x) = (pairRes φ s').pull2 x := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ preIncl (fun _ _ ↦ rfl) x

variable (h : φ ≫ s = s' ≫ spMap σ)

theorem pairToPre_pull1_pairPull (y : HO1 s) :
    (pairToPre φ s').pull1 ((pairPull h).pull1 y) = (preCoef h).pull1 y := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ congrArg _ (mp_id (OAff s) _ b)) y

theorem pairToPre_pull2_pairPull (y : HO2 s) :
    (pairToPre φ s').pull2 ((pairPull h).pull2 y) = (preCoef h).pull2 y := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ congrArg _ (mp_id (OAff s) _ b)) y

theorem preToPairRes_preα (q : (Pair φ)ᵒᵖ) (b : (OAff s).obj ((pairSnd φ).obj q)) :
    (preToPairRes φ s').α q (preα φ s s' ((pairSnd φ).obj q) b) = (pairPull h).α q b :=
  congrArg (fun t ↦ t.hom b) (φ.appLE_map _ (homOfLE q.unop.2).op)

end Lemmas

theorem red_iff_pre : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by
  intro R R' _ _ X X' s s' σ φ h _
  refine ⟨fun f x ↦ ⟨?_, ?_⟩, fun v z ↦ ⟨?_, ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackOneCocycle c, fun U V a ↦ hc _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyOne_class, hx, pairToPre_pull1_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackOneCocycle c, fun p q a ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc]
      exact preToPairRes_preα h q _
    · rw [← CoefMap.pullCohomologyOne_class, hx, preToPairRes_pull1_preRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackTwoCocycle c, fun U V W a b ↦ hc _ _ _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyTwo_class, hx, pairToPre_pull2_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackTwoCocycle c, fun p q r a b ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc]
      exact preToPairRes_preα h r _
    · rw [← CoefMap.pullCohomologyTwo_class, hx, preToPairRes_pull2_preRes]
  · have e := congrArg (pairToPre φ s').pull1 (isPullO_pullHO1 h y)
    rw [pairToPre_pull1_pairPull, pairToPre_pull1_pairRes] at e
    exact e.symm
  · have e : (pairRes φ s').pull2 (pullHO2 h y) = (pairPull h).pull2 y :=
      (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).apply_symm_apply _
    have e' := congrArg (pairToPre φ s').pull2 e
    rw [pairToPre_pull2_pairPull, pairToPre_pull2_pairRes] at e'
    exact e'

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocyclePullback_iff_preimage_affineHom : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by
  first | exact @GlobalTheory.AbCoh.red_iff_pre | exact GlobalTheory.AbCoh.red_iff_pre | (intros; apply GlobalTheory.AbCoh.red_iff_pre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverBaseChangeComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pull_over_baseChange_comm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A Y : Over (Sp R)) (A' Y' : Over (Sp R')) (f : Y ⟶ A) (f' : Y' ⟶ A') (φ : A'.left ⟶ A.left) (ψ : Y'.left ⟶ Y.left) (hA : φ ≫ A.hom = A'.hom ≫ spMap σ) (hY : ψ ≫ Y.hom = Y'.hom ≫ spMap σ), f'.left ≫ φ = ψ ≫ f.left → (∀ x, pullHO1 hY (pO1 f x) = pO1 f' (pullHO1 hA x)) ∧ ∀ x, pullHO2 hY (structureSheafH2Pullback f x) = structureSheafH2Pullback f' (pullHO2 hA x) := by
  intro R R' _ _ σ A Y A' Y' f f' φ ψ hA hY hcomm
  have hχ : (ψ ≫ f.left) ≫ A.hom = Y'.hom ≫ spMap σ := by
    rw [Category.assoc, Over.w f, hY]
  have H := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
  · have e1 := (H R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) R'
      Y'.left Y'.hom σ ψ hY σ (ψ ≫ f.left) hχ rfl (fun _ ↦ rfl)).1 x
    have e2 := (H R R' A.left A'.left A.hom A'.hom σ φ hA R' Y'.left Y'.hom
      (RingHom.id R') f'.left (ovw f') σ (ψ ≫ f.left) hχ hcomm.symm (fun _ ↦ rfl)).1 x
    simp only [pO1]
    rw [e1, e2]
  · have e1 := (H R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) R'
      Y'.left Y'.hom σ ψ hY σ (ψ ≫ f.left) hχ rfl (fun _ ↦ rfl)).2.1 x
    have e2 := (H R R' A.left A'.left A.hom A'.hom σ φ hA R' Y'.left Y'.hom
      (RingHom.id R') f'.left (ovw f') σ (ψ ≫ f.left) hχ hcomm.symm (fun _ ↦ rfl)).2.1 x
    simp only [structureSheafH2Pullback]
    rw [e1, e2]

end GlobalTheory.AbCoh
end

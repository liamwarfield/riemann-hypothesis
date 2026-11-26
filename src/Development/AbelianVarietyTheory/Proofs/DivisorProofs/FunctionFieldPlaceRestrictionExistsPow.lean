module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PlaceResiduePowerBound

open WithZero

variable {F : Type} [Field F]

theorem pow_inj {e : ℕ} (he : e ≠ 0) {a b : ℤᵐ⁰} (h : a ^ e = b ^ e) : a = b :=
  le_antisymm ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.le)
    ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.ge)

theorem pow_le_one_iff' {e : ℕ} (he : e ≠ 0) {a : ℤᵐ⁰} : a ^ e ≤ 1 ↔ a ≤ 1 := by
  simpa using (pow_le_pow_iff_left₀ (zero_le' (a := a)) (zero_le' (a := (1 : ℤᵐ⁰))) he)

theorem pow_of_iff (v q : Valuation F ℤᵐ⁰) (hq : Function.Surjective q)
    (h : ∀ x, v x ≤ 1 ↔ q x ≤ 1) : ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  obtain ⟨π, hπ⟩ := hq (exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hvπ0 : v π ≠ 0 := (Valuation.ne_zero_iff v).2 hπ0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, v π = exp b := ⟨log (v π), (exp_log hvπ0).symm⟩
  have hb0 : b < 0 := by
    have h1 : v π ≤ 1 := (h π).2 (by rw [hπ, ← exp_zero, exp_le_exp]; norm_num)
    have h2 : v π ≠ 1 := by
      intro h1'
      have : q π⁻¹ ≤ 1 := (h _).1 (by rw [map_inv₀, h1', inv_one])
      rw [map_inv₀, hπ, ← exp_neg, ← exp_zero, exp_le_exp] at this
      norm_num at this
    rw [hb, ← exp_zero, exp_le_exp] at h1
    rw [hb, ne_eq, exp_eq_one] at h2
    omega
  have hbe : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
  refine ⟨(-b).toNat, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero, zero_pow (by omega)]
  have hqx : q x ≠ 0 := (Valuation.ne_zero_iff q).2 hx
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
  obtain ⟨c, hc⟩ : ∃ c : ℤ, q x = exp c := ⟨log (q x), (exp_log hqx).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a := ⟨log (v x), (exp_log hvx).symm⟩
  have hqu : q (x * π ^ c) = 1 := by
    rw [map_mul, map_zpow₀, hc, hπ, ← exp_zsmul, ← exp_add, exp_eq_one, smul_eq_mul]; ring
  have hvu : v (x * π ^ c) = exp (a + c * b) := by
    rw [map_mul, map_zpow₀, ha, hb, ← exp_zsmul, ← exp_add, smul_eq_mul]
  have h1 : v (x * π ^ c) ≤ 1 := (h _).2 hqu.le
  have h2 : v (x * π ^ c)⁻¹ ≤ 1 := (h _).2 (by rw [map_inv₀, hqu, inv_one])
  rw [hvu, ← exp_zero, exp_le_exp] at h1
  rw [map_inv₀, hvu, ← exp_neg, ← exp_zero, exp_le_exp] at h2
  have h3 : a + c * b = 0 := by omega
  rw [ha, hc, ← exp_nsmul, exp_inj, nsmul_eq_mul, hbe]
  linear_combination h3

theorem root (v : Valuation F ℤᵐ⁰) (hv : ∃ a, 1 < v a) :
    ∃ q : Valuation F ℤᵐ⁰, Function.Surjective q ∧ ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  classical
  have hS : ∃ n : ℕ, 0 < n ∧ ∃ x, v x = exp (n : ℤ) := by
    obtain ⟨a, ha⟩ := hv
    have ha0 : v a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
    obtain ⟨b, hb⟩ : ∃ b : ℤ, v a = exp b := ⟨_, (exp_log ha0).symm⟩
    rw [hb, ← exp_zero, exp_lt_exp] at ha
    exact ⟨b.toNat, by omega, a, by rw [hb, Int.toNat_of_nonneg ha.le]⟩
  have he0 : 0 < Nat.find hS := (Nat.find_spec hS).1
  obtain ⟨π, hπ⟩ := (Nat.find_spec hS).2
  have hdvd : ∀ x, x ≠ 0 → ∃ m : ℤ, v x = exp ((Nat.find hS : ℤ) * m) := by
    intro x hx
    obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a :=
      ⟨_, (exp_log ((Valuation.ne_zero_iff v).2 hx)).symm⟩
    refine ⟨a / (Nat.find hS : ℤ), ?_⟩
    have hr0 : 0 ≤ a % (Nat.find hS : ℤ) := Int.emod_nonneg _ (by omega)
    have hr1 : a % (Nat.find hS : ℤ) < Nat.find hS := Int.emod_lt_of_pos _ (by omega)
    have hdec := Int.mul_ediv_add_emod a (Nat.find hS : ℤ)
    by_contra hne
    have hr : 0 < a % (Nat.find hS : ℤ) := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; rw [ha, exp_inj]; linear_combination -hdec - h
    have hval : v (x * π ^ (-(a / (Nat.find hS : ℤ)))) = exp (((a % (Nat.find hS : ℤ)).toNat : ℕ) : ℤ) := by
      rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, Int.toNat_of_nonneg hr0, exp_inj,
        smul_eq_mul]
      linear_combination -hdec
    exact Nat.find_min hS (show (a % (Nat.find hS : ℤ)).toNat < Nat.find hS by omega)
      ⟨by omega, _, hval⟩
  have hroot : ∀ x, ∃ c : ℤᵐ⁰, c ^ Nat.find hS = v x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero, zero_pow he0.ne']⟩
    · obtain ⟨m, hm⟩ := hdvd x hx
      exact ⟨exp m, by rw [hm, ← exp_nsmul, nsmul_eq_mul]⟩
  choose qf hqf using hroot
  have hle : ∀ {a b : ℤᵐ⁰}, a ^ Nat.find hS ≤ b ^ Nat.find hS → a ≤ b :=
    fun h => (pow_le_pow_iff_left₀ zero_le' zero_le' he0.ne').1 h
  let q : Valuation F ℤᵐ⁰ :=
    { toFun := qf
      map_zero' := pow_inj he0.ne' (by rw [hqf, map_zero, zero_pow he0.ne'])
      map_one' := pow_inj he0.ne' (by rw [hqf, map_one, one_pow])
      map_mul' := fun x y => pow_inj he0.ne' (by rw [hqf, mul_pow, hqf, hqf, map_mul])
      map_add_le_max' := fun x y => by
        have h := v.map_add x y
        rw [← hqf x, ← hqf y, ← hqf (x + y)] at h
        rcases le_max_iff.1 h with h | h
        · exact le_max_of_le_left (hle h)
        · exact le_max_of_le_right (hle h) }
  have hqq : ∀ x, q x = qf x := fun _ => rfl
  refine ⟨q, ?_, Nat.find hS, he0, fun x => by rw [hqq, hqf]⟩
  have hqπ : q π = exp 1 :=
    pow_inj he0.ne' (by rw [hqq, hqf, hπ, ← exp_nsmul, nsmul_eq_mul, mul_one])
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨0, map_zero q⟩
  · refine ⟨π ^ log t, ?_⟩
    rw [map_zpow₀, hqπ, ← exp_zsmul, smul_eq_mul, mul_one, exp_log ht]

theorem exists_one_lt {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : Valuation E ℤᵐ⁰) (hp : Function.Surjective p) : ∃ a : F, 1 < p (algebraMap F E a) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hp (exp (1 : ℤ))
  have hy1 : 1 < p y := by rw [hy, ← exp_zero, exp_lt_exp]; norm_num
  obtain ⟨f, hfm, hfy⟩ := Algebra.IsIntegral.isIntegral (R := F) y
  rw [hfm.as_sum] at hfy
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hfy
  have hlt : p (∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i) <
      p y ^ f.natDegree := by
    apply p.map_sum_lt (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy1)))
    intro i hi
    rw [map_mul, map_pow]
    calc p (algebraMap F E (f.coeff i)) * p y ^ i ≤ 1 * p y ^ i := mul_le_mul_of_nonneg_right (hcon _) zero_le'
      _ = p y ^ i := one_mul _
      _ < p y ^ f.natDegree := pow_lt_pow_right₀ hy1 (Finset.mem_range.1 hi)
  have hs : ∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i =
      -(y ^ f.natDegree) := by linear_combination hfy
  rw [hs, Valuation.map_neg, map_pow] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory.Nef.PlaceResiduePowerBound

namespace GlobalTheory.Nef

open WithZero

theorem place_res_exists_pow : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E],
    (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p,
      ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧
        ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  intro k F E _ _ _ _ _ _ _ _
  refine ⟨?_, fun ρ hρ p => ?_⟩
  · have hex : ∀ p : Place k E, ∃ q : Place k F,
        ∀ x, p.1 (algebraMap F E x) ≤ 1 ↔ q.1 x ≤ 1 := by
      intro p
      obtain ⟨a, ha⟩ := PlaceResiduePowerBound.exists_one_lt (F := F) p.1 p.2.1
      obtain ⟨q, hq, e, he, hpow⟩ := PlaceResiduePowerBound.root (p.1.comap (algebraMap F E)) ⟨a, ha⟩
      refine ⟨⟨q, hq, fun c hc => ?_⟩, fun x => ?_⟩
      · apply PlaceResiduePowerBound.pow_inj he.ne'
        rw [← hpow, Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, p.2.2 c hc, one_pow]
      · have h := hpow x
        rw [Valuation.comap_apply] at h
        rw [h, PlaceResiduePowerBound.pow_le_one_iff' he.ne']
    choose ρ hρ using hex
    exact ⟨ρ, hρ⟩
  · obtain ⟨e, he, hpow⟩ :=
      PlaceResiduePowerBound.pow_of_iff (p.1.comap (algebraMap F E)) (ρ p).1 (ρ p).2.1 (fun x => hρ p x)
    refine ⟨e, he, fun x => hpow x, fun x => ?_⟩
    have h : p.1 (algebraMap F E x) = (ρ p).1 x ^ e := hpow x
    unfold ord
    rw [h, log_pow, nsmul_eq_mul]
    ring

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPowStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldPlace_restriction_exists_pow : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p, ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧ ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  first | exact @GlobalTheory.Nef.place_res_exists_pow | exact GlobalTheory.Nef.place_res_exists_pow | (intros; apply GlobalTheory.Nef.place_res_exists_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSections
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeHom

variable {R : Type} [CommRing R]

theorem val_eq {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val s U x = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
      (ModuleCat.freeMk (ULift.up x)) := rfl

theorem freePresheaf_map_freeMk (P : PSh) {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (x : P.obj U) :
    (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (P.map g))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

theorem freePresheaf_map_app_freeMk {P P' : PSh} (f : P' ⟶ P) (U : Scheme.{0}ᵒᵖ) (x : P'.obj U) :
    (((freeP R).map f).app U).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (f.app U x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (f.app U))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

theorem ext {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (h : ∀ U x, val s U x = val s' U x) : s = s' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have hx := h U.unop x
  rw [val_eq, val_eq] at hx
  exact hx

def descP (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun x => φ U.unop x.down)
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    rintro ⟨x⟩
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x))) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)))
    rw [freePresheaf_map_freeMk]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact hφ V.unop U.unop g.unop x

def desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (free R).obj P ⟶ G :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm (descP P G φ hφ)

theorem val_desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x))
    (U : Scheme.{0}) (x : P.obj (op U)) : val (desc P G φ hφ) U x = φ U x := by
  rw [val_eq]
  have key : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ (desc P G φ hφ).hom = descP P G φ hφ := by
    have hs := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
      (descP P G φ hφ)
    rw [Adjunction.homEquiv_unit] at hs
    exact hs
  rw [key]
  change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)) = _
  erw [ModuleCat.freeDesc_apply]
  rfl

private theorem val_nat_lemma {P : PSh} {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (η : (freeP R).obj P ⟶ F)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x))) =
      (F.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) :=
  calc (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x)))
      = (η.app (op V)).hom ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x))) :=
        congrArg (η.app (op V)).hom (freePresheaf_map_freeMk P g.op x).symm
    _ = _ := congrArg (fun k => k.hom (ModuleCat.freeMk (ULift.up x))) (η.naturality g.op)

theorem val_nat {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)) :
    val s V (P.map g.op x) = Sec.res g (val s U x) := by
  rw [val_eq, val_eq]
  exact val_nat_lemma _ g x

theorem val_free_map {P P' : PSh} (f : P' ⟶ P) {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P'.obj (op U)) :
    val ((free R).map f ≫ s) U x = val s U (f.app (op U) x) := by
  rw [val_eq, val_eq]
  have hn : toSheafify Scheme.etaleTopology ((freeP R).obj P') ≫ ((free R).map f ≫ s).hom
      = (freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom :=
    (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map f) s.hom).symm
  rw [hn]
  change ((toSheafify _ _ ≫ s.hom).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) = _
  rw [freePresheaf_map_app_freeMk]

theorem val_comp {P : PSh} {G G' : Shv R} (s : (free R).obj P ⟶ G) (ψ : G ⟶ G') (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s ≫ ψ) U x = Sec.map ψ (val s U x) := rfl

theorem val_add {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s + s') U x = val s U x + val s' U x := rfl

def valHom (P : PSh) (G : Shv R) (U : Scheme.{0}) (x : P.obj (op U)) : ((free R).obj P ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun s => val s U x) (fun s s' => val_add s s' U x)

theorem val_zsmul {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (m : ℤ) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (m • s) U x = m • val s U x := by
  exact map_zsmul (valHom P G U x) m s

theorem main : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧ (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) → ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧ (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), val s V (P.map g.op x) = Sec.res g (val s U x)) ∧ (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x, val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧ (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x, val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧ ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x, val (s + s') U x = val s U x + val s' U x ∧ val (m • s) U x = m • val s U x := by
  intro R _ P G
  exact ⟨fun s s' h => ext s s' h, fun φ hφ => ⟨desc P G φ hφ, val_desc P G φ hφ⟩,
    fun s V U g x => val_nat s V U g x, fun P' f s U x => val_free_map f s U x,
    fun G' ψ s U x => val_comp s ψ U x, fun s s' m U x => ⟨val_add s s' U x, val_zsmul s m U x⟩⟩

end GlobalTheory.EtC.FreeHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSectionsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
open GlobalTheory.EtC.FreeHom in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections :
    ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R),
      (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧
      (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U,
        (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)),
          φ V (P.map g.op x) = Sec.res g (φ U x)) →
        ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧
      (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)),
        val s V (P.map g.op x) = Sec.res g (val s U x)) ∧
      (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x,
        val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧
      (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x,
        val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧
      ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x,
        val (s + s') U x = val s U x + val s' U x ∧
        val (m • s) U x = m • val s U x := by
  intro R _ P G
  have evaluate {Q : PSh} {F : Shv R} (s : (free R).obj Q ⟶ F)
      (U : Scheme.{0}) (x : Q.obj (op U)) :
      val s U x =
        ((toSheafify Scheme.etaleTopology ((freeP R).obj Q) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up x)) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s s' h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ G.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨x⟩
    have hx := h U.unop x
    rw [evaluate, evaluate] at hx
    exact hx
  · intro φ hφ
    refine ⟨desc P G φ hφ, ?_⟩
    intro U x
    rw [evaluate]
    have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ (desc P G φ hφ).hom =
        descP P G φ hφ := by
      have h := ((sheafificationAdjunction Scheme.etaleTopology.{0}
        (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply (descP P G φ hφ)
      rw [Adjunction.homEquiv_unit] at h
      exact h
    rw [hdesc]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  · intro s V U g x
    rw [evaluate, evaluate]
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x))) =
      (G.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    rw [← freePresheaf_map_freeMk P g.op x]
    exact congrArg (fun k => k.hom (ModuleCat.freeMk (ULift.up x))) (η.naturality g.op)
  · intro P' f s U x
    rw [evaluate, evaluate]
    have h : toSheafify Scheme.etaleTopology ((freeP R).obj P') ≫ ((free R).map f ≫ s).hom =
        (freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom :=
      (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map f) s.hom).symm
    rw [h]
    change ((toSheafify _ _ ≫ s.hom).app (op U)).hom
      ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) = _
    rw [freePresheaf_map_app_freeMk]
  · intros
    rfl
  · intro s s' m U x
    let evaluation : ((free R).obj P ⟶ G) →+ Sec G U :=
      AddMonoidHom.mk' (fun t => val t U x) (fun _ _ => rfl)
    exact ⟨rfl, map_zsmul evaluation m s⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClasses
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cocycle_comp_assoc_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  intro R _ K L M N a b c ab bc abc h1 h2 h3 h4
  have hA : a + b + c = abc := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨z, rfl⟩ := z.mk_surjective
    rw [cpre_mk, cpre_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [cpre_mk, cpost_mk, cpost_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpost_mk, cpost_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA).symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClassesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  first | (exact @GlobalTheory.cocycle_comp_assoc_classes) | (exact GlobalTheory.cocycle_comp_assoc_classes) | (intros; apply GlobalTheory.cocycle_comp_assoc_classes  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSpecLocalRingConstBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSpecLocalRingConstBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem locallyConstant_spec_local_eq_closedPoint {R A : Type} [CommRing A] [IsLocalRing A]
    (f : LocallyConstant (Spec (CommRingCat.of A)) R) (x : Spec (CommRingCat.of A)) :
    f x = f (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
  have hx : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum A).isPrime.ne_top)
  have ho : IsOpen (f ⁻¹' {f (IsLocalRing.closedPoint A : PrimeSpectrum A)}) := f.isLocallyConstant _
  exact hx.mem_open ho rfl

theorem locallyConstant_spec_local_bijective :
    ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A],
      Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  intro R A _ _
  refine ⟨fun c d h => ?_, fun f => ⟨f (IsLocalRing.closedPoint A : PrimeSpectrum A), ?_⟩⟩
  · have := congrArg (fun g : LocallyConstant (Spec (CommRingCat.of A)) R =>
      g (IsLocalRing.closedPoint A : PrimeSpectrum A)) h
    exact this
  · ext x
    simp only [LocallyConstant.coe_const, Function.const_apply]
    exact (locallyConstant_spec_local_eq_closedPoint f x).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSpecLocalRingConstBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyConstant_spec_localRing_const_bijective : ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A], Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  first | (exact @GlobalTheory.locallyConstant_spec_local_bijective) | (exact GlobalTheory.locallyConstant_spec_local_bijective) | (intros; apply GlobalTheory.locallyConstant_spec_local_bijective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatIffExistsRatFunc
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isRat_iff_exists_ratFunc : ∀ (F : Type) [Field F] (φ : PowerSeries F), IsRat φ ↔
    ∃ ρ : RatFunc F, algebraMap (RatFunc F) (LaurentSeries F) ρ = algebraMap (PowerSeries F) (LaurentSeries F) φ := by
  intro F _ φ
  have key : ∀ P : F[X], algebraMap (RatFunc F) (LaurentSeries F) (algebraMap F[X] (RatFunc F) P) =
      algebraMap (PowerSeries F) (LaurentSeries F) (P : PowerSeries F) := by
    intro P
    exact (RatFunc.coe_coe P).symm
  constructor
  · rintro ⟨p, q, hq, h⟩
    refine ⟨algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q, ?_⟩
    have hq' : algebraMap (PowerSeries F) (LaurentSeries F) (q : PowerSeries F) ≠ 0 := by
      rw [← key]
      exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 hq)
    rw [map_div₀, key, key, div_eq_iff hq', ← h, map_mul, mul_comm]
  · rintro ⟨ρ, h⟩
    refine ⟨ρ.num, ρ.denom, ρ.denom_ne_zero, ?_⟩
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries F) (LaurentSeries F) _ = algebraMap (PowerSeries F) (LaurentSeries F) _
    rw [map_mul, ← key, ← key, ← h, ← map_mul]
    congr 1
    have hd : algebraMap F[X] (RatFunc F) ρ.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 ρ.denom_ne_zero
    have e : ρ = algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom :=
      (RatFunc.num_div_denom ρ).symm
    calc algebraMap F[X] (RatFunc F) ρ.denom * ρ
        = algebraMap F[X] (RatFunc F) ρ.denom *
            (algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom) := congrArg _ e
      _ = algebraMap F[X] (RatFunc F) ρ.num := mul_div_cancel₀ _ hd

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTerms
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cochain_shortExact_of_injective :
    ∀ (R : Type) [CommRing R] (I : _root_.GlobalTheory.EtC.Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (_root_.GlobalTheory.EtC.Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  intro R _ I hI S hS n
  have hp : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).ShortExact :=
    fun p => hS.map_of_exact _
  have hmono : ∀ p : ℤ, Mono (S.f.f p) := fun p => (hp p).mono_f
  have hepi : ∀ p : ℤ, Epi (S.g.f p) := fun p => (hp p).epi_g
  refine ⟨fun a => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · refine ⟨Cochain.mk (fun p q h => Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩
    ext p q h
    simp
  · have hb' : ∀ p q (h : p + n = q), S.f.f p ≫ b.v p q h = 0 := by
      intro p q h
      have := Cochain.congr_v hb p q h
      simpa using this
    refine ⟨Cochain.mk (fun p q h =>
      (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).1), ?_⟩
    refine Cochain.ext _ _ (fun p q h => ?_)
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
    exact (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).2
  · refine Cochain.ext _ _ (fun p q h => ?_)
    have := Cochain.congr_v hc p q h
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at this
    simpa using (cancel_epi (S.g.f p)).mp (this.trans (comp_zero).symm)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTermsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCochain_shortExact_of_injective_terms : ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  first | exact @GlobalTheory.EtC.cochain_shortExact_of_injective | exact GlobalTheory.EtC.cochain_shortExact_of_injective | (intros; apply GlobalTheory.EtC.cochain_shortExact_of_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFreeEtaleMayerVietorisLeftMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFreeEtaleMayerVietorisLeftMap
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.MVLeft

theorem mono_freePresheaf_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((freeP R).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [ModuleCat.mono_iff_injective]
  have hf : Function.Injective (f.app U) := (mono_iff_injective (f.app U)).1 inferInstance
  have hu : Function.Injective (uliftFunctor.{1}.map (f.app U)) := by
    intro a b h; cases a; cases b; exact congrArg ULift.up (hf (congrArg ULift.down h))
  exact Finsupp.mapDomain_injective hu

theorem free_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((free R).map f) := by
  haveI := mono_freePresheaf_map R f
  exact (presheafToSheaf _ _).map_mono ((freeP R).map f)

theorem left_mono : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), Mono (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) := by
  intro R _ A A' _ _ _ f
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))
  haveI : Mono (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))) :=
    yoneda.map_mono _
  haveI := free_mono R (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))
  exact mono_of_mono_fac (biprod.lift_snd _ _)

end GlobalTheory.EtC.MVLeft
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFreeEtaleMayerVietorisLeftMapStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mono_free_etale_mayerVietoris_left_map : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), Mono (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) := by
  first | (exact @GlobalTheory.EtC.MVLeft.left_mono) | (exact GlobalTheory.EtC.MVLeft.left_mono) | (intros; apply GlobalTheory.EtC.MVLeft.left_mono  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHensel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHensel
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


open Polynomial in
theorem prim_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  intro q A _ hSH hq
  obtain ⟨hH, hsep⟩ := hSH
  let k := IsLocalRing.ResidueField A
  have hqk : IsUnit ((q : ℕ) : k) := by
    have := hq.map (IsLocalRing.residue A)
    rwa [map_natCast] at this
  haveI : NeZero ((q : ℕ) : k) := ⟨hqk.ne_zero⟩
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hqk
    · exact h
  have hsepk : (cyclotomic q k).Separable := separable_cyclotomic q k
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (cyclotomic q k)
    (degree_cyclotomic_pos q k hq0).ne' hsepk
  have hmap : (cyclotomic q A).map (algebraMap A k) = cyclotomic q k := map_cyclotomic q _
  have h1 : aeval a₀ (cyclotomic q A) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]; exact ha₀
  have h2 : aeval a₀ (derivative (cyclotomic q A)) ≠ 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, hmap]
    have := hsepk.aeval_derivative_ne_zero (x := a₀) (by simpa [aeval_def] using ha₀)
    simpa [aeval_def] using this
  have hT := (HenselianLocalRing.TFAE A).out 1 2
  obtain ⟨a, ha, -⟩ := hT.mp hH (cyclotomic q A) (cyclotomic.monic q A) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  have : (cyclotomic q ℤ).map (Int.castRingHom A) = cyclotomic q A := map_cyclotomic q _
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, this]
  exact ha

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHenselStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  first | (exact @GlobalTheory.EtC.prim_of_strictlyHenselian) | (exact GlobalTheory.EtC.prim_of_strictlyHenselian) | (intros; apply GlobalTheory.EtC.prim_of_strictlyHenselian  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPow
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_gal (F : Type) [Field F] [Finite F] (t : F ≃+* F) (S : F[X] → ℂ) :
    ∀ (n : ℕ) (x : GL (Fin n) F),
      psiG S n (gal (t : F →+* F) n x) = psiG (fun P => S (P.map (t : F →+* F))) n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n (gal (t : F →+* F) n x), GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n x]
    congr 1
    · simp only [chG, gal]
      congr 1
      rw [← Matrix.charpoly_map]
      rfl
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t a (n - a) n]
      have ha' : a < n := Finset.mem_range.1 ha
      congr 1
      funext y
      exact ih a ha' y

theorem cusp_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F),
    cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  intro F _ _ θ t j ht m k x
  simp only [cusp]
  rw [psiG_gal F t]
  congr 2
  funext P
  exact GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (t : F →+* F) j (fun y => ht y) k P

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F), cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  first | (exact @GlobalTheory.Shin.cusp_gal) | (exact GlobalTheory.Shin.cusp_gal) | (intros; apply GlobalTheory.Shin.cusp_gal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory

open scoped Pointwise

theorem compact_finite_leftCoset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  intro G _ _ _ K hK C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Finset.mem_image] at hr hr'
    obtain ⟨a, -, rfl⟩ := hr
    obtain ⟨b, -, rfl⟩ := hr'
    have h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b) :=
      QuotientGroup.eq.2 hrr'
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro g hg
    have hm := ht hg
    simp only [Set.mem_iUnion] at hm
    obtain ⟨gi, hgi, hmem⟩ := hm
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩
    have h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [smul_eq_mul, mul_assoc] using K.mul_mem h1 hk

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosetsStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_covered_by_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  first | exact @GlobalTheory.compact_finite_leftCoset_reps | exact GlobalTheory.compact_finite_leftCoset_reps | (intros; apply GlobalTheory.compact_finite_leftCoset_reps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem flatS_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  intro R _
  refine ⟨?_, ?_⟩
  · intro M N e ⟨P, φ, hs, hi, hf⟩
    refine ⟨P, φ ≫ e.hom.hom, ?_, ?_, hf⟩
    · intro U y
      obtain ⟨S, hS, hy⟩ := hs U (Sec.map e.inv y)
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hy V g hg
      refine ⟨x, ?_⟩
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [hx]
      have h1 := congrArg ModuleCat.Hom.hom (e.hom.hom.naturality g.op)
      have h2 := congrArg (fun (f : N ⟶ N) => (f.hom.app (op U)).hom y) e.inv_hom_id
      simp only [ModuleCat.hom_comp] at h1
      have h3 := LinearMap.congr_fun h1 ((e.inv.hom.app (op U)).hom y)
      simp only [LinearMap.comp_apply] at h3
      simp only [Sec.res, Sec.map]
      rw [h3]
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      rw [h2]
    · intro U x hx
      apply hi U x
      have h2 := congrArg (fun (f : M ⟶ M) => (f.hom.app (op U)).hom ((φ.app (op U)).hom x)) e.hom_inv_id
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
      rw [← h2, hx, map_zero]
  · intro M hM
    refine ⟨(Functor.const _).obj (ModuleCat.of (ULift.{1} R) PUnit.{2}), 0, ?_, ?_, ?_⟩
    · intro U y
      refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨0, ?_⟩⟩
      have h := congrArg (fun (f : M ⟶ M) => (f.hom.app (op V)).hom (Sec.res g y)) (hM.eq_of_src (𝟙 M) 0)
      simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h
      rw [h]
      simp
    · intro U x _
      exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ => Subsingleton.elim (α := PUnit.{2}) _ _⟩
    · intro U _
      show Module.Flat (ULift.{1} R) PUnit.{2}
      infer_instance

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  first | exact @GlobalTheory.EtC.flatS_iso_and_zero | exact GlobalTheory.EtC.flatS_iso_and_zero | (intros; apply GlobalTheory.EtC.flatS_iso_and_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory

theorem bialgHom_factor_through_split :
    ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  intro O _ A B D _ _ _ _ _ _ j ρ f hρ hf
  have hjinj : Function.Injective j := fun x y h => by
    have := congrArg ρ h; rwa [hρ, hρ] at this
  have hjg : ∀ d, j (ρ (f d)) = f d := fun d => by
    obtain ⟨b, hb⟩ := hf d; rw [← hb, hρ]
  have hmapinj : Function.Injective (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) := by
    have hid : (TensorProduct.map ρ ρ).comp (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      simp [hρ]
    intro x y h
    have := congrArg (TensorProduct.map ρ ρ) h
    simpa [← LinearMap.comp_apply, hid] using this
  let gl : D →ₗ[O] B := ρ ∘ₗ (f : D →ₗ[O] A)
  have hgl : ∀ d, j (gl d) = f d := hjg
  have hcomp : (j : B →ₗ[O] A) ∘ₗ gl = (f : D →ₗ[O] A) := LinearMap.ext hgl
  refine ⟨{ gl with
    counit_comp := ?_
    map_comp_comul := ?_
    map_one' := ?_
    map_mul' := ?_ }, hgl⟩
  · ext d
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← CoalgHomClass.counit_comp_apply j, hgl, CoalgHomClass.counit_comp_apply]
  · ext d
    apply hmapinj
    show TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (TensorProduct.map gl gl (comul d)) =
      TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (comul (gl d))
    rw [CoalgHomClass.map_comp_comul_apply j, hgl, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hcomp,
      CoalgHomClass.map_comp_comul_apply f]
  · apply hjinj
    show j (gl 1) = j 1
    rw [hgl, map_one, map_one]
  · intro x y
    apply hjinj
    show j (gl (x * y)) = j (gl x * gl y)
    rw [hgl, map_mul, map_mul, hgl, hgl]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjectionStatement
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgHom_factor_through_split_injection : ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  first | exact @GlobalTheory.bialgHom_factor_through_split | exact GlobalTheory.bialgHom_factor_through_split | (intros; apply GlobalTheory.bialgHom_factor_through_split <;> assumption)
end
end

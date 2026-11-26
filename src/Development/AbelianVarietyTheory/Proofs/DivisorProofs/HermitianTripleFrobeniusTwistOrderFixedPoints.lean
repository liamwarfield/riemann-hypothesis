module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdIterateTwistedConj
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKResNrmConj

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem coe_frobQ_iterate (r k : ℕ) (b : Qr p r) :
    (((⇑(frobQ p r))^[k] b : Qr p r) : PadicAlgCl p) = (frobK p (LKRes.Q0 p) ^ k) (b : PadicAlgCl p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
    rfl

theorem frobQ_iterate_self (r : ℕ) (hr : 0 < r) (b : Qr p r) : (⇑(frobQ p r))^[r] b = b := by
  refine Subtype.ext ?_
  have hK : FiniteDimensional ℚ_[p] (LKRes.Q0 p) := inferInstance
  rw [coe_frobQ_iterate]
  exact (IsFrobOn.pow_fixes_iff p (LKRes.Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ b.2

theorem sigKQ_iterate_self (r : ℕ) (hr : 0 < r) (y : KQ p K r) : (⇑(sigKQ p K r))^[r] y = y := by
  have ht : ∀ (k : ℕ) (a : K) (b : Qr p r), (⇑(sigKQ p K r))^[k] (inclK p K r a * inclQ p K r b) =
      inclK p K r a * inclQ p K r ((⇑(frobQ p r))^[k] b) := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, sigKQ_apply_inclK, sigKQ_apply_inclQ,
        Function.iterate_succ_apply']
  have key : ∀ z : K ⊗[ℚ_[p]] Qr p r, (⇑(sigKQ p K r))^[r] (z : KQ p K r) = (z : KQ p K r) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact iterate_map_zero (sigKQ p K r) r
    | tmul a b =>
      have e : inclK p K r a * inclQ p K r b = (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) := by
        change (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b) = a ⊗ₜ[ℚ_[p]] b
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have h := ht r a b
      rw [frobQ_iterate_self p r hr, e] at h
      exact h
    | add z w hz hw =>
      exact (iterate_map_add (sigKQ p K r) r (z : KQ p K r) (w : KQ p K r)).trans (congrArg₂ (· + ·) hz hw)
  exact key y

theorem sigRes_iterate_self (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    (⇑(sigRes p K n r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin n), ((⇑(sigRes p K n r))^[k] g).val i j = (⇑(sigKQ p K r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, sigKQ_iterate_self p K r hr]

end GlobalTheory.LKResNrmConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigKQFixedEqInclK
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem frobQ_fixed_mem (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (b : Qr p r) (hb : frobQ p r b = b) :
    ∃ c : ℚ_[p], algebraMap ℚ_[p] (Qr p r) c = b := by
  have h1 : frobK p (Q0 p) (b : PadicAlgCl p) = b := congrArg Subtype.val hb
  have h2 : (b : PadicAlgCl p) ∈ Q0 p := mem_of_frobK_fixed inferInstance (Kn_le_Kur hr b.2) h1
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 h2
  exact ⟨c, Subtype.ext hc⟩

theorem sigKQ_fixed_eq_inclK : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ x : GlobalTheory.LKRes.KQ p K r, GlobalTheory.LKRes.sigKQ p K r x = x → ∃ a : K, GlobalTheory.LKRes.inclK p K r a = x := by
  intro p _ K r hr
  change ∀ x : K ⊗[ℚ_[p]] Qr p r, Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) x = x →
    ∃ a : K, (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] Qr p r) a = x
  intro x hx
  let f : ℚ_[p] →ₗ[ℚ_[p]] Qr p r := Algebra.linearMap _ _
  let g : Qr p r →ₗ[ℚ_[p]] Qr p r := (frobQ p r).toLinearMap - LinearMap.id
  have hex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : frobQ p r b = b := sub_eq_zero.1 hb
      exact frobQ_fixed_mem p r hr b hb'
    · rintro ⟨c, rfl⟩
      simp [g, f]
  have hex2 := Module.Flat.lTensor_exact K hex
  have hg : g.lTensor K =
      (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)).toLinearMap - LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [g, TensorProduct.tmul_sub]
  have hx0 : g.lTensor K x = 0 := by
    rw [hg, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    exact sub_eq_zero.2 hx
  obtain ⟨y, hy⟩ := (hex2 x).1 hx0
  refine ⟨TensorProduct.rid ℚ_[p] K y, ?_⟩
  rw [← hy]
  clear hy hx hx0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, f, Algebra.linearMap_apply]
    change (c • a) ⊗ₜ[ℚ_[p]] (1 : Qr p r) = a ⊗ₜ[ℚ_[p]] (algebraMap ℚ_[p] (Qr p r) c)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add u v hu hv =>
    rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _)]

end GlobalTheory.LKRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem iterate_fst (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    ((⇑(sigG G r))^[k] g).1 = (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem iterate_snd (G : HTGroup p) (r k : ℕ) (g : Gr G r) (i : Fin G.m) :
    ((⇑(sigG G r))^[k] g).2 i = (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem unramifiedExtFrobeniusGL_one_iterate_degree (r : ℕ) (hr : 0 < r) (g : GL (Fin 1) (Qr p r)) :
    (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin 1), ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g).val i j
      = (⇑(frobQ p r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, GlobalTheory.LKResNrmConj.frobQ_iterate_self p r hr]

theorem inclK_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    Function.Injective (inclK p K r) :=
  Algebra.TensorProduct.includeLeft_injective (S := ℚ_[p]) (algebraMap ℚ_[p] (Qr p r)).injective

theorem iterate_self (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [iterate_fst, unramifiedExtFrobeniusGL_one_iterate_degree r hr]
  · rw [iterate_snd, GlobalTheory.LKResNrmConj.sigRes_iterate_self p (G.Fw i) G.n r hr]

theorem fix_incl (G : HTGroup p) (r : ℕ) (γ : Gp G) : sigG G r (inclG G r γ) = inclG G r γ := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change frobQ p r (((inclG G r γ).1 : Matrix (Fin 1) (Fin 1) (Qr p r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe]
    by_cases h : a = b
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h]
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change sigKQ p (G.Fw i) r (((inclG G r γ).2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_snd, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact sigKQ_apply_inclK p (G.Fw i) r _

end GlobalTheory.LKMid.SigIter

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem incl_injective (G : HTGroup p) (r : ℕ) : Function.Injective (inclG G r) := by
  intro γ γ' h
  have h1 := congrArg (fun g : Gr G r => ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) h
  have h2 := fun i (a b : Fin G.n) =>
    congrArg (fun g : Gr G r => ((g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) h
  simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
    MonoidHom.coe_coe, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.diagonal_apply_eq] at h1 h2
  refine Prod.ext (Units.ext ((algebraMap ℚ_[p] (Qr p r)).injective h1)) (funext fun i => ?_)
  exact Units.ext (Matrix.ext fun a b => inclK_injective (G.Fw i) r (h2 i a b))

theorem fixed_mem_range (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) (hg : sigG G r g = g) :
    g ∈ (inclG G r).range := by
  have hf : frobQ p r ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) = (g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 :=
    congrArg (fun x : Gr G r => ((x.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) hg
  obtain ⟨c, hc⟩ := frobQ_fixed_mem p r hr _ hf
  have hdet1 : IsUnit ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) := by
    have := Matrix.isUnits_det_units g.1
    rwa [Matrix.det_fin_one] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_isUnit_zero (hc ▸ hdet1)
  have hfix : ∀ i (a b : Fin G.n), ∃ x : G.Fw i,
      inclK p (G.Fw i) r x = (g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b := fun i a b =>
    sigKQ_fixed_eq_inclK p (G.Fw i) r hr _
      (congrArg (fun x : Gr G r => ((x.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) hg)
  choose M hM using hfix
  have hmap : ∀ i, (Matrix.of (M i)).map (inclK p (G.Fw i) r) = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
    fun i => Matrix.ext fun a b => hM i a b
  have hdet : ∀ i, (Matrix.of (M i)).det ≠ 0 := by
    intro i h0
    have e := RingHom.map_det (inclK p (G.Fw i) r).toRingHom (Matrix.of (M i))
    rw [h0, map_zero, RingHom.mapMatrix_apply] at e
    have e' : (Matrix.of (M i)).map (inclK p (G.Fw i) r).toRingHom = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
      hmap i
    rw [e'] at e
    have hu := Matrix.isUnits_det_units (g.2 i)
    rw [← e] at hu
    have hsub : Subsingleton (KQ p (G.Fw i) r) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
    have := inclK_injective (G.Fw i) r (Subsingleton.elim (inclK p (G.Fw i) r 1) (inclK p (G.Fw i) r 0))
    exact one_ne_zero this
  refine ⟨(Units.mk0 c hc0, fun i => GeneralLinearGroup.mkOfDetNeZero (Matrix.of (M i)) (hdet i)), ?_⟩
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (funext fun i => Units.ext ?_)
  · have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe, Matrix.diagonal_apply_eq, Units.val_mk0]
    exact hc
  · rw [← hmap i]
    rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
    (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧
      Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range :=
  fun _ _ G r hr => ⟨iterate_self G r hr, fix_incl G r, incl_injective G r, fixed_mem_range G r hr⟩

end GlobalTheory.LKMid.SigIter
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPointsStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := by
  first | (exact @GlobalTheory.LKMid.SigIter.main) | (exact GlobalTheory.LKMid.SigIter.main) | (intros; apply GlobalTheory.LKMid.SigIter.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedRootRealSignatureOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem eval_eq_zero_of_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (μ : ℂ) (hx : x ≠ 0)
    (hM : M *ᵥ x = μ • x) (q : Polynomial ℂ) (hq : Polynomial.aeval M q = 0) : q.eval μ = 0 := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) μ x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hM), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector hv (p := q)
  have h2 : Polynomial.aeval (Matrix.toLin' M) q = Matrix.toLin' (Polynomial.aeval M q) := by
    exact Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toAlgHom M q
  rw [h2, hq, map_zero, LinearMap.zero_apply] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right hx

theorem mark_isRoot_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → P.pol.eval₂ v.embedding μ = 0 := by
  intro p _ G P μ ha hm v hv
  obtain ⟨v₀, hv₀, x, hx, hpos⟩ := hm
  have hvv : v = v₀ := by
    unfold HTGroup.a at ha
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 ha
    have e1 := hw ⟨v, hv⟩
    have e2 := hw ⟨v₀, hv₀⟩
    exact congrArg Subtype.val (e1.trans e2.symm)
  subst hvv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hpos
  have hq : Polynomial.aeval (G.psi v (P.γ : G.C)) (P.pol.map v.embedding) = 0 := by
    have h0 : G.psi v (Polynomial.aeval (P.γ : G.C) P.pol) = 0 := by
      rw [Pair.pol, minpoly.aeval, map_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    have e : (algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)).comp v.embedding = (G.psi v).comp (algebraMap G.F G.C) := by
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, G.psi_F, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [e]
    exact h0
  have := eval_eq_zero_of_eigenvector _ x μ hx0 hx _ hq
  rwa [Polynomial.eval_map] at this

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToP
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem den_dvd_of_natCast_mul_eq_int (n : ℕ) (q : ℚ) (a : ℤ) (h : (n : ℚ) * q = a) :
    q.den ∣ n := by
  have h1 : ((n : ℤ) * q.num : ℚ) = (a * q.den : ℤ) := by
    push_cast
    rw [← Rat.mul_den_eq_num q, ← mul_assoc, h]
  have h2 : (n : ℤ) * q.num = a * q.den := by exact_mod_cast h1
  have h3 : (q.den : ℤ) ∣ (n : ℤ) * q.num := ⟨a, by rw [h2]; ring⟩
  have h4 : q.den ∣ n * q.num.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h3
    simpa [Int.natAbs_mul] using this
  exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm q.reduced) h4)

theorem exists_int_of_den_dvd (n : ℕ) (q : ℚ) (h : q.den ∣ n) :
    ∃ a : ℤ, (n : ℚ) * q = a := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨c * q.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num q]
  ring

theorem den_comb : ∀ (p D K k : ℕ), p.Prime → ∀ q : ℚ,
    (∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ K * m : ℕ) : ℚ) * q = a) →
    (∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = a) →
    ∃ a : ℤ, ((D * p ^ K : ℕ) : ℚ) * q = a := by
  intro p D K k _ q ⟨m, hm, a, ha⟩ ⟨b, hb⟩
  have d1 := den_dvd_of_natCast_mul_eq_int _ q a ha
  have d2 := den_dvd_of_natCast_mul_eq_int _ q b hb
  apply exists_int_of_den_dvd
  have e1 : q.den ∣ D * p ^ K * m := by
    have : p ^ K * m ∣ D * p ^ K * m := ⟨D, by ring⟩
    exact d1.trans this
  have e2 : q.den ∣ D * p ^ K * p ^ k := by
    have : D * p ^ k ∣ D * p ^ K * p ^ k := ⟨p ^ K, by ring⟩
    exact d2.trans this
  have e3 := Nat.dvd_gcd e1 e2
  rw [Nat.gcd_mul_left, (Nat.Coprime.pow_right k hm : Nat.Coprime m (p ^ k)), mul_one] at e3
  exact e3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToPStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.den_bound_combine_padic_primeToP : ∀ (p D K k : ℕ), p.Prime → ∀ q : ℚ, (∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ K * m : ℕ) : ℚ) * q = a) → (∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = a) → ∃ a : ℤ, ((D * p ^ K : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.den_comb) | (exact GlobalTheory.den_comb) | (intros; apply GlobalTheory.den_comb  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulInt
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isIntegral_smul_of_charpoly_coeff_mul_int
    (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ)
    (h : ∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) :
    IsIntegral ℤ ((M : ℤ) • x) := by
  set χ := (LinearMap.mulLeft ℚ x).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _

  have hx : Polynomial.aeval x χ = 0 := by
    have h1 : Polynomial.aeval (LinearMap.mulLeft ℚ x) χ = 0 := LinearMap.aeval_self_charpoly _
    have h2 : Polynomial.aeval (Algebra.lmul ℚ A x) χ = Algebra.lmul ℚ A (Polynomial.aeval x χ) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h3 : Algebra.lmul ℚ A x = LinearMap.mulLeft ℚ x := rfl
    rw [h3, h1] at h2
    have := congrArg (fun f : A →ₗ[ℚ] A => f 1) h2
    simpa using this.symm
  have hs : Polynomial.aeval (algebraMap ℚ A (M : ℚ) * x) (χ.scaleRoots (M : ℚ)) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero hx
  have hsmon : (χ.scaleRoots (M : ℚ)).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    rw [Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero,
      mul_one]
    exact hmon
  have hlift : χ.scaleRoots (M : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy n χ.natDegree with hn | hn | hn
    · obtain ⟨a, ha⟩ := h n
      refine ⟨a * (M : ℤ) ^ (χ.natDegree - n - 1), ?_⟩
      have he : χ.natDegree - n = (χ.natDegree - n - 1) + 1 := by omega
      rw [he, pow_succ, map_mul, map_pow, eq_intCast, eq_intCast, ← ha]
      push_cast
      ring
    · subst hn
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by simpa using hmon.coeff_natDegree.symm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, -, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hsmon
  refine ⟨q, hqmon, ?_⟩
  have : Polynomial.aeval ((M : ℤ) • x) q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ, hq]
    convert hs using 2
    rw [Algebra.smul_def]
    simp
  simpa [Polynomial.aeval_def] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulIntStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ), (∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) → IsIntegral ℤ ((M : ℤ) • x) := by
  first | (exact @GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (exact GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (intros; apply GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceOffLevelSetProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open SplitOffPlaces Formalism.L2.Col Formalism.HermitianLatticesTheory in
theorem offS_not_type_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ PP ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) → OffS D S P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
  intro D Pb Pg S P hPg hS hP
  have key : ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP h
    obtain ⟨x, hx, hxP⟩ := hP _ (hS PP h)
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
    refine ⟨fun e => hxP _ rfl (e ▸ hx'), fun hc => ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hx'
    refine hxP c' ?_ h1
    rw [h2]
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h => (key PP h).1
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := by
    intro PP h e
    apply (key PP h).2
    intro c hc
    rw [e] at hc
    exact ⟨cO D.host.E c, hc, rfl⟩
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, key⟩
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdele
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdele
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.AfPCpctDen

theorem natCast_mul_apply {p : ℕ} (n : ℕ) (a : AfP p) (v : AwayP p) :
    (LevelExists.rp ((n : AfP p) * a)).1 v = (n : v.1.adicCompletion ℚ) * (LevelExists.rp a).1 v :=
  rfl

theorem natCast_mem_int (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.mpr hb0, ?_⟩
  rcases Int.natAbs_eq b with h | h
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, mul_comm]
    exact hbx
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = -algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, neg_mul, mul_comm]
    exact neg_mem hbx

theorem exists_nat_adele {p : ℕ} (a : AfP p) :
    ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 ((LevelExists.rp a).1 v)
  have hS : {v : AwayP p | ¬ (LevelExists.rp a).1 v ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (LevelExists.rp a).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [natCast_mul_apply]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem_int w.1 k) (hm w)
  · have hw' : (LevelExists.rp a).1 w ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem_int w.1 _) hw'

theorem exists_den (p : ℕ) (S : Set (AfP p)) (hS : IsCompact S) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' (LevelExists.intAfP p : Set (AfP p)))
    (fun a => (LevelExists.isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := Set.mem_iUnion₂.mp (ht hf)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hfa' : (m a : AfP p) * f ∈ LevelExists.intAfP p := hfa
  rw [hk, Nat.cast_mul, mul_comm ((m a : ℕ) : AfP p), mul_assoc]
  exact mul_mem (natCast_mem _ k) hfa'

theorem main : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p :=
  exists_den

end GlobalTheory.AfPCpctDen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdeleStatement
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  first | (exact @GlobalTheory.AfPCpctDen.main) | (exact GlobalTheory.AfPCpctDen.main) | (intros; apply GlobalTheory.AfPCpctDen.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsi
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem roots_eig : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) (w : ℂ),
    P.pol.eval₂ v.embedding w = 0 → ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  intro p _ G P v w hw
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v P.γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF ((P.γ : G.C) ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) (P.γ : G.C))
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => (1 : ℂ) ⊗ₜ[G.F] ((P.γ : G.C) ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hd : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hpm : P.pol.Monic := minpoly.monic hint
  set Q := P.pol.map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = G.n := by rw [hQ, hpm.natDegree_map]; exact P.reg.1
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF (P.γ : G.C)) P.pol = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [Pair.pol, minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = G.n - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F (P.γ : G.C)).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), hd, ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel G.n_pos]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum ⟨G.n - 1, by rw [hd]; have := G.n_pos; omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsiStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenvector_of_minpoly_root_hermitianPsi : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) (w : ℂ),
    P.pol.eval₂ v.embedding w = 0 → ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  first | (exact @GlobalTheory.LKMid.roots_eig) | (exact GlobalTheory.LKMid.roots_eig) | (intros; apply GlobalTheory.LKMid.roots_eig  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_change_baseFrame_orthonormal : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ u : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (β * intGL D.host.F D.host.E V.rank u).val * V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (β * intGL D.host.F D.host.E V.rank u).val = 1 := by
  first | exact @GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | exact GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | (intros; apply GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.FinIsoExists

theorem exists_isometry {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (σ : A →+* A) {n n' : ℕ} (h : n = n')
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n') (Fin n') A) (β : GL (Fin n) A) (β' : GL (Fin n') A)
    (u : GL (Fin n) R) (u' : GL (Fin n') R)
    (hu : Formalism.UG.cT σ (β * Formalism.UG.bc φ u).val * J * (β * Formalism.UG.bc φ u).val = 1)
    (hu' : Formalism.UG.cT σ (β' * Formalism.UG.bc φ u').val * J' * (β' * Formalism.UG.bc φ u').val = 1) :
    ∃ u₀ : GL (Fin n') R, ∀ y : GL (Fin n') R, β' * Formalism.UG.bc φ y * β'⁻¹ ∈ Formalism.UG.UJ σ J' →
      ∃ (j : Matrix (Fin n') (Fin n) A) (j' : Matrix (Fin n) (Fin n') A), j * j' = 1 ∧ j' * j = 1 ∧
        Formalism.UG.cT σ j * J' * j = J ∧ j * β.val = (β' * Formalism.UG.bc φ (y * u₀)).val.submatrix id (Fin.cast h) := by
  subst h
  refine ⟨u' * u⁻¹, fun y hy => ?_⟩
  set k := β' * Formalism.UG.bc φ y * β'⁻¹ with hk
  set B := β * Formalism.UG.bc φ u with hB
  set B' := β' * Formalism.UG.bc φ u' with hB'
  have hy' : Formalism.UG.cT σ k.val * J' * k.val = J' := hy
  refine ⟨(k * B' * B⁻¹).val, (k * B' * B⁻¹)⁻¹.val, Units.mul_inv _, Units.inv_mul _, ?_, ?_⟩
  · calc Formalism.UG.cT σ (k * B' * B⁻¹).val * J' * (k * B' * B⁻¹).val
        = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B'.val * (Formalism.UG.cT σ k.val * J' * k.val) * B'.val) * B⁻¹.val := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B.val * J * B.val) * B⁻¹.val := by rw [hy', hu, hu']
      _ = Formalism.UG.cT σ (B.val * B⁻¹.val) * J * (B.val * B⁻¹.val) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · have e : k * B' * B⁻¹ * β = β' * Formalism.UG.bc φ (y * (u' * u⁻¹)) := by
      rw [hk, hB, hB', map_mul, map_mul, map_inv]
      group
    rw [← Units.val_mul, e]
    rfl

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := by
    rw [mem_blockTri]
    intro i j hij
    simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr hg]
  rfl

theorem exists_isFinIso : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)), V.rank = V'.rank → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Lev.IsConjPl PP PP') → ∃ j Φ, IsFinIso V V' β β' Pg j Φ := by
  intro D V V' β Λ N β' Λ' N' Pg h hβ hβ' hPg
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V β Λ N hβ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V' β' Λ' N' hβ'
  obtain ⟨u₀, hu₀⟩ := exists_isometry (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h _ _ β β' u u' hu hu'
  have hL := GlobalTheory.T.finite_group_lifts_to_parahoric_level V' β' (datW V'.rank Pg (LevelP.triv Pg V'.rank ℂ) Frm.B) Λ' N' hβ' rfl hPg
  obtain ⟨κ, -, hκ, hred⟩ := hL (fun PP => (Formalism.UG.bc (resS D.host.F PP.1) u₀)⁻¹)
  obtain ⟨y, hy⟩ := parLev_St hκ
  have hU : β' * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype y * β'⁻¹ ∈
      UA D.sp.cm V'.gram := by
    have h1 := parLev_UA hκ
    rw [← hy] at h1
    exact h1
  obtain ⟨j, j', h1, h2, h3, h4⟩ := hu₀ y hU
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso V V' j j' h1 h2 h3
  refine ⟨j, Φ, h3, hΦ, h, y * u₀, h4, fun PP hPP => ?_⟩
  have h5 : upperLeftBlock le_rfl (redFn β' PP (finE V' κ)) = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ := congrFun hred ⟨PP, hPP⟩
  have h6 : redFn β' PP (finE V' κ) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (redFn β' PP) hy).symm.trans (redFn_frGL β' PP y)
  have h7 : Formalism.UG.bc (resS D.host.F PP) y = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ :=
    h6.symm.trans ((restrictedBlock_self_apply _ _).symm.trans h5)
  exact (map_mul _ y u₀).trans (mul_eq_one_iff_eq_inv.2 h7)

end GlobalTheory.FinIsoExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_isometry_matching_frames : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)), V.rank = V'.rank → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Lev.IsConjPl PP PP') → ∃ j Φ, IsFinIso V V' β β' Pg j Φ := by
  first | exact @GlobalTheory.FinIsoExists.exists_isFinIso | exact GlobalTheory.FinIsoExists.exists_isFinIso | (intros; apply GlobalTheory.FinIsoExists.exists_isFinIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitIdempotentConjugation
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_ne (G : HTGroup p) : ∃ x ∈ G.Kq, IsCMField.complexConj G.F x ≠ x := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  obtain ⟨x, hx, him⟩ := G.hKq.2 v.embedding
  refine ⟨x, hx, fun h => him ?_⟩
  have h2 := IsCMField.complexEmbedding_complexConj G.F v.embedding x
  rw [h] at h2
  have := congrArg Complex.im h2
  simp only [Complex.conj_im] at this
  linarith

end GlobalTheory.CentAtP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjLToLiftReal
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftResInj

theorem resInjL_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.models_inf → RecTie.ResInjL (RecTie.toLiftReal R F tupT hm hTop hinj) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hθ i w hw h0
  let U : MMap (R.MW i (sg0 D A)) := PiTensorProduct.lift.symm w
  have hU : U ∈ Mult.Mult R.θ (R.MW i (sg0 D A)) _ _ := (Mult.mem_multT _ _ _ _ w).1 hw
  have hT : U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
      have e := LinearMap.congr_fun h0 (PiTensorProduct.tprod ℂ v)
      have e2 : w (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
      rw [PiTensorProduct.map_tprod] at e2
      show (PiTensorProduct.lift.symm w : MMap (R.MW i (sg0 D A))) (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0
      exact e2)
  have e3 : PiTensorProduct.lift U = w := LinearEquiv.apply_symm_apply _ w
  rw [← e3, hT]
  exact map_zero _

end GlobalTheory.LiftResInj

end
end

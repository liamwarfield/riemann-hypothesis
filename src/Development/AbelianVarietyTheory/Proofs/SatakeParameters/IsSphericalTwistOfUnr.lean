module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CrysTwistBack

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {a : ℕ}

theorem isCrysAt_of_tw {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
    [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ)
    (r : ↥Gw →* GL (Fin a) (Om l)) (h : IsCrysAt P Bw (UpperTheory.V.Af.tw r c))
    (hc : IsCrysAt P Bw (GlobalTheory.TripleGal.rk1 c)) : IsCrysAt P Bw r := by
  obtain ⟨L₁, r₁, m₁, hr₁⟩ := h
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  have hp := (local_ext P Bw l₁ r₁).1.2 hr₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    simp [GlobalTheory.TripleGal.rk1]
  have hM : IsModel Bw r L (UpperTheory.V.Af.tw r₁' d⁻¹) := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        ((UpperTheory.V.Af.tw r c g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((UpperTheory.V.Af.tw r₁' d⁻¹ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul, map_mul, e, UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀,
      show algebraMap ↥L.1 (Om l) (d g : ↥L.1) = (c g : Om l) from hcd g, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  refine ⟨L, _, hM, ?_⟩
  let θ : ↥(GK Bw.Kw) →* (↥L.1)ˣ := d.comp Bw.e.symm.toMonoidHom
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T Bw.Kw L (Bw.repE L (UpperTheory.V.Af.tw r₁' d⁻¹)) (Bw.repE L r₁') θ
    (fun g x => ?_) ?_).2 hp
  · rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul]
    change _ = ((d (Bw.e.symm g) : ↥L.1) * ((d⁻¹ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)) • _
    rw [MonoidHom.inv_apply, Units.mul_inv, one_smul]
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) hq
    change (Bw.repE L c₂' g x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm g))

end GlobalTheory.CrysTwistBack

namespace GlobalTheory.CrysTwistBack

theorem isSpherical_twist_of_unr {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (κ : HChar E) (hκ : κ.UnrAt w)
    (h : GlobalTheory.SmGL.IsSpherical σ.ρ) :
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a κ w) (CuspSub.isOpen_ker_locDet κ w)).ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have hg : g.1 ∈ GlobalTheory.LFun.KGL w (n := a) := hK ▸ g.2
  have h1 : CuspSub.locDet a κ w g.1 = 1 := hκ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)
  have h3 := hv g
  show ((CuspSub.locDet a κ w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

theorem holds_good_crys : AutomorphicFormsFiniteGL → HeckeLAdicCharacterAbove → Holds .csd .crys → Holds .good .crys := by
  intro hF hA hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw
  intro P AI hT A hAw O _ _ _ Bw hj σ hσ hsph
  obtain ⟨κ, m, hκ, hκu, hcs⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hch⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hch l ι κ m (fun k _ => hκ k)
  have hw' : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ hr.1 hμc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have h1 := hC E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hcs (UpperTheory.V.Af.tw r μ) hw' w hw P AI hT A hAw O Bw hj _
    (hσ.twist κ) (isSpherical_twist_of_unr a w σ κ hκu hsph)
  have h2 := (hA E Ω l P AI hT ι art hart κ m μ (fun k _ => hκ k) hμc hμ w A hAw O Bw hj).2.2.1 hκu
  obtain ⟨T⟩ := hT
  exact isCrysAt_of_tw T Bw (μ.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype) h1 h2

end GlobalTheory.CrysTwistBack

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CsdScopeOfLift
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.CsdLift

theorem val_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).val w = 1 := by
  rfl

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

theorem compNorm_quadChar_pow (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) :
    compNorm E (quadChar E ^ a) = 1 := by
  rw [map_pow, compNorm_quadChar, one_pow]

end GlobalTheory.CsdLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut.SsTwist

open Polynomial

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {c : ℂ} (hc : c ≠ 0) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  generalize LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f = M
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (x.charPol g).scaleRoots (ξ g : ℂ) := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, charpoly_smul_end _ (Units.ne_zero _)]

theorem scaleRoots_cancel {p q : ℂ[X]} {c : ℂ} (hc : c ≠ 0) (H : p.scaleRoots c = q.scaleRoots c) : p = q := by
  have := congrArg (fun P : ℂ[X] => P.scaleRoots c⁻¹) H
  simpa only [← scaleRoots_mul, mul_inv_cancel₀ hc, scaleRoots_one] using this

end GlobalTheory.GalCut.SsTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibFiniteAndSep
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibFin

variable (k : Type) [Field k] {F : Type} (K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} (x : Fin (d + 1) → F)

abbrev coordIdeal : Ideal (rB k K x {0}) :=
  Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))

def incl : rA k x {0} →ₐ[k] rB k K x {0} where
  toFun a := ⟨algebraMap F K a, (integralClosure (rA k x {0}) K).algebraMap_mem a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' r := by ext; simp [← IsScalarTower.algebraMap_apply]

theorem coe_incl (a : rA k x {0}) : (incl k K x a : K) = algebraMap F K a := rfl

theorem mk_incl (hpd : IsPd k x) : ∃ ε : rA k x {0} →ₐ[k] k,
    (Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x) = (Algebra.ofId k _).comp ε := by
  obtain ⟨e, he⟩ := GlobalTheory.PD.rA_single_polyEquiv k F d x hpd 0
  refine ⟨(MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom, ?_⟩
  have key : ((Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x)).comp e.toAlgHom =
      ((Algebra.ofId k _).comp ((MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom)).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    have h1 : incl k K x (e (MvPolynomial.X j)) = (⟨_, tco_mem k K x j⟩ : rB k K x {0}) := by
      apply Subtype.ext
      rw [coe_incl, he j, Fin.succAbove_zero]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk _ (incl k K x (e (MvPolynomial.X j))) =
      Algebra.ofId k _ (MvPolynomial.aeval (0 : Fin d → k) (e.symm (e (MvPolynomial.X j))))
    rw [h1, AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X, Pi.zero_apply, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
  ext a
  have := congrArg (fun φ : MvPolynomial (Fin d) k →ₐ[k] _ => φ (e.symm a)) key
  simpa using this

theorem finite_quot (h : IsFinCover k K x) : Module.Finite k (rB k K x {0} ⧸ coordIdeal k K x) := by
  haveI := h.smooth 0
  haveI : Algebra.FiniteType k (rB k K x {0} ⧸ coordIdeal k K x) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨ε, hε⟩ := mk_incl k K x h.pd
  have hε' : (algebraMap k (rB k K x {0} ⧸ coordIdeal k K x)).comp ε.toRingHom =
      (Ideal.Quotient.mk (coordIdeal k K x)).comp (incl k K x).toRingHom :=
    RingHom.ext fun a => by simpa using (AlgHom.congr_fun hε a).symm
  have hcomp : (rB k K x {0}).val.toRingHom.comp (incl k K x).toRingHom = algebraMap (rA k x {0}) K :=
    RingHom.ext fun a => rfl
  haveI : Algebra.IsIntegral k (rB k K x {0} ⧸ coordIdeal k K x) := ⟨fun q => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA k x {0}) (b : K) := b.2
    have hq : Polynomial.eval₂ (incl k K x).toRingHom b p = 0 := by
      apply Subtype.ext
      change (rB k K x {0}).val.toRingHom (Polynomial.eval₂ (incl k K x).toRingHom b p) = (0 : K)
      rw [Polynomial.hom_eval₂, hcomp]
      exact hp
    refine ⟨p.map ε.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hε', ← Polynomial.hom_eval₂, hq, map_zero]⟩
  exact Algebra.IsIntegral.finite

theorem fib_finite_and_sep [IsAlgClosed k] (h : IsFinCover k K x)
    (hred : IsReduced (rB k K x {0} ⧸ coordIdeal k K x)) :
    Finite (fib k K x) ∧ ∀ f : rB k K x {0}, (∀ e : fib k K x, e.1 f = 0) → f ∈ coordIdeal k K x := by
  haveI := finite_quot k K x h
  have hker : ∀ e : fib k K x, coordIdeal k K x ≤ RingHom.ker e.1 := fun e => by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact e.2 j
  let L : fib k K x → (rB k K x {0} ⧸ coordIdeal k K x →ₐ[k] k) := fun e =>
    Ideal.Quotient.liftₐ _ e.1 (fun a ha => hker e ha)
  have hL : ∀ e f, L e (Ideal.Quotient.mk _ f) = e.1 f := fun e f => rfl
  refine ⟨Finite.of_injective L fun e₁ e₂ he => Subtype.ext (AlgHom.ext fun f => by rw [← hL, ← hL, he]),
    fun f hf => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsArtinianRing (rB k K x {0} ⧸ coordIdeal k K x) := IsArtinianRing.of_finite k _
  have hmem : Ideal.Quotient.mk (coordIdeal k K x) f ∈ Ideal.jacobson (⊥ : Ideal (rB k K x {0} ⧸ coordIdeal k K x)) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    haveI := hm.isPrime
    haveI : Module.Finite k (_ ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)
    haveI : Algebra.IsIntegral k (_ ⧸ m) := Algebra.IsIntegral.of_finite k _
    have hbij : Function.Bijective (algebraMap k (_ ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
    let ψ := (AlgEquiv.ofBijective (Algebra.ofId k (_ ⧸ m)) hbij).symm
    let χ := (ψ.toAlgHom.comp (Ideal.Quotient.mkₐ k m)).comp (Ideal.Quotient.mkₐ k (coordIdeal k K x))
    have hχ : ∀ j : Fin d, χ ⟨_, tco_mem k K x j⟩ = 0 := fun j => by
      have hz : Ideal.Quotient.mkₐ k (coordIdeal k K x) ⟨_, tco_mem k K x j⟩ = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2
          (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
      simp only [χ, AlgHom.comp_apply, hz, map_zero]
    have h0 : ψ (Ideal.Quotient.mk m (Ideal.Quotient.mk (coordIdeal k K x) f)) = 0 := hf ⟨χ, hχ⟩
    rw [map_eq_zero_iff _ ψ.injective, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := rB k K x {0} ⧸ coordIdeal k K x)
  have hpow : (Ideal.Quotient.mk (coordIdeal k K x) f) ^ n = 0 := by
    have := Ideal.pow_mem_pow hmem n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  exact IsNilpotent.eq_zero ⟨n, hpow⟩

end GlobalTheory.PD.FibFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCotangentBasis
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem exists_basis_mod_sq {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ)
    (hb : letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ]))) :
    ∃ g : Fin d → A, (∀ j, e (g j) = 0) ∧
      (∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  obtain ⟨b⟩ := hb
  have hs : Function.Surjective (algebraMap A ℂ) := fun c => ⟨algebraMap ℂ A c, he c⟩
  have key : ∀ (c : ℂ) (w : Ω[A⁄ℂ]), (1 : ℂ) ⊗ₜ[A] (c • w) = c • ((1 : ℂ) ⊗ₜ[A] w) := by
    intro c w
    rw [← algebraMap_smul A c w, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    exact he c
  let φ : A →ₗ[ℂ] ℂ ⊗[A] Ω[A⁄ℂ] :=
    { toFun := fun a => (1 : ℂ) ⊗ₜ[A] D ℂ A a
      map_add' := fun a b => by rw [map_add (f := _), TensorProduct.tmul_add]
      map_smul' := fun c a => by rw [(D ℂ A).map_smul c a, key]; rfl }
  have hφ : ∀ x : RingHom.ker (algebraMap A ℂ), φ x =
      kerCotangentToTensor ℂ A ℂ ((RingHom.ker (algebraMap A ℂ)).toCotangent x) :=
    fun x => (kerCotangentToTensor_toCotangent ℂ A ℂ x).symm
  have hinj := GlobalTheory.SmoothTangent.kerCotangentToTensor_injective ℂ A ℂ hs
  have hsurj : ∀ v, ∃ x : RingHom.ker (algebraMap A ℂ), φ x = v := by
    intro v
    obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ A ℂ hs v).mp (Subsingleton.elim _ _)
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
    exact ⟨x, (hφ x).trans hy⟩
  have hker : ∀ x : RingHom.ker (algebraMap A ℂ), φ x = 0 → (x : A) ∈ RingHom.ker e ^ 2 := by
    intro x hx
    rw [hφ, ← map_zero (kerCotangentToTensor ℂ A ℂ), hinj.eq_iff, Ideal.toCotangent_eq_zero] at hx
    exact hx
  choose g hg using fun j => hsurj (b j)
  have hmemg : ∀ c : Fin d → ℂ, ∑ j, c j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) := fun c =>
    Ideal.sum_mem _ fun j _ => by rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (g j).2
  have hφg : ∀ c : Fin d → ℂ, φ (∑ j, c j • (g j : A)) = ∑ j, c j • b j := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp only [map_smul, hg]
  refine ⟨fun j => g j, fun j => (g j).2, ?_, ?_⟩
  · intro a ha
    refine ⟨fun j => b.repr (φ a) j, ?_⟩
    have hmem : a - ∑ j, b.repr (φ a) j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) :=
      Ideal.sub_mem _ ha (hmemg _)
    refine hker ⟨_, hmem⟩ ?_
    change φ (a - _) = 0
    rw [map_sub, hφg, b.sum_repr, sub_self]
  · intro c hc
    have h0 : φ (∑ j, c j • (g j : A)) = 0 := by
      have h1 := hφ ⟨_, hmemg c⟩
      rw [(Ideal.toCotangent_eq_zero _ _).2 hc, map_zero] at h1
      exact h1
    rw [hφg] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h0 i

end GlobalTheory.CotDim

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem nonempty_basis_fibre {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ) (t : A) (ht : e t ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away t)] :
    letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ])) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  let et : Localization.Away t →+* ℂ := IsLocalization.Away.lift t (isUnit_iff_ne_zero.2 ht)
  letI : Algebra (Localization.Away t) ℂ := et.toAlgebra
  haveI : IsScalarTower A (Localization.Away t) ℂ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq t (isUnit_iff_ne_zero.2 ht) a).symm
  haveI : Nontrivial (Localization.Away t) := et.domain_nontrivial
  haveI : Algebra.FormallyEtale A (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.IsStandardSmooth ℂ (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := ℂ) (S := Localization.Away t) d
  haveI : Module.Finite (Localization.Away t) Ω[Localization.Away t⁄ℂ] := Module.finite_of_rank_eq_nat hr
  let b0 := Module.finBasisOfFinrankEq (Localization.Away t) Ω[Localization.Away t⁄ℂ]
    (Module.finrank_eq_of_rank_eq hr)
  let b1 : Module.Basis (Fin d) ℂ (ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ]) := b0.baseChange ℂ
  let E1 : ℂ ⊗[Localization.Away t] (Localization.Away t ⊗[A] Ω[A⁄ℂ]) ≃ₗ[ℂ]
      ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
      (tensorKaehlerEquivOfFormallyEtale ℂ A (Localization.Away t))
  let E2 := TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) ℂ ℂ Ω[A⁄ℂ]
  exact ⟨(b1.map E1.symm).map E2⟩

end GlobalTheory.CotDim

theorem GlobalTheory.CotDim.exists_cotangent_basis : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (U : X.Opens), IsAffineOpen U → ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
    let e : Sec p U →+* ℂ := CxPts.evHom hy; ∃ g : Fin d → Sec p U, (∀ j, e (g j) = 0) ∧
      (∀ a : Sec p U, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  intro X p d _ U hU y hy e
  have he : ∀ c : ℂ, e (algebraMap ℂ (Sec p U) c) = c := fun c => by
    exact (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hts, ht⟩ : ∃ t : Sec p U, t ∈ s ∧ e t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (↑s : Set Γ(X, U)) ≤ RingHom.ker (e : Γ(X, U) →+* ℂ) :=
      Ideal.span_le.2 fun t ht => hcon t ht
    have h1 : (1 : Γ(X, U)) ∈ RingHom.ker (e : Γ(X, U) →+* ℂ) := hle (by rw [hs]; exact Submodule.mem_top)
    have h2 : e 1 = 0 := h1
    rw [map_one] at h2
    exact one_ne_zero h2
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
    (@h t hts (Localization.Away t) _ (inferInstance : Algebra (Sec p U) (Localization.Away t))
      (by exact (inferInstance : IsLocalization (Submonoid.powers t) (Localization.Away t))))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away (t : Sec p U)) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap,
      IsScalarTower.algebraMap_eq ℂ (Sec p U) (Localization.Away (t : Sec p U))]
    first
      | exact h₁
      | (convert h₁ using 1 <;> rfl)
  exact GlobalTheory.CotDim.exists_basis_mod_sq e he d (GlobalTheory.CotDim.nonempty_basis_fibre e he d t ht)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstOfIsSst
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut.IwaAll

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

theorem isPst_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) {K : FinExt l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsPst P ρ := by
  rw [← GlobalTheory.PstCoeff.isPst_resQ_iff]
  apply GlobalTheory.PMon.isPst_of_isSst_resTo l P AI T K K le_rfl V
  have hD : Dst P (resTo (GlobalTheory.PstCoeff.resQ ρ) (le_refl K.1)) = Dst P (GlobalTheory.PstCoeff.resQ ρ) := by
    ext x
    rw [mem_Dst_resTo, mem_Dst]
    exact ⟨fun H g => H g g.2, fun H g _ => H g⟩
  have := isSst_resQ P ρ h
  rw [IsSst] at this ⊢
  rw [hD]
  exact this

theorem isPstAt_of_isSstAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* GL (Fin a) (Om l)) :
    IsSstAt P Bw r → IsPstAt P Bw r := by
  rintro ⟨LL', r', hm, hs⟩
  obtain ⟨T⟩ := hT
  haveI := LL'.2
  exact ⟨LL', r', hm, isPst_of_isSst P AI T _ hs⟩

end GlobalTheory.GalCut.IwaAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsProjFormNonvanishingGenericPointComplexPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsProjFormNonvanishingGenericPointComplexPoi
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem exists_form_forall_notMem (N n : ℕ) (T : Finset (PSpace ℂ N)) :
    ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n, ∀ x ∈ T, f ∉ x.asHomogeneousIdeal := by
  classical
  let V : T → Submodule ℂ (GlobalTheory.ProjSpace.grading ℂ N 1) := fun x =>
    ((x.1.asHomogeneousIdeal.toIdeal).restrictScalars ℂ).comap (GlobalTheory.ProjSpace.grading ℂ N 1).subtype
  have hV : ∀ x, V x ≠ ⊤ := by
    intro x h
    obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℂ N x.1
    have hX : (⟨MvPolynomial.X i, GlobalTheory.ProjSpace.X_mem ℂ N i⟩ : GlobalTheory.ProjSpace.grading ℂ N 1) ∈ V x :=
      h ▸ Submodule.mem_top
    exact (Proj.mem_basicOpen _ _ _).1 hi hX
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  have hpow : ℓ.1 ^ n ∈ GlobalTheory.ProjSpace.grading ℂ N n := by
    simpa using SetLike.pow_mem_graded n ℓ.2
  refine ⟨ℓ.1 ^ n, hpow, fun x hx hmem => hℓ ⟨x, hx⟩ ?_⟩
  exact x.isPrime.mem_of_pow_mem n hmem

theorem exists_form_genericPoint_cxPts : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ)
    (ι : X ⟶ PSpace ℂ N) (n : ℕ) (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  intro X _ p N ι n F
  classical
  obtain ⟨f, hf, hT⟩ := exists_form_forall_notMem N n
    (insert (ι.base (genericPoint X)) (F.image fun z => ι.base (z.1 (IsLocalRing.closedPoint ℂ))))
  refine ⟨f, hf, hT _ (Finset.mem_insert_self _ _), fun z hz => ?_⟩
  exact CxPts.mem_ptsIn.2 (hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.EtProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsProjFormNonvanishingGenericPointComplexPoiStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projForm_nonvanishing_genericPoint_complexPoints : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N) (n : ℕ)
    (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  first | (exact @GlobalTheory.EtProj.exists_form_genericPoint_cxPts) | (exact GlobalTheory.EtProj.exists_form_genericPoint_cxPts) | (intros; apply GlobalTheory.EtProj.exists_form_genericPoint_cxPts  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusAllOfGood
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GamGalEqOfPlaceIso
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.FunExt GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RSGam.Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'}

theorem wdRel_mk (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : WDRep h V) (b' : WDRep h' V)
    (hN : b.N = b'.N) (hρ : ∀ σ, b'.ρ (c σ) = b.ρ σ) : WDRel φ (WD.mk b) (WD.mk b') := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨_, b.transport e, b'.transport e, WD.sound (b.iso_transport e).symm,
    WD.sound (b'.iso_transport e).symm, ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ b.N = e.conjAlgEquiv ℂ b'.N
    rw [hN]
  · show e.conjAlgEquiv ℂ (b.ρ σ) = e.conjAlgEquiv ℂ (b'.ρ σ')
    rw [← (hcr σ σ').1 hσ, hρ]

theorem wdRel_lpUnr (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    (hdeg : ∀ σ, deg (c σ) = deg σ) (m : Multiset ℂ) :
    WDRel φ (WD.lpUnr (h := h) m) (WD.lpUnr (h := h') m) := by
  classical
  unfold WD.lpUnr
  refine wdRel_mk c hcr _ _ rfl fun σ => ?_
  rw [WDRep.diag_ρ, WDRep.diag_ρ, hdeg]

end GlobalTheory.RSGam.Transport

end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiDescent

theorem wdRel_trivWD {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (a : ℕ) :
    WDRel φ (trivWD h a) (trivWD h' a) := by
  refine ⟨a, WDRep.diag h fun _ : Fin a => 1, WDRep.diag h' fun _ : Fin a => 1, rfl, rfl, ?_, ?_⟩
  · rfl
  · intro σ σ' _
    ext v i
    simp [WDRep.diag, WDRep.ofChars, GlobalTheory.WeilDeligne.unrChar]

theorem charPol_eq {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

end GlobalTheory.RoadU.PhiDescent


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioLinear
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.RatLin

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac MvPolynomial

theorem frac_smul {N : ℕ} (V : (PSpace ℂ N).Opens) (f g : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) (hV : V ≤ Proj.basicOpen (grading ℂ N) g) (c : ℂ)
    (hcf : c • f ∈ grading ℂ N 1) :
    frac (grading ℂ N) V (c • f) g hcf hg hV =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c *
        frac (grading ℂ N) V f g hf hg hV := by
  rw [← algebraMap_sections_eq]
  refine ext fun x hx => ?_
  obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℂ N x
  have hW : V ⊓ chart ℂ N i ≤ V := inf_le_left
  have hxW : x ∈ V ⊓ chart ℂ N i := ⟨hx, hi⟩
  rw [← ev_resG hW x hxW, ← ev_resG hW x hxW, map_mul, resG_algebraMap, resG_frac, resG_frac,
    ← formOn_C (hi := (inf_le_right : V ⊓ chart ℂ N i ≤ chart ℂ N i)), formOn]
  congr 1
  refine (frac_mul_eq ?_).symm
  rw [smul_eq_C_mul]
  ring

theorem app_const {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N) (hι : ι ≫ PSpace.str ℂ N = p)
    (V : (PSpace ℂ N).Opens) (c : ℂ) :
    (ι.app V).hom (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c) =
      algebraMap ℂ (Sec p (ι ⁻¹ᵁ V)) c := by
  subst hι
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (ι ≫ PSpace.str ℂ N).appLE ⊤ (ι ⁻¹ᵁ V) _).hom c
  rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE]
  rfl

theorem fRatio_add {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (f₁ f₂ g : MvPolynomial (Fin (N + 1)) ℂ)
    (h₁ : f₁ ∈ grading ℂ N 1) (h₂ : f₂ ∈ grading ℂ N 1) (h : f₁ + f₂ ∈ grading ℂ N 1)
    (hg : g ∈ grading ℂ N 1) :
    fRatio ι (f₁ + f₂) g h hg = fRatio ι f₁ g h₁ hg + fRatio ι f₂ g h₂ hg := by
  unfold fRatio
  rw [frac_add (ha := h₁) (ha₂ := h₂)]
  exact map_add _ _ _

theorem fRatio_zero {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (g : MvPolynomial (Fin (N + 1)) ℂ)
    (h : (0 : MvPolynomial (Fin (N + 1)) ℂ) ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    fRatio ι 0 g h hg = 0 := by
  unfold fRatio
  rw [frac_zero]
  exact map_zero _

theorem fRatio_smul {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hι : ι ≫ PSpace.str ℂ N = p) (f g : MvPolynomial (Fin (N + 1)) ℂ) (c : ℂ)
    (hf : f ∈ grading ℂ N 1) (h : c • f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    (show Sec p (fOpen ι g) from fRatio ι (c • f) g h hg) = c • (show Sec p (fOpen ι g) from fRatio ι f g hf hg) := by
  have e := app_const p ι hι (Proj.basicOpen (grading ℂ N) g) c
  refine Eq.trans ?_ (Algebra.smul_def (A := Sec p (fOpen ι g)) c _).symm
  refine Eq.trans ?_ (congrArg (· * (show Sec p (fOpen ι g) from fRatio ι f g hf hg)) e)
  unfold fRatio
  rw [frac_smul _ f g hf hg le_rfl c h]
  exact map_mul _ _ _

end GlobalTheory.EtProj.RatLin


open GlobalTheory.EtProj.RatLin in
theorem GlobalTheory.EtProj.fRatio_linear : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), ι ≫ PSpace.str ℂ N = p → ∀ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ GlobalTheory.ProjSpace.grading ℂ N 1) (c : Fin (N + 1) → ℂ) (hf : (∑ l, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1), let U := GlobalTheory.EtProj.fOpen ι g; let q : Sec p U := GlobalTheory.EtProj.fRatio ι (∑ l, c l • MvPolynomial.X l) g hf hg; let r : Fin (N + 1) → Sec p U := fun l => GlobalTheory.EtProj.fRatio ι (MvPolynomial.X l) g (GlobalTheory.ProjSpace.X_mem ℂ N l) hg; q = ∑ l, c l • r l := by
  intro X p N ι hι g hg c hf U q r
  have key : ∀ (s : Finset (Fin (N + 1)))
      (h : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1),
      (show Sec p U from GlobalTheory.EtProj.fRatio ι (∑ l ∈ s, c l • MvPolynomial.X l) g h hg) = ∑ l ∈ s, c l • r l := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact fRatio_zero ι g _ hg
    | insert a s ha ih =>
      intro h
      have hs : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N l)
      have ha' : (c a • MvPolynomial.X a : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N a)
      simp only [Finset.sum_insert ha]
      rw [fRatio_add ι _ _ g ha' hs _ hg, ← ih hs]
      congr 1
      exact fRatio_smul p ι hι _ g (c a) (GlobalTheory.ProjSpace.X_mem ℂ N a) ha' hg
  exact key Finset.univ hf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominator
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominator
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem mem_of_algebraMap_mem_map_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (s : R)
    [IsLocalization.Away s S] {I m : Ideal R} (hm : m.IsMaximal) (hI : m ^ 2 ≤ I) (hs : s ∉ m) {x : R}
    (hx : algebraMap R S x ∈ I.map (algebraMap R S)) : x ∈ I := by
  obtain ⟨⟨y, t⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) S).1 hx
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) S).1 e
  have hw : ((c : R) * t) * x ∈ I := by
    have : (c : R) * y ∈ I := I.mul_mem_left _ y.2
    rw [← hc] at this
    convert this using 1; ring
  have hwm : (c : R) * t ∉ m := by
    obtain ⟨k, hk⟩ := c.2
    obtain ⟨l, hl⟩ := t.2
    rw [← hk, ← hl, ← pow_add]
    exact fun h => hs (hm.isPrime.mem_of_pow_mem _ h)
  obtain ⟨u, i, hi, h1⟩ := hm.exists_inv hwm
  have hi2 : i ^ 2 ∈ I := hI (Ideal.pow_mem_pow hi 2)
  have hx' : x = (u ^ 2 * ((c : R) * t) + 2 * u * i) * (((c : R) * t) * x) + x * i ^ 2 := by
    linear_combination (-x * (u * ((c : R) * t) + i + 1)) * h1
  rw [hx']
  exact I.add_mem (I.mul_mem_left _ hw) (I.mul_mem_left _ hi2)

theorem ker_le_map_ker_away {R S K : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] (s : R)
    [IsLocalization.Away s S] (evR : R →+* K) (evS : S →+* K) (h : ∀ x, evS (algebraMap R S x) = evR x) :
    RingHom.ker evS ≤ (RingHom.ker evR).map (algebraMap R S) := by
  intro w hw
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) w
  dsimp only at hw ⊢
  have hx : evR x = 0 := by
    have := congrArg evS (IsLocalization.mk'_spec S x t)
    rw [map_mul, RingHom.mem_ker.1 hw, zero_mul, h] at this
    exact this.symm
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

theorem span_ratio_of_span_ratio (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N)
    (hι : IsClosedImmersion ι) (n : ℕ) (hn : 0 < n) (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ)
    (a b : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
    (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
    (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
    (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b))
    (h : RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2) :
    RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  haveI := hι
  set 𝒜 := ProjSpace.grading ℂ N
  set D := Proj.basicOpen 𝒜 a ⊓ Proj.basicOpen 𝒜 b with hDdef
  set W : X.Opens := ι ⁻¹ᵁ D with hWdef
  have hWa : W ≤ fOpen ι a := fun x hx => hx.1
  have hWb : W ≤ fOpen ι b := fun x hx => hx.2
  have hzW : z ∈ CxPts.ptsIn p (RingHom.id ℂ) W :=
    CxPts.mem_ptsIn.2 ⟨CxPts.mem_ptsIn.1 hza, CxPts.mem_ptsIn.1 hzb⟩
  have hUa : IsAffineOpen (fOpen ι a) := (Proj.isAffineOpen_basicOpen 𝒜 a ha hn).preimage ι
  have hUb : IsAffineOpen (fOpen ι b) := (Proj.isAffineOpen_basicOpen 𝒜 b hb hn).preimage ι
  have hres : ∀ {c d : MvPolynomial (Fin (N + 1)) ℂ} (hc : c ∈ 𝒜 n) (hd : d ∈ 𝒜 n) (hW : W ≤ fOpen ι d)
      (hD : D ≤ Proj.basicOpen 𝒜 d),
      resG X hW (fRatio ι c d hc hd) = (ι.app D).hom (ProjFrac.frac 𝒜 D c d hc hd hD) := by
    intro c d hc hd hW hD
    have := congrArg (fun φ => φ.hom (ProjFrac.frac 𝒜 _ c d hc hd le_rfl)) (ι.naturality (homOfLE hD).op)
    simp only [CommRingCat.comp_apply] at this
    rw [← ProjFrac.resG_frac hD]
    exact this.symm

  have hratio : ∀ j, resG X hWa (fRatio ι (f j) a (hf j) ha) =
      resG X hWb (fRatio ι (f j) b (hf j) hb) * (ι.app D).hom (ProjFrac.frac 𝒜 D b a hb ha inf_le_left) := by
    intro j
    rw [hres _ _ hWa inf_le_left, hres _ _ hWb inf_le_right, ← map_mul]
    congr 1
    exact (ProjFrac.frac_mul_eq (by ring)).symm

  set sa := fRatio ι b a hb ha
  set sb := fRatio ι a b ha hb
  have eA : W = X.basicOpen sa := by
    rw [show sa = (ι.app _).hom (ProjFrac.frac 𝒜 _ b a hb ha le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
  have eB : W = X.basicOpen sb := by
    rw [show sb = (ι.app _).hom (ProjFrac.frac 𝒜 _ a b ha hb le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
    exact congrArg (fun U => ι ⁻¹ᵁ U) (inf_comm _ _)
  letI algA : Algebra Γ(X, fOpen ι a) Γ(X, W) := (resG X hWa).toAlgebra
  letI algB : Algebra Γ(X, fOpen ι b) Γ(X, W) := (resG X hWb).toAlgebra
  haveI locA : IsLocalization.Away sa Γ(X, W) := hUa.isLocalization_of_eq_basicOpen sa (homOfLE hWa) eA
  haveI locB : IsLocalization.Away sb Γ(X, W) := hUb.isLocalization_of_eq_basicOpen sb (homOfLE hWb) eB
  have evA : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι a) Γ(X, W) g) = CxPts.evHom hza g := fun g => by
    change CxPts.evHom hzW (resG X hWa g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWa hzW g
  have evB : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι b) Γ(X, W) g) = CxPts.evHom hzb g := fun g => by
    change CxPts.evHom hzW (resG X hWb g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWb hzW g
  have h1A := ker_le_map_ker_away sa _ _ evA
  have h1B := ker_le_map_ker_away sb _ _ evB
  have h2A : (RingHom.ker (CxPts.evHom hza)).map (algebraMap Γ(X, fOpen ι a) Γ(X, W)) ≤ RingHom.ker (CxPts.evHom hzW) :=
    Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, evA]; exact hx
  have h3 : RingHom.ker (CxPts.evHom hzW) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ⊔
        RingHom.ker (CxPts.evHom hzW) ^ 2 := by
    intro x hx
    have := Ideal.map_mono h (h1A hx)
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span] at this
    exact sup_le_sup le_rfl (Ideal.pow_right_mono h2A 2) this
  have h4 : Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι b) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) b (hf j) hb) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change resG X hWa _ ∈ _
    rw [hratio j]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩)

  have hsurj : Function.Surjective (CxPts.evHom hzb) := fun c =>
    ⟨ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι b) c, by rw [← CxPts.ev_eq]; exact CxPts.ev_algX hzb c⟩
  have hmax : (RingHom.ker (CxPts.evHom hzb)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hs : sb ∉ RingHom.ker (CxPts.evHom hzb) := by
    rw [RingHom.mem_ker, ← CxPts.ev_eq]
    exact (CxPts.mem_ptsIn_basicOpen hzb sb).1 (eB ▸ hzW)
  intro g hg
  refine mem_of_algebraMap_mem_map_away (S := Γ(X, W)) sb hmax le_sup_right hs ?_
  have hgW : algebraMap Γ(X, fOpen ι b) Γ(X, W) g ∈ RingHom.ker (CxPts.evHom hzW) := by
    rw [RingHom.mem_ker, evB]; exact hg
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span]
  exact sup_le_sup h4 (Ideal.pow_right_mono h1B 2) (h3 hgW)

end GlobalTheory.EtProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RatioSpanCotangentChangeDenominatorStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_span_cotangent_change_denominator : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ∀ (n : ℕ), 0 < n →
    ∀ (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ) (a b : MvPolynomial (Fin (N + 1)) ℂ)
      (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
      (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
      (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
      (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b)),
      RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2 →
      RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  first | (exact @GlobalTheory.EtProj.span_ratio_of_span_ratio) | (exact GlobalTheory.EtProj.span_ratio_of_span_ratio) | (intros; apply GlobalTheory.EtProj.span_ratio_of_span_ratio  <;> assumption)
end
end

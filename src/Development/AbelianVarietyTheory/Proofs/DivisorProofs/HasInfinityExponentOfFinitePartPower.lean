module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPower
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact.InfExp

open IsDedekindDomain

theorem finAdEquiv_one_tmul (D : D7) (k : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) =
      GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D k) := by
  apply FiniteAdeleRing.ext
  intro w
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp only [GlobalTheory.BotFormula.toFinE, Formalism.MainNotions.StandardLatticesGL3.inc, Formalism.UG.inclE, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.comm_tmul]
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp

theorem eq_inf {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ)
    (hf : HasFinPart χ c e) (k : D.host.Eˣ) (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y)
    (hy : infPart D (y : AE D) = 1) (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((χ x : Circle) : ℂ) =
      ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
  have hfin : ((χ y : Circle) : ℂ) = ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) ^ e : ℂˣ) : ℂ) :=
    hf y _ ⟨hy, by rw [hy']; exact finAdEquiv_one_tmul D k⟩
  have h5 : ((χ x : Circle) : ℂ) * ((χ y : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← map_mul, ← hxy, hχ.2 k, Circle.coe_one]
  have haut := c.aut k
  set F : ℂ := ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) : ℂˣ) : ℂ) with hF
  have hF0 : F ≠ 0 := (c.f _).ne_zero
  have hP : ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (c.n τ) = F⁻¹ :=
    eq_inv_of_mul_eq_one_right haut
  rw [Units.val_zpow_eq_zpow_val, ← hF] at hfin
  rw [hfin] at h5
  have hx : ((χ x : Circle) : ℂ) = (F ^ e)⁻¹ := eq_inv_of_mul_eq_one_left h5
  rw [hx, ← inv_zpow, ← hP, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]


set_option maxHeartbeats 1000000 in
open Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfExp_of_hasFinPart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    HasFinPart χ c e → ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  intro D N c e χ hχ hf τ₀
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  refine ⟨e * c.n τ₀, by push_cast; ring, ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩, fun θ hθ => ?_⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨τ₀⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((χ (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
    intro z
    refine (denseRange_units (tauE D) hd).induction_on z (isClosed_eq
      (continuous_subtype_val.comp (hχ.1.comp Tc)) (continuous_finsetProd _ fun τ _ => ?_)) fun k => ?_
    · have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h2 : ∀ z : D.what₂.Tau → ℂˣ, ((‖(z τ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
        Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (z τ).ne_zero)
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h2).zpow₀ _ fun z =>
        Or.inl (div_ne_zero (z τ).ne_zero (h2 z))
    · refine Eq.trans ?_ (GlobalTheory.NormExact.InfExp.eq_inf c e χ hχ hf k _ _ (hab _) (hb _).1 (hb _).2)
      rw [hT _ (ha (Units.map (incA D).toMonoidHom k)).2]
      congr 3
      funext τ
      exact Units.ext ((congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)).symm
  intro x hx hx'
  refine (congrArg (fun u => ((χ u : Circle) : ℂ)) (hT x hx)).trans ((key _).trans ?_)
  refine Finset.prod_eq_single τ₀ (fun τ _ hτ => ?_) (fun h => absurd (Finset.mem_univ _) h)
  have : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom x : ℂˣ) : ℂ) = 1 := hx' τ hτ
  rw [this, norm_one, Complex.ofReal_one, div_one, one_zpow]

end GlobalTheory.NormExact.InfExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPowerStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasInfinityExponent_of_finitePartPower : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → HasFinPart χ c e →
  ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  first | exact @GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart | exact GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart | (intros; apply GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHalfOfSmul
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CoverTransform

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem qRep_sub_mem {K : Submodule (𝓞 E) Dw.La} (a : Dw.La) :
    qRep (Submodule.Quotient.mk a : Dw.La ⧸ K) - a ∈ K :=
  (Submodule.Quotient.eq _).1 (GlobalTheory.HalfPairing.qRep_mk _)

theorem pd_mem_half (d : DeltaDat Xo c n) (h : d.IsLev) :
    (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [GlobalTheory.LevelCoverDatum.half_mul_conj d h]; exact Ideal.mem_span_singleton_self _
  exact Ideal.mul_le_right h1

theorem mfr_cover (d : DeltaDat Xo c n) (h : d.IsLev) :
    Mfr d.l₂ = Mfr l * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold Mfr; rw [h.2.2.2.1, Ideal.map_mul]

theorem finite_laJ (d : DeltaDat Xo c n) (h : d.IsLev) : Finite (LaJ Xo c d) := by
  have hp := GlobalTheory.LevelCoverDatum.pd_pos d h
  have hb : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro e
    have := pd_mem_half d h
    rw [e, Ideal.mem_bot] at this
    exact hp.ne' (by exact_mod_cast this)
  have := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)).finiteQuotientOfFreeOfNeBot hb
  have := Dw.fin
  exact Submodule.finite_quotient_smul _ (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem exists_bezout (d : DeltaDat Xo c n) (h : d.IsLev) :
    ∃ α β : 𝓞 E, α * d.pd + β * l.M = 1 := Nat.Coprime.cast (R := 𝓞 E) h.2.2.1

theorem mem_half_of_smul (d : DeltaDat Xo c n) (h : d.IsLev) {u : Dw.La}
    (hu : l.M • u ∈ (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) :
    u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  have h1 : l.M • u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mono_left (by rw [mfr_cover d h]; exact Ideal.mul_le_right) hu
  have h2 : u = (α * d.pd) • u + β • l.M • u := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, ← add_smul, e, one_smul]
  rw [h2]
  exact add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) trivial) (Submodule.smul_mem _ _ h1)

theorem exists_class (d : DeltaDat Xo c n) (h : d.IsLev) {x u : Dw.La}
    (hu : u - d.pd • x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ z : LaJ Xo c d, (Submodule.Quotient.mk (d.pd • x + l.M • qRep z) : LevQc Dw d.l₂) = Submodule.Quotient.mk u := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  refine ⟨Submodule.Quotient.mk (β • (u - d.pd • x)), (Submodule.Quotient.eq _).2 ?_⟩
  have h1 := qRep_sub_mem (K := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) (β • (u - d.pd • x))
  generalize qRep (Submodule.Quotient.mk (β • (u - d.pd • x)) : LaJ Xo c d) = r at h1 ⊢
  have h2 : d.pd • x + l.M • r - u =
      (l.M : 𝓞 E) • (r - β • (u - d.pd • x)) - (α * d.pd) • (u - d.pd • x) := by
    have e' : α * (d.pd : 𝓞 E) = 1 - l.M * β := by linear_combination e
    rw [e', ← Nat.cast_smul_eq_nsmul (𝓞 E) l.M]
    generalize d.pd • x = v
    module
  rw [h2, mfr_cover d h]
  refine sub_mem ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul (GlobalTheory.Dict.CoverFourier.natCast_mem l).2 h1
  · rw [mul_comm (Mfr l), Submodule.mul_smul]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) hu

theorem dvd_pairing (d : DeltaDat Xo c n) (h : d.IsLev) (x z y : Dw.La) :
    (d.l₂.M : ℤ) ∣ Dw.EF (qRep (Submodule.Quotient.mk (d.pd • x + l.M • z) : LevQc Dw d.l₂)) (cSep d.l₂ • y) -
      (d.pd * Dw.EF x (cSep l • y) + l.M * Dw.EF z (cHalf H d.I • y)) := by
  have h1 := GlobalTheory.LevelPairing.dvd_left (l := d.l₂) y
    (qRep_sub_mem (K := (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) (d.pd • x + l.M • z))
  obtain ⟨a1, a2⟩ := GlobalTheory.LevelPairing.cSep_spec d.l₂
  obtain ⟨b1, b2⟩ := GlobalTheory.LevelPairing.cSep_spec l
  have h2 : (l.M : ℤ) ∣ Dw.EF x ((cSep d.l₂ - cSep l) • y) := by
    refine GlobalTheory.HalfPairing.dvd_of_mem _ _ _ ?_
    rw [← l.prod, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 l.coprime)]
    refine ⟨?_, sub_mem ?_ b1⟩
    · simpa using sub_mem (h.1.2.1 a2) b2
    · rw [mfr_cover d h] at a1
      exact Ideal.mul_le_left a1
  have h3 := GlobalTheory.Dict.CoverFourier.pd_dvd d h (by rw [mfr_cover d h]; exact Ideal.mul_le_right) z
    (a := y) (a' := y) (by rw [sub_self]; exact zero_mem _)
  have hM : (d.l₂.M : ℤ) = l.M * d.pd := by rw [h.2.1]; push_cast; rfl
  have h4 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_right h2 (d.pd : ℤ)
  have h5 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_left (l.M : ℤ) h3
  have h6 := dvd_add (dvd_add h1 h4) h5
  simp only [map_sub, map_add (f := _), map_nsmul, sub_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at h6
  refine h6.trans (dvd_of_eq ?_)
  ring

end

theorem hatC_eq_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (xJ : Fin n → LaJ Xo c d), d.PhiPin ph ψ xJ → ∀ (x₀ : Fin n → Dw.La) (ζ : ℂ) (φc : (Fin n → LevQc Dw d.l₂) → ℂ), (∀ z : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (d.pd • x₀ b + l.M • z b)) = ζ * ((ph (fun b => Submodule.Quotient.mk (z b)) : c.F) : ℂ)) → (∀ x : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (x b)) ≠ 0 → ∀ b, x b - d.pd • x₀ b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) → GlobalTheory.AdTh.hatC d.l₂ φc = fun q => ζ * ((d.eF.symm (d.w x₀ q) : c.F) : ℂ) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin x₀ ζ φc hval hsupp
  funext q
  haveI := finite_laJ d hd
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw d.l₂
  haveI := Fintype.ofFinite (Fin n → LaJ Xo c d)
  haveI := Fintype.ofFinite (Fin n → LevQc Dw d.l₂)
  have hM₂ : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  have he : zeta d.l₂.M ^ d.l₂.M = 1 := (Complex.isPrimitiveRoot_exp _ hM₂).pow_eq_one
  have he0 : zeta d.l₂.M ≠ 0 := Complex.exp_ne_zero _
  have hz : d.c₂.F.val (zetaM d.c₂) = zeta d.l₂.M := GlobalTheory.LevelPairing.zetaM_coe d.c₂
  have hz1 : c.F.val (zetaM c) = zeta d.l₂.M ^ d.pd := by
    rw [← hz, ← map_pow, GlobalTheory.LevelCoverDatum.zetaM_cover d hd.2.1]; rfl
  have hφ : c.F.val (d.φδ q) = ∑ z : Fin n → LaJ Xo c d, ((ph z : c.F) : ℂ) * (zeta d.l₂.M ^ l.M) ^
      (∑ b, Dw.EF (qRep (z b)) (cHalf H d.I • levRep (q b))) := by
    change d.c₂.F.val (d.eF (d.φδ q)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hpin.2.2.2.2.2 q, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul, map_zpow₀, ← GlobalTheory.Dict.CoverFourier.zetaM_pow d hd, map_pow, hz]
    rfl
  rw [DeltaDat.w, AlgEquiv.symm_apply_apply]
  change _ = ζ * c.F.val (zetaM c ^ pairL (l := l) x₀ (fun b => levRep (q b)) * d.φδ q)
  rw [map_mul, map_zpow₀, hz1, hφ, Finset.mul_sum, Finset.mul_sum, GlobalTheory.AdTh.hatC, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_of_injective
    (fun (z : Fin n → LaJ Xo c d) b => (Submodule.Quotient.mk (d.pd • x₀ b + l.M • qRep (z b)) : LevQc Dw d.l₂))
    (fun z z' e => funext fun b => ?_) _ _ (fun x hx => ?_) (fun z => ?_)
  · have h1 := (Submodule.Quotient.eq _).1 (congrFun e b)
    rw [add_sub_add_left_eq_sub, ← smul_sub] at h1
    rw [← GlobalTheory.HalfPairing.qRep_mk (z b), ← GlobalTheory.HalfPairing.qRep_mk (z' b)]
    exact (Submodule.Quotient.eq _).2 (mem_half_of_smul d hd h1)
  · refine mul_eq_zero_of_left ?_ _
    by_contra hne
    have hx' : (fun b => (Submodule.Quotient.mk (qRep (x b)) : LevQc Dw d.l₂)) = x :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    choose z hz' using fun b => exists_class d hd (hsupp (fun b => qRep (x b)) (by rwa [hx']) b)
    exact hx ⟨z, (funext hz').trans hx'⟩
  · have hz' : (fun b => (Submodule.Quotient.mk (qRep (z b)) : LaJ Xo c d)) = z :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    rw [hval (fun b => qRep (z b)), hz', mul_left_comm, ← mul_assoc ζ, mul_left_comm]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ he0]
    symm
    refine GlobalTheory.Dict.CoverFourier.zpow_congr' hM₂ he ?_
    rw [pairL, pairL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun b _ => dvd_pairing d hd _ _ _

end GlobalTheory.CoverTransform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroup
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinEmbStd

variable {D : D7}

theorem eq_of_finHom (V : HSp D) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g' : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    g = g' := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [MonoidHom.mem_ker.1 hg, MonoidHom.mem_ker.1 hg']
  · exact Units.ext (Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective (h i j))

theorem toFinE_inc (e : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd ℚ D.host.E (1 ⊗ₜ[ℚ] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem finAdEquiv_inclR (e : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (inclR (F := D.host.F) (Af D.host.F) e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E (1 ⊗ₜ[D.host.F] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem toFinE_toAfE_symm (y : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
  simp [GlobalTheory.BotFormula.toAfE]

theorem finAdEquiv_finHom_rat (V : HSp D) (γ : GA D V) (u : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u = matHom V γ) (i j : Fin V.rank) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      algebraMap D.host.E _ ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
  have : ((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j =
      inclR (F := D.host.F) (Af D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (((matHom V γ : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) = _
    rw [← hγ]
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (F := D.host.F) (AF D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
    simp [inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rw [this, finAdEquiv_inclR]

theorem exists_std_of_GfC (V : HSp D) (hG : V.gram = 1) (g : GA D V) (hg : g ∈ GfC V) :
    ∃ x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, IsFinPt V g x := by
  let M : Matrix (Fin V.rank) (Fin V.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := (finHom V g).val
  have hM : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) M * M = 1 := by
    have h2 := GlobalTheory.UnitarySplit.finHom_mem V g
    change Formalism.UG.cT _ M * JR (Af D.host.F) V.gram * M = JR (Af D.host.F) V.gram at h2
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hu : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom = 1 := by
    refine GlobalTheory.DefU.ClassFin.unitary_map _ (sigR (Af D.host.F) D.sp.cm.sig) _ ?_ _ hM
    intro y
    apply (GlobalTheory.BotFormula.toAfE D).injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, GlobalTheory.BotFormula.toAfE_sgA]
  let x0 : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D) := Formalism.UG.bc (GlobalTheory.BotFormula.toAfE D).symm.toRingHom (finHom V g)
  have hx0 : x0 ∈ Formalism.MainNotions.StandardLatticesGL3.GA D V.rank := by
    change Formalism.UG.cT _ (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _ * (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact hu
  refine ⟨⟨x0, hx0⟩, hg, rfl, fun i j => ?_⟩
  exact (toFinE_toAfE_symm _).symm

theorem exists_GQ_of_rat (V : HSp D) (hG : V.gram = 1) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (hxr : x ∈ ratG D V.rank)
    (g : GA D V) (hg : ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    ∃ γ ∈ GQ V, finHom V γ = finHom V g := by
  rw [GlobalTheory.NormSum.ratG_eq_ratPts] at hxr
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hxr)
  let U : Matrix (Fin V.rank) (Fin V.rank) D.host.E := u.val
  have huV : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U * V.gram * U = V.gram := by
    have h : Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U * 1 * U = 1 := hu
    have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U = Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U := by
      exact Matrix.ext fun i j => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
    rw [hG, hc]; exact h
  have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U).map (inclR (F := D.host.F) (AF D.host.F)) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * U.map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [hcT, JR, ← Matrix.map_mul, ← Matrix.map_mul, huV]
  let γ : GA D V := ⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u, hmem⟩
  refine ⟨γ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨u, huV, rfl⟩), ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [finAdEquiv_finHom_rat V γ u rfl i j, hg i j, ← toFinE_inc]
  congr 1
  rw [← hu']
  rfl

theorem exists_finEmb : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
    (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
      ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  intro D V n hG hr
  subst hr
  have key : ∀ (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank), IsFinPt V g x ↔ g ∈ GfC V ∧ ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) := by
    intro g x
    constructor
    · rintro ⟨h1, e, h2⟩
      exact ⟨h1, fun i j => by simpa using h2 i j⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, rfl, fun i j => by simpa using h2 i j⟩
  choose f hf using fun x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG x rfl
  have uniq : ∀ g x, IsFinPt V g x → g = f x := by
    intro g x hg
    obtain ⟨g1, g2⟩ := (key g x).1 hg
    obtain ⟨f1, f2⟩ := (key _ x).1 (hf x)
    exact eq_of_finHom V g1 f1 fun i j => (g2 i j).trans (f2 i j).symm
  have hfx : ∀ x, ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (((finHom V (f x) : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) :=
    fun x => ((key _ x).1 (hf x)).2
  let ι : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* GA D V :=
    { toFun := f
      map_one' := (uniq 1 1 ((key 1 1).2 ⟨one_mem _, fun i j => by
          simp [Matrix.one_apply, apply_ite]; split_ifs <;> simp_all⟩)).symm
      map_mul' := fun x y => (uniq _ _ ((key _ _).2 ⟨mul_mem ((key _ x).1 (hf x)).1 ((key _ y).1 (hf y)).1, fun i j => by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, hfx]⟩)).symm }
  refine ⟨ι, hf, ?_, ?_, ?_⟩
  · intro x y hxy
    change f x = f y at hxy
    apply Subtype.ext; apply Units.ext; ext i j
    apply (GlobalTheory.BotFormula.toFinE D).injective
    rw [← hfx x, ← hfx y, hxy]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ((key _ x).1 (hf x)).1
    · intro g hg
      obtain ⟨x, hx⟩ := exists_std_of_GfC V hG g hg
      exact ⟨x, (uniq g x hx).symm⟩
  · intro x
    constructor
    · rintro ⟨γ, hγ, he⟩
      change finHom V γ = finHom V (f x) at he
      obtain ⟨u, -, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
      rw [GlobalTheory.NormSum.mem_ratG]
      refine ⟨(u : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ?_⟩
      refine Matrix.ext fun i j => ?_
      apply (GlobalTheory.BotFormula.toFinE D).injective
      rw [Matrix.map_apply, toFinE_inc, ← hfx x, ← he, finAdEquiv_finHom_rat V γ u hu' i j]
    · intro hxr
      exact exists_GQ_of_rat V hG x hxr (f x) (hfx x)

end GlobalTheory.FinEmbStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroupStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicEmbedding_standardUnitaryGroup : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
  (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
    ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  first | exact @GlobalTheory.FinEmbStd.exists_finEmb | exact GlobalTheory.FinEmbStd.exists_finEmb | (intros; apply GlobalTheory.FinEmbStd.exists_finEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticCh
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticCh
noncomputable section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

def mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) :
    ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) (x : κ → R) : mulQ χ h A φ x = χ (quad h A x) * φ x := rfl

theorem mulQ_neg_mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) : mulQ χ h (-A) (mulQ χ h A φ) = φ := by
  funext x
  rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

theorem mulQ_schr {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (χ : AddChar R ℂ) (B : Matrix κ κ R)
    (hB : Bᵀ = B) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    mulQ χ (⅟2) (-B) (schr χ w φ) = schr χ (w.1, B *ᵥ w.1 + w.2) (mulQ χ (⅟2) (-B) φ) := by
  have hB' : (-B)ᵀ = -B := by rw [Matrix.transpose_neg, hB]
  funext x
  have key := quad_add (-B) hB' x w.1 w.2
  rw [Matrix.neg_mulVec, neg_neg] at key
  simp only [mulQ_apply, schr]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key]

theorem act_unip {F R κ : Type} [Field F] [CommRing R] [Algebra F R] [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F)
    (w : (κ → R) × (κ → R)) :
    act ((Matrix.fromBlocks 1 0 b 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) w =
      (w.1, b.map (algebraMap F R) *ᵥ w.1 + w.2) := by
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), act_fromBlocks]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def qI (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem eventually_integral (x : κ → AF F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun i => (x i).2.2

theorem finite_mulSupport {φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
  refine (Filter.eventually_cofinite.1 (hφ.2.and (eventually_integral x))).subset fun v hv => ?_
  intro h
  apply hv
  change φ v _ = 1
  rw [h.1, ind, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from h.2), Pi.one_apply]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulQ_mem_SB {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) {φ : (κ → K) → ℂ} (hφ : φ ∈ SB (κ → K)) :
    mulQ χ h A φ ∈ SB (κ → K) :=
  ⟨((GlobalTheory.SchrSBFin.isLocallyConstant_addChar χ hχ).comp_continuous (continuous_quad h A)).mul hφ.1, hφ.2.mul_left⟩

theorem mulQ_bijOn {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) :
    Set.BijOn (mulQ χ h A) (SB (κ → K) : Set _) (SB (κ → K) : Set _) := by
  refine Set.InvOn.bijOn (f' := mulQ χ h (-A)) ⟨fun φ _ => mulQ_neg_mulQ χ h A φ, fun φ _ => ?_⟩
    (fun φ hφ => mulQ_mem_SB χ hχ h A hφ) (fun φ hφ => mulQ_mem_SB χ hχ h (-A) hφ)
  have := mulQ_neg_mulQ χ h (-A) φ
  rwa [neg_neg] at this

theorem quad_mem {v : Pl (F := F)} {h : Fv F v} (hh : h ∈ v.adicCompletionIntegers F) {A : Matrix κ κ (Fv F v)}
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) {x : κ → Fv F v} (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    quad h A x ∈ v.adicCompletionIntegers F := by
  unfold quad
  refine mul_mem hh (sum_mem fun i _ => mul_mem (hx i) (sum_mem fun j _ => mul_mem (hA i j) (hx j)))

theorem invOf_two_eq (v : Pl (F := F)) : ⅟(2 : Fv F v) = algebraMap F (Fv F v) (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem eventually_mulQ_ind (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (b : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (ind κ v) = ind κ v := by
  filter_upwards [GlobalTheory.psiLoc_eventually_trivial_integers ψ hψ, eventually_algebraMap_mem_integers (2⁻¹ : F),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_algebraMap_mem_integers (b i j)] with v h1 h2 h3
  funext x
  rw [mulQ_apply]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hq : quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) x ∈ v.adicCompletionIntegers F :=
      quad_mem (show ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F by rw [invOf_two_eq]; exact h2) (fun i j => neg_mem (h3 i j)) hx
    rw [GlobalTheory.LatVac.psiAt_apply, h1 _ hq, one_mul]
  · rw [ind, Set.indicator_of_notMem (show x ∉ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), mul_zero]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem invOf_two_eq' (R : Type) [CommRing R] [Algebra F R] [Invertible (2 : R)] : ⅟(2 : R) = algebraMap F R (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem evFin_quad (b : Matrix κ κ F) (v : Pl (F := F)) (x : κ → AF F) :
    evFin F v (quad (⅟2) (-(b.map (algebraMap F (AF F)))) x) =
      quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) (fun i => evFin F v (x i)) := by
  have h : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    have hmap : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
      refine (invOf_eq_right_inv ?_).symm
      have hmul : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
      rwa [map_mul, map_ofNat] at hmul
    rw [hmap, invOf_eq_inv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [quad, dotProduct, Matrix.mulVec, map_sum, h]

theorem psi_quad_rat (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (ξ : κ → F) :
    ψ (quad (⅟2) (-(b.map (algebraMap F (AF F)))) (fun i => algebraMap F (AF F) (ξ i))) = 1 := by
  have h := map_quad (algebraMap F (AF F)) (2⁻¹ : F) (-b) ξ
  rw [Matrix.map_neg _ (map_neg _), ← invOf_two_eq'] at h
  rw [← h]
  exact hψ.2.1 _

theorem thetaSum_mulQ (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) Φ) = thetaSum F Φ := by
  unfold thetaSum
  congr 1
  funext ξ
  rw [mulQ_apply, psi_quad_rat ψ hψ b ξ, one_mul]

theorem archMul_neg_mul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : archMul h A y * archMul h (-A) y = 1 := by
  unfold archMul
  rw [← AddChar.map_add_eq_mul, quad_neg, map_neg, neg_neg, neg_add_cancel, AddChar.map_zero_eq_one]

theorem surjective_arch (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.Surjective (SchwartzMap.smulLeftCLM ℂ (archMul h A) : SInf F κ →L[ℂ] SInf F κ) := by
  intro f
  refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul h (-A)) f, ?_⟩
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul, smul_eq_mul, ← mul_assoc,
    archMul_neg_mul, one_mul]

theorem at_pairA (a : AF F) : At (evI F) (pairA F (fstA F a) 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem mulQ_pure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (f : SInf F κ)
    {φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ} (hφ : IsFam φ) :
    mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.smulLeftCLM ℂ
                   (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
        (fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (φ v)) := by
  funext x
  set Q := quad (⅟2) (-(b.map (algebraMap F (AF F)))) x with hQ
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local F ψ hψ.1 Q
  simp only [hQ, evFin_quad] at hfin hprod
  have harch : ψ (pairA F (fstA F Q) 0) =
      archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) := by
    rw [hψ.2.2 _ (at_pairA Q)]
    have e1 : evI F (pairA F (fstA F Q) 0) =
        quad (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) :=
      map_quad (qI F) _ _ x
    rw [e1, archMul, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [← hQ] at hprod
  change ψ Q * (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
    (SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
      (fun i => evI F (x i)) * ∏ᶠ v, (GlobalTheory.LatVac.psiAt ψ v (quad (⅟2) (-(b.map (algebraMap F (Fv F v))))
        (fun i => evFin F v (x i))) * φ v fun i => evFin F v (x i))
  rw [finprod_mul_distrib hfin (finite_mulSupport hφ x), SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    smul_eq_mul, hprod, harch]
  ring

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad archMul)


open scoped Classical in
theorem hasOp_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b → HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  intro F _ _ ψ hψ κ _ _ b hb
  have hB : ∀ (R : Type) [CommRing R] [Algebra F R], (b.map (algebraMap F R))ᵀ = b.map (algebraMap F R) :=
    fun R _ _ => by rw [← Matrix.transpose_map, hb]
  refine ⟨mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))), 1,
    SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))),
    fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))), one_ne_zero,
    surjective_arch _ _, fun v => mulQ_bijOn _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v) _ _, fun v w φ _ => ?_,
    eventually_mulQ_ind ψ hψ.1 b, fun f φ hφ => ⟨mulQ_pure ψ hψ b f hφ, fun w => ?_, ?_⟩⟩
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [thetaSum_mulQ ψ hψ b, one_mul]

end GlobalTheory.RatWeilUnip

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticChStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b →
    HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  first | exact @GlobalTheory.RatWeilUnip.hasOp_unip | exact GlobalTheory.RatWeilUnip.hasOp_unip | (intros; apply GlobalTheory.RatWeilUnip.hasOp_unip <;> assumption)
end
end

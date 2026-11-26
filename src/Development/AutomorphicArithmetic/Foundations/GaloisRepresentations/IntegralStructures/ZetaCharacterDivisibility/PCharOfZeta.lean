module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCharOfZeta
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.charOfZeta_of :
    CharOfZeta := by
  intro E _ _ _ a U hU ζ hζ hcen hrat hsc
  choose c hc using hsc
  obtain ⟨φ₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ₀ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hval : ∀ z, φ₀ (g₀ * ζ z) = c z * φ₀ g₀ := fun z => by
    have := congrFun (hc z φ₀ h₀) g₀
    rwa [GlobalTheory.DefU.RU_apply, Pi.smul_apply, smul_eq_mul] at this
  have hcz : ∀ z, c z = φ₀ (g₀ * ζ z) / φ₀ g₀ := fun z => by
    rw [hval z, mul_div_cancel_right₀ _ hg₀]
  have hcont : Continuous c := by
    have h1 : Continuous fun z => φ₀ (g₀ * ζ z) :=
      (hU.aut φ₀ h₀).cont.comp (continuous_const.mul hζ)
    have h2 : c = fun z => φ₀ (g₀ * ζ z) / φ₀ g₀ := funext hcz
    rw [h2]
    exact h1.div_const _
  have hone : c 1 = 1 := by
    rw [hcz, map_one, mul_one, div_self hg₀]
  have hmul : ∀ z z', c (z * z') = c z * c z' := fun z z' => by
    have h1 : RU E a (ζ (z * z')) φ₀ = (c z * c z') • φ₀ := by
      rw [map_mul, map_mul, Module.End.mul_apply, hc z' φ₀ h₀, map_smul, hc z φ₀ h₀, smul_smul, mul_comm]
    rw [hc _ φ₀ h₀] at h1
    exact smul_left_injective ℂ hne h1
  let f : Ideles E →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  have hinvc : Continuous fun z => (c z)⁻¹ := by
    refine hcont.inv₀ fun z => ?_
    intro h0
    have := hmul z z⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  refine ⟨⟨f.toHomUnits, ?_, fun k => ?_⟩, fun z φ hφ => ?_⟩
  · refine Units.continuous_iff.2 ⟨hcont, ?_⟩
    have : (fun z => (((f.toHomUnits z)⁻¹ : ℂˣ) : ℂ)) = fun z => (c z)⁻¹ := by
      funext z
      rw [Units.val_inv_eq_inv_val]
      rfl
    exact this ▸ hinvc
  · refine Units.ext ?_
    change c (diagUnits E k) = 1
    rw [hcz, ← hcen, (hU.aut φ₀ h₀).left _ (hrat k), div_self hg₀]
  · exact hc z φ hφ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PAlgOfFix
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

private theorem chi_fixed {E : Type} [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (hfix : ∀ z, cj E z = z → χ.1 z = 1) (τ : E →+* ℂ) (z : ℂ)
    (hs : expU (atEmb τ (starRingEnd ℂ z)) = expU (atEmb τ z)) :
    Complex.exp (expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z) = 1 := by
  rw [← chiInf_expU_atEmb]
  have h1 : cj E (infId E (expU (atEmb τ z))) = infId E (expU (atEmb τ z)) := by
    refine (GlobalTheory.NormExpo.conjAd_infId E _).trans ?_
    rw [GlobalTheory.NormExpo.star_expU_atEmb, hs]
  have h2 : chiInf χ (expU (atEmb τ z)) = 1 := hfix _ h1
  rw [h2]
  rfl

private theorem expU_neg_pi {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    expU (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I))) = expU (atEmb τ ((Real.pi : ℂ) * Complex.I)) := by
  classical
  refine Units.ext (funext fun w => ?_)
  change Complex.exp (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I)) w) =
    Complex.exp (atEmb τ ((Real.pi : ℂ) * Complex.I) w)
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    split_ifs <;> simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  · simp [Pi.single_eq_of_ne hw]

private theorem add_eq_zero_of {p q : ℂ} (h : ∀ t : ℝ, Complex.exp (p * t + q * starRingEnd ℂ (t : ℂ)) = 1) : p + q = 0 := by
  have hf : (fun t : ℝ => Complex.exp ((p + q) * t)) = fun _ => 1 := by
    funext t
    have := h t
    rw [Complex.conj_ofReal] at this
    rw [add_mul]; exact this
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((p + q) * t)) (Complex.exp ((p + q) * ((0 : ℝ) : ℂ)) * ((p + q) * 1)) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (p + q) * (t : ℂ)) ((p + q) * 1) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (p + q)
    exact h0.cexp
  rw [hf] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using this

theorem UpperTheory.Gal.Int.Div.algOfFix_of :
    AlgOfFix := by
  intro E _ _ _ χ hfix
  have key : ∀ τ : E →+* ℂ, ∃ n : ℤ, expo χ τ = n := by
    intro τ
    have hpq : expo χ τ + expo χ (ComplexEmbedding.conjugate τ) = 0 :=
      add_eq_zero_of fun t => chi_fixed χ hfix τ t (by rw [Complex.conj_ofReal])
    have h := chi_fixed χ hfix τ _ (expU_neg_pi τ)
    have hq : expo χ (ComplexEmbedding.conjugate τ) = - expo χ τ := by linear_combination hpq
    rw [hq] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ h2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hn
    linear_combination hn
  choose n hn using key
  exact ⟨n, isAlgPos_of_expo E χ n hn⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaEx
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem cj_cj (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (UpperTheory.Gal.Int.Div.cj E z) = z :=
  Units.ext (GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol _)

private theorem cj_quo_mul (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (quo E z) * quo E z = 1 := by
  rw [quo_apply, _root_.map_div, cj_cj, div_mul_div_comm, mul_comm z, div_self']

private theorem scal_mem (a : ℕ) (y : Ideles E) (h : UpperTheory.Gal.Int.Div.cj E y * y = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin a) y ∈ UA E a := by
  have hy : conjAd E (y : Ad E) * (y : Ad E) = 1 := congrArg Units.val h
  have e : ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) =
      Matrix.diagonal fun _ => (y : Ad E) := rfl
  show (((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).map (conjAd E)).transpose * 1 *
    ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1
  rw [e, Matrix.mul_one, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  simp only [Function.comp_apply, hy]
  exact Matrix.diagonal_one

private theorem continuous_scal (a : ℕ) :
    Continuous (fun y : Ideles E => (Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a)) := by
  have h : Continuous ((Matrix.scalar (Fin a)).toMonoidHom : Ad E →* Matrix (Fin a) (Fin a) (Ad E)) :=
    Continuous.matrix_diagonal (A := fun (x : Ad E) (_ : Fin a) => x) (continuous_pi fun _ => continuous_id)
  exact Continuous.units_map _ h

private theorem continuous_quo : Continuous (quo E) :=
  continuous_id.div' (Continuous.units_map _ GlobalTheory.BCT.GlobLev.continuous_conj_ad)

private theorem ratGL_scalar (a : ℕ) (k : Eˣ) :
    ratGL E a (Matrix.GeneralLinearGroup.scalar (Fin a) k) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (diagUnits E k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap E (Ad E) (Matrix.diagonal (fun _ => (k : E)) i j) =
    Matrix.diagonal (fun _ => algebraMap E (Ad E) (k : E)) i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private theorem quo_diag (k : Eˣ) :
    quo E (diagUnits E k) =
      diagUnits E (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) := by
  have e : UpperTheory.Gal.Int.Div.cj E (diagUnits E k) =
      diagUnits E (Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) :=
    Units.ext (conjAd_algebraMap (k : E))
  rw [quo_apply, e, _root_.map_div]

end

theorem UpperTheory.Gal.Int.Div.zetaEx_of :
    ZetaEx := by
  intro E _ _ _ a
  refine ⟨MonoidHom.codRestrict ((Matrix.GeneralLinearGroup.scalar (Fin a)).comp (quo E)) (UA E a)
    (fun z => scal_mem a _ (cj_quo_mul z)), fun z => rfl, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk ((continuous_scal a).comp continuous_quo) _
  · intro z x
    refine Subtype.ext (Units.ext ?_)
    exact (Matrix.scalar_commute ((quo E z : Ideles E) : Ad E) (fun r => mul_comm _ r) x.1.val).eq
  · intro k
    refine Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.scalar (Fin a)
      (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k), ?_⟩
    rw [ratGL_scalar, ← quo_diag]
    rfl
  · intro z hz
    refine Subtype.ext ?_
    change Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z) = 1
    rw [quo_apply, hz, div_self', map_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaLoc
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

private theorem map_scalar' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin a) y) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (Units.map f.toMonoidHom y) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, h]

section

open GlobalTheory.SplitPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem pInf_quo (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map (pInf E).toMonoidHom (quo E (localIdele E w u)) = 1 := by
  have h1 : pInf E ((localIdele E w u : Ideles E) : Ad E) = 1 := by
    change (infEq E).symm (1 : InfiniteAdeleRing E) = 1
    exact map_one _
  have h2 : Units.map (pInf E).toMonoidHom (localIdele E w u) = 1 := Units.ext h1
  have h3 : Units.map (pInf E).toMonoidHom (cj E (localIdele E w u)) = 1 := by
    refine Units.ext ?_
    change pInf E (conjAd E ((localIdele E w u : Ideles E) : Ad E)) = 1
    rw [GlobalTheory.CompanionTheory.OnlyStab.pInf_conj, h1, map_one]
  rw [quo_apply, _root_.map_div, h2, h3, div_one]

private theorem loc_quo (w v : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (quo E (localIdele E w u)) =
      Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (localIdele E w u) /
        Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (cj E (localIdele E w u)) := by
  rw [quo_apply, _root_.map_div]

private theorem loc_id_ne {w v : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (localIdele E w u) = 1 :=
  Units.ext ((Neutral.B1.localIdele_isSupportedAt E w u).2 v h)

private theorem loc_cj_ne {w v : HeightOneSpectrum (𝓞 E)} (h : conjSrc (conjE E) v ≠ w)
    (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (cj E (localIdele E w u)) = 1 := by
  refine Units.ext ?_
  change conjLoc (conjE E) v (((localIdele E w u : Ideles E) : Ad E).2 (conjSrc (conjE E) v)) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt E w u).2 _ h, map_one]

private theorem loc_id_self (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E w).comp (pFin E)).toMonoidHom (localIdele E w u) = u :=
  Units.ext (Neutral.B1.localIdele_snd_self E w u)

end

open GlobalTheory.SplitPts in
theorem UpperTheory.Gal.Int.Div.zetaLoc_of :
    ZetaLoc := by
  intro E _ _ _ a ζ hζ w hw u
  obtain ⟨hne, hund, -⟩ := over_split hw
  have hc : ∀ v, cLoc v (ζ (localIdele E w u)) = Matrix.GeneralLinearGroup.scalar (Fin a)
      (Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (quo E (localIdele E w u))) := by
    intro v
    change Matrix.GeneralLinearGroup.map _ ((ζ (localIdele E w u) : UA E a) : GA E a) = _
    rw [hζ, map_scalar']
  have hi : cInf (ζ (localIdele E w u)) = 1 := by
    change Matrix.GeneralLinearGroup.map _ ((ζ (localIdele E w u) : UA E a) : GA E a) = _
    rw [hζ, map_scalar', pInf_quo, map_one]
  refine ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 hi, Subgroup.mem_iInf.2 fun v =>
    Subgroup.mem_iInf.2 fun hv => MonoidHom.mem_ker.2 ?_⟩, ?_⟩
  · have h1 : v ≠ w := fun e => hv (by rw [e])
    have h2 : conjSrc (conjE E) v ≠ w := fun e => hv (by
      rw [← hund, ← e, conjSrc_conjSrc_cm])
    rw [hc, loc_quo, loc_id_ne h1, loc_cj_ne h2, div_one, map_one]
  · rw [hc, loc_quo, loc_id_self, loc_cj_ne hne, div_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatCent
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div


open GlobalTheory.LFun Formalism.UG Matrix in
private theorem scalar_unit_mem {E : Type} [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    GeneralLinearGroup.scalar (Fin a) u ∈ KGL w a := by
  have hv : Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have m1 : (u : w.adicCompletion E) ∈ Ov E w := le_of_eq hu
  have m2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Ov E w := le_of_eq hv
  have hinj : Function.Injective fun M : Matrix (Fin a) (Fin a) (Ov E w) => M.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.scalar (Fin a) (⟨u, m1⟩ : Ov E w), Matrix.scalar (Fin a) (⟨_, m2⟩ : Ov E w), hinj ?_, hinj ?_⟩,
    Units.ext ?_⟩
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · ext i j
    by_cases h : i = j
    · subst h; simp [bc]
    · simp [bc, h]


open GlobalTheory.LFun Formalism.UG Matrix in
private theorem satEig_self (q n : ℕ) (B : Multiset ℂˣ) (hB : B.card = n) :
    satEig q n B n = ((B.prod : ℂˣ) : ℂ) := by
  subst hB
  have hc : (B.map fun b : ℂˣ => (b : ℂ)).card = B.card := Multiset.card_map _ _
  rw [satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
  conv_lhs => rw [← hc]
  rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
  exact (map_multiset_prod (Units.coeHom ℂ) B).symm


open GlobalTheory.LFun Formalism.UG Matrix in
private theorem scalar_unif_act {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V] {a : ℕ}
    {w : HeightOneSpectrum (𝓞 E)} {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {x : V}
    {B : Multiset ℂˣ} (hx : IsSatVecGL w ρ x B) (u : (w.adicCompletion E)ˣ)
    (hu : IsUnifV E w (u : w.adicCompletion E)) :
    ρ (GeneralLinearGroup.scalar (Fin a) u) x = ((B.prod : ℂˣ) : ℂ) • x := by
  have h0 : (u : w.adicCompletion E) ≠ 0 := u.ne_zero
  set z : GL (Fin a) (w.adicCompletion E) := GlobalTheory.WeylGL.tor h0 fun _ => 1 with hz
  have hzs : z = GeneralLinearGroup.scalar (Fin a) u := by
    ext i j
    simp [hz, GlobalTheory.WeylGL.tor_val, Matrix.diagonal_apply]
  have hcomm : ∀ g, z * g = g * z := GlobalTheory.WeylGL.tor_const_comm h0 1
  have hT : Tj ℂ a (Ov E w) (u : w.adicCompletion E) a = dosetInd ℂ (KGL w a) z := by
    rw [GlobalTheory.WeylGL.Tj_eq h0]; simp [hz]
  have h1 := hx.2.2.2 _ hu a le_rfl
  rw [hT, heckeVec_dosetInd (R := {z}) hx.2.1, Finset.sum_singleton, satEig_self _ _ _ hx.2.2.1, hzs] at h1
  · exact h1
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro g hg
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← hcomm c, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hc hd

theorem UpperTheory.Gal.Int.Div.satCent_of :
    SatCent := by
  intro E _ _ a w σ B hB
  obtain ⟨x, hx⟩ := hB.exists_vec
  exact ⟨x, hx.1, fun u hu => GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ (scalar_unit_mem a w u hu),
    fun u hu => scalar_unif_act hx u hu⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSchurU
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.schurU_of :
    SchurU := by
  intro E _ _ _ a U hU z hz
  classical
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  have hcomm : ∀ (x : UA E a) (ψ : UA E a → ℂ), RU E a z (RU E a x ψ) = RU E a x (RU E a z ψ) := fun x ψ => by
    rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.RU_RU, hz]
  let S : Submodule ℂ (UA E a → ℂ) := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)
  haveI hSfd : FiniteDimensional ℂ S := (hU.aut φ hφU).kfin
  have hSU : S ≤ U := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact hU.stable _ _ hφU)
  have hφS : φ ∈ S := Submodule.subset_span ⟨1, by simp⟩
  have hSst : ∀ x : infU E a, ∀ v ∈ S, RU E a x v ∈ S := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      exact Submodule.subset_span ⟨x * k, by simp only [Subgroup.coe_mul, GlobalTheory.DefU.RU_RU]⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add p q _ _ hp hq => rw [map_add (f := _)]; exact S.add_mem hp hq
    | smul c p _ hp => rw [map_smul]; exact S.smul_mem c hp
  let ρ : infU E a → Module.End ℂ S := fun x => (RU E a x).restrict (hSst x)
  let K : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by
        change RU E a ((1 : finU (E := E) (n := a)) : UA E a) φ = φ
        simp
      mul_mem' := fun {p q} hp hq => by
        have hp' : RU E a p φ = φ := hp
        have hq' : RU E a q φ = φ := hq
        change RU E a ((p * q : finU (E := E) (n := a)) : UA E a) φ = φ
        rw [Subgroup.coe_mul, ← GlobalTheory.DefU.RU_RU, hq', hp']
      inv_mem' := fun {p} hp => by
        have hp' : RU E a p φ = φ := hp
        change RU E a ((p⁻¹ : finU (E := E) (n := a)) : UA E a) φ = φ
        conv_lhs => rw [← hp']
        rw [GlobalTheory.DefU.RU_RU, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hKo : IsOpen (K : Set (finU (E := E) (n := a))) := (hU.aut φ hφU).level
  have hKS : ∀ k ∈ K, ∀ v ∈ S, RU E a (k : finU (E := E) (n := a)) v = v := by
    intro k hk v hv
    have hk' : RU E a k φ = φ := hk
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      change RU E a k (RU E a x φ) = RU E a x φ
      rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf k.2 x.2, ← GlobalTheory.DefU.RU_RU, hk']
    | zero => rw [map_zero]
    | add p q _ _ hp hq => rw [map_add (f := _), hp, hq]
    | smul c p _ hp => rw [map_smul, hp]
  let M : Submodule ℂ (S →ₗ[ℂ] (UA E a → ℂ)) :=
    { carrier := {f | (∀ v, f v ∈ U) ∧ (∀ (x : infU E a) v, f (ρ x v) = RU E a x (f v)) ∧
        ∀ k ∈ K, ∀ v, RU E a (k : finU (E := E) (n := a)) (f v) = f v}
      add_mem' := fun {f g} hf hg => ⟨fun v => U.add_mem (hf.1 v) (hg.1 v),
        fun x v => by rw [LinearMap.add_apply, LinearMap.add_apply, hf.2.1, hg.2.1, map_add (f := _)],
        fun k hk v => by rw [LinearMap.add_apply, map_add (f := _), hf.2.2 k hk, hg.2.2 k hk]⟩
      zero_mem' := ⟨fun _ => U.zero_mem, fun x v => by simp, fun k _ v => by simp⟩
      smul_mem' := fun c f hf => ⟨fun v => U.smul_mem c (hf.1 v),
        fun x v => by rw [LinearMap.smul_apply, LinearMap.smul_apply, hf.2.1, map_smul],
        fun k hk v => by rw [LinearMap.smul_apply, map_smul, hf.2.2 k hk]⟩ }
  haveI hMfd : FiniteDimensional ℂ M := UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level E a S ρ K hKo M fun f hf =>
    ⟨fun v γ hγ g => (hU.aut _ (hf.1 v)).left γ hγ g, hf.2.1, hf.2.2⟩
  have hsub : S.subtype ∈ M :=
    ⟨fun v => hSU v.2, fun _ _ => rfl, fun k hk v => hKS k hk v.1 v.2⟩
  haveI : Nontrivial M := ⟨⟨⟨S.subtype, hsub⟩, 0, fun h => hφ0 (by
    have h1 := LinearMap.congr_fun (congrArg Subtype.val h) (⟨φ, hφS⟩ : S)
    exact h1)⟩⟩
  let T : Module.End ℂ M :=
    { toFun := fun f => ⟨(RU E a z).comp f.1, fun v => hU.stable z _ (f.2.1 v),
        fun x v => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, f.2.2.1, hcomm],
        fun k hk v => by
          rw [LinearMap.comp_apply, ← hcomm, f.2.2.2 k hk]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.ext fun v => map_add (RU E a z) _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.ext fun v => map_smul (RU E a z) c _) }
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨f, hf⟩ := hc.exists_hasEigenvector
  have hTf : ∀ v, RU E a z (f.1 v) = c • f.1 v := fun v =>
    LinearMap.congr_fun (congrArg Subtype.val hf.apply_eq_smul) v
  have hfne : ∃ v, f.1 v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf.2 (Subtype.ext (LinearMap.ext h))
  obtain ⟨v, hv⟩ := hfne
  let W : Submodule ℂ (UA E a → ℂ) :=
    { carrier := {ψ | ψ ∈ U ∧ RU E a z ψ = c • ψ}
      add_mem' := fun {p q} hp hq => ⟨U.add_mem hp.1 hq.1, by rw [map_add (f := _), hp.2, hq.2, smul_add]⟩
      zero_mem' := ⟨U.zero_mem, by rw [map_zero, smul_zero]⟩
      smul_mem' := fun b p hp => ⟨U.smul_mem b hp.1, by rw [map_smul, hp.2, smul_comm]⟩ }
  have hWU : W ≤ U := fun _ h => h.1
  have hWst : ∀ x, ∀ ψ ∈ W, RU E a x ψ ∈ W := fun x ψ hψ =>
    ⟨hU.stable x ψ hψ.1, by rw [hcomm, hψ.2, map_smul]⟩
  have hvW : f.1 v ∈ W := ⟨f.2.1 v, hTf v⟩
  rcases hU.irred W hWU hWst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hvW)) hv
  · exact ⟨c, fun ψ hψ => (h ▸ hψ : ψ ∈ W).2⟩
end

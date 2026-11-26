module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
noncomputable section

namespace GlobalTheory.RankOneComp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locPar_ofChar_unr_iff (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  rw [ParLaws.locPar_ofChar, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

theorem locPar_ofChar_frob (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  have e2 : ParLaws.locPar hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLaws.locPar_ofChar, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  simp

end Char

end GlobalTheory.RankOneComp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeTame

def invTranspose {R : Type} [CommRing R] (n : ℕ) : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invTranspose_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    (invTranspose n g).val = (g⁻¹).val.transpose := rfl

theorem invTranspose_inv_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((invTranspose n g)⁻¹).val = g.val.transpose := rfl

theorem invTranspose_invTranspose {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    invTranspose n (invTranspose n g) = g := by
  apply Units.ext
  rw [invTranspose_val, invTranspose_inv_val, Matrix.transpose_transpose]

theorem continuous_invTranspose {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (invTranspose (R := R) n) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invTranspose_mem_GLint {F : Type} [Field F] (n : ℕ) (O : Subring F) {g : GL (Fin n) F}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) : invTranspose n g ∈ Formalism.UG.GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨invTranspose n h, Units.ext rfl⟩

theorem conjSP_proj {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : AL L) :
    (conjSP s).proj x = s.proj (conjAL L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem conjSP_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (κ : GA L n) :
    (conjSP s).loc n κ = invTranspose n (s.loc n κ) := by
  have hm : κ.1.val * conjT (conjAL L) κ.1.val = 1 := κ.2
  have h1 : (κ.1⁻¹).val = conjT (conjAL L) κ.1.val := Units.inv_eq_of_mul_eq_one_right hm
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (conjSP s).proj (κ.1.val i j) = s.proj ((κ.1⁻¹).val j i)
  rw [h1, conjSP_proj]
  rfl

theorem exists_conj_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  intro L _ _ _ n s K θ hK hθ
  have key : ∀ (g' : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g) (hg : g ∈ K),
      g' = invTranspose n g → ∃ h' : g' ∈ K.comap (invTranspose n),
        θ.comp ((invTranspose n).subgroupComap K) ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
    rintro g' g hg rfl
    refine ⟨by rw [Subgroup.mem_comap, invTranspose_invTranspose]; exact hg, ?_⟩
    rw [MonoidHom.comp_apply]
    exact congrArg θ (Subtype.ext (invTranspose_invTranspose n g))
  refine ⟨K.comap (invTranspose n), θ.comp ((invTranspose n).subgroupComap K), ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have := invTranspose_mem_GLint n _ (hK _ hg)
    rwa [invTranspose_invTranspose] at this
  · have hc : Continuous ((invTranspose n).subgroupComap K) :=
      Continuous.subtype_mk ((continuous_invTranspose n).comp continuous_subtype_val) _
    exact hθ.preimage hc
  · intro κ
    rw [conjSP_loc]
    change invTranspose n (invTranspose n (s.loc n κ)) ∈ K ↔ _
    rw [invTranspose_invTranspose]
  · intro κ h h'
    exact (key _ _ h (conjSP_loc n s κ)).2
  · intro g hg g' hg'
    exact key g' g hg (Units.ext hg')

end GlobalTheory.TypeTame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_character_at_conjugateSplitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  first | exact @GlobalTheory.TypeTame.exists_conj_level | exact GlobalTheory.TypeTame.exists_conj_level | (intros; apply GlobalTheory.TypeTame.exists_conj_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuTameQS

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ Valued.v y < 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem val_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ Valued.v y = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem isTame_loc {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.TameAt w) : GlobalTheory.SplitWeil.IsTame (χ.loc w) := by
  intro x hx
  have h1 : Valued.v ((x : w.adicCompletion E) - 1) < 1 := (val_lt_one_iff w _).1 hx
  refine h x ?_ ?_
  · have := Valuation.map_one_add_of_lt _ h1
    rwa [add_sub_cancel] at this
  · rw [← WithZero.exp_zero] at h1
    exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)

theorem not_isUnram_loc {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : ¬ χ.UnrAt w) : ¬ GlobalTheory.SplitWeil.IsUnram (χ.loc w) := fun hu =>
  h fun x hx => hu x ((val_eq_one_iff w _).2 hx)

theorem tameAt_mul {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.TameAt w) (h' : χ'.TameAt w) : (χ * χ').TameAt w := fun x hx hx' => by
  change χ.loc w x * χ'.loc w x = 1
  rw [h x hx hx', h' x hx hx', one_mul]

theorem unrAt_mul {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) (h' : χ'.UnrAt w) : (χ * χ').UnrAt w := fun x hx => by
  change χ.loc w x * χ'.loc w x = 1
  rw [h x hx, h' x hx, one_mul]

theorem unrAt_of_mul_left {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) (h' : (χ * χ').UnrAt w) : χ'.UnrAt w := fun x hx => by
  have := h' x hx
  change χ.loc w x * χ'.loc w x = 1 at this
  rwa [h x hx, one_mul] at this

end GlobalTheory.MuTameQS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitConjVal

theorem eq_of_isEquiv {F : Type} [Field F] (v1 v2 : Valuation F (WithZero (Multiplicative ℤ)))
    (h : v1.IsEquiv v2) (a b : F) (ha : v1 a = WithZero.exp (-1)) (hb : v2 b = WithZero.exp (-1))
    (x : F) : v1 x = v2 x := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact WithZero.exp_ne_zero ha.symm
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact WithZero.exp_ne_zero hb.symm
  have hlt : ∀ r s : F, v1 r < v1 s ↔ v2 r < v2 s := fun r s => by
    rw [← not_le, ← not_le, h s r]
  have hval : ∀ y : F, y ≠ 0 → v2 y = WithZero.exp (WithZero.log (v2 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have hval1 : ∀ y : F, y ≠ 0 → v1 y = WithZero.exp (WithZero.log (v1 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have ha2 : v2 a = WithZero.exp (-1) := by
    have h1 : v2 a < 1 := by
      rw [← map_one v2, ← hlt, map_one, ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h2 : v1 b < 1 := by
      rw [← map_one v1, hlt, map_one, hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h3 : ¬ v1 b < v1 a := by
      intro h3
      rw [hlt, hb] at h3
      rw [hval a ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [hval a ha0, WithZero.exp_lt_exp] at h3
      omega
    have h4 : v1 b = v1 a := by
      rw [hval1 b hb0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [hval1 b hb0, ha, WithZero.exp_lt_exp] at h3
      rw [hval1 b hb0, ha, WithZero.exp_inj]
      omega
    rw [← hb]
    exact ((h.eq_iff).1 h4).symm
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set k := WithZero.log (v1 x)
  have e1 : v1 x = v1 (a ^ (-k)) := by
    rw [map_zpow₀, ha, ← WithZero.exp_zsmul, hval1 x hx]
    congr 1; simp [k]
  rw [e1, (h.eq_iff).1 e1, map_zpow₀, map_zpow₀, ha, ha2]

theorem valuation_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ x : s.v.adicCompletion (maximalRealSubfield L), Valued.v (c x) = Valued.v x := by
  intro L _ _ _ s c hc hci x
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have ho : IsOpenMap c :=
    AddMonoidHom.isOpenMap_of_sigmaCompact c.toAddEquiv.toAddMonoidHom c.surjective hc
  have hc' : Continuous c.symm := c.toEquiv.continuous_symm_iff.2 ho
  let v' : Valuation (s.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)) :=
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).comap c.toRingHom
  have hE : v'.IsEquiv Valued.v := by
    rw [Valuation.isEquiv_iff_val_lt_one]
    intro y
    refine ⟨fun h => ?_, fun h => GlobalTheory.ConjParahoric.val_lt_one_map c.toRingHom hc h⟩
    simpa using GlobalTheory.ConjParahoric.val_lt_one_map c.symm.toRingHom hc' h
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  obtain ⟨ϖ, hϖ⟩ := s.w.valuation_exists_uniformizer L
  have h1 : v' (s.i ϖ) = WithZero.exp (-1) := by
    show Valued.v (c (s.i ϖ)) = _
    rw [hci, ReciprocityTheory.Aut.adic_valued_algebraMap, hϖ]
  have h2 : Valued.v (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) π) =
      WithZero.exp (-1) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  exact eq_of_isEquiv v' Valued.v hE _ _ h1 h2 x

end GlobalTheory.SplitConjVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_completionIso_preserves_valuation : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ x : s.v.adicCompletion (maximalRealSubfield L), Valued.v (c x) = Valued.v x := by
  first | exact @GlobalTheory.SplitConjVal.valuation_eq | exact GlobalTheory.SplitConjVal.valuation_eq | (intros; apply GlobalTheory.SplitConjVal.valuation_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumExist

open scoped TensorProduct

theorem isCMExt (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

theorem mem_tensInt_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v) ↔
      Algebra.TensorProduct.comm F E (v.adicCompletion F) x ∈ GlobalTheory.AdelicU.intLoc F E v := by
  constructor
  · intro hx
    have hle : Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v) ≤
        (GlobalTheory.AdelicU.intLoc F E v).comap (Algebra.TensorProduct.comm F E (v.adicCompletion F)).toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · show Algebra.TensorProduct.comm F E _ (((a : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ GlobalTheory.AdelicU.intLoc F E v
        rw [Algebra.TensorProduct.comm_tmul]
        exact GlobalTheory.AdelicU.tmul_mem_intLoc (one_mem _) a
      · show Algebra.TensorProduct.comm F E _ ((1 : E) ⊗ₜ[F] y) ∈ GlobalTheory.AdelicU.intLoc F E v
        rw [Algebra.TensorProduct.comm_tmul]
        have := GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) hy (1 : 𝓞 E)
        simpa using this
    exact hle hx
  · intro hx
    have h := GlobalTheory.AdelicU.intLoc_induction
      (p := fun y => (Algebra.TensorProduct.comm F E (v.adicCompletion F)).symm y ∈
        Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v))
      (fun a ha z => by
        have e1 : (Algebra.TensorProduct.comm F E (v.adicCompletion F)).symm (a ⊗ₜ[F] (z : E)) =
            ((z : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rfl
        rw [e1]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(z : E), z, rfl⟩, rfl⟩))
          (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)))
      (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun y hy => by rw [map_neg]; exact neg_mem hy) hx
    simpa using h

theorem exists_inertDatum : ∀ (D : D7) (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))),
    (∀ s : SplitPlace D.host.E, s.v ≠ v) → ∃ w : HeightOneSpectrum (𝓞 D.host.E), NG.OverPl w v ∧
      ¬ IsSplitPl D.host w ∧ Nonempty (InertDatum D.host.E n v w) := by
  intro D n v hv
  classical
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by
    rw [hQv.over, h0]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _))⟩
  have hov : NG.OverPl w v := hQv.over.symm
  have hunder : w.under (𝓞 (maximalRealSubfield D.host.E)) = v := HeightOneSpectrum.ext hov
  have key : ∀ x ∈ w.asIdeal, IsCMField.ringOfIntegersComplexConj D.host.E x ∈ w.asIdeal := by
    intro x hx
    by_contra hc
    have hspl : IsSplitPl D.host w := ⟨x, hx, fun y hy hym => hc (by
      have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
        apply RingOfIntegers.ext
        rw [hy, IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']
      simpa [this] using hym)⟩
    obtain ⟨s, ϖ, hs, hϖ⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hspl
    apply hv s
    apply HeightOneSpectrum.ext
    rw [← s.w_under, ← hov]
    ext a
    have ha : D.host.conj ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) := by
      rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
      exact congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ((IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩)
    exact (hs _ _ ha.symm).symm
  have hnsp : ¬ IsSplitPl D.host w := by
    rintro ⟨x, hx, hy⟩
    exact hy _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']) (key x hx)
  have hnsa : ¬ GlobalTheory.UnitaryBC.IsSplitAt w := by
    rintro ⟨u, hne, hu⟩
    apply hne
    apply HeightOneSpectrum.ext
    apply u.isMaximal.eq_of_le w.isPrime.ne_top
    intro x hx
    by_contra hxw
    have hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) =
        x * IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      simp [IsCMField.coe_ringOfIntegersComplexConj, mul_comm]
    obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hcom := congrArg HeightOneSpectrum.asIdeal hu
    change u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) at hcom
    have hp : a ∈ u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      change algebraMap _ _ a ∈ u.asIdeal
      rw [ha]; exact u.asIdeal.mul_mem_right _ hx
    rw [hcom] at hp
    change algebraMap _ _ a ∈ w.asIdeal at hp
    rw [ha] at hp
    rcases w.isPrime.mem_or_mem hp with h | h
    · exact hxw h
    · apply hxw
      have hh := key _ h
      have he : IsCMField.ringOfIntegersComplexConj D.host.E (IsCMField.ringOfIntegersComplexConj D.host.E x) = x := by
        apply RingOfIntegers.ext
        simp [IsCMField.coe_ringOfIntegersComplexConj]
      rwa [he] at hh
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield D.host.E) D.host.E v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w (GlobalTheory.DefiniteBC.host_unramified D.host w) hnsa
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj D.host.E).toAlgHom hw hunder
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt D.host.E) hw hc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov D.host.E w = Formalism.UG.intL (w.adicCompletion D.host.E) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield D.host.E) D.host.E
    (v.adicCompletion (maximalRealSubfield D.host.E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨w, hov, hnsp, ⟨⟨e, c, ϖ, k, ?_, hU, ?_, ?_, ?_⟩⟩⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj D.host.E).toAlgHom _ x)) =
      c (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumExist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonsplit_place_with_inertDatum : ∀ (D : D7) (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), (∀ s : SplitPlace D.host.E, s.v ≠ v) → ∃ w : HeightOneSpectrum (𝓞 D.host.E), NG.OverPl w v ∧ ¬ IsSplitPl D.host w ∧ Nonempty (InertDatum D.host.E n v w) := by
  first | exact @GlobalTheory.InertDatumExist.exists_inertDatum | exact GlobalTheory.InertDatumExist.exists_inertDatum | (intros; apply GlobalTheory.InertDatumExist.exists_inertDatum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Pst.BridgeWD

theorem wdAt_bridge_indep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O O' _ _ _ _ _ _ Bw Bw' hj hj' a r hc hr hr'
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge l P AI hT ι E Ω A w O O' Bw Bw' h hj hj' a r hc hr hr'

end GlobalTheory.Pst.BridgeWD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_independent_of_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  first | exact @GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep | exact GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep | (intros; apply GlobalTheory.Pst.BridgeWD.wdAt_bridge_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.EigTwist

open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def sumL (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) : Σ m : ℕ, Γ →* GL (Fin m) K :=
  L.foldr (fun p s => ⟨p.1 + s.1, Formalism.MainNotions.SumRepresentations.At.sumRep p.2 s.2⟩) ⟨0, 1⟩

theorem isSSRep_sumL : ∀ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, IsSSRep p.2) →
    IsSSRep (sumL L).2
  | [], _ => GlobalTheory.BCGal.ss_zero _
  | p :: L, h => GlobalTheory.BCGal.ss_sumRep _ _ (h p List.mem_cons_self)
      (isSSRep_sumL L fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem charpoly_sumRep {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K).charpoly =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K).charpoly *
        ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K).charpoly := by
  rw [GlobalTheory.BCGal.sumRep_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]

theorem charpoly_sumL : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ),
    (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod
  | [], g => by
    rw [List.map_nil, List.prod_nil]
    exact Polynomial.eq_one_of_monic_natDegree_zero (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; rfl)
  | p :: L, g => by
    rw [List.map_cons, List.prod_cons, ← charpoly_sumL L g]
    exact charpoly_sumRep p.2 (sumL L).2 g

theorem sumRep_mulVec_inl {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (i : Fin a) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inl i)) =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inl)) i := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem sumRep_mulVec_inr {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (j : Fin b) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inr j)) =
      (((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inr)) j := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem eigen_pair (χ : Γ →* Kˣ) {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K)
    (w : Fin (a + b) → K) (hw : w ≠ 0)
    (he : ∀ g, ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) :
    (∃ v : Fin a → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ v = ((χ g : Kˣ) : K) • v) ∨
    (∃ v : Fin b → K, v ≠ 0 ∧ ∀ g, ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ v = ((χ g : Kˣ) : K) • v) := by
  by_cases h1 : w ∘ finSumFinEquiv ∘ Sum.inl = 0
  · right
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inr, fun h2 => hw ?_, fun g => ?_⟩
    · funext j
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
      rcases s with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    · funext j
      have h3 := congrFun (he g) (finSumFinEquiv (Sum.inr j))
      rw [sumRep_mulVec_inr] at h3
      rw [h3]
      simp
  · left
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inl, h1, fun g => ?_⟩
    funext i
    have h3 := congrFun (he g) (finSumFinEquiv (Sum.inl i))
    rw [sumRep_mulVec_inl] at h3
    rw [h3]
    simp

theorem eigen_sumL (χ : Γ →* Kˣ) : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (w : Fin (sumL L).1 → K),
    w ≠ 0 → (∀ g, (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K) *ᵥ v = ((χ g : Kˣ) : K) • v := by
  intro L
  induction L with
  | nil =>
    intro w hw _
    exact (hw (funext fun i => (Nat.not_lt_zero _ i.2).elim)).elim
  | cons p L ih =>
    intro w hw he
    rcases eigen_pair χ p.2 (sumL L).2 w hw he with ⟨v, hv0, hv⟩ | ⟨v, hv0, hv⟩
    · exact ⟨p, List.mem_cons_self, v, hv0, hv⟩
    · obtain ⟨q, hq, u, hu0, hu⟩ := ih v hv0 hv
      exact ⟨q, List.mem_cons_of_mem _ hq, u, hu0, hu⟩

theorem eigen_transfer {n m : ℕ} (ρ : Γ →* GL (Fin n) K) (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ)
    (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly)
    (χ : Γ →* Kˣ) (v : Fin n → K) (hv0 : v ≠ 0)
    (hv : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v = ((χ g : Kˣ) : K) • v) :
    ∃ w : Fin m → K, w ≠ 0 ∧ ∀ g, ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ w = ((χ g : Kˣ) : K) • w := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  refine ⟨((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v, fun h0 => hv0 ?_, fun g => ?_⟩
  · have h1 := congrArg (fun u => ((P : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ u) h0
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
  · rw [Matrix.mulVec_mulVec, hP g]
    have e : ((P⁻¹ * ρ g * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) * ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]

end GlobalTheory.EigTwist


open GlobalTheory.EigTwist in
theorem GlobalTheory.eigenCharTwist_holds : EigenCharTwist := by
  intro K _ _ Γ _ n ρ L χ hρ hL hc hv
  obtain ⟨v, hv0, hv⟩ := hv
  have hS := isSSRep_sumL L hL
  have hcS : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly :=
    fun g => (hc g).trans (charpoly_sumL L g).symm
  obtain ⟨w, hw0, hw⟩ := eigen_transfer ρ (sumL L).2 hρ hS hcS χ v hv0 hv
  exact eigen_sumL χ L w hw0 hw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConj

open Matrix
open Formalism.UG (bc GLint)

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

section Pure

variable {K : Type} [Field K] {n : ℕ}

theorem inv_val_of_diagonal {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0) :
    (d⁻¹ : GL (Fin n) K).val = Matrix.diagonal fun i => (D i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hd, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with i
  exact mul_inv_cancel₀ (hD i)

theorem conj_diag_apply {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0)
    (g : GL (Fin n) K) (p q : Fin n) : (d * g * d⁻¹).val p q = D p * g.val p q * (D q)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, inv_val_of_diagonal hd hD, hd, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_GLint_of {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) :
    x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable (v : Valuation K (WithZero (Multiplicative ℤ))) {r : ℕ} {ϖ : K}

theorem conj_le_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (h2 : ∀ q p : Fin n, p.val < r → q ≠ p → v (M q p) < 1) (p q : Fin n) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) ≤ 1 := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [map_mul, map_mul, map_inv₀]
  by_cases hp : (p : ℕ) < r <;> by_cases hq : (q : ℕ) < r <;>
    simp only [hp, hq, if_true, if_false, map_one, inv_one, one_mul, mul_one, hϖ]
  · exact h1 q p
  · have hqp : q ≠ p := fun e => hq (e ▸ hp)
    calc v (M q p) * (WithZero.exp (-1))⁻¹ ≤ WithZero.exp (-1) * (WithZero.exp (-1))⁻¹ :=
          mul_le_mul' (le_exp_neg_one_of_lt_one (h2 q p hp hqp)) le_rfl
      _ = 1 := mul_inv_cancel₀ hne
  · calc WithZero.exp (-1) * v (M q p) ≤ 1 * 1 := mul_le_mul' exp_neg_one_lt_one.le (h1 q p)
      _ = 1 := one_mul 1
  · rw [mul_comm (WithZero.exp (-1)), mul_assoc, mul_inv_cancel₀ hne, mul_one]; exact h1 q p

theorem conj_lower_lt_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (p q : Fin n) (hp : r ≤ p.val) (hq : q.val < r) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) < 1 := by
  rw [if_neg (not_lt.2 hp), if_pos hq, inv_one, mul_one, map_mul, hϖ]
  calc WithZero.exp (-1) * v (M q p) ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl (h1 q p)
    _ < 1 := by rw [mul_one]; exact exp_neg_one_lt_one

end Pure

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem valued_lt_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem valued_le_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem facts_of_mem (s : SplitPlace L) (r t : ℕ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (a : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)))
    (ha : Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t) :
    (∀ i j, Valued.v (a.val i j) ≤ 1) ∧
      ∀ q p : Fin (r + t), p.val < r → Valued.v (a.val q p - if q = p then 1 else 0) < 1 := by
  obtain ⟨hK, hcol⟩ := ha
  refine ⟨fun i j => ?_, fun q p hp => ?_⟩
  · have := val_le_one_of_mem_KO hK i j
    rw [valued_le_one_iff_w] at this
    simpa [hc] using this
  · have := hcol q ⟨p, hp⟩
    have e : Fin.castAdd t (⟨p, hp⟩ : Fin r) = p := Fin.ext rfl
    rw [e, valued_lt_one_iff_w] at this
    have e2 : ((Matrix.GeneralLinearGroup.map c.toRingHom a).val - 1) q p =
        c (a.val q p - if q = p then 1 else 0) := by
      by_cases h : q = p <;> simp [Matrix.one_apply, h]
    rw [e2, hc] at this
    exact this

end Place

end GlobalTheory.BlockConj

namespace GlobalTheory.BlockConj

open Formalism.UG (GLint)

theorem conj_transpose_inv_uniRT : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → NG.UniRT s r (d * b * d⁻¹) ∧ Valued.v (NG.supDiag s r (d * b * d⁻¹)) < 1 := by
  intro L _ _ _ s r t c hc a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hD : ∀ i : Fin (r + t), (if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) ≠ 0 := by
    intro i; split_ifs
    · exact one_ne_zero
    · exact hϖ0
  obtain ⟨ha1, ha2⟩ := facts_of_mem s r t c hc a ha
  obtain ⟨hi1, hi2⟩ := facts_of_mem s r t c hc a⁻¹ (by rw [map_inv]; exact (blockGrp _ r t).inv_mem ha)
  have ha2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v (a.val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using ha2 q p hp
  have hi2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v ((a⁻¹).val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using hi2 q p hp
  have hbinv : (b⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val = a.val.transpose := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hb, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hN : ∀ p q, (d * b * d⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * (a⁻¹).val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    intro p q; rw [conj_diag_apply hd hD, hb, Matrix.transpose_apply]
  have hNi : ∀ p q, ((d * b * d⁻¹)⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * a.val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    have e : (d * b * d⁻¹)⁻¹ = d * b⁻¹ * d⁻¹ := by group
    intro p q; rw [e, conj_diag_apply hd hD, hbinv, Matrix.transpose_apply]

  have hUL : ∀ p q : Fin (r + t), p.val < r → q.val < r → (d * b * d⁻¹).val p q = (a⁻¹).val q p := by
    intro p q hp hq; rw [hN, if_pos hp, if_pos hq, inv_one, one_mul, mul_one]
  refine ⟨⟨⟨mem_GLint_of (fun i j => ?_) (fun i j => ?_), fun p q hp hq => ?_⟩, fun p q hp hq => ⟨fun hlt => ?_, fun he => ?_⟩⟩, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hN]
    exact conj_le_one Valued.v hϖ hi1 hi2' i j
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hNi]
    exact conj_le_one Valued.v hϖ ha1 ha2' i j
  · rw [hN]; exact conj_lower_lt_one Valued.v hϖ hi1 p q hp hq
  · rw [hUL p q hp hq]; exact hi2' q p hp (Fin.ne_of_lt hlt)
  · subst he; rw [hUL p p hp hp]; simpa using hi2 p p hp
  · unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · rw [hUL p q (by omega) h.2]
      exact hi2' q p (by omega) (fun e => by rw [e] at h; omega)
    · rw [map_zero]; exact zero_lt_one

end GlobalTheory.BlockConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoricStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagUniformiserConj_transposeInv_mem_upperParahoric : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → NG.UniRT s r (d * b * d⁻¹) ∧ Valued.v (NG.supDiag s r (d * b * d⁻¹)) < 1 := by
  first | exact @GlobalTheory.BlockConj.conj_transpose_inv_uniRT | exact GlobalTheory.BlockConj.conj_transpose_inv_uniRT | (intros; apply GlobalTheory.BlockConj.conj_transpose_inv_uniRT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeTame

theorem conjSP_w_of_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), IsConjPl D.host w s.w → (GlobalTheory.TypeTame.conjSP s).w = w ∧ ∀ x : D.host.E, (GlobalTheory.TypeTame.conjSP s).i x = s.i (D.host.conj x) := by
  intro D s w hw
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  refine ⟨?_, fun x => by rw [conjSP_i, hc]⟩
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ∀ e : 𝓞 D.host.E, ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) :=
    fun e => rfl
  ext x
  have h1 : x ∈ (conjSP s).w.asIdeal ↔ c x ∈ s.w.asIdeal := by
    show Valued.v ((conjSP s).i (x : D.host.E)) < 1 ↔ Valued.v (s.i ((c x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [conjSP_i, hce]
  rw [h1, hw x (c x) (by rw [hce, hc])]

end GlobalTheory.TypeTame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), IsConjPl D.host w s.w → (GlobalTheory.TypeTame.conjSP s).w = w ∧ ∀ x : D.host.E, (GlobalTheory.TypeTame.conjSP s).i x = s.i (D.host.conj x) := by
  first | exact @GlobalTheory.TypeTame.conjSP_w_of_isConjPl | exact GlobalTheory.TypeTame.conjSP_w_of_isConjPl | (intros; apply GlobalTheory.TypeTame.conjSP_w_of_isConjPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GalRepRankTwo
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp


end GlobalTheory.GalFirstClause
end
end

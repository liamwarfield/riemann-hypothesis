module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriContractionHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRational
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegralEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.CuspRep
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem v_thetaGL_apply (w : Pl E) (a : ℕ) (g : GLw a w) (i j : Fin a) :
    Valued.v ((thetaGL a (cj w) g).val i j) = Valued.v ((g⁻¹).val j.rev i.rev) := by
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, GlobalTheory.PrincCong.v_cj, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]

theorem thetaGL_mem_KGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ GlobalTheory.LFun.KGL w (n := a)) :
    thetaGL a (cj w) k ∈ GlobalTheory.LFun.KGL w (n := a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a k).1 hk
  refine (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _

theorem thetaGL_mem_iwGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ iwGL a w) :
    thetaGL a (cj w) k ∈ iwGL a w := by
  obtain ⟨h1, h2, -⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k).1).1 hk
  obtain ⟨-, -, h3⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k⁻¹).1).1 (inv_mem hk)
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a _).1).2 ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _
  · rw [v_thetaGL_apply]
    exact h3 _ _ (Fin.rev_lt_rev.2 hij)

theorem isCompact_support_dcos (w : Pl E) (a : ℕ) (t : GLw a w) :
    IsCompact {g : GLw a w | dcos a w t g ≠ 0} := by
  have hI : IsCompact (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin a)
  have hS : IsCompact ((fun p : GLw a w × GLw a w => p.1 * t * p.2) ''
      ((iwGL a w : Set (GLw a w)) ×ˢ (iwGL a w : Set (GLw a w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  convert hS using 1
  ext g
  simp only [Set.mem_setOf_eq, dcos, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
  constructor
  · intro h
    by_contra hn
    refine h (if_neg ?_)
    rintro ⟨x, hx, y, hy, rfl⟩
    exact hn ⟨x, y, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    rw [if_pos ⟨x, hx, y, hy, rfl⟩]
    exact one_ne_zero

end GlobalTheory.CompanionTheory.IwFacts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.IwahoriContraction

open PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_iwGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ iwGL n w ↔ g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) (w.adicCompletion E) := by
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1]
  show _ ↔ g ∈ PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.adicCompletion E) ∧ _
  rw [GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff, and_assoc]
  simp only [GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff, GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff]


omit [IsCMField E] in
theorem v_le_of_ordL_eq_one (w : Pl E) {ϖ x : w.adicCompletion E} (h0 : ϖ ≠ 0) (h1 : ordL ϖ = 1)
    (hx : Valued.v x < 1) : Valued.v x ≤ Valued.v ϖ := by
  have h0' : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0'
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm
    omega
  by_cases hx0 : Valued.v x = 0
  · rw [hx0]
    exact zero_le
  obtain ⟨c, hc⟩ := WithZero.ne_zero_iff_exists.1 hx0
  rw [← hu, ← hc]
  rw [← hc] at hx
  have hc1 : c < 1 := by exact_mod_cast hx
  have hc2 : Multiplicative.toAdd c < 0 := hc1
  have : c ≤ u := by
    show Multiplicative.toAdd c ≤ Multiplicative.toAdd u
    omega
  exact_mod_cast this


omit [IsCMField E] in
theorem v_lt_one_of_ordL_eq_one (w : Pl E) {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (h1 : ordL ϖ = 1) :
    Valued.v ϖ < 1 := by
  have h0' : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0'
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm
    omega
  rw [← hu]
  have : u < 1 := by
    show Multiplicative.toAdd u < 0
    omega
  exact_mod_cast this


omit [IsCMField E] in
theorem torusO_subset_TO (w : Pl E) (n : ℕ) (t : GLw n w)
    (ht : t ∈ PositivityTheory.Rg.Tf.Loc.torusO (n := n) (w.adicCompletion E)) : t ∈ TO n w := by
  obtain ⟨hu, hd⟩ := ht
  obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff t).1 hu
  refine ⟨hd, fun i => ?_⟩
  have hmul : ((t⁻¹ : GLw n w).val * t.val) i i = 1 := by
    have : (t⁻¹ : GLw n w).val * t.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => by rw [hd j i hj, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)] at hmul
  have ha := (GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h1 i i)
  have hb := (GlobalTheory.CompanionTheory.IwEntries.rel_le_one_iff w _).1 (h2 i i)
  have hv : Valued.v ((t⁻¹ : GLw n w).val i i) * Valued.v (t.val i i) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v ((t⁻¹ : GLw n w).val i i) * Valued.v (t.val i i) := hv.symm
    _ ≤ 1 * Valued.v (t.val i i) := mul_le_mul' hb le_rfl
    _ = _ := one_mul _

theorem contr_id : PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw.P_contr_id := by
  intro E _ _ _ w ϖ hϖ n y hy δ hδ
  have hδ' : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ y * z := by
    by_contra h
    exact hδ (if_neg h)
  obtain ⟨a, ha, b, hb, hab⟩ := hδ'
  obtain ⟨⟨U, hU⟩, -, hcpt, -⟩ := GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_compact_open_galois.1 (w.adicCompletion E) n
  have hcomp : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hmap : ∀ g : GL (Fin n) (w.adicCompletion E),
      Matrix.GeneralLinearGroup.map ((RingEquiv.refl (w.adicCompletion E) : _ ≃+* _) : _ →+* _) g = g := by
    intro g
    apply Units.ext
    ext i j
    rfl
  have hρ1 : ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 (v_lt_one_of_ordL_eq_one w hϖ0 hϖ.1)
  have hunif : ∀ x : w.adicCompletion E, ValuativeRel.valuation (w.adicCompletion E) x < 1 →
      ValuativeRel.valuation (w.adicCompletion E) x ≤
        ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := fun x hx =>
    (hequiv.le_iff_le).2 (v_le_of_ordL_eq_one w hϖ0 hϖ.1 ((GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).1 hx))
  let e : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have he : ∀ i, e i ≠ 0 := fun i => Units.ne_zero _
  have hc : ∀ i l, i < l → ValuativeRel.valuation (w.adicCompletion E) (e i) ≤
      ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) *
        ValuativeRel.valuation (w.adicCompletion E) (e l) := fun i l h => by
    obtain ⟨c, hcn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)
    have hyi : y i = y l + ((c + 1 : ℕ) : ℤ) := by push_cast; omega
    have hei : e i = e l * (ϖ : w.adicCompletion E) ^ (c + 1) := by
      show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _
      rw [hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hei, map_mul, map_pow, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ (c + 1)
        ≤ ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ 1 :=
          pow_le_pow_right_of_le_one' hρ1.le (Nat.succ_le_succ (Nat.zero_le c))
      _ = _ := pow_one _
  have hx : ((tdiag ϖ y : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal e := by
    rw [tdiag, GlobalTheory.SmGL.val_diagT]
  have hδI : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (tdiag ϖ y : GLw n w) :=
    ⟨a, (mem_iwGL_iff w n a).1 ha, b, (mem_iwGL_iff w n b).1 hb, hab⟩
  obtain ⟨m, hm, t, ht, h⟩ := GlobalTheory.CompanionTheory.TwContraction.contraction U hU hcpt (RingEquiv.refl _)
    (fun _ => rfl) (fun g hg => by rw [hmap]; exact hg) _ hρ1 hunif e he hc _ hx δ hδI
  rw [hmap] at h
  exact ⟨m, (mem_iwGL_iff w n m).2 hm, t, torusO_subset_TO w n t ht, h⟩

end GlobalTheory.CompanionTheory.IwahoriContraction
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isArithVar_mpStr (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem dim_of_isArithVar (hD : GlobalTheory.CompanionTheory.MixZ.PtDict) {m : ℕ} {n : Fin (m + 1) → ℕ} {Z : Scheme.{0}} [IsIntegral Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {d : ℕ} (hd : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) d) :
    topologicalKrullDim Z = d := by
  obtain ⟨d', hd'⟩ := (isArithVar_mpStr m n).exists_dim_eq i
  obtain ⟨-, -, h₃, -⟩ := hD m n Z i d' hd'
  have h₄ := h₃ hd.2.2.1
  have e : d' + Fintype.card (Fin (m + 1)) = d + Fintype.card (Fin (m + 1)) := by
    exact_mod_cast h₄.2.2.2.symm.trans hd.2.2.2
  rw [hd', Nat.add_right_cancel e]

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExists
noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuOpen

theorem isOpen_ker_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) (w : HeightOneSpectrum (𝓞 L)) :
    IsOpen ((χ.loc w).ker : Set (w.adicCompletion L)ˣ) :=
  GroundTheory.Global.isOpen_ker_of_continuous w GroundTheory.Global.Complex.units_noSmallSubgroups (χ.loc w)
    (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w))

theorem unrChar_apply_of_isUnitAt {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (α : ℂˣ)
    (x : (w.adicCompletion L)ˣ) (hx : IsUnitAt w x) : GlobalTheory.SmGL.unrChar (w.adicCompletion L) α x = 1 := by
  rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion]
  have hx' : Valued.v (x : w.adicCompletion L) = 1 := hx
  rw [hx']
  simp

end GlobalTheory.CompanionTheory.MuOpen


open GlobalTheory.CompanionTheory.MuOpen in
theorem GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  intro h E _ _ _ hU
  obtain ⟨μ, e, hμ⟩ := h E hU
  refine ⟨μ, e, hμ, fun w hw x hx => ?_, GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ |>.1, fun w => isOpen_ker_loc μ w⟩
  rw [hμ.2.2.1 w hw]
  exact unrChar_apply_of_isUnitAt w _ x hx

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExistsStatement
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_character_exists : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  first | exact @GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | exact GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | (intros; apply GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerImageNoDualComponent
noncomputable section

open scoped NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SWLaw (zeroSp)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

theorem mul_eq_one_of_gram {R : Type} [CommRing R] {c x G Gi : R} (hg : G * Gi = 1) (h : c * (G * x) = G) : c * x = 1 := by
  linear_combination Gi * h + (1 - c * x) * hg

theorem nnreal_eq_one_of_sq {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  rw [← sq] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (n := 2) (by norm_num)).1 h

theorem absA_eq_one_of_conj (u : (AE D)ˣ) (h : conjUnit D.sp.cm.sig u * u = 1) : absA D u = 1 := by
  have h3 := congrArg (absE D.host.F D.host.E) h
  rw [map_mul, absE_conjUnit, map_one] at h3
  exact nnreal_eq_one_of_sq h3

theorem absA_det_matHom (g : GA D T₀) : absA D (Matrix.GeneralLinearGroup.det (matHom T₀ g)) = 1 := by
  have hg : (gA T₀).det * (giA T₀).det = 1 := by rw [← Matrix.det_mul, gA_mul_giA, Matrix.det_one]
  have h := congrArg Matrix.det (mt_unitary T₀ g)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hadj : (adj (mt T₀ g)).det = cA D (mt T₀ g).det := by
    rw [adj, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [hadj] at h
  have h2 : conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom T₀ g)) *
      Matrix.GeneralLinearGroup.det (matHom T₀ g) = 1 := Units.ext (mul_eq_one_of_gram hg h)
  exact absA_eq_one_of_conj _ h2

section Blocks

variable {R : Type} [CommRing R] {n a b : ℕ}

end Blocks

end GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
open ResidueKilled.Tr
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.TChartProof

open Matrix

theorem mat_mul' {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one' {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem blkA_mul_of_lowerLeft {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (hY : ∀ i j : Fin n, Y (Fin.natAdd n i) (Fin.castAdd n j) = 0) : blkA (X * Y) = blkA X * blkA Y := by
  ext i j
  simp only [blkA, Matrix.mul_apply, Fin.sum_univ_add, hY, mul_zero, Finset.sum_const_zero, add_zero,
    toBlocks₁₁, Matrix.of_apply, submatrix_apply, finSumFinEquiv_apply_left]

theorem blkA_one' {R : Type} [CommRing R] {n : ℕ} : blkA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkA, toBlocks₁₁, Matrix.one_apply]

theorem exists_gl_blkA {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) :
    ∃ a : GL (Fin n) (AE D), blkA (mat g) = a.1 := by
  have hg' : g⁻¹ ∈ P D n := inv_mem hg
  have e₁ : blkA (mat g) * blkA (mat g⁻¹) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg'), ← mat_mul', mul_inv_cancel, mat_one', blkA_one']
  have e₂ : blkA (mat g⁻¹) * blkA (mat g) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg), ← mat_mul', inv_mul_cancel, mat_one', blkA_one']
  exact ⟨⟨_, _, e₁, e₂⟩, rfl⟩

theorem tChart : TChart := by
  intro hDict hDI hStd D χ V a hMaj
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D V m0 hm0
  obtain ⟨p, hp⟩ := hp0 V a hMaj κ hκ
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D V m0 hm0 κ hκ
  obtain ⟨Ψ, h1, h2, h3, h4⟩ := hStd hDict hDI D χ V.rank
  have hG := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D V m0 hm0 κ hκ
  have hP := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D V m0 hm0 κ hκ
  let κt : GA D (dblSp V) ≃ₜ* G D V.rank :=
    { κ with continuous_toFun := hc, continuous_invFun := hc' }
  have hκt : ∀ g, κt g = κ g := fun _ => rfl
  refine ⟨κt.trans Ψ, p, fun g => ?_, fun g => ?_, fun k => ?_, fun q => ?_, fun x => ?_⟩
  · exact (hG g).trans (h1 (κ g))
  · exact (hP g).trans (h2 (κ g))
  · exact (hp k).trans (h3 _)
  · obtain ⟨b, hb⟩ := exists_gl_blkA ((hP q).1 q.2)
    have e₁ := GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D V m0 hm0 κ hκ q b hb
    have e₂ := h4 (κ q) b hb
    rw [e₁]
    exact e₂
  · have e := (hDict D.host.F D.host.E).2.2.2.2 x
    show Real.log _ = _
    rw [e]

end GlobalTheory.CompanionTheory.TChartProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExistsStatement
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_section_exists : TChart := by
  first | exact @GlobalTheory.CompanionTheory.TChartProof.tChart | exact GlobalTheory.CompanionTheory.TChartProof.tChart | (intros; apply GlobalTheory.CompanionTheory.TChartProof.tChart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
noncomputable section

namespace GlobalTheory.CompanionTheory.ScalWall

open PositivityTheory.RgEis ResidueKilled.Tr GlobalTheory.CompanionTheory.SiegelFrame

theorem pos_eq_norm_cosetSum {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (l : G' → ℝ) (hc : Conv Γ' P' l)
    (hl : ∀ γ ∈ Γ', γ ∈ P' → ∀ y, l (γ * y) = l y) (g : G) :
    pos Γ' P' l (Φ g) = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp (l (Φ x)) : ℂ)) g‖ := by
  have hs : HasSum (fun q : PositivityTheory.RgEis.Cos P' Γ' => Real.exp (l (PositivityTheory.RgEis.rep q * Φ g)))
      (PositivityTheory.RgEis.pos Γ' P' l (Φ g)) := (hc (Φ g)).hasSum
  have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ Γ P Γ' P' hΓ hP (fun y => Real.exp (l y))
    (fun γ hγ hγP y => by simp only [hl γ hγ hγP y]) (Φ g) _ hs
  have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ => ((Real.exp (l (Φ (PositivityTheory.RgEis.rep q * g))) : ℝ) : ℂ))
      ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr (by simpa only [map_mul] using h2)
  have h4 : GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (l (Φ x)) : ℝ) : ℂ)) g
      = ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) := h3.tsum_eq
  rw [h4, Complex.norm_real, Real.norm_of_nonneg (hs.nonneg fun _ => (Real.exp_pos _).le)]

theorem fin_along {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (K' : Subgroup G') (f : G → ℂ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Φ.symm k)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))) := by
  have e : (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))
      = (LinearMap.funLeft ℂ ℂ (⇑Φ.symm)) '' (Set.range fun k : K' => fun x => f (x * Φ.symm k)) := by
    rw [← Set.range_comp]
    congr 1
    funext k y
    simp [LinearMap.funLeft_apply, map_mul]
  rw [e, ← Submodule.map_span]
  exact Module.Finite.map _ _

theorem tScal : TScal := by
  unfold ResidueKilled.Tr.TScal ResidueKilled.Tr.Scal
  intro hSec hWL G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η N hK hPar hHt hΓ hP hW f hf hlaw hfin
  have hcrat : ∀ γ ∈ Γ', γ ∈ P' → c γ = 1 := by
    obtain ⟨_, _, ⟨_, _, h, _⟩⟩ := hPar
    exact h
  have hηl : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g := by
    obtain ⟨h, _, _, _⟩ := hHt
    exact h
  have hηr : ∀ γ ∈ Γ', γ ∈ P' → η γ = 0 := by
    obtain ⟨_, _, h, _⟩ := hHt
    exact h
  have hβ : PositivityTheory.RgEis.IsHt Γ' K' P' (fun g => N * η g) := by
    obtain ⟨h1, h2, h3, h4⟩ := hHt
    exact ⟨fun p hp g => by simp only [h1 p hp g, mul_add], fun g k hk => by simp only [h2 g k hk],
      fun γ hγ hγP => by simp only [h3 γ hγ hγP, mul_zero], continuous_const.mul h4⟩
  have hlaw' : ∀ p ∈ P', ∀ x : G', (fun y => f (Φ.symm y)) (p * x)
      = c p * Complex.exp (0 * ↑(η p)) * (fun y => f (Φ.symm y)) x := by
    intro p hp x
    have hp' : Φ.symm p ∈ P := (hP (Φ.symm p)).mpr (by simpa using hp)
    simp only [map_mul, zero_mul, Complex.exp_zero, mul_one]
    rw [hlaw _ hp']
    simp
  have hfin' := fin_along Φ.toMulEquiv K' f hfin
  obtain ⟨R, D, H, hD, hDz, hHd, hHc, hconv1, hconv2, hbd, hsum⟩ :=
    GlobalTheory.CompanionTheory.SiegelFrame.scalar_wall hSec hWL Γ' K' P' c η (fun g => N * η g) hK hPar hHt hβ hW
      (fun y => f (Φ.symm y)) 0 (hf.comp (map_continuous Φ.symm)) hlaw' hfin'
  refine ⟨D, fun z g => H z (Φ g), R, hD, hDz, fun g => hHd (Φ g), ?_, ?_, ?_⟩
  · exact hHc.comp (continuous_fst.prodMk ((map_continuous Φ).comp continuous_snd))
  · intro z hz g
    show H z (Φ g) = _
    have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ.toMulEquiv Γ P Γ' P' hΓ hP
      (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
      (fun γ hγ hγP y => by
        have hγ' : Φ.symm γ ∈ P := (hP (Φ.symm γ)).mpr (by simpa using hγP)
        simp only [hηl γ hγP y, hηr γ hγ hγP, zero_add, map_mul]
        rw [hlaw _ hγ']
        simp [hcrat γ hγ hγP])
      (Φ g) _ (hsum z hz (Φ g))
    have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ =>
        D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g))) (H z (Φ g)) := by
      have e : (fun q : PositivityTheory.RgEis.Cos P Γ =>
          D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g)))
          = fun q => (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
              (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g) := by
        funext q
        have hm : Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g = Φ (PositivityTheory.RgEis.rep q * g) :=
          (map_mul Φ _ _).symm
        show _ = D z * (Complex.exp ((z - 0) * ↑(η (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
          * f (Φ.symm (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
        rw [hm, sub_zero, ContinuousMulEquiv.symm_apply_apply]
      rw [e]
      exact h2
    rw [← h3.tsum_eq, tsum_mul_left]
    rfl
  · intro a b ha hb
    obtain ⟨M, hM⟩ := hbd a b ha hb
    refine ⟨M, fun z hz1 hz2 g => ?_⟩
    have hl2 : (fun x : G' => N * η x - b * η x) = fun x => (N - b) * η x := by
      funext x
      ring
    have hinv : ∀ (t : ℝ), ∀ γ ∈ Γ', γ ∈ P' → ∀ y, t * η (γ * y) = t * η y := by
      intro t γ hγ hγP y
      rw [hηl γ hγP y, hηr γ hγ hγP, zero_add]
    have e1 : PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (a * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => a * η x) (hconv1 a ha)
      (fun γ hγ hγP y => hinv a γ hγ hγP y) g
    have hc2 : PositivityTheory.RgEis.Conv Γ' P' (fun x => (N - b) * η x) := by
      rw [← hl2]
      exact hconv2 b hb
    have e2 : PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp ((N - b) * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => (N - b) * η x) hc2
      (fun γ hγ hγP y => hinv (N - b) γ hγ hγP y) g
    have key := hM z hz1 hz2 (Φ g)
    have e3 : PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)
        = PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g) := by
      rw [hl2]
    calc ‖H z (Φ g)‖ ≤ M * (PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
          + PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)) := key
      _ = _ := by
        rw [e3, e1, e2]
        try rfl

end GlobalTheory.CompanionTheory.ScalWall

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExistsStatement
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_section_exists : TScal := by
  first | exact @GlobalTheory.CompanionTheory.ScalWall.tScal | exact GlobalTheory.CompanionTheory.ScalWall.tScal | (intros; apply GlobalTheory.CompanionTheory.ScalWall.tScal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExists
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

namespace GlobalTheory.CompanionTheory.UnifFix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conj_real (x : maximalRealSubfield E) :
    IsCMField.complexConj E (algebraMap (maximalRealSubfield E) E x) = algebraMap (maximalRealSubfield E) E x := by
  exact (IsCMField.complexConj E).commutes x

theorem cj_real (w : Pl E) (x : maximalRealSubfield E) :
    GlobalTheory.BCT.cj w (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x)) =
      algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x) := by
  unfold GlobalTheory.BCT.cj
  split_ifs with h
  · rw [h.choose_spec.2, conj_real]
  · rfl

theorem valuation_up (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (x : maximalRealSubfield E) :
    w.valuation E (algebraMap (maximalRealSubfield E) E x) =
      (w.under (𝓞 (maximalRealSubfield E))).valuation (maximalRealSubfield E) x := by
  have := hU w
  have h1 := HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 (maximalRealSubfield E))) w x
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← h1, he, pow_one]

theorem neg_toAdd_unzero (a : WithZero (Multiplicative ℤ)) (h : a ≠ 0) (ha : a = WithZero.exp (-1 : ℤ)) :
    -Multiplicative.toAdd (WithZero.unzero h) = 1 := by
  subst ha
  rfl

theorem unifEx : UnifEx := by
  intro E _ _ _ hU w
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield E)
    (w.under (𝓞 (maximalRealSubfield E)))
  have hy : w.valuation E (algebraMap (maximalRealSubfield E) E π) = WithZero.exp (-1) := by
    rw [valuation_up hU w π, hπ]
  have hy0 : algebraMap (maximalRealSubfield E) E π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact WithZero.zero_ne_coe hy
  have hne : algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π) ≠ 0 :=
    (map_ne_zero _).2 hy0
  have hv : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) =
      WithZero.exp (-1) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 E) E w, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
  have hv0 : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  refine ⟨Units.mk0 _ hne, ⟨?_, ?_⟩, ?_⟩
  · show Formalism.UG.ordL (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = 1
    unfold Formalism.UG.ordL
    rw [dite_eq_right hv0]
    exact neg_toAdd_unzero _ hv0 hv
  · exact cj_real w π
  · exact hv

end GlobalTheory.CompanionTheory.UnifFix
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistsStatement
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_exists : UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.UnifFix.unifEx | exact GlobalTheory.CompanionTheory.UnifFix.unifEx | (intros; apply GlobalTheory.CompanionTheory.UnifFix.unifEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExists
noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open GlobalTheory.PrincCong (congSub mem_congSub_iff isOpen_congSub exists_mat_subset)
open GlobalTheory.LFun.ConjPlace (invT invT_val mem_iff_invT map_mem_Ov_iff)
open GlobalTheory.ThetaSatake (cw cloc)
open GlobalTheory.CompanionTheory.ThetaSatPair (embT_cw invT_symm)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.KExLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le_KGL (w : Pl E) (n k : ℕ) : congSub w n k ≤ KGL w (n := n) :=
  fun g hg => ((mem_congSub_iff w n k g).1 hg).1

theorem eventually_congSub_le (w : Pl E) (a : ℕ) (U : Subgroup (GLw a w)) (hU : IsOpen (U : Set (GLw a w))) :
    ∀ᶠ k in atTop, congSub w a k ≤ U := by
  have hVn : (U : Set (GLw a w)) ∈ 𝓝 (1 : GLw a w) := hU.mem_nhds U.one_mem
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hVn
  obtain ⟨t, htn, htV⟩ := Filter.mem_comap.1 hVn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 htn
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨N₀, hN₀⟩ := exists_mat_subset w a (Filter.inter_mem hA hB')
  filter_upwards [eventually_ge_atTop N₀] with m hm γ hγ
  have a1 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 hγ).2
  have a2 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 (inv_mem hγ)).2
  exact htV (hAB ⟨a1.1, a2.2⟩)

theorem continuous_detGL (w : Pl E) (a : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw a w → (w.adicCompletion E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_det Units.continuous_val
  · have e : (fun g : GLw a w => (((GeneralLinearGroup.det g)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) =
        fun g => ((g⁻¹ : GLw a w) : Matrix (Fin a) (Fin a) _).det := by
      funext g
      rw [← map_inv]
      rfl
    exact e ▸ Continuous.matrix_det (Units.continuous_val.comp continuous_inv)

theorem eventually_det (w : Pl E) (a : ℕ) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) :
    ∀ᶠ k in atTop, ∀ g ∈ congSub w a k, μ (GeneralLinearGroup.det g) = 1 := by
  have hU : IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw a w)) : Set (GLw a w)) :=
    hμ.preimage (continuous_detGL w a)
  filter_upwards [eventually_congSub_le w a _ hU] with k hk g hg
  exact hk hg

theorem isCompact_congSub (w : Pl E) (n k : ℕ) : IsCompact (congSub w n k : Set (GLw n w)) :=
  (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congSub w n k)) (congSub_le_KGL w n k)

theorem blocks_mem_congSub {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) {k : ℕ} (hg : blk h w m X ∈ congSub w n k) :
    m.1 ∈ congSub w a k ∧ m.2 ∈ congSub w b k := by
  obtain ⟨hK, hc⟩ := (mem_congSub_iff w n k _).1 hg
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have v := GlobalTheory.CompanionTheory.CtS.blk_val_eq h w m X
  have iv := GlobalTheory.CompanionTheory.CtS.blk_inv_val h w m X
  let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  have v11 : ∀ i j, (blk h w m X).val (e (Sum.inl i)) (e (Sum.inl j)) = m.1.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have v22 : ∀ i j, (blk h w m X).val (e (Sum.inr i)) (e (Sum.inr j)) = m.2.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have i11 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inl i)) (e (Sum.inl j)) = (m.1⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have i22 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inr i)) (e (Sum.inr j)) = (m.2⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have o11 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inl i)) (e (Sum.inl j)) =
      (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  have o22 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inr i)) (e (Sum.inr j)) =
      (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  refine ⟨(mem_congSub_iff w a k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩,
    (mem_congSub_iff w b k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩⟩
  · rw [← v11]; exact h1 _ _
  · rw [← i11]; exact h2 _ _
  · rw [← v11, ← o11]; exact hc _ _
  · rw [← v22]; exact h1 _ _
  · rw [← i22]; exact h2 _ _
  · rw [← v22, ← o22]; exact hc _ _

theorem conj_mem_congSub (w : Pl E) (n k : ℕ) {x g : GLw n w} (hx : x ∈ KGL w (n := n)) (hg : g ∈ congSub w n k) :
    x * g * x⁻¹ ∈ congSub w n k := by
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z * y * z⁻¹, (MonoidHom.normal_ker _).conj_mem y hy z, by simp only [map_mul, map_inv]⟩

theorem invT_mem_congSub {u w : Pl E} (c : u.adicCompletion E ≃+* w.adicCompletion E)
    (hc : ∀ x, Valued.v (c x) = Valued.v x) (a k : ℕ) {g : GLw a u} (hg : g ∈ congSub u a k) :
    invT c a g ∈ congSub w a k := by
  have h1 := (mem_congSub_iff u a k _).1 hg
  have h2 := (mem_congSub_iff u a k _).1 (inv_mem hg)
  refine (mem_congSub_iff w a k _).2 ⟨(mem_iff_invT c (map_mem_Ov_iff c hc) g).1 h1.1, fun i j => ?_⟩
  have e : (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      c ((1 : Matrix (Fin a) (Fin a) (u.adicCompletion E)) j i) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  rw [invT_val, e, ← map_sub, hc]
  exact h2.2 j i

theorem under_cw (w : Pl E) :
    (cw w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) (cw w) w).2
    (Or.inr (conjPl_conjSrc _ w))).symm

end GlobalTheory.CompanionTheory.KExLevel

namespace GlobalTheory.CompanionTheory.KExLevel

theorem kEx : KEx := by
  intro E _ _ _ n Sec _ R _ μ hμ L hL
  let T : Finset (Pl E) := R ∪ R.image cw
  have A : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ R, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k → m ∈ L a w := by
    intro a ha w hw
    obtain ⟨L₁, L₂, e, l1, l2⟩ := hL a (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)) w hw
    filter_upwards [eventually_congSub_le w a L₁ l1.1, eventually_congSub_le w (n - a) L₂ l2.1] with k h1 h2 m m1 m2
    rw [e]
    exact ⟨h1 m1, h2 m2⟩
  have B : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ T, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k →
        μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 := by
    intro a _ w _
    filter_upwards [eventually_det w a (μ w) (hμ w), eventually_det w (n - a) (μ w) (hμ w)] with k h1 h2 m m1 m2
    rw [map_mul, map_pow, map_pow, h1 _ m1, h2 _ m2, one_pow, one_pow, one_mul]
  obtain ⟨M, hA, hB⟩ := (((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (A a ha)).and ((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (B a ha))).exists
  have hT : ∀ w, w ∈ T → (if w ∈ T then congSub w n M else KGL w (n := n)) = congSub w n M := fun w hw => if_pos hw
  refine ⟨fun w => if w ∈ T then congSub w n M else KGL w (n := n), ⟨fun w => ?_, ?_⟩, fun w => ?_, fun w hw => ?_,
    fun a ha w hw m X hm => ?_, fun a ha w hw hs u hc m X hm => ?_⟩
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isOpen_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1
  · refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    refine hw ?_
    have h' : w ∉ T := h
    simp only [if_neg h']
    exact le_rfl
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isCompact_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  · refine if_neg fun h => ?_
    rcases Finset.mem_union.1 h with h | h
    · exact hw w h rfl
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact hw r hr (under_cw r).symm
  · have hwT : w ∈ T := Finset.mem_union_left _ hw
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos hwT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ w m X hm
    exact ⟨hA a ha' w hw m b1 b2, hB a ha' w hwT m b1 b2⟩
  · have hu : u = cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
    have huT : u ∈ T := Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hw, hu.symm⟩)
    have hw' : w = cw u := by rw [hu]; exact (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos huT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ u m X hm
    clear hu hc
    subst hw'
    have hv : ∀ x, Valued.v ((cloc u).symm x) = Valued.v x := fun x => by
      have := (GlobalTheory.CuspRep.conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 ((cloc u).symm x)
      have e : GlobalTheory.CuspRep.conjLoc (IsCMField.complexConj E).toRingEquiv u ((cloc u).symm x) = x :=
        (cloc u).apply_symm_apply x
      rw [e] at this
      exact this.symm
    let p : ∀ c : ℕ, GLw c u → GLw c (cw u) := fun c g =>
      (invT (cloc u) c).symm ((PhiU c (u.adicCompletion E))⁻¹ * g * PhiU c (u.adicCompletion E))
    have hp : ∀ c (g : GLw c u), g ∈ congSub u c M → p c g ∈ congSub (cw u) c M := fun c g hg => by
      have hk : (PhiU c (u.adicCompletion E))⁻¹ ∈ KGL u (n := c) := inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ c)
      have h1 := conj_mem_congSub u c M hk hg
      rw [inv_inv] at h1
      change (invT (cloc u) c).symm _ ∈ _
      rw [invT_symm]
      exact invT_mem_congSub (cloc u).symm hv c M h1
    have he : ∀ c (g : GLw c u), embW c u g = embT c (cw u) (p c g) := fun c g => by
      rw [embT_cw]
      simp only [p, MulEquiv.apply_symm_apply]
      congr 1
      group
    exact ⟨hB a ha' u huT m b1 b2, (p a m.1, p (n - a) m.2), hA a ha' (cw u) hw _ (hp _ _ b1) (hp _ _ b2),
      he _ _, he _ _⟩

end GlobalTheory.CompanionTheory.KExLevel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExistsStatement
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_level_exists : KEx := by
  first | exact @GlobalTheory.CompanionTheory.KExLevel.kEx | exact GlobalTheory.CompanionTheory.KExLevel.kEx | (intros; apply GlobalTheory.CompanionTheory.KExLevel.kEx <;> assumption)
end
end

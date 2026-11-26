module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaRatInv

theorem invOf_two_eq' {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] :
    ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

theorem thetaSum_schr_rat_add {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (a b : κ → F)
    (w : (κ → AF F) × (κ → AF F)) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ ((fun i => algebraMap F (AF F) (a i), fun i => algebraMap F (AF F) (b i)) + w) Φ) =
      ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ (fun i => algebraMap F (AF F) (b i)) - (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ w.2)) *
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ) := by
  set ra : κ → AF F := fun i => algebraMap F (AF F) (a i) with hra
  set rb : κ → AF F := fun i => algebraMap F (AF F) (b i) with hrb
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : κ → F => ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ rb - ra ⬝ᵥ w.2)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  set rξ : κ → AF F := fun i => algebraMap F (AF F) (ξ i) with hrξ
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rξ + ra := by
    funext i; simp [hrξ, hra]
  have e3 : ∀ c d : κ → F, (fun i => algebraMap F (AF F) (c i)) ⬝ᵥ (fun i => algebraMap F (AF F) (d i)) =
      algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [dotProduct]
  rw [e1]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have hx : rξ + (ra + w.1) = rξ + ra + w.1 := (add_assoc _ _ _).symm
  rw [hx]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  conv_rhs => rw [← mul_one (ψ _), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq', ← e3, ← e3]
  simp only [add_dotProduct, dotProduct_add]
  have t : ∀ z : AF F, ⅟(2 : AF F) * z + ⅟(2 : AF F) * z = z := fun z => by
    rw [← add_mul, invOf_two_add_invOf_two, one_mul]
  linear_combination t (ra ⬝ᵥ w.2)

theorem norm_thetaSum_schr_ratPair_add : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ),
    ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (γ + w) Φ)‖ = ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).mp hγ
  rw [thetaSum_schr_rat_add ψ hψ.2.2.1 Φ a b w, norm_mul, hψ.2.1, one_mul]

end GlobalTheory.ThetaRatInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvariStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ),
    ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (γ + w) Φ)‖ = ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ := by
  first | exact @GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add | exact GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add | (intros; apply GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
open NumberField GlobalTheory.CuspRep

noncomputable section

section LieGrowth

open MeasureTheory Topology Matrix GroundTheory.Automorphic

namespace GlobalTheory.CuspStab.LieGrowth

open GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

end GlobalTheory.CuspStab.LieGrowth

end LieGrowth

namespace GlobalTheory.CuspStab

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zfin_of_comm (T : Module.End ℂ (Sm E a)) (hT : ∀ z ∈ Zalg E a, z * T = T * z) {φ : Sm E a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (T φ)) '' Zalg E a)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
    Zalg E a)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, (LinearMap.congr_fun (hT z hz) φ).symm⟩

theorem zalg_comm_fin (k : GL (Fin a) (Af E)) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    z * finRep E a k = finRep E a k * z := _root_.GlobalTheory.CuspStabFin.zalg_comm_fin (z := z) k hz

theorem level_of_le {φ ψ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ})
    (hle : ∀ k, finRep E a k φ = φ → finRep E a k ψ = ψ) : IsOpen {k | finRep E a k ψ = ψ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.mem_nhds (by simp)) fun k hk => hle k hk)

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

theorem height_mul_le (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖, by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_mul {f : GL (Fin a) (Cinf E) → ℂ} (c : GL (Fin a) (Cinf E))
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (y * c)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  obtain ⟨B, hB, hB'⟩ := height_mul_le c
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => (hC _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * c)]) (hB' y) N) C0

end GlobalTheory.CuspStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfFlatWtSome
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}


open Classical in
theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) =
      if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  by_cases h1 : σ = τ.1
  · subst h1
    have hi : (i : ℕ) < Dw.p := by
      have := i.2; simp only [Datum.mult, if_pos τ.2] at this; exact this
    rw [if_pos rfl]
    show (wtOf Dw (flatWt Dw τ) 0).1 (τ.1, i) = -1
    rw [wtOf_big _ _ τ i hi]; simp [flatWt, parWt]
  · rw [if_neg h1]
    by_cases h2 : σ = conjEmb τ.1
    · subst h2
      have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg (conj_not_mem τ)] at this; exact this
      rw [if_pos rfl]
      show (wtOf Dw (flatWt Dw τ) 0).1 (conjEmb τ.1, i) = 1
      rw [wtOf_small _ _ τ i hi]; simp [flatWt, parWt]
    · rw [if_neg h2]
      show (wtOf Dw (flatWt Dw τ) 0).1 (σ, i) = 0
      simp only [wtOf]
      split_ifs with h h' h''
      · have hne : (⟨σ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [flatWt, parWt, hne]
      · rfl
      · have hne : (⟨conjEmb σ, h''⟩ : Psi H) ≠ τ := fun e => h2 (by
          rw [← congrArg Subtype.val e, GlobalTheory.AllWt.conjEmb_conjEmb])
        simp [flatWt, parWt, hne]
      · rfl
      · rfl

theorem exOf_flatWt_none (τ : Psi H) : exOf Dw (flatWt Dw τ) 0 none = 0 := by
  simp [exOf, exZ, wtOf]

theorem ne_conjEmb (τ : Psi H) : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)

end GlobalTheory.FlatFrameLaw

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem evR_flat_frChg {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0)) {C : Type} [Field C] [Algebra c.F C]
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) C) (a : C)
    (z y : FrPt Xo c C) (hch : FrChg g a z y) (hg : ∀ σ i j, i < j → g σ i j = 0)
    (hdet : ∀ σ, IsUnit (g σ).det) (ha : a ≠ 0) :
    evR Xo c f y = ((g τ.1).det)⁻¹ * (g (conjEmb τ.1)).det * evR Xo c f z := by
  classical
  have hdiag : ∀ σ, (g σ).det = ∏ i, g σ i i := fun σ =>
    Matrix.det_of_lowerTriangular _ fun i j hij => hg σ i j hij
  have hd : ∀ σ i, g σ i i ≠ 0 := fun σ i => by
    have hu := (hdet σ).ne_zero
    rw [hdiag σ] at hu
    exact Finset.prod_ne_zero_iff.1 hu i (Finset.mem_univ i)
  obtain ⟨h1, h2, pm, h3, h4, h5⟩ := hch
  let t : Ix Dw → Cˣ := fun i => Option.rec (Units.mk0 a ha) (fun s => Units.mk0 _ (hd s.1 s.2)) i
  have hb : FrBor t z y := by
    refine ⟨h1, fun σ i => ⟨g σ i, rfl, hg σ i, h2 σ i⟩, pm, h3, ?_, h5⟩
    rw [h4, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]
    exact Category.comp_id _
  rw [GlobalTheory.FlagTan.evR_frBor hf hb]
  congr 1
  rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
  have hF : ∀ σ, ∏ i : Fin (Dw.mult σ), ((t (some ⟨σ, i⟩) ^ exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) : Cˣ) : C) =
      if σ = τ.1 then ((g σ).det)⁻¹ else if σ = conjEmb τ.1 then (g σ).det else 1 := fun σ => by
    simp only [exOf_flatWt_some, t, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    by_cases e1 : σ = τ.1
    · simp only [if_pos e1, zpow_neg_one, Finset.prod_inv_distrib, hdiag]
    · by_cases e2 : σ = conjEmb τ.1
      · simp only [if_neg e1, if_pos e2, zpow_one, hdiag]
      · simp only [if_neg e1, if_neg e2, zpow_zero, Finset.prod_const_one]
  simp only [hF, exOf_flatWt_none, zpow_zero, Units.val_one, one_mul]
  rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) (ne_conjEmb τ) fun σ hσ => by rw [if_neg hσ.1, if_neg hσ.2],
    if_pos rfl, if_neg (ne_conjEmb τ).symm, if_pos rfl]

end GlobalTheory.FlatFrameLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSphLat

open GlobalTheory.InertLocField InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_inclR (a : AF F) (e : E) : a • inclR (F := F) (AF F) e = a ⊗ₜ[F] e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem iotaW_toCompl {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (y : Fv F v ⊗[F] E) :
    GlobalTheory.InertBigCell.iotaW hw (toCompl (under_eq_of_isInertAt hw) y) = liftT (E := E) v y := by
  show liftT (E := E) v ((complEquiv hw (under_eq_of_isInertAt hw)).symm
    (complEquiv hw (under_eq_of_isInertAt hw) y)) = liftT (E := E) v y
  rw [RingEquiv.symm_apply_apply]

theorem gen_mem {v : Pl (F := F)} {d : ℕ} (W : Spc F E d) {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F)
    {y : Fin d → E} (hy : y ∈ W.L) :
    (fun i => GlobalTheory.LatVac.liftV v t ⊗ₜ[F] y i) ∈ GlobalTheory.InertSph.latAt W v :=
  AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v t, GlobalTheory.LatVac.at_liftV v t,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ht, y, hy, by funext i; rw [Pi.smul_apply, smul_inclR]⟩

theorem mem_latAt_iff {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ}
    (W : Spc F E d) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ ∃ u ∈ GlobalTheory.LFun.latAt w W.L, z = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := by
  have liftT_tmul (a : Fv F v) (e : E) :
      liftT (E := E) v (a ⊗ₜ[F] e) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] e := rfl
  have h := under_eq_of_isInertAt hw
  let f : (Fin d → w.adicCompletion E) →+ (Fin d → AE F E) :=
    AddMonoidHom.compLeft (GlobalTheory.InertBigCell.iotaW hw) (Fin d)
  have hf : ∀ u, f u = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := fun _ => rfl
  constructor
  · intro hz
    have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.LFun.latAt w W.L).toAddSubgroup.map f := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, haO, y, hy, rfl⟩
      refine ⟨fun i => complMap h (evFin F v a) * algebraMap E _ (y i), ?_, ?_⟩
      · have e1 : (fun i => complMap h (evFin F v a) * algebraMap E (w.adicCompletion E) (y i)) =
            (⟨complMap h (evFin F v a), complMap_mem h haO⟩ : Formalism.UG.Ov E w) •
              (fun i => algebraMap E (w.adicCompletion E) (y i)) := rfl
        rw [Submodule.coe_toAddSubgroup, SetLike.mem_coe, e1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      · funext i
        rw [hf]
        dsimp only
        rw [← toCompl_tmul, iotaW_toCompl, liftT_tmul, ← eq_liftV_of_at v ha, Pi.smul_apply, smul_inclR]
    obtain ⟨u, hu, e⟩ := AddSubgroup.mem_map.1 (hle hz)
    exact ⟨u, hu, e.symm⟩
  · rintro ⟨u, hu, rfl⟩
    have key : ∀ u ∈ GlobalTheory.LFun.latAt w W.L, ∀ o : Formalism.UG.Ov E w, f (o • u) ∈ GlobalTheory.InertSph.latAt W v := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        intro o
        obtain ⟨t, ht⟩ := GlobalTheory.LFun.toCompl_surjective h (o : w.adicCompletion E)
        have htI : t ∈ intLoc F E v := (mem_intLoc_iff hw h t).2 (ht ▸ o.2)
        have e1 : f (o • fun i => algebraMap E (w.adicCompletion E) (y i)) =
            fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i)) := by
          funext i
          rw [hf]
          dsimp only
          rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, ← ht,
            show algebraMap E (w.adicCompletion E) (y i) = toCompl h ((1 : Fv F v) ⊗ₜ[F] y i) by
              rw [toCompl_tmul, map_one, one_mul], ← map_mul, iotaW_toCompl]
        rw [e1]
        refine intLoc_induction (p := fun t => (fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i))) ∈
          GlobalTheory.InertSph.latAt W v) (fun a ha x => ?_) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) htI
        · convert gen_mem W ha (W.L.smul_mem x hy) using 1
          funext i
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, liftT_tmul, Pi.smul_apply, Algebra.smul_def]
        · convert (zero_mem (GlobalTheory.InertSph.latAt W v)) using 1
          funext i
          simp
        · convert add_mem hp hq using 1
          funext i
          simp [add_mul, map_add (f := _)]
        · convert neg_mem hp using 1
          funext i
          simp [neg_mul, map_neg]
      | zero => intro o; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro o; rw [smul_add, map_add (f := _)]; exact add_mem (hx o) (hy o)
      | smul a x _ hx => intro o; rw [smul_smul]; exact hx (o * a)
    have := key u hu 1
    rw [one_smul] at this
    exact this

end GlobalTheory.InertSphLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInertStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicLatticeAtFinitePlace_iff_inert : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ} (W : Spc F E d) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
  z ∈ GlobalTheory.InertSph.latAt W v ↔ ∃ u ∈ GlobalTheory.LFun.latAt w W.L, z = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := by
  first | exact @GlobalTheory.InertSphLat.mem_latAt_iff | exact GlobalTheory.InertSphLat.mem_latAt_iff | (intros; apply GlobalTheory.InertSphLat.mem_latAt_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqComponentTensorEqConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqComponentTensorEqConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.AdelicPush

open GlobalTheory.AdelicU

theorem lintegral_tens_eq_const_mul : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (r : (κ → AF F) → ℂ),
    @Measurable _ _ (borel _) _ r →
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) →
    ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ K : Set (κ → Fv F v), IsCompact K → (interior K).Nonempty →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : (κ → Fv F v) → ℂ, Continuous φ → HasCompactSupport φ →
      ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ v r hr hinv μA hμA μ hμ K hK hKi hK0 hKt
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have hcont : Continuous (evFin F v) := by
    change Continuous fun a => _
    exact (PI.LevelKSplit.W.Cont.continuous_evalV v).comp continuous_snd
  let evK : (κ → AF F) → (κ → Fv F v) := fun x i => evFin F v (x i)
  have hevKm : Measurable evK := (continuous_pi fun i => hcont.comp (continuous_apply i)).measurable
  let ρ : (κ → AF F) → ENNReal := fun x => ‖r x‖ₑ ^ 2
  have hρ : Measurable ρ := hr.enorm.pow_const 2
  let ν : Measure (κ → Fv F v) := (μA.withDensity ρ).map evK
  have hνA : ∀ A, MeasurableSet A → ν A = ∫⁻ x, A.indicator 1 (evK x) * ρ x ∂μA := by
    intro A hA
    rw [Measure.map_apply hevKm hA, withDensity_apply _ (hevKm hA), ← lintegral_indicator (hevKm hA)]
    refine lintegral_congr fun x => ?_
    by_cases h : evK x ∈ A <;> simp [Set.indicator, h]
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro y
    ext A hA
    rw [Measure.map_apply (measurable_const_add y) hA, hνA _ hA, hνA _ (measurable_const_add y hA)]
    let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
    have hev : ∀ x, evK (x + z) = y + evK x := fun x => funext fun i => by
      simp [evK, z, GlobalTheory.LatVac.evFin_liftV, add_comm]
    rw [← lintegral_add_right_eq_self (fun x => A.indicator 1 (evK x) * ρ x) z]
    refine lintegral_congr fun x => ?_
    simp only [hev, ρ, hinv x z hz]
    by_cases h : y + evK x ∈ A <;> simp [Set.indicator, h]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  haveI : ν.IsAddHaarMeasure := Measure.isAddHaarMeasure_of_isCompact_nonempty_interior ν K hK hKi
    (by rw [hνA K hKm]; exact hK0) (by rw [hνA K hKm]; exact hKt)
  have hsc : ∀ s : Set (κ → Fv F v), IsCompact (closure s) →
      ν s = (Measure.addHaarScalarFactor ν μ : ENNReal) * μ s := fun s hs => by
    rw [Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ hs, ENNReal.smul_def, smul_eq_mul]
  refine ⟨(Measure.addHaarScalarFactor ν μ : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · intro h0
    have := hsc K (by rw [hK.isClosed.closure_eq]; exact hK)
    rw [h0, zero_mul, hνA K hKm] at this
    exact hK0 this
  intro φ hφ hφc
  set C : ENNReal := (Measure.addHaarScalarFactor ν μ : ENNReal)
  let T := tsupport φ
  have hrest : ν.restrict T = C • μ.restrict T := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact hsc _ (hφc.isCompact.of_isClosed_subset isClosed_closure
      (closure_minimal Set.inter_subset_right (isClosed_tsupport φ)))
  have hf : Measurable fun y => ‖φ y‖ₑ ^ 2 := hφ.measurable.enorm.pow_const 2
  have hsupp : Function.support (fun y => ‖φ y‖ₑ ^ 2) ⊆ T := by
    intro y hy
    by_contra h
    exact hy (by simp [image_eq_zero_of_notMem_tsupport h])
  calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA
      = ∫⁻ x, (ρ * fun x => (fun y => ‖φ y‖ₑ ^ 2) (evK x)) x ∂μA := by
        refine lintegral_congr fun x => ?_
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.mul_apply, ρ, evK, enorm_mul, mul_pow, mul_comm]
    _ = ∫⁻ x, (fun y => ‖φ y‖ₑ ^ 2) (evK x) ∂(μA.withDensity ρ) :=
        (lintegral_withDensity_eq_lintegral_mul _ hρ (hf.comp hevKm)).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂ν := (lintegral_map hf hevKm).symm
    _ = ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂ν := (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(C • μ.restrict T) := by rw [hrest]
    _ = C * ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂μ := lintegral_smul_measure _ _
    _ = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by rw [setLIntegral_eq_of_support_subset hsupp]

end GlobalTheory.AdelicPush

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqComponentTensorEqConstMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_normSq_componentTensor_eq_const_mul : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (r : (κ → AF F) → ℂ),
    @Measurable _ _ (borel _) _ r →
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) →
    ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ K : Set (κ → Fv F v), IsCompact K → (interior K).Nonempty →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : (κ → Fv F v) → ℂ, Continuous φ → HasCompactSupport φ →
      ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul | exact GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul | (intros; apply GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem compatibleGlobalOneForms_finite_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  intro R _ C _ F hF h0
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let L : Glob1 F →ₗ[R] (Fin n → R) := LinearMap.pi l
  let S : (Fin n → R) →ₗ[R] Glob1 F := Fintype.linearCombination R Φ.w
  have hSL : S.comp L = LinearMap.id := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, S, L, Fintype.linearCombination_apply, LinearMap.pi_apply]
    exact (hl w).symm
  have hsurj : Function.Surjective S := fun w ↦ ⟨L w, by
    simpa using LinearMap.congr_fun hSL w⟩
  exact ⟨Module.Finite.of_surjective S hsurj, Module.Projective.of_split L S hSL⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glob1_finite_and_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  first | exact @GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | exact GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | (intros; apply GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRank
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem smooth_of_openImm {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (g : ℕ) (hs : SmoothOfRelativeDimension g s) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B))
    [IsOpenImmersion x] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B) ∧ Algebra.Smooth R B := by
  have h : SmoothOfRelativeDimension g (x ≫ s) := by
    have := smoothOfRelativeDimension_comp 0 g x s
    simpa using this
  rw [hx] at h
  constructor
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).1 h
  · have h2 : Smooth (spMap (algebraMap R B)) := SmoothOfRelativeDimension.smooth g _
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2)

theorem rankAtStalk_kaehler_of_locally {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (g : ℕ) (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B))
    (p : PrimeSpectrum B) : Module.rankAtStalk Ω[B⁄R] p = g := by
  obtain ⟨s, hs, H⟩ := h
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p.asIdeal := by
    by_contra! hc
    exact p.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  let Bt := Localization.Away t
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension g R Bt :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).1
      (by rw [IsScalarTower.algebraMap_eq R B Bt]; exact H t ht)
  have : Algebra.FormallyEtale B Bt := .of_isLocalization (Submonoid.powers t)
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B Bt
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum Bt, PrimeSpectrum.comap (algebraMap B Bt) q = p := by
    have : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B Bt)) := by
      rw [PrimeSpectrum.localization_away_comap_range Bt t]
      exact htp
    exact this
  have : Nontrivial Bt := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  have : Algebra.IsStandardSmooth R Bt := hstd.isStandardSmooth
  have : Module.Free Bt Ω[Bt⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have h1 := Module.rankAtStalk_baseChange (R := B) (S := Bt) (M := Ω[B⁄R]) q
  rw [hq] at h1
  rw [← h1, Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free]
  have hf : Module.finrank Bt Ω[Bt⁄R] = g := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := Bt) g]
    simp
  simp [hf]

theorem globForm_FP : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.glob1_finite_and_projective R _ (OAff A.hom) hF h0
  refine ⟨hfin, hproj, fun p ↦ ?_⟩

  have hη : (η[A]).left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  let x : A.left := (η[A]).left.base p
  have hxp : A.hom.base x = p := by
    change ((η[A]).left ≫ A.hom).base p = p
    rw [hη]; rfl
  obtain ⟨U, hU⟩ : ∃ U : A.left.affineOpens, x ∈ U.1 := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  let T : AffOp A.left := Opposite.op U
  let B := (OAff A.hom).obj T
  have hUa : IsAffineOpen U.1 := U.2
  obtain ⟨q, hq⟩ : ∃ q : Sp (Sec A.hom U.1), (affPt A.hom U).base q = x := by
    have : x ∈ Set.range hUa.fromSpec.base := by
      rw [hUa.range_fromSpec]; exact hU
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  have hqp : PrimeSpectrum.comap (algebraMap R (Sec A.hom U.1)) q = p := by
    have := congrArg (fun f ↦ f.base q) (affPt_w A.hom U)
    change A.hom.base ((affPt A.hom U).base q) = _ at this
    rw [hq, hxp] at this
    exact this.symm
  haveI : IsOpenImmersion (affPt A.hom U) := IsAffineOpen.isOpenImmersion_fromSpec hUa
  obtain ⟨hloc, hsm⟩ := smooth_of_openImm A.hom g hg (affPt A.hom U) (affPt_w A.hom U)
  have hrk := rankAtStalk_kaehler_of_locally g hloc q
  let e : Glob1 (OAff A.hom) →ₗ[R] Ω[B⁄R] := (LinearMap.proj T).comp (Glob1 (OAff A.hom)).subtype
  have he : IsBaseChange B e := GlobalTheory.T.isBaseChange_compatibleGlobalOneForms R _ (OAff A.hom) hF h0 T e (fun _ ↦ rfl)
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := Glob1 (OAff A.hom)) (S := B) q
  rw [Module.rankAtStalk_eq_of_equiv he.equiv] at h1
  rw [← hqp]
  exact h1.symm.trans hrk

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRankStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_global_oneForms_projective_rank : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  first | exact @GlobalTheory.AbCoh.globForm_FP | exact GlobalTheory.AbCoh.globForm_FP | (intros; apply GlobalTheory.AbCoh.globForm_FP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIterated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIterated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Pointwise

namespace GlobalTheory.PeriodicIterated

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem prod_isAddFundamentalDomain (Γ₁ : AddSubgroup V) (Γ : AddSubgroup (V × V))
    (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁) (μ : Measure V) [SFinite μ]
    (𝓕₁ : Set V) (h : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) (μ.prod μ) := by
  refine ⟨h.nullMeasurableSet.prod h.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h.ae_covers
    filter_upwards [h1, h2] with p ha hb
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exact ⟨⟨((a : V), (b : V)), (hΓ _).2 ⟨a.2, b.2⟩⟩, ha, hb⟩
  · intro g g' hne
    have hset : ∀ k : Γ, k +ᵥ (𝓕₁ ×ˢ 𝓕₁) =
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁) +ᵥ 𝓕₁) ×ˢ
          ((⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁) +ᵥ 𝓕₁) := by
      intro k
      ext ⟨x, y⟩
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod, AddSubgroup.vadd_def,
        AddSubgroup.coe_neg, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
    show μ.prod μ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₁))) = 0
    rw [hset g, hset g', Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : (g : V × V).1 = (g' : V × V).1
    · have h2 : (g : V × V).2 ≠ (g' : V × V).2 := by
        intro h2
        exact hne (Subtype.ext (Prod.ext h1 h2))
      have := h.aedisjoint (i := ⟨(g : V × V).2, ((hΓ _).1 g.2).2⟩)
        (j := ⟨(g' : V × V).2, ((hΓ _).1 g'.2).2⟩) (fun h' => h2 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, mul_zero]
    · have := h.aedisjoint (i := ⟨(g : V × V).1, ((hΓ _).1 g.2).1⟩)
        (j := ⟨(g' : V × V).1, ((hΓ _).1 g'.2).1⟩) (fun h' => h1 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, zero_mul]

theorem lintegral_fundamentalDomain_eq_iterated (Γ₁ : AddSubgroup V) [Countable Γ₁]
    (Γ : AddSubgroup (V × V)) (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (mW : MeasurableSpace (V × V)) (hmW : mW = Prod.instMeasurableSpace)
    (ν : @Measure (V × V) mW) (hν : @Measure.IsAddHaarMeasure _ _ _ mW ν)
    (𝓕 : Set (V × V)) (h𝓕 : @IsAddFundamentalDomain Γ _ _ _ mW 𝓕 ν)
    (𝓕₁ : Set V) (h𝓕₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : V × V → ENNReal, @Measurable _ _ mW _ G →
      (∀ γ ∈ Γ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  subst hmW
  haveI := hν
  haveI : Countable Γ := by
    have hinj : Function.Injective (fun k : Γ =>
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁), (⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁))) := by
      intro k k' hk
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk
      exact Subtype.ext (Prod.ext hk.1 hk.2)
    exact hinj.countable
  have hmeq := Measure.isAddLeftInvariant_eq_smul ν (μ.prod μ)
  set c : NNReal := Measure.addHaarScalarFactor ν (μ.prod μ)
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (μ.prod μ)
  have hν' : ν = (c : ENNReal) • μ.prod μ := by
    rw [← ENNReal.smul_def]; exact hmeq
  refine ⟨(c : ENNReal), by exact_mod_cast hcpos.ne', ENNReal.coe_ne_top, fun G hG hper => ?_⟩
  have hD : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) ν :=
    (prod_isAddFundamentalDomain Γ₁ Γ hΓ μ 𝓕₁ h𝓕₁).mono (by rw [hν']; exact Measure.smul_absolutelyContinuous)
  rw [h𝓕.setLIntegral_eq hD G (fun g x => hper g g.2 x), hν', Measure.restrict_smul,
    lintegral_smul_measure, ← Measure.prod_restrict, lintegral_prod _ hG.aemeasurable, smul_eq_mul]

end General

end GlobalTheory.PeriodicIterated

namespace GlobalTheory.PeriodicIterated

theorem countable_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  exact (AddMonoidHom.rangeRestrict_surjective _).countable

theorem mem_ratPair_iff_ratVec (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AF F) × (κ → AF F)) :
    w ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ ↔
      w.1 ∈ GlobalTheory.ThetaParseval.ratVec F κ ∧ w.2 ∈ GlobalTheory.ThetaParseval.ratVec F κ := by
  rw [GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff, GlobalTheory.ThetaParseval.mem_ratVec_iff,
    GlobalTheory.ThetaParseval.mem_ratVec_iff]
  constructor
  · rintro ⟨y, z, rfl⟩
    exact ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨y, z, Prod.ext hy hz⟩

theorem lintegral_ratPair_fundamentalDomain_eq_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ (𝓕 : Set ((κ → AF F) × (κ → AF F))), @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  intro F _ _ κ _ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := countable_ratVec F κ
  haveI := hμ
  exact lintegral_fundamentalDomain_eq_iterated (GlobalTheory.ThetaParseval.ratVec F κ)
    (GlobalTheory.WeilUnitaryTransport.ratPair F κ) (mem_ratPair_iff_ratVec F κ) μ (borel _)
    (Prod.borelSpace (α := κ → AF F) (β := κ → AF F)).measurable_eq.symm ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁

end GlobalTheory.PeriodicIterated

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIteratedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ (𝓕 : Set ((κ → AF F) × (κ → AF F))), @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  first | exact @GlobalTheory.PeriodicIterated.lintegral_ratPair_fundamentalDomain_eq_iterated | exact GlobalTheory.PeriodicIterated.lintegral_ratPair_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.PeriodicIterated.lintegral_ratPair_fundamentalDomain_eq_iterated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW

theorem psiLoc_addChar_locallyConstant_ne_one :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ,
      (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  intro E _ _ w
  refine ⟨psiLocChar w, fun x => rfl, ?_, ?_⟩
  · have hc : Continuous (psiLocChar w) := by
      have : (psiLocChar w : w.adicCompletion E → ℂ) = fun x => ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) := by
        funext x; exact GlobalTheory.JSW.WhitModel.psiLoc_eq w x
      rw [this]
      exact continuous_subtype_val.comp (GroundTheory.Global.continuous_localAdelicChar w)
    exact GlobalTheory.SchrSBFin.isLocallyConstant_addChar _ hc
  · intro h
    apply GroundTheory.Global.localAdelicChar_ne_one (K := E) (v := w)
    refine AddChar.ext _ _ fun x => ?_
    have h1 : psiLocChar w x = 1 := by rw [h]; rfl
    have h2 : ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) = 1 := by
      rw [← GlobalTheory.JSW.WhitModel.psiLoc_eq]; exact h1
    exact Subtype.ext h2

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivialStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ, (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  first | exact @GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | exact GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | (intros; apply GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one <;> assumption)
end
end

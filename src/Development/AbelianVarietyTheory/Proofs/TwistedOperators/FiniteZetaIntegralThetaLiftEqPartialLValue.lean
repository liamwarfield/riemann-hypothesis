module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumLocalSphericalZetaUnramified
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalZetaSumsAbsolutelyConvergentUniform
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorKeepsLatticeVacuumOfTrivialAt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorKeepsLatticeVacuumOfTrivialAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.MoveVac

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_one_eq {D : D7} {S T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D T}
    (hg : projV T v g = 1) {u : WO S T} (hu : u ∈ latO S T (frameLat S) (frameLat T) fun w => w = v) :
    actO S T 1 g u = u := by
  have hid : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ((GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v).2.2
  have hgA : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt T (.inl v) g = 1 := by
    show GlobalTheory.AdelicU.emb D.sp.cm.sig T.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig T.gram v g) = 1
    rw [show GlobalTheory.AdelicU.proj D.sp.cm.sig T.gram v g = 1 from hg, map_one]
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • Formalism.L2.Theta.mt T g =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    have h := GlobalTheory.PlaceComponent.mt_gAt T (.inl v) g
    rw [hgA, mt_one'] at h
    rw [eq_sub_of_add_eq h.symm, sub_smul, one_smul, sub_sub_cancel]
  have hu' : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • u = u := GlobalTheory.InertVac.placeIdem_smul_eq hid hu
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one, ← hu', Matrix.mul_smul, ← Matrix.smul_mul, hm,
    Matrix.smul_mul, Matrix.one_mul]

theorem vacFin_om_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D T), projV T v g = 1 → ∀ f, VacFin ψ S T v f → VacFin ψ S T v (om (1, g) f) := by
  intro D ψ S T χS χT om hW v g hg f hf
  obtain ⟨hth, hl1, hl2⟩ := hf
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have h2 : 2 • u ∈ (latO S T (frameLat S) (frameLat T) fun w => w = v) := nsmul_mem hu 2
    rw [← actO_one_eq hg h2, ← hW.om_heis 1 g _ f hth, hl1 u hu]
  · rw [← actO_one_eq hg hu, ← hW.om_heis 1 g _ f hth, hl2 e he u hu hh]

end GlobalTheory.FinZeta.MoveVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorKeepsLatticeVacuumOfTrivialAtStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_keeps_latticeVacuum_of_trivialAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D T), projV T v g = 1 → ∀ f, VacFin ψ S T v f → VacFin ψ S T v (om (1, g) f) := by
  first | exact @GlobalTheory.FinZeta.MoveVac.vacFin_om_one | exact GlobalTheory.FinZeta.MoveVac.vacFin_om_one | (intros; apply GlobalTheory.FinZeta.MoveVac.vacFin_om_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasProdLocalTwistedLFactorDivUnitaryLocalFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasProdLocalTwistedLFactorDivUnitaryLocalFactor
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem abs_quadTerm_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) {i : ℕ} (hi : 2 ≤ i) :
    ‖-quadTerm D v i‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm v
  have hs : |quadSign D v| = 1 := by unfold quadSign; split_ifs <;> simp
  rw [norm_neg, Real.norm_eq_abs, quadTerm, abs_div, abs_pow, abs_pow, hs, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)), Real.rpow_neg (by positivity),
    Real.rpow_two]
  have h2 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i :=
    pow_le_pow_right₀ hN.le hi
  rw [one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast h2)

theorem hasProd_dLoc (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => dLoc D v.1) (dOff D Sb) ∧ dOff D Sb ≠ 0 := by
  have ht := D.R.rank_add_five_le
  set f : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV → ℝ :=
    fun p => -quadTerm D p.1.1 p.2.1 with hf
  have hsum0 := summable_rpow (K := D.host.F) (Sb : Set _) (σ := 2) (by norm_num)
  have hsum1 : Summable fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV =>
      ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) * (1 : ℝ) := by
    refine summable_mul_of_summable_norm (f := fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ))) (g := fun _ : Finset.Ioc D.R.t D.R.nV => (1 : ℝ)) ?_ ?_
    · refine hsum0.congr fun v => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact Summable.of_finite
  have hsum : Summable fun p => ‖f p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hsum1
    rw [mul_one]
    have := (Finset.mem_Ioc.1 p.2.2).1
    exact abs_quadTerm_le D p.1.1 (by omega)
  have hne : ∀ p, 1 + f p ≠ 0 := fun p => by
    have h1 := abs_quadTerm_le D p.1.1 (i := p.2.1) (by have := (Finset.mem_Ioc.1 p.2.2).1; omega)
    have hN : (1 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm p.1.1
    have h2 : ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hN (by norm_num)
    intro h0
    have : f p = -1 := by linarith
    rw [hf] at this
    simp only at this
    rw [this, norm_neg, norm_one] at h1
    linarith
  have hm := multipliable_one_add_of_summable hsum
  have hz := tprod_one_add_ne_zero_of_summable hne hsum
  have hinv : HasProd (fun p => (1 + f p)⁻¹) (∏' p, (1 + f p))⁻¹ := hm.hasProd.inv₀ hz
  have e1 : (fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV => (1 + f p)⁻¹) =
      fun p => (1 - quadTerm D p.1.1 p.2.1)⁻¹ := by
    funext p; rw [hf]; ring_nf
  rw [e1] at hinv
  have hd : dOff D Sb = (∏' p, (1 + f p))⁻¹ := hinv.tprod_eq
  refine ⟨?_, hd ▸ inv_ne_zero hz⟩
  rw [hd]
  refine hinv.prod_fiberwise fun v => ?_
  have := hasProd_fintype (fun c : Finset.Ioc D.R.t D.R.nV => (1 - quadTerm D v.1 c.1)⁻¹)
  rw [Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) (fun i => (1 - quadTerm D v.1 i)⁻¹)] at this
  exact this

theorem hasProd_LvTw_div_dLoc : ∀ (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : Fam D.host.E) (χ : (AE D)ˣ →* Circle), Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (GlobalTheory.LFun.twist B (val χ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) → HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v.1 : ℂ)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) := by
  intro D Sb B χ h
  have h1 : HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2)) :=
    hasProd_Lv h
  obtain ⟨h2, h3⟩ := hasProd_dLoc D Sb
  have h4 := (h2.map Complex.ofRealHom Complex.continuous_ofReal).inv₀
    (by simpa using h3 : Complex.ofRealHom (dOff D Sb) ≠ 0)
  have h5 := h1.mul h4
  simpa [div_eq_mul_inv, Function.comp_def] using h5

end GlobalTheory.FinZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasProdLocalTwistedLFactorDivUnitaryLocalFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProd_localTwistedLFactor_div_unitaryLocalFactor : ∀ (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : Fam D.host.E) (χ : (AE D)ˣ →* Circle), Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (GlobalTheory.LFun.twist B (val χ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) → HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v.1 : ℂ)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) := by
  first | exact @GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc | exact GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc | (intros; apply GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalLevelRelIndexLiftLevelEqCard
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalLevelRelIndexLiftLevelEqCard
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevIdx

open Formalism.IndefR.Lev (finE)

variable {D : D7} {T0 : Type} (C : LevCh D T0) (i : Fin D.R.m)

theorem mem_levG_datWp (P : LevelP C.Pg D.R.r ℂ) (κ : GA D (Wc D i)) :
    κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) ↔ κ ∈ GfC (Wc D i) ∧
      finE (Wc D i) κ ∈ parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i C.triv) ∧
      rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ) ∈ P.H := by
  rw [levG, Formalism.IndefR.Lev.mem_levA]
  refine and_congr_right fun _ => ?_
  exact Iff.rfl

def blkHom (P : LevelP C.Pg D.R.r ℂ) : levG (Wc D i) (C.βW i) (C.datWp i P) →* G0 C.Pg D.R.r where
  toFun κ := rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ.1)
  map_one' := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) 1) = 1
    rw [map_one]; exact rTup_one
  map_mul' x y := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) (x.1 * y.1)) = _
    rw [map_mul]
    exact rTup_mul (hc := D.sp.cm) (J := (Wc D i).gram) ((mem_levG_datWp C i P _).1 x.2).2.1
      ((mem_levG_datWp C i P _).1 y.2).2.1

theorem ker_blkHom (P : LevelP C.Pg D.R.r ℂ) :
    (blkHom C i P).ker = (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).subgroupOf
      (levG (Wc D i) (C.βW i) (C.datWp i P)) := by
  ext κ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_levG_datWp C i C.triv]
  obtain ⟨hG, hpar, -⟩ := (mem_levG_datWp C i P κ.1).1 κ.2
  constructor
  · intro h1
    exact ⟨hG, hpar, Subgroup.mem_bot.2 h1⟩
  · rintro ⟨-, -, hb⟩
    exact Subgroup.mem_bot.1 hb

theorem range_blkHom {μ0 : T0} (hC : C.Is μ0) (P : LevelP C.Pg D.R.r ℂ) : (blkHom C i P).range = P.H := by
  ext g
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨κ, rfl⟩
    exact ((mem_levG_datWp C i P κ.1).1 κ.2).2.2
  · intro hg
    obtain ⟨c, hB⟩ := hC.βW i
    have hsep := (GlobalTheory.StepLifts.places_apart C hC μ0).1
    obtain ⟨κ, hG, hpar, hred⟩ := GlobalTheory.ParahoricLift.liftsExist (Wc D i) (C.βW i) (C.datWp i C.triv) (C.ΛW i) _ hB
      (fun PP hPP PP' hPP' => hsep PP hPP PP' (hPP'.elim Or.inl fun h => absurd h (Finset.notMem_empty PP')))
      (Finset.disjoint_empty_right _) g
    have hmem : κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) := by
      refine (mem_levG_datWp C i P κ).2 ⟨hG, hpar, ?_⟩
      rw [hred]
      exact hg
    exact ⟨⟨κ, hmem⟩, hred⟩

theorem levidx : ∀ (D : D7) (T0 : Type) (C : LevCh D T0) (μ0 : T0), C.Is μ0 → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → C.Pg ⊆ Z → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) ∧ (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).relIndex (levG (Wc D i) (C.βW i) (C.datWp i P)) = Nat.card P.H ∧ Nat.card P.H ≠ 0 := by
  intro D T0 C μ0 hC _ _ _ _ i P
  have hle : levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) := by
    intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (mem_levG_datWp C i C.triv κ).1 hκ
    refine (mem_levG_datWp C i P κ).2 ⟨h1, h2, ?_⟩
    rw [Subgroup.mem_bot.1 h3]
    exact P.H.one_mem
  refine ⟨hle, ?_, Nat.card_pos.ne'⟩
  rw [Subgroup.relIndex, ← ker_blkHom C i P, Subgroup.index_ker, range_blkHom C i hC P]

end GlobalTheory.LevIdx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalLevelRelIndexLiftLevelEqCardStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_relIndex_liftLevel_eq_card : ∀ (D : D7) (T0 : Type) (C : LevCh D T0) (μ0 : T0), C.Is μ0 → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → C.Pg ⊆ Z → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) ∧ (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).relIndex (levG (Wc D i) (C.βW i) (C.datWp i P)) = Nat.card P.H ∧ Nat.card P.H ≠ 0 := by
  first | exact @GlobalTheory.LevIdx.levidx | exact GlobalTheory.LevIdx.levidx | (intros; apply GlobalTheory.LevIdx.levidx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsSmallerLevelRelIndexMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsSmallerLevelRelIndexMul
namespace GlobalTheory

open QuotientGroup

theorem hasSum_comp_fst_card_mul_of_fintype {α β : Type} [Fintype β] (f : α → ℂ) (a : ℂ) (hf : HasSum f a) :
    HasSum (fun p : α × β => f p.1) ((Fintype.card β : ℂ) * a) := by
  classical
  have hdec : (fun p : α × β => f p.1) = fun p => ∑ b : β, (if p.2 = b then f p.1 else 0) := by
    funext p
    simp
  rw [hdec]
  have hterm : ∀ b ∈ (Finset.univ : Finset β),
      HasSum (fun p : α × β => if p.2 = b then f p.1 else 0) a := by
    intro b _
    have hinj : Function.Injective (fun x : α => (x, b)) := fun x y h => by
      simpa using congrArg Prod.fst h
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def] using hf
    · intro p hp
      by_cases h : p.2 = b
      · exact absurd ⟨p.1, by ext <;> simp [h]⟩ hp
      · simp [h]
  have := hasSum_sum hterm
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

theorem hasSum_cosets_smaller_level_relIndex_mul : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  intro G _ K J H Γ hKJ hJH hHΓ hidx Ψ z hvan hinv hsum
  classical

  set f : Γ ⧸ J.subgroupOf Γ → ℂ := fun x => Ψ (x.out : Γ) with hf
  have hfmk : ∀ g : Γ, f (mk g) = Ψ (g : G) := by
    intro g
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf Γ) g
    simp only [hf, hj, Subgroup.coe_mul]
    exact hinv _ g.2 _ (Subgroup.mem_subgroupOf.mp j.2)

  let ι : H ⧸ J.subgroupOf H → Γ ⧸ J.subgroupOf Γ := fun y => mk (Subgroup.inclusion hHΓ y.out)
  have hιmk : ∀ a : H, ι (mk a) = mk (Subgroup.inclusion hHΓ a) := by
    intro a
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) a
    show (mk (Subgroup.inclusion hHΓ (mk a : H ⧸ J.subgroupOf H).out) : Γ ⧸ J.subgroupOf Γ) = _
    rw [hj, QuotientGroup.eq]
    simp [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp j.2
  have hιinj : Function.Injective ι := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [hιmk, hιmk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hxy
  have h1 : HasSum f z := by
    rw [← hιinj.hasSum_iff]
    · convert hsum using 1
      funext y
      show f (mk (Subgroup.inclusion hHΓ y.out)) = _
      rw [hfmk]
      rfl
    · intro x hx
      show Ψ (x.out : G) = 0
      apply hvan _ x.out.2
      intro hH
      apply hx
      refine ⟨mk ⟨(x.out : G), hH⟩, ?_⟩
      rw [hιmk]
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rfl

  have hle : K.subgroupOf Γ ≤ J.subgroupOf Γ := fun x hx => by
    simpa [Subgroup.mem_subgroupOf] using hKJ (Subgroup.mem_subgroupOf.mp hx)
  let e := Subgroup.quotientEquivProdOfLE hle
  have hJΓ : J ≤ Γ := hJH.trans hHΓ
  have hrel : (K.subgroupOf Γ).relIndex (J.subgroupOf Γ) = K.relIndex J :=
    Subgroup.relIndex_subgroupOf hJΓ
  haveI : (((K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))).FiniteIndex := ⟨by
    rw [← Subgroup.relIndex, hrel]; exact hidx⟩
  haveI : Finite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))
  have hcard : (Fintype.card (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) : ℂ)
      = (K.relIndex J : ℂ) := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index, ← Subgroup.relIndex, hrel]
  have h2 := hasSum_comp_fst_card_mul_of_fintype (β := J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) f z h1
  rw [hcard, ← e.hasSum_iff] at h2
  convert h2 using 1
  funext y
  have he1 : (e y).1 = mk y.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  simp only [Function.comp_apply, he1, hfmk]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsSmallerLevelRelIndexMulStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  first | exact @GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | exact GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | (intros; apply GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsEulerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsEulerProduct
open Filter Topology

namespace GlobalTheory.CosetEuler

variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]

section
variable (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G)

def offSet (T : Finset ι) : Set (H ⧸ J.subgroupOf H) :=
  {y | ∀ v ∉ T, p v ((y.out : H) : G) ∈ K v}

def shift (v : ι) (g : G) : G := g * (e v (p v g))⁻¹

end

theorem e_mem_J {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
    (v : ι) (k : L v) (hk : k ∈ K v) : e v k ∈ J := by
  refine (hJ _ (he v k)).2 fun u => ?_
  by_cases h : u = v
  · subst h; rw [hpe]; exact hk
  · rw [hpe' u v h]; exact (K u).one_mem

theorem cls_eq {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (g h : H) :
    ((g : H ⧸ J.subgroupOf H) = h) ↔ ∀ v, (p v g)⁻¹ * p v h ∈ K v := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hJ _ (g⁻¹ * h).2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]

theorem out_mul {J H : Subgroup G} (hJH : J ≤ H) (g : H) :
    ∃ k ∈ J, (((g : H ⧸ J.subgroupOf H).out : H) : G) = g * k := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) g
  exact ⟨((k : H) : G), Subgroup.mem_subgroupOf.1 k.2, by rw [hk]; rfl⟩

theorem inv_out {E : Type} {J H : Subgroup G} (hJH : J ≤ H) (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (g : H) :
    f (((g : H ⧸ J.subgroupOf H).out : H) : G) = f g := by
  obtain ⟨k, hk, h⟩ := out_mul hJH g
  rw [h, hf _ g.2 _ hk]

theorem mem_offSet_mk {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (T : Finset ι) (g : H) :
    (g : H ⧸ J.subgroupOf H) ∈ offSet p K J H T ↔ ∀ v ∉ T, p v g ∈ K v := by
  obtain ⟨k, hk, h⟩ := out_mul hJH g
  have hk' := (hJ k (hJH hk)).1 hk
  simp only [offSet, Set.mem_setOf_eq, h, map_mul]
  exact forall₂_congr fun v _ => Subgroup.mul_mem_cancel_right _ (hk' v)

theorem p_shift_self {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} (hpe : ∀ v a, p v (e v a) = a)
    (v : ι) (g : G) : p v (shift e p v g) = 1 := by
  simp [shift, hpe]

theorem p_shift_ne {e : ∀ v, L v →* G} {p : ∀ v, G →* L v}
    (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) {u v : ι} (h : u ≠ v) (g : G) :
    p u (shift e p v g) = p u g := by
  simp [shift, hpe' u v h]

theorem shift_mem {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {H : Subgroup G}
    (he : ∀ v a, e v a ∈ H) (v : ι) {g : G} (hg : g ∈ H) : shift e p v g ∈ H :=
  H.mul_mem hg (H.inv_mem (he _ _))

theorem shift_val {E : Type} {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (v : ι) {g : G} (hg : g ∈ H) (hv : p v g ∈ K v) :
    f (shift e p v g) = f g := by
  rw [shift, ← map_inv]
  exact hf g hg _ (e_mem_J hpe hpe' he hJ v _ ((K v).inv_mem hv))

noncomputable def stepMap (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G)
    (he : ∀ v a, e v a ∈ H) (T : Finset ι) (v : ι) :
    offSet p K J H T × (L v ⧸ K v) → H ⧸ J.subgroupOf H :=
  fun x => ((⟨shift e p v ((x.1.1.out : H) : G) * e v x.2.out,
    H.mul_mem (shift_mem he v (x.1.1.out).2) (he _ _)⟩ : H) : H ⧸ J.subgroupOf H)

section step
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hpe hpe' he hJ

theorem stepMap_mem (T : Finset ι) (v : ι) (x : offSet p K J H T × (L v ⧸ K v)) :
    stepMap e p K J H he T v x ∈ offSet p K J H (insert v T) := by
  refine (mem_offSet_mk hJH hJ _ _).2 fun u hu => ?_
  rw [Finset.mem_insert, not_or] at hu
  simp only [map_mul, p_shift_ne hpe' hu.1, hpe' u v hu.1, mul_one]
  exact x.1.2 u hu.2

theorem stepMap_injective (T : Finset ι) (v : ι) (hv : v ∉ T) :
    Function.Injective (stepMap e p K J H he T v) := by
  rintro ⟨y1, a1⟩ ⟨y2, a2⟩ h
  have h' := (cls_eq hJ _ _).1 h
  have ha : a1 = a2 := by
    have := h' v
    simp only [map_mul, p_shift_self hpe, hpe, one_mul] at this
    rw [← QuotientGroup.out_eq' a1, ← QuotientGroup.out_eq' a2]
    exact QuotientGroup.eq.2 this
  have hy : y1 = y2 := by
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' y1.1, ← QuotientGroup.out_eq' y2.1]
    refine (cls_eq hJ _ _).2 fun u => ?_
    rcases eq_or_ne u v with rfl | hu
    · exact (K u).mul_mem ((K u).inv_mem (y1.2 u hv)) (y2.2 u hv)
    · have := h' u
      simpa only [map_mul, p_shift_ne hpe' hu, hpe' u v hu, mul_one] using this
  exact Prod.ext hy ha

theorem mem_range_stepMap (T : Finset ι) (v : ι) (y : H ⧸ J.subgroupOf H)
    (hy : y ∈ offSet p K J H (insert v T)) : y ∈ Set.range (stepMap e p K J H he T v) := by
  set g : H := y.out with hg
  let h : H := ⟨shift e p v g, shift_mem he v g.2⟩
  have hh : (h : H ⧸ J.subgroupOf H) ∈ offSet p K J H T := by
    refine (mem_offSet_mk hJH hJ _ _).2 fun u hu => ?_
    rcases eq_or_ne u v with rfl | huv
    · show p u (shift e p u g) ∈ K u
      rw [p_shift_self hpe]; exact (K u).one_mem
    · show p u (shift e p v g) ∈ K u
      rw [p_shift_ne hpe' huv]
      exact hy u (by simp [huv, hu])
  refine ⟨(⟨_, hh⟩, (p v g : L v ⧸ K v)), ?_⟩
  rw [← QuotientGroup.out_eq' y]
  refine (cls_eq hJ _ _).2 fun u => ?_
  obtain ⟨k, hk, hk'⟩ := out_mul hJH h
  rcases eq_or_ne u v with rfl | huv
  · simp only [map_mul, p_shift_self hpe, hpe, one_mul]
    exact QuotientGroup.eq.1 (QuotientGroup.out_eq' (p u g : L u ⧸ K u))
  · simp only [map_mul, p_shift_ne hpe' huv, hpe' u v huv, mul_one, hk']
    have e1 : p u (h : G) = p u (y.out : G) := p_shift_ne hpe' huv _
    simp only [mul_inv_rev, mul_assoc, e1, inv_mul_cancel, mul_one]
    exact (K u).inv_mem ((hJ k (hJH hk)).1 hk u)

theorem comp_stepMap {E : Type} [Zero E] (f : G → E) (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (T : Finset ι) (v : ι) (x : offSet p K J H T × (L v ⧸ K v)) :
    ((offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) ∘
      stepMap e p K J H he T v) x = f (shift e p v ((x.1.1.out : H) : G) * e v x.2.out) := by
  simp only [Function.comp, Set.indicator_of_mem (stepMap_mem hJH hpe hpe' he hJ T v x)]
  exact inv_out hJH f hf _

theorem zero_off_stepMap {E : Type} [Zero E] (f : G → E) (T : Finset ι) (v : ι) :
    ∀ x ∉ Set.range (stepMap e p K J H he T v),
      (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) x = 0 :=
  fun x hx => Set.indicator_of_notMem (fun h => hx (mem_range_stepMap hJH hpe hpe' he hJ T v x h)) _

theorem hasSum_step {E : Type} [NormedField E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : E) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : E} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s)
    (hsum : Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G))) :
    HasSum ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) (c * s) := by
  have hinj := stepMap_injective hJH hpe hpe' he hJ T v hv
  have hzero := zero_off_stepMap hJH hpe hpe' he hJ f T v
  have h1 := (hinj.hasSum_iff hzero).2 hsum.hasSum
  have h2 : HasSum (fun y : offSet p K J H T => c * f ((y.1.out : H) : G))
      (∑' y, (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) y) := by
    refine h1.prod_fiberwise fun y => ?_
    have := hfib _ (shift_mem he v (y.1.out).2) (p_shift_self hpe v _)
    rw [shift_val hpe hpe' he hJ f hf v (y.1.out).2 (y.2 v hv)] at this
    simpa only [comp_stepMap hJH hpe hpe' he hJ f hf] using this
  have h3 : HasSum (fun y : offSet p K J H T => c * f ((y.1.out : H) : G)) (c * s) :=
    (hasSum_subtype_iff_indicator.2 hs).mul_left c
  rw [h2.unique h3] at h1
  exact (hinj.hasSum_iff hzero).1 h1

theorem summable_step (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : ℝ) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : ℝ} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s) :
    Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) := by
  have hinj := stepMap_injective hJH hpe hpe' he hJ T v hv
  have hzero := zero_off_stepMap hJH hpe hpe' he hJ f T v
  refine (hinj.summable_iff hzero).1 ?_
  have hnn : 0 ≤ (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) ∘
      stepMap e p K J H he T v :=
    fun x => Set.indicator_nonneg (fun y _ => hf0 _ (y.out).2) _
  have hfib' : ∀ y : offSet p K J H T, HasSum
      (fun a : L v ⧸ K v => f (shift e p v ((y.1.out : H) : G) * e v a.out))
      (c * f ((y.1.out : H) : G)) := fun y => by
    have := hfib _ (shift_mem he v (y.1.out).2) (p_shift_self hpe v _)
    rwa [shift_val hpe hpe' he hJ f hf v (y.1.out).2 (y.2 v hv)] at this
  refine (summable_prod_of_nonneg hnn).2 ⟨fun y => ?_, ?_⟩
  · simpa only [comp_stepMap hJH hpe hpe' he hJ f hf] using (hfib' y).summable
  · simp only [comp_stepMap hJH hpe hpe' he hJ f hf, fun y => (hfib' y).tsum_eq]
    exact ((hasSum_subtype_iff_indicator.2 hs).mul_left c).summable
end step

section ind
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hJ

theorem offSet_empty : offSet p K J H ∅ = {((1 : H) : H ⧸ J.subgroupOf H)} := by
  ext y
  rw [Set.mem_singleton_iff, ← QuotientGroup.out_eq' y, mem_offSet_mk hJH hJ, cls_eq hJ]
  simp

theorem hasSum_base {E : Type} [AddCommMonoid E] [TopologicalSpace E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) :
    HasSum ((offSet p K J H ∅).indicator fun y => f ((y.out : H) : G)) (f 1) := by
  rw [offSet_empty hJH hJ]
  have := hasSum_single
    (f := ({((1 : H) : H ⧸ J.subgroupOf H)} : Set (H ⧸ J.subgroupOf H)).indicator
      fun y => f ((y.out : H) : G))
    ((1 : H) : H ⧸ J.subgroupOf H) (fun b hb => Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 hb) _)
  rw [Set.indicator_of_mem (Set.mem_singleton _), inv_out hJH f hf] at this
  exact this

include hpe hpe' he

theorem hasSum_offSet_nonneg (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (A : ι → ℝ)
    (hA : ∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (A v * f g))
    (T : Finset ι) :
    HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) ((∏ v ∈ T, A v) * f 1) := by
  induction T using Finset.induction_on with
  | empty => simpa using hasSum_base hJH hJ f hf
  | @insert v T hv ih =>
    rw [Finset.prod_insert hv, mul_assoc]
    exact hasSum_step hJH hpe hpe' he hJ f hf (A v) T v hv (hA v) ih
      (summable_step hJH hpe hpe' he hJ f hf0 hf (A v) T v hv (hA v) ih)

theorem hasSum_offSet_summable {E : Type} [NormedField E] [CompleteSpace E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (Z : ι → E)
    (hZ : ∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (Z v * f g))
    (hsum : Summable fun y : H ⧸ J.subgroupOf H => f ((y.out : H) : G)) (T : Finset ι) :
    HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) ((∏ v ∈ T, Z v) * f 1) := by
  induction T using Finset.induction_on with
  | empty => simpa using hasSum_base hJH hJ f hf
  | @insert v T hv ih =>
    rw [Finset.prod_insert hv, mul_assoc]
    exact hasSum_step hJH hpe hpe' he hJ f hf (Z v) T v hv (hZ v) ih (hsum.indicator _)
end ind

theorem hasSum_cosets_eulerProduct : ∀ {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)] (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G), J ≤ H → (∀ v a, p v (e v a) = a) → (∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) → (∀ v a, e v a ∈ H) → (∀ v a g, p v g = 1 → Commute (e v a) g) → (∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) → (∀ g ∈ H, {v | p v g ∉ K v}.Finite) → ∀ (Ψ : G → ℂ) (Φ : G → ℝ) (Z : ι → ℂ) (A : ι → ℝ) (z : ℂ), (∀ g ∈ H, ∀ k ∈ J, Ψ (g * k) = Ψ g) → (∀ g ∈ H, ∀ k ∈ J, Φ (g * k) = Φ g) → (∀ g ∈ H, ‖Ψ g‖ ≤ Φ g) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Ψ (g * e v a.out)) (Z v * Ψ g)) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Φ (g * e v a.out)) (A v * Φ g)) → Summable (fun v => A v - 1) → HasProd Z z → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) (z * Ψ 1) := by
  intro G ι _ L _ e p K J H hJH hpe hpe' he _ hJ hfin Ψ Φ Z A z hΨ hΦ hΨΦ hZ hA hA1 hz
  classical
  have hΦ0 : ∀ g ∈ H, 0 ≤ Φ g := fun g hg => (norm_nonneg _).trans (hΨΦ g hg)
  have hphi := hasSum_offSet_nonneg hJH hpe hpe' he hJ Φ hΦ0 hΦ A hA
  have hsA : Summable (fun v => |A v - 1|) := hA1.abs
  have hφ : Summable fun y : H ⧸ J.subgroupOf H => Φ ((y.out : H) : G) := by
    refine summable_of_sum_le (c := Real.exp (∑' v, |A v - 1|) * Φ 1)
      (fun y => hΦ0 _ (y.out).2) fun u => ?_
    let T : Finset ι := u.biUnion fun y => (hfin _ (y.out).2).toFinset
    have hu : ∀ y ∈ u, y ∈ offSet p K J H T := fun y hy v hv => by
      by_contra h
      exact hv (Finset.mem_biUnion.2 ⟨y, hy, (Set.Finite.mem_toFinset _).2 h⟩)
    calc ∑ y ∈ u, Φ ((y.out : H) : G)
        = ∑ y ∈ u, (offSet p K J H T).indicator (fun y => Φ ((y.out : H) : G)) y :=
          Finset.sum_congr rfl fun y hy =>
            (Set.indicator_of_mem (hu y hy) (fun y => Φ ((y.out : H) : G))).symm
      _ ≤ (∏ v ∈ T, A v) * Φ 1 :=
          sum_le_hasSum u (fun y _ => Set.indicator_nonneg (fun y _ => hΦ0 _ (y.out).2) _) (hphi T)
      _ ≤ Real.exp (∑' v, |A v - 1|) * Φ 1 := by
        refine mul_le_mul_of_nonneg_right ?_ (hΦ0 1 H.one_mem)
        calc ∏ v ∈ T, A v ≤ ∏ v ∈ T, |A v| := (le_abs_self _).trans (Finset.abs_prod _ _).le
          _ ≤ ∏ v ∈ T, Real.exp |A v - 1| :=
              Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v _ => by
                have h1 := Real.add_one_le_exp |A v - 1|
                have h2 := abs_sub_abs_le_abs_sub (A v) 1
                rw [abs_one] at h2
                linarith
          _ = Real.exp (∑ v ∈ T, |A v - 1|) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑' v, |A v - 1|) :=
              Real.exp_le_exp.2 (hsA.sum_le_tsum T fun v _ => abs_nonneg _)
  have hψ : Summable fun y : H ⧸ J.subgroupOf H => Ψ ((y.out : H) : G) :=
    Summable.of_norm_bounded hφ fun y => hΨΦ _ (y.out).2
  have hpsi := hasSum_offSet_summable hJH hpe hpe' he hJ Ψ hΨ Z hZ hψ
  have hlim : Tendsto (fun T : Finset ι =>
      ∑' y, (offSet p K J H T).indicator (fun y => Ψ ((y.out : H) : G)) y) atTop
      (𝓝 (∑' y : H ⧸ J.subgroupOf H, Ψ ((y.out : H) : G))) := by
    refine tendsto_tsum_of_dominated_convergence hφ (fun y => ?_)
      (Eventually.of_forall fun T y => ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (hfin _ (y.out).2).toFinset] with T hT
      refine (Set.indicator_of_mem (show y ∈ offSet p K J H T from fun v hv => ?_)
        (fun y => Ψ ((y.out : H) : G))).symm
      by_contra h
      exact hv (hT ((Set.Finite.mem_toFinset _).2 h))
    · exact (norm_indicator_le_norm_self _ _).trans (hΨΦ _ (y.out).2)
  have hlim2 : Tendsto (fun T : Finset ι =>
      ∑' y, (offSet p K J H T).indicator (fun y => Ψ ((y.out : H) : G)) y) atTop
      (𝓝 (z * Ψ 1)) := by
    simp only [fun T => (hpsi T).tsum_eq]
    exact (hz : Tendsto (fun s : Finset ι => ∏ b ∈ s, Z b) atTop (𝓝 z)).mul_const _
  rw [← tendsto_nhds_unique hlim hlim2]
  exact hψ.hasSum

end GlobalTheory.CosetEuler
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsEulerProductStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_cosets_eulerProduct_alt : ∀ {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)] (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G), J ≤ H → (∀ v a, p v (e v a) = a) → (∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) → (∀ v a, e v a ∈ H) → (∀ v a g, p v g = 1 → Commute (e v a) g) → (∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) → (∀ g ∈ H, {v | p v g ∉ K v}.Finite) → ∀ (Ψ : G → ℂ) (Φ : G → ℝ) (Z : ι → ℂ) (A : ι → ℝ) (z : ℂ), (∀ g ∈ H, ∀ k ∈ J, Ψ (g * k) = Ψ g) → (∀ g ∈ H, ∀ k ∈ J, Φ (g * k) = Φ g) → (∀ g ∈ H, ‖Ψ g‖ ≤ Φ g) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Ψ (g * e v a.out)) (Z v * Ψ g)) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Φ (g * e v a.out)) (A v * Φ g)) → Summable (fun v => A v - 1) → HasProd Z z → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) (z * Ψ 1) := by
  first | exact @GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | exact GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | (intros; apply GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

variable {D : D7}

theorem hasSum_of_eq {ι M : Type} [NormedAddCommGroup M] {f g : ι → M} {a b : M} (h : HasSum f a) (hf : ∀ i, g i = f i)
    (ha : b = a) : HasSum g b := by
  rwa [funext hf, ha]

theorem l2_smul_left {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (c : ℂ) (f g : X → ℂ) :
    l2 μ 𝓕 (c • f) g = c * l2 μ 𝓕 f g := by
  simp only [l2, Formalism.IndefR.Lift.pet, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem l2_self_eq_setIntegral_norm_sq {a b : ℕ} (μ : Measure (Mx D a b)) (𝓕 : Set (Mx D a b)) (f : Mx D a b → ℂ) :
    l2 μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  simp only [l2, Formalism.IndefR.Lift.pet, nrm2, Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal]

theorem mult_values (hP : GlobalTheory.Published.CuspRapidDecay) {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} (hθ : IsInfFam θ)
    {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (x : M.Vec) :
    U x ∈ bddAut V ∧ ∀ k ∈ J, ∀ g, U x (g * k) = χ k * U x g := by
  induction hU using Submodule.span_induction with
  | mem U h => exact ⟨⟨(h.aut x).cont, (h.aut x).left, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h.aut x) (h.cusp x)⟩, h.lev x⟩
  | zero => exact ⟨zero_mem _, fun _ _ _ => by simp⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, fun k hk g => by simp [ha.2 k hk, hb.2 k hk, mul_add]⟩
  | smul c a _ ha => exact ⟨(bddAut V).smul_mem c ha.1, fun k hk g => by simp [ha.2 k hk, mul_left_comm]⟩

theorem part_eigen {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ} {U : MMap M}
    (hU : U ∈ partFull θ M J χ Sb c) (x : M.Vec) (w d R) (h : Hecke₂ V J χ Sb w d R) :
    heckeLin V R (U x) = c w d • U x := by
  have h1 := hU.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
  exact congrArg (fun T : MMap M => T x) (h1 w d R h)

theorem isParamVec_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : IsParamVec σ J L h ρ' (f x) B) : IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

def satur (V : HSp D) (J : Subgroup (GA D V)) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GA D V) where
  carrier := {g | g ∈ GfC V ∧ ∃ k ∈ J, ∀ v ∈ S, projV V v g = projV V v k}
  one_mem' := ⟨one_mem _, 1, one_mem _, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, k, hk, h⟩ ⟨hb, k', hk', h'⟩
    exact ⟨mul_mem ha hb, k * k', mul_mem hk hk', fun v hv => by rw [map_mul, map_mul, h v hv, h' v hv]⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk, h⟩
    exact ⟨inv_mem ha, k⁻¹, inv_mem hk, fun v hv => by rw [map_inv, map_inv, h v hv]⟩


set_option maxHeartbeats 1000000 in
theorem zeta_sum (hG : GlobalTheory.Published.UnramifiedDoublingGL) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (rS : S.rank = D.R.nV)
    (rT : T.rank = D.R.r) {μ : Measure (WO S T)} {𝓧 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓧)
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hu : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sb → UnrAt χS w ∧ UnrAt χT w)
    {K J : Subgroup (GA D T)} {χ : GA D T → ℂ} (hKJ : K ≤ J) (hidx : K.relIndex J ≠ 0) (hJf : J ≤ GfC T)
    (hJ : ∀ g ∈ GfC T, g ∈ J ↔ (∃ k ∈ J, ∀ v ∈ Sb, projV T v g = projV T v k) ∧ ∀ v ∉ Sb, projV T v g ∈ Kv T v)
    (hfin : ∀ g : GA D T, {v | projV T v g ∉ Kv T v}.Finite) (hχ : ∀ k ∈ J, ‖χ k‖ = 1)
    {f : WO S T → ℂ} (hvac : ∀ v ∉ Sb, VacFin ψ S T v f) (hlaw : ∀ k ∈ J, om (1, k) f = χ k • f)
    (hvan : ∀ g ∈ GfC T, g ∉ satur T J Sb → l2 μ 𝓧 (om (1, g) f) f = 0)
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν)
    (F₁ F₂ : bddAut T) (hlev : ∀ k ∈ J, ∀ g, F₁.1 (g * k) = χ k * F₁.1 g) {B : Fam D.host.E} (hB : IsParamFunV T Sb F₁.1 B)
    (hb : Bounded (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2))
    (hc : Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (GlobalTheory.LFun.twist B (val χS)⁻¹) ((1 + (D.R.t : ℂ)) / 2)) :
    HasSum (fun y : FinCos T K => l2 μ 𝓧 (om (1, y.rep) f) f * starRingEnd ℂ (l2 ν 𝓕 (rTr T y.rep F₁) F₂))
      ((K.relIndex J : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (LSD D Sb B χS ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) *
        starRingEnd ℂ (l2 ν 𝓕 F₁ F₂)) := by
  obtain ⟨hun, hℓ⟩ := GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded D T
  obtain ⟨ℓ, hℓ, hbd⟩ := hℓ ν 𝓕 hν h𝓕 F₂
  obtain ⟨C, hC⟩ := hbd F₁
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  choose φ hφ hφ' using fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
    GlobalTheory.T.weilMatrixCoefficient_vacua_unramifiedPlace D ψ S T χS χT om hW μ 𝓧 hμ v.1 fun w h => hu w (h ▸ v.2)
  rw [rS] at hφ
  obtain ⟨A, hA, hA'⟩ := GlobalTheory.T.localZetaSums_absolutely_convergent_uniform hG D T rT (val χS) (norm_val χS) Sb φ hφ
  let co : GA D T → ℂ := fun g => l2 μ 𝓧 (om (1, g) f) f
  let Ψ : GA D T → ℂ := fun g => co g * starRingEnd ℂ (ℓ (bddRep T g F₁))
  have hmul : ∀ g k : GA D T, om (1, g * k) f = om (1, g) (om (1, k) f) := fun g k => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have co1 : ∀ g, ∀ k ∈ J, co (g * k) = χ k * co g := fun g k hk => by
    simp only [co, hmul, hlaw k hk, map_smul, l2_smul_left]
  have F1 : ∀ k ∈ J, bddRep T k F₁ = χ k • F₁ := fun k hk => Subtype.ext (funext fun g => hlev k hk g)
  have Ψ1 : ∀ g, ∀ k ∈ J, Ψ (g * k) = Ψ g := fun g k hk => by
    have h1 : χ k * starRingEnd ℂ (χ k) = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ k hk]; simp
    simp only [Ψ, co1 g k hk, map_mul, Module.End.mul_apply, F1 k hk, map_smul, smul_eq_mul]
    linear_combination (co g * starRingEnd ℂ (ℓ (bddRep T g F₁))) * h1
  have co2 : ∀ (v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}) g, projV T v.1 g = 1 → ∀ a,
      co (g * embV T v.1 a) = φ v a * co g := fun v g hg a => by
    simp only [co]
    rw [← (commute_emb D.sp.cm.sig T.gram a hg).eq, hmul]
    exact hφ' v a _ _ (GlobalTheory.T.weilOperator_keeps_latticeVacuum_of_trivialAt D ψ S T χS χT om hW v.1 g hg f (hvac v.1 v.2)) (hvac v.1 v.2)
  have hJH : J ≤ satur T J Sb := fun k hk => ⟨hJf hk, k, hk, fun _ _ => rfl⟩
  have key := GlobalTheory.T.hasSum_cosets_eulerProduct_alt (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => embV T v.1) (fun v => projV T v.1)
    (fun v => Kv T v.1) J (satur T J Sb) hJH (fun v a => proj_emb_self _ _ _ _)
    (fun u v h a => proj_emb_ne _ _ (fun e => h (Subtype.ext e)) a)
    (fun v a => ⟨mem_finPts.2 (projInf_emb _ _ _ _), 1, one_mem _, fun u hu' => by
      rw [map_one]; exact proj_emb_ne _ _ (fun e : u = v.1 => v.2 (e ▸ hu')) a⟩)
    (fun v a g hg => commute_emb _ _ a hg)
    (fun g hg => (hJ g hg.1).trans ⟨fun h v => h.2 v.1 v.2, fun h => ⟨hg.2, fun v hv => h ⟨v, hv⟩⟩⟩)
    (fun g _ => (hfin g).preimage Subtype.val_injective.injOn)
    Ψ (fun g => C * ‖co g‖) _ A _ (fun g _ => Ψ1 g) (fun g _ k hk => by rw [co1 g k hk, norm_mul, hχ k hk, one_mul])
    (fun g _ => by
      simp only [Ψ, norm_mul, RCLike.norm_conj]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hC g) (norm_nonneg _))
    (fun v g _ hg => by
      have h1 := GlobalTheory.T.hasSum_localSphericalZeta_unramified hG D T rT χS (rS ▸ hW.resS) v.1 (fun w h => (hu w (h ▸ v.2)).1) (φ v) (hφ v) _
        ((bddRep T).comp (embV T v.1)) (by
          obtain ⟨b, b1, b2, b3⟩ := hun
          exact ⟨b, b1, b2, fun g => b3 _⟩) F₁ B
        (fun w h => ⟨isParamVec_sub (bddAut T).subtype (fun _ _ => rfl) Subtype.val_injective (hB v.1 v.2 w h),
          (hb w (show w.under (𝓞 D.host.F) ∉ (Sb : Set _) from h ▸ v.2)).2⟩) (ℓ ∘ₗ bddRep T g)
        ⟨C, fun a => by
          have := hC (g * embV T v.1 a)
          rwa [map_mul] at this⟩
      refine hasSum_of_eq (h1.mul_left (co g)) (fun a => ?_) ?_
      · simp only [Ψ, co2 v g hg, map_mul, Module.End.mul_apply, LinearMap.comp_apply, MonoidHom.comp_apply]
        ring
      · simp only [Ψ, LinearMap.comp_apply]
        ring)
    (fun v g _ hg => by
      refine hasSum_of_eq ((hA' v).mul_right (C * ‖co g‖)) (fun a => ?_) rfl
      rw [co2 v g hg, norm_mul]
      ring)
    hA (GlobalTheory.T.hasProd_localTwistedLFactor_div_unitaryLocalFactor D Sb B χS hc)
  have fin := GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt K J (satur T J Sb) (GfC T) hKJ hJH (fun g hg => hg.1) hidx Ψ _
    (fun g hg hg' => by simp only [Ψ, co, hvan g hg hg', zero_mul]) (fun g _ => Ψ1 g) key
  refine hasSum_of_eq fin (fun y => ?_) ?_
  · simp only [Ψ, co, hℓ, coe_bddRep, FinCos.rep]
  · have : ((1, 1) : GA D S × GA D T) = 1 := rfl
    simp only [Ψ, co, this, map_one, Module.End.one_apply, l2_self_eq_setIntegral_norm_sq, hℓ]
    ring


set_option maxHeartbeats 1000000 in
theorem finiteZetaL : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
      [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F := by
  classical
  intro hP _ hG D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨hft, hvac⟩ := GlobalTheory.T.levelVector_finiteDatum_isTheta_vacuum_off R F i t σ s P cμ cη m ω BW f₀ f c io hd
  have hlaw := GlobalTheory.T.finiteLevelDatumVector_transforms_by_levelCharacter R F i t σ s P cμ cη m ω BW f₀ f c io hd
  obtain ⟨hC, -, -, -, hch, hW, -, hf, -⟩ := hd
  obtain ⟨-, e, he, hΘ⟩ := isLevelVec_iff.1 hf
  have rV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨a, bV⟩ := hC.lev.βV i
  obtain ⟨b, bW⟩ := hC.lev.βW i
  rw [one_pow] at bV bW
  obtain ⟨hs, hJ, hfin, hχ⟩ := GlobalTheory.T.datumLevel_hyperspecial_off_finite_places D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i P) (finS R t) bW fun PP h =>
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ (h.resolve_right (Finset.notMem_empty _)))
  obtain ⟨hKJ, hidx, hidx'⟩ := GlobalTheory.T.principalLevel_relIndex_liftLevel_eq_card D T R.toLevCh A.μ0 hC.lev _ e he Finset.subset_union_left i P
  have hu := (GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hC.lev i t s cμ cη m hch).2.2
  have hvan : ∀ g ∈ GfC (Wc D i), g ∉ satur (Wc D i) (levG _ (R.βW i) (R.datWp i P)) (finS R t) →
      l2 μ 𝓧 (ω (1, g) f) f = 0 := fun g hg hg' => by
    refine GlobalTheory.T.thetaTranslate_orthogonal_of_support_moved_off D _ _ _ _ _ ω hW _ _ sdV sdW _ e he f₀ _ f (GlobalTheory.T.levelFiniteDatum_isSchwartzBruhat_half D _ _ _ _ _ _ _ _ _ _ e sdV sdW bV.1 bW.1 he) hΘ hft μ 𝓧 hμ g hg
      fun x hx => by_contra fun hx' => hg' ⟨hg, ?_⟩
    obtain ⟨k, hk, h⟩ := GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate D _ _ _ _ _ _ _ _ _ e sdW bW.1 (by rw [rV, rW]; exact Nat.le_add_right _ _) rfl he
      (fun PP => Finset.mem_union) g hg x hx hx'
    refine ⟨k, hk, fun v hv => ?_⟩
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    exact h PP hPP
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hU0 : (R.HW i σ).e x ≠ 0 := fun h => hx0 ((hC.models.HW i σ).1 (h.trans (map_zero _).symm))
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, (R.HW i σ).e x v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hU0 (MultilinearMap.ext h)
  obtain ⟨m1, m2⟩ := mult_values hP hC.models.inf hx.1 v₀
  obtain ⟨B, hB, hb⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D (Wc D i) _ _ (finS R t) hs _ m1 hv₀ m2 ev (part_eigen hx v₀)
  have hsys := (isParamFunV_iff_of_mem_partFull hs hx hv₀ B).1 hB
  rw [rW] at hb
  have hconv := hb.converges_twist_val cμ (s := (1 + (D.R.t : ℂ)) / 2) (by
    have h5 : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have : ((1 + (D.R.t : ℂ)) / 2).re = (1 + (D.R.t : ℝ)) / 2 := by
      rw [show (1 + (D.R.t : ℂ)) / 2 = (((1 + (D.R.t : ℝ)) / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    rw [this]
    linarith)
  refine ⟨B, rW ▸ hsys, fun w hw => (hb w (offS_iff.1 hw)).2, hconv, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  by_cases h0 : U₁ v₁ = 0
  · have : ∀ g, rTr (Wc D i) g 0 = 0 := fun _ => rfl
    simp only [h0, this, petW, l2, Formalism.IndefR.Lift.pet, Pi.zero_apply, zero_mul, integral_zero, map_zero, mul_zero]
    exact hasSum_zero
  obtain ⟨n1, n2⟩ := mult_values hP hC.models.inf h₁.1 v₁
  rw [← hidx]
  exact zeta_sum hG hW rV rW hμ hu hKJ (hidx ▸ hidx') (fun k hk => hk.1) hJ hfin hχ hvac hlaw hvan (hC.models.νW i).1.1
    (hC.models.νW i).2 ⟨_, n1⟩ ⟨_, (mult_values hP hC.models.inf h₂ v₂).1⟩ n2
    ((isParamFunV_iff_of_mem_partFull hs h₁ h0 B).2 hsys) hb hconv

end GlobalTheory.FinZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F := by
  first | exact @GlobalTheory.FinZeta.finiteZetaL | exact GlobalTheory.FinZeta.finiteZetaL | (intros; apply GlobalTheory.FinZeta.finiteZetaL <;> assumption)
end

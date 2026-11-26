module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DatumTopStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsWeilDatumOOmTAtLast
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEq
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumProd
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEqProd
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocFProdLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocFProdLevel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MovedDat
theorem locF_prod_level_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ (j : ℕ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP)), omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) y = ∏ i, GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (GlobalTheory.MovedDat.RdAt (G i) (pl i).1) (fun x => (G i).S.P.lam x) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f v n G pl hG j y
  have hlev := hG.lev
  have hRd : ∀ (i i' : Fin n) (h : i' = i) (PP : Formalism.L2.DIV.Pl D.host.E) (z : (G i').S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)),
      RdAt (G i') PP z g → RdAt (G i) PP (cast (congrArg (fun k => (↥(G k).S.P.J : Type _)) h) z) g := by
    intro i i' h; subst h; intro PP z g hz; exact hz
  have hlam : ∀ (i i' : Fin n) (h : i' = i) (z : (G i').S.P.J),
      (G i').S.P.lam z = (G i).S.P.lam (cast (congrArg (fun k => (↥(G k).S.P.J : Type _)) h) z) := by
    intro i i' h; subst h; intro z; rfl
  have hw : ∀ (w w' : (_root_.GlobalTheory.Fam.pk_z W).Pg) (h : w' = w) (k : Fin n) (z : (G k).S.P.J) (g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1)),
      RdAt (G k) w'.1 z (g w') → RdAt (G k) w.1 z (g w) := by
    intro w w' h; subst h; intro k z g hz; exact hz
  have key := GlobalTheory.LocMod.StepVec.omegaG_eq_prod (t := D.R.t) (j := j) (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1)
    (X := fun w => (G (pl.symm w)).S.P.J) (fun w => RdAt (G (pl.symm w)) w.1) (fun w x => (G (pl.symm w)).S.P.lam x)
    (fun g => by
      rw [(hlev g).1]
      constructor
      · intro h w
        obtain ⟨x, hx⟩ := h (pl.symm w)
        exact ⟨x, hw w (pl (pl.symm w)) (pl.apply_symm_apply w) _ x g hx⟩
      · intro h i
        obtain ⟨x, hx⟩ := h (pl i)
        exact ⟨_, hRd i (pl.symm (pl i)) (pl.symm_apply_apply i) _ x _ hx⟩)
    (fun g x hx => by
      have e := (hlev g.1).2 g.2 (fun i => cast (congrArg (fun k => (↥(G k).S.P.J : Type _)) (pl.symm_apply_apply i)) (x (pl i)))
        (fun i => hRd i (pl.symm (pl i)) (pl.symm_apply_apply i) _ (x (pl i)) _ (hx (pl i)))
      refine e.trans ?_
      rw [← Equiv.prod_comp pl (fun w => (G (pl.symm w)).S.P.lam (x w))]
      exact Finset.prod_congr rfl fun i _ => (hlam i (pl.symm (pl i)) (pl.symm_apply_apply i) (x (pl i))).symm)
    y
  refine key.trans ?_
  rw [← Equiv.prod_comp pl]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hF : ∀ i' : Fin n, i' = i →
      GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (RdAt (G i') (pl i).1) (fun x => (G i').S.P.lam x)
        (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) =
      GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (RdAt (G i) (pl i).1) (fun x => (G i).S.P.lam x)
        (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) := by
    intro i' h; subst h; rfl
  exact hF _ (pl.symm_apply_apply i)
end GlobalTheory.MovedDat
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocFProdLevelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_groups_matrix_reading_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ (j : ℕ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP)), omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) y = ∏ i, GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (GlobalTheory.MovedDat.RdAt (G i) (pl i).1) (fun x => (G i).S.P.lam x) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) := by
  first | exact @_root_.GlobalTheory.MovedDat.locF_prod_level_alt | exact _root_.GlobalTheory.MovedDat.locF_prod_level_alt | (intros; apply _root_.GlobalTheory.MovedDat.locF_prod_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiCompatPk
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiCompatPk
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Fam.chi_compat_pk_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : Formalism.IndefR.Datum.EAf D →+* k, (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi j PP) μ := by
  intro D L hT Gi Gl Kc Yd cX ex W hW k _ _ _ _ q PP hP hI π' hπ hR j hj1 hj2 μ hμ hC
  have hL := hW.bot.hyp.2.2.2.1.lev
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) =
      Formalism.IndefR.Datum.toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hUnr : UnramEverywhere D (_root_.GlobalTheory.Fam.pk_z W).eta :=
    GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta (Formalism.L2.Host.CharFrame.isEta _).unr
  have hη : (_root_.GlobalTheory.Fam.pk_z W).eta y = 1 := hUnr y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1 y = (_root_.GlobalTheory.Fam.pk_z W).mu0 j y := by
    unfold Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  have hH1 := hL.mu0 ⟨j - 1, by omega⟩
  have hH2 := hL.chi ⟨j - 1, by omega⟩
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiCompatPkStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_at_level_place_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : Formalism.IndefR.Datum.EAf D →+* k, (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi j PP) μ := by
  first | exact @_root_.GlobalTheory.Fam.chi_compat_pk_alt | exact _root_.GlobalTheory.Fam.chi_compat_pk_alt | (intros; apply _root_.GlobalTheory.Fam.chi_compat_pk_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEqProd
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MovedDat
open GlobalTheory.LocMod.StepVec
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
end GlobalTheory.MovedDat
namespace GlobalTheory.MovedDat
open GlobalTheory.LocMod.StepVec
theorem phi_down_eq_alt (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (G0 : GLoc v)
    (π' : Formalism.IndefR.Datum.EAf D →+* G0.k) (hπ : ∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) (j a : ℕ) (ha : j + a = G0.s)
    (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank)
    (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin (Yc D (j + 1)).rank)
    (mS : MovedTo (ofSplit G0.q) (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      (((G0.FY j (a + 1) (by omega)).β * ((G0.S.T (Fin D.R.t)).bas j (a + 1) (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega) (ea.symm i)))
    (mT : MovedTo (ofSplit G0.q) (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
      (((G0.FY (j + 1) a (by omega)).β * ((G0.S.T (Fin D.R.t)).bas (j + 1) a (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega) (eb.symm i)))
    (x : WO (Yc D j) (Yc D (j + 1))) :
    ((G0.S.T (Fin D.R.t)).Phi j a ha ((ofSplit G0.q).down (G0.FY j (a + 1) (by omega)) (G0.FY (j + 1) a (by omega)) x)) =
      G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j
        (((frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
          (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)).map π').submatrix eb ea) := by
  have hS := map_eq_of_movedTo (ofSplit G0.q) (G0.FY j (a + 1) (by omega)) hπ _ _ mS
  have hT := map_eq_of_movedTo (ofSplit G0.q) (G0.FY (j + 1) a (by omega)) hπ _ _ mT
  have key := coords_down (ofSplit G0.q) _ _ hπ (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega)))
    (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega))) ea eb hS hT
    (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)
  rw [down_moved_actO] at key
  rw [← key]
  rfl
end GlobalTheory.MovedDat
namespace GlobalTheory.MovedDat
theorem moved_datum_eq_prod_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (a : Fin n → ℕ) (ha : ∀ i, j + a i = (G i).s), ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x : WO (Yc D j) (Yc D (j + 1)), (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧ IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) * omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) else 0) = κ * (if IsHalf (∑ i, (G i).q.e) x then ∏ i, ((G i).S.T (Fin D.R.t)).Phi j (a i) (ha i) ((ofSplit (G i).q).down ((G i).FY j (a i + 1) (by have := ha i; omega)) ((G i).FY (j + 1) (a i) (by have := ha i; omega)) x) else 0) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hRow v hv hVT n G pl hGP hGR j hj a ha
  refine ⟨1, one_ne_zero, fun x => ?_⟩
  rw [one_mul, isHalf_actO_iff]
  choose π' hπ hred hint hres using fun i => GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D (G i).k (G i).q (pl i).1 (hGR.idem i).1
  choose ea hea mS using fun i => hGR.frame i j (a i + 1) (by have := ha i; omega)
  choose eb heb mT using fun i => hGR.frame i (j + 1) (a i) (by have := ha i; omega)
  have hC := fun i => _root_.GlobalTheory.MovedDat.phi_down_eq_alt D L hT Gi Gl Kc Yd cX ex W f v (G i) (π' i) (hπ i) j (a i) (ha i) (ea i) (eb i) (mS i) (mT i) x
  by_cases hx : IsHalf (∑ i, (G i).q.e) x
  · rw [if_pos hx]
    have hx' := (isHalf_actO_iff _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ _ x).2 hx
    have hQ : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP),
        omegaQ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi
          (fun _ => 1) Frm.B).r (fun _ => 1) 1 y = 1 := fun y => by
      rw [omegaQ, dite_eq_left (by simp)]; simp
    by_cases hI : IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
      (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))
    · rw [if_pos ⟨hx, hI⟩, hQ, mul_one, _root_.GlobalTheory.T.local_groups_matrix_reading_alt D L hT Gi Gl Kc Yd cX ex W u f v n G pl hGR j]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hC i, GlobalTheory.LocMod.StepVec.redM_eq_map (pl i).1 hI, GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum D f.c v (G i) (pl i).1 (π' i) (hπ i) (hred i) (_root_.GlobalTheory.Fam.pk_z W).chi j
        (fun c hc => _root_.GlobalTheory.T.reduction_at_level_place_alt D L hT Gi Gl Kc Yd cX ex W hP (G i).k (G i).q (pl i).1 (pl i).2 (hGR.idem i).1 (π' i) (hπ i) (hred i)
          (c + 1) (by omega) (by omega) _ ((G i).S.tame _) (hGR.mu i (c + 1) (by omega) (by omega)))
        _ _ (r_le_Y j) (ea i) (eb i) (hea i) (heb i)]
      rfl
    · rw [if_neg (fun h => hI h.2)]
      symm
      by_contra hne
      apply hI
      have hnz := fun i h => hne (Finset.prod_eq_zero (Finset.mem_univ i) h)
      intro r s
      refine GlobalTheory.T.integral_finiteAdele_of_split_place_components D n (fun i => (G i).k) (fun i => (G i).q) (fun i => (pl i).1) (fun i => (hGR.idem i).1)
        (fun i l h => pl.injective (Subtype.ext h)) π' hπ hint _ ?_ fun i => ?_
      · rw [← GlobalTheory.LocMod.StepVec.frMapO_smul]
        congr 1
        exact Matrix.ext fun r' s' => hx' r' s'
      · have h1 := hnz i
        rw [hC i] at h1
        have h2 := GlobalTheory.StepData.TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ _ j).symm ((eb i).symm r)) ((ea i).symm s)
        simpa using h2
  · rw [if_neg (fun h => hx h.1), if_neg hx]
end GlobalTheory.MovedDat
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEqProdStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_exponents_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (a : Fin n → ℕ) (ha : ∀ i, j + a i = (G i).s), ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x : WO (Yc D j) (Yc D (j + 1)), (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧ IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) * omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) else 0) = κ * (if IsHalf (∑ i, (G i).q.e) x then ∏ i, ((G i).S.T (Fin D.R.t)).Phi j (a i) (ha i) ((ofSplit (G i).q).down ((G i).FY j (a i + 1) (by have := ha i; omega)) ((G i).FY (j + 1) (a i) (by have := ha i; omega)) x) else 0) := by
  first | exact @_root_.GlobalTheory.MovedDat.moved_datum_eq_prod_alt | exact _root_.GlobalTheory.MovedDat.moved_datum_eq_prod_alt | (intros; apply _root_.GlobalTheory.MovedDat.moved_datum_eq_prod_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumProd
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.MidDat
end GlobalTheory.MidDat
open GlobalTheory.MidDat in
theorem GlobalTheory.MidDat.moved_datum_prod_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) → ∃ κ : ℂ, κ ≠ 0 ∧ ∃ Lp : Fin n → GlobalTheory.SeeSaw.LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M', (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, (Lp i).e = (G i).eg j) ∧ (∀ i, IntIn (Lp i).q (Yc D j) (Lp i).FS (v.N j) ∧ IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FT (v.N (j + 1))) ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∃ F, IsThetaFunO f.c.ψ (Yc D j) (Yc D (j + 1)) F ∧ IsThetaAt f.c.ψ (symplO (Yc D j) (Yc D (j + 1))) (heisO f.c.ψ (Yc D j) (Yc D (j + 1))) (∑ i, (Lp i).q.e) (latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) fun _ => True) 1 ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) (GlobalTheory.SeeSaw.prodDat Lp) F ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  have ha : ∀ i, j + ((G i).s - j) = (G i).s := fun i => by have := (G i).hs; omega
  have hA := _root_.GlobalTheory.T.descent_data_step_exponents_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj (fun i => (G i).s - j) ha
  obtain ⟨κ, hκ, hdat⟩ := hA
  have ho : ∀ i, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ x ∈ o.support, IsHalf ((G i).q.e + cA D (G i).q.e) x) ∧
      ∀ Tm, (ofSplit (G i).q).IsModel f.c.ψ ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit (G i).q).up ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) x ∈ latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) (· = (G i).q.v)} (fun _ => 1) →
        Tm Φ₁ = comb f.c.ψ (Yc D j) (Yc D (j + 1)) o (Tm Φ₀) := fun i => exists_o hstd (G i).q _ _ hM hM'
  choose o ho1 ho2 using ho
  let Lp : Fin n → LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M' := fun i =>
    { k := (G i).k, q := (G i).q, unit := (G i).unit, Y := _, Y' := _,
      FS := (G i).FY j ((G i).s - j + 1) (by have := ha i; omega), FT := (G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega),
      Φ := ⟨((G i).S.T (Fin D.R.t)).Phi j ((G i).s - j) (ha i), (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ (ha i)⟩,
      e := (G i).eg j, e_is := (G i).eg_is j _ (ha i), o := o i, o_at := ho1 i, o_is := ho2 i }
  refine ⟨κ, hκ, Lp, fun i => rfl, fun i => rfl, fun i => ⟨(G i).latY _ _ _, (G i).latY _ _ _⟩, fun d hd => ?_⟩
  obtain ⟨-, e, he, hθ⟩ := hd.2
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sdY : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((_root_.GlobalTheory.Fam.pk_z W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
  have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
  have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vac j) := hd₀.2.1.2.theta
  have hcth := GlobalTheory.VecTheta.isThetaFunO_stepVec hd.2
  have he' : IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg) := by simpa only [datY, Finset.union_empty] using he
  have hee : e = ∑ i, (G i).q.e := idem_eq he' _ pl fun i => (hRead.idem i).1
  have hmove := GlobalTheory.VacMove.isThetaAt_moveLat D f.c.ψ _ _ _ _ _ hWe ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (sdY j (by omega)) hM (sdY (j + 1) hj) hM'
    _ hb _ hb' hmv hmv' e _ _ _ (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) hvth hcth hθ
  subst hee
  have hfun : (fun x => (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧
          IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then
        omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1))
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) *
          omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)))
        else 0)) = κ • prodDat Lp := funext fun x => hdat x
  rw [hfun] at hmove
  refine ⟨κ⁻¹ • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)),
    GlobalTheory.OrientedHeis.theta_smul _ (hWe.om_pres _ _ hcth), isThetaAt_smul hκ hmove, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hκ, one_smul]
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumProdStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_vector_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) → ∃ κ : ℂ, κ ≠ 0 ∧ ∃ Lp : Fin n → GlobalTheory.SeeSaw.LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M', (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, (Lp i).e = (G i).eg j) ∧ (∀ i, IntIn (Lp i).q (Yc D j) (Lp i).FS (v.N j) ∧ IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FT (v.N (j + 1))) ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∃ F, IsThetaFunO f.c.ψ (Yc D j) (Yc D (j + 1)) F ∧ IsThetaAt f.c.ψ (symplO (Yc D j) (Yc D (j + 1))) (heisO f.c.ψ (Yc D j) (Yc D (j + 1))) (∑ i, (Lp i).q.e) (latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) fun _ => True) 1 ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) (GlobalTheory.SeeSaw.prodDat Lp) F ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • F := by
  first | exact @_root_.GlobalTheory.MidDat.moved_datum_prod_alt | exact _root_.GlobalTheory.MidDat.moved_datum_prod_alt | (intros; apply _root_.GlobalTheory.MidDat.moved_datum_prod_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsRest
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsRest
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MidVacLat
variable {D : D7}
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j hj d₀ hd₀
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sd0 : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j (by omega))
  have sd1 : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) hj)
  obtain ⟨M, hM, hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd0).1 (f.g.b j)
  obtain ⟨M', hM', hmv'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd1).1 (f.g.b (j + 1))
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hvth := hd₀.2.1.2.theta
  have hvlat := hd₀.2.1.2.lat
  exact ⟨M, M', hM, hM', hmv _, hmv' _, hWe.om_pres _ _ hvth,
    isLatVac_move hWe sd0 hM sd1 hM' (hmv _) (hmv' _) hvth hvlat⟩
end GlobalTheory.MidVacLat
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsRestStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_lattice_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  first | exact @_root_.GlobalTheory.MidVacLat.main_alt_alt | exact _root_.GlobalTheory.MidVacLat.main_alt_alt | (intros; apply _root_.GlobalTheory.MidVacLat.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatVNEqOffLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatVNEqOffLevel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.Fam.OffLevel
open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit
variable {D : D7}
end GlobalTheory.Fam.OffLevel
end
open GlobalTheory.Fam.OffLevel in
theorem GlobalTheory.Fam.latV_N_eq_off_level_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ _ v _ hv n G pl _ _ j hj M M' hM hM' p hp
  have hP : ∀ q, (· = p) q → q ∉ v.gP := fun q hq => hq ▸ hp
  exact ⟨latV_eq_of_moves _ _ _ _ _ p (hv.moves j (by omega) _ hP) hM,
    latV_eq_of_moves _ _ _ _ _ p (hv.moves (j + 1) hj _ hP) hM'⟩
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatVNEqOffLevelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_self_dual_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  first | exact @_root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | exact _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | (intros; apply _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.MidDatum
theorem moved_datum_eq_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  obtain ⟨M, M', hM, hM', hmv, hmv', hvac⟩ := _root_.GlobalTheory.T.descent_data_step_lattice_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  obtain ⟨κ, hκ, Lp, hq, he, hint, hdat⟩ :=
    _root_.GlobalTheory.T.descent_data_step_vector_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hinj : Function.Injective fun i => (Lp i).q.v := by
    intro a b h
    apply hPin.inj
    simpa only [hq] using h
  have hP : ∀ i, (Lp i).q.v ∈ v.gP := fun i => (hPin.places _).2 ⟨i, hq i⟩
  obtain ⟨o', ho', hcomb⟩ := GlobalTheory.T.localCombinations_compose_finitely_many_places D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj (· ∈ v.gP) hP
  have hN : IsSelfDualC (Yc D j) (v.N j) := hv.sd j (by omega)
  have hN' : IsSelfDualC (Yc D (j + 1)) (v.N (j + 1)) := hv.sd (j + 1) hj
  have hoff := _root_.GlobalTheory.T.descent_data_step_self_dual_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj M M' hmv hmv'
  obtain ⟨F₀, hF₀t, hF₀at, -⟩ := hdat d₀ hd₀
  have hV := (GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F₀ hvac hF₀at hF₀t).2 (v.N j) (v.N (j + 1)) hN hN' hint
    (fun p hp => hoff p (by
      rw [hPin.places]
      rintro ⟨i, rfl⟩
      exact hp i (hq i).symm))
  have hth : IsThetaFunO f.c.ψ _ _ (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
    rw [hcomb]; exact hV.1
  refine ⟨M, M', o', hM, hM', ho', vac_true_mono _ hvac, ?_, ?_, κ, hκ, ?_⟩
  · rw [hcomb]; exact vac_true_mono _ hV
  · intro hne; rw [hcomb]; exact GlobalTheory.T.foldr_splitPlaceSecondCombinations_vacuum_ne_zero D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ hvac hne
  · intro d hd
    obtain ⟨F, hFt, hFat, hFeq⟩ := hdat d hd
    rw [hFeq]
    congr 1
    rw [(GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F hvac hFat hFt).1, GlobalTheory.T.heisenbergCombinations_distinct_split_places_collect D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj, ← hcomb,
      hPin.eG j hj _ hth]
    simp only [he]
end GlobalTheory.MidDatum
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEqStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_chain_step_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
  first | exact @_root_.GlobalTheory.MidDatum.moved_datum_eq_alt | exact _root_.GlobalTheory.MidDatum.moved_datum_eq_alt | (intros; apply _root_.GlobalTheory.MidDatum.moved_datum_eq_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsWeilDatumOOmTAtLast
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.GVecAt
section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
end Gen
end GlobalTheory.GVecAt
namespace GlobalTheory.GVecAt
theorem datum_mid_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := _root_.GlobalTheory.T.descent_data_chain_step_alt
theorem datum_top_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (M' : GlobalTheory.FinPl.Lat D.sp.X') (o' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), IsSelfDualC (Yc D (j + 1)) M ∧ IsSelfDualC D.sp.X' M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) ∧ ((omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0 → comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) := _root_.GlobalTheory.T.descent_data_top_step_alt
section Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
theorem exists_isWeilDatumO_omT_at_last (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) := by
  have hω := W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact hω
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩
end Fam
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ _root_.GlobalTheory.Fam.GVectorCondition f v s := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR
  have fin : ∀ {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) (e : WO S T →₀ ℂ), IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) →
      GlobalTheory.FinPl.CombAt P e → IsFinComb e := fun P e hψ he =>
    ((GlobalTheory.DisjComb.main D (_root_.GlobalTheory.Fam.pk_z W).ψ hψ _ _ P (fun _ => False) (fun _ _ h => h)).2.1 e he).1
  have mid : ∀ j, j + 1 < D.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1))
        (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
          (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P)) = c • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a') := by
    intro j hj
    by_cases hex : ∃ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := _root_.GlobalTheory.GVecAt.datum_mid_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j hj d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.Ψ j hj
    have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vac j) := hd₀.2.1.2.theta
    have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
    have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
    have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hΨ1 : v.Ψ j 1 1 1 = comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one, one_mul, one_mul]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.Ψ j hj 1 1 (one_mem _) 1 (one_mem _))
    have honz : comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.1 j hj
      apply hP
      rw [hΨ, one_mul, one_mul]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ _ hWe hinf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (f.g.b j) (f.g.b (j + 1))
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N j) M' (v.N (j + 1)) v.gP o o' _ hstd hM hM' (hv.sd j (by omega))
      (hv.sd (j + 1) hj) ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P a ha a' ha' => ?_⟩
    have hbase : (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) =
        (κ / c) • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P a a']
    exact fock hinf hWe _ _ _ _ (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd (hv.atG j).1) hvth hb hb' hbase P ha ha'
  have top : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c : ℂ, c ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d →
      ∀ P, omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
        (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P)) =
        c • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P) := by
    intro j h
    by_cases hex : ∃ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := _root_.GlobalTheory.GVecAt.datum_top_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j h d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.ΨT j h
    have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) := hd₀.2.1.2.theta
    obtain ⟨χS, χT, hWe⟩ := _root_.GlobalTheory.GVecAt.exists_isWeilDatumO_omT_at_last W j h
    have hb : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hb' : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
    have hΨ1 : v.ΨT j h 1 = comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.ΨT j h 1)
    have honz : comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.2 j h
      apply hP
      rw [hΨ]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ _ hWe hinf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (f.g.b (j + 1)) f.g.bT
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N (j + 1)) M' v.NT v.gP o o' _ hstd hM hM' (hv.sd (j + 1) (by omega))
      hv.sdT ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P => ?_⟩
    have hbase : omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) =
        (κ / c) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P]
    have := fock hinf hWe (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd ((hv.atG j).2.2 h)) hvth hb hb' hbase P
      (one_mem (GinfC _)) (one_mem (GinfC _))
    simpa only [one_mul] using this
  choose cm hcm using mid
  choose ct hct using top
  let s : ℕ → ℂ := fun i => if hi : i + 1 < D.R.m then cm i hi else
    match i with
    | 0 => 1
    | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1
  refine ⟨s, fun i => ?_, fun j hj d hd P a ha a' ha' => ?_, fun j h d hd P => ?_⟩
  · show (if hi : i + 1 < D.R.m then cm i hi else
      (match i with
      | 0 => 1
      | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1)) ≠ 0
    split_ifs with hi
    · exact (hcm i hi).1
    · split
      · exact one_ne_zero
      · split_ifs with hk
        · exact (hct _ hk).1
        · exact one_ne_zero
  · have hs : s j = cm j hj := dif_pos hj
    rw [hs]
    exact (hcm j hj).2 d hd P a ha a' ha'
  · have hs : s (j + 1) = ct j h := by
      show (if hi : j + 1 + 1 < D.R.m then cm (j + 1) hi else if hk : j + 2 * 0 + 2 = D.R.m then ct j hk else 1) = ct j h
      rw [dite_eq_right (by omega), dif_pos h]
    rw [hs]
    exact (hct j h).2 d hd P
end GlobalTheory.GVecAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsWeilDatumOOmTAtLastStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_scalars_gVec : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ _root_.GlobalTheory.Fam.GVectorCondition f v s := by
  first | exact @_root_.GlobalTheory.GVecAt.main_alt_alt | exact _root_.GlobalTheory.GVecAt.main_alt_alt | (intros; apply _root_.GlobalTheory.GVecAt.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDescentDataChain
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitDatum
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitDatum
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamSplit
end GlobalTheory.FamSplit
namespace GlobalTheory.FamSplit
theorem split_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ), j < D.R.m → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ), IsSDFrame V β Λ 1 ∨ IsSDFrame V β Λ (D.host.g 0 * D.host.g 1) → IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ vac → ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W j M Λ β vac dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t j M Λ β vac dQ ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac v ↔ v = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG vac) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW j hj V S M Λ β vac hSD hvac
  have hLev := hW.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hY⟩ := hLev.βY j hj
  have sdY : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j hj)
  have frY : Formalism.L2.DIV.IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) := hY.1
  have sdV : IsSelfDualC V Λ := hSD.elim (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _)
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _)
  have frV : Formalism.L2.DIV.IsFrame β Λ := hSD.elim (fun h => h.elim fun _ h => h.1) (fun h => h.elim fun _ h => h.1)
  have hex := GlobalTheory.PlaceDatum.stepVecExists D
  obtain ⟨⟨eG, heG⟩, hQt⟩ := _root_.GlobalTheory.T.level_places_disjoint_idempotents_alt W hW
  obtain ⟨fG, hfG⟩ := hex (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
    (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ∅
    (fun _ => 1) sdY sdV frY frV (Finset.disjoint_empty_right _) ⟨eG, heG⟩ vac hvac
  obtain ⟨dG, hdG, rfl⟩ := GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdV frY frV hfG
  have hdG' : GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dG := by
    simpa only [datY, Finset.union_empty] using hdG
  refine ⟨dG, ⟨hdG', hfG⟩, fun t => ?_⟩
  obtain ⟨hdis, hne, ⟨e, he⟩, ⟨eQ, heQ⟩⟩ := hQt t
  obtain ⟨fQ, hfQ⟩ := hex (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
    (datY _ D.R.r D.R.t j (r_le_Y j) ∅ ((_root_.GlobalTheory.Fam.pk_z W).Q t) (LevelP.triv _ _ _) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) Frm.B)
    ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) sdY sdV frY frV (Finset.disjoint_empty_left _) ⟨eQ, heQ⟩ vac hvac
  obtain ⟨dQ, hdQ, rfl⟩ := GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdV frY frV hfQ
  have hdQ' : GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dQ := by
    simpa only [datY, Finset.empty_union] using hdQ
  have hfull := GlobalTheory.T.thetaStepVector_eq_tupleComb_of_levelComb D _ _ (Yc D j) V _ _ _ _ _ _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi
    ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac dG dQ sdY sdV frY frV hdis hne ⟨e, he⟩ hdG' hdQ' hfG hfQ
  refine ⟨dQ, ⟨hdQ', hfQ⟩, fun v => ⟨fun hv => stepVecOf_unique hv hfull, ?_⟩⟩
  rintro rfl
  exact hfull
end GlobalTheory.FamSplit
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitDatumStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_frame_vacuum_step_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ), j < D.R.m → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ), IsSDFrame V β Λ 1 ∨ IsSDFrame V β Λ (D.host.g 0 * D.host.g 1) → IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ vac → ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W j M Λ β vac dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t j M Λ β vac dQ ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac v ↔ v = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG vac) := by
  first | exact @_root_.GlobalTheory.FamSplit.split_datum_alt | exact _root_.GlobalTheory.FamSplit.split_datum_alt | (intros; apply _root_.GlobalTheory.FamSplit.split_datum_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.StepSplit
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → (∀ j, j + 1 < D.R.m → ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) dQ ∧ (f.row t).vP j = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ ∀ j h, ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) dQ ∧ (f.row t).vT j h = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR
  have hlev := W.Q.charW.base.lev
  refine ⟨fun j hj => ?_, fun j h => ?_⟩
  · have hv := (hR.row W.P.A3.A.μ0).vP j hj
    obtain ⟨dG, hG, hQ⟩ := _root_.GlobalTheory.T.self_dual_frame_vacuum_step_alt W u hP j (by omega) (Yc D (j + 1)) _ ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) (Or.inr (hlev.βY (j + 1) hj)) hv.1
    refine ⟨dG, hG, fun t => ?_⟩
    obtain ⟨dQ, hdQ, hiff⟩ := hQ t
    exact ⟨dQ, hdQ, (hiff _).1 ((hR.row t).vP j hj)⟩
  · have hm : D.R.m = j + 1 + 1 := by omega
    have hv := (hR.row W.P.A3.A.μ0).vT j h
    obtain ⟨dG, hG, hQ⟩ := _root_.GlobalTheory.T.self_dual_frame_vacuum_step_alt W u hP (j + 1) (by omega) D.sp.X' _ (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX
      (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) (Or.inl hlev.βX) hv.1
    refine ⟨dG, hG, fun t => ?_⟩
    obtain ⟨dQ, hdQ, hiff⟩ := hQ t
    refine ⟨dQ, hdQ, (hiff _).1 ?_⟩
    have hvt := (hR.row t).vT j h
    have e : (_root_.GlobalTheory.Fam.pk_z W).chi D.R.m = (_root_.GlobalTheory.Fam.pk_z W).chi (j + 1 + 1) := congrArg _ hm
    rw [e] at hvt
    exact hvt
end GlobalTheory.StepSplit
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_data_chain_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → (∀ j, j + 1 < D.R.m → ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) dQ ∧ (f.row t).vP j = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ ∀ j h, ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) dQ ∧ (f.row t).vT j h = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) := by
  first | exact @_root_.GlobalTheory.StepSplit.main_alt_alt | exact _root_.GlobalTheory.StepSplit.main_alt_alt | (intros; apply _root_.GlobalTheory.StepSplit.main_alt_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBis
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.StepVacForm
section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
end Gen
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ ∀ w : VTup (f.t t), (∀ p, p ∈ w.Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ j, GlobalTheory.FinPl.CombAt (· ∈ w.Q) (w.eQ j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ w.Q) (w.eQT j h)) → _root_.GlobalTheory.Fam.RationalVectorCondition f w → _root_.GlobalTheory.Fam.VectorFunctionCondition f v w fun j => s j * ζ j := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hVT n G pl hGP hGR
  obtain ⟨s, hs, hGm, hGt⟩ := _root_.GlobalTheory.T.exists_ne_zero_scalars_gVec D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hVT n G pl hGP hGR
  obtain ⟨hSm, hSt⟩ := _root_.GlobalTheory.T.exists_descent_data_chain_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR
  refine ⟨s, hs, fun t => ?_⟩
  obtain ⟨ζ, hζ, hZm, hZt, -⟩ := _root_.GlobalTheory.TupRoot.weil_tuple_root_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR t
  refine ⟨ζ, hζ, fun w hwQ heQ hQ => ?_⟩
  have hc := W.Q.charW.base
  have eP : (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) = (· ∈ v.gP) :=
    funext fun p => propext (hVT.gP p).symm
  have eQ : (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) = (· ∈ w.Q) :=
    funext fun p => propext (hwQ p).symm
  have hd : ∀ p, p ∈ v.gP → ¬ p ∈ w.Q := fun p h h' => by
    obtain ⟨PP, h1, e1⟩ := (hVT.gP p).1 h
    obtain ⟨PP', h2, e2⟩ := (hwQ p).1 h'
    exact under_ne _ hc.lev t h1 h2 (e1.symm.trans e2)
  have hb : ∀ j, f.g.b j ∈ GfC _ := fun j => hVT.b j ▸ hv.b j
  have hbT : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
  refine ⟨fun j hj P a ha a' ha' => ?_, fun j h P => ?_⟩
  · obtain ⟨dG, hdG, hall⟩ := hSm j hj
    obtain ⟨dQ, hdQ, hvP⟩ := hall t
    have hvac := hdG.2.1.2
    rw [hVT.b, hVT.b]
    have key := step (c := s j * ζ j) (Ψ := v.Ψ j P a a') hvac.inf (hc.chain.ωY t j hj) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) hd ⟨hvac.theta, hvac.lat⟩ (by have h1 := hdG.1; rw [eP] at h1; exact h1)
      (by have h1 := hdQ.1; rw [eQ] at h1; exact h1) (hv.atG j).1 (heQ j).1
      (hb j) (hb (j + 1)) ha ha' (hQ.1 j hj dQ hdQ) P fun hth => by
        have e1 := hZm j hj (hb j) (hb (j + 1)) a ha a' ha' _ hth
        have e2 := hGm j hj dG hdG P a ha a' ha'
        refine e1.trans ?_
        rw [mul_comm, mul_smul]
        exact congrArg _ e2
    rw [← hvP] at key
    exact key
  · obtain ⟨dG, hdG, hall⟩ := hSt j h
    obtain ⟨dQ, hdQ, hvT⟩ := hall t
    have hvac := hdG.2.1.2
    rw [hVT.b, hVT.bT.1]
    have hWt := GlobalTheory.TupRoot.isWeil_rec (idx_top h) _ (hc.chain.ωX t)
    have key := step (c := s (j + 1) * ζ (j + 1)) (Ψ := v.ΨT j h P) hvac.inf hWt (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) hd ⟨hvac.theta, hvac.lat⟩ (by have h1 := hdG.1; rw [eP] at h1; exact h1)
      (by have h1 := hdQ.1; rw [eQ] at h1; exact h1) ((hv.atG j).2.2 h) ((heQ j).2 h)
      (hb (j + 1)) hbT (one_mem _) (one_mem _) (hQ.2 j h dQ hdQ) P fun hth => by
        have e1 := hZt j h _ hth
        have e2 := hGt j h dG hdG P
        rw [one_mul, one_mul]
        refine e1.trans ?_
        rw [mul_comm, mul_smul]
        exact congrArg _ e2
    rw [← hvT, one_mul, one_mul] at key
    exact key
end GlobalTheory.StepVacForm
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_scalars_roots_of_unity_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ ∀ w : VTup (f.t t), (∀ p, p ∈ w.Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ j, GlobalTheory.FinPl.CombAt (· ∈ w.Q) (w.eQ j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ w.Q) (w.eQT j h)) → _root_.GlobalTheory.Fam.RationalVectorCondition f w → _root_.GlobalTheory.Fam.VectorFunctionCondition f v w fun j => s j * ζ j := by
  first | exact @_root_.GlobalTheory.StepVacForm.main_alt_alt | exact _root_.GlobalTheory.StepVacForm.main_alt_alt | (intros; apply _root_.GlobalTheory.StepVacForm.main_alt_alt <;> assumption)
end
end

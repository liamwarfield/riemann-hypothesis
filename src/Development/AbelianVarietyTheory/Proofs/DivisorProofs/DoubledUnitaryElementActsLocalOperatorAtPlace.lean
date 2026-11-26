module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblActs

theorem schr_trans' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem liftV_one_mul' {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hunit : ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ))
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨(R 0)⁻¹ • fun t => T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul']
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

theorem dbl_acts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
      IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ (v : Pl (F := F)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G hB dd omd hS v p hp φ hφ
  refine acts_of_comm v B.ψ hB.std (omd p) (fun Φ hΦ => hS.pres p Φ hΦ)
    (fun μ hμ Φ hΦ => hS.unit μ hμ p Φ hΦ) ?_ φ hφ
  intro u hu x y Φ hΦ
  set w := dd.e.symm (x, y) with hw
  have he : dd.e (u • w) = (u • x, u • y) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h2 := hp u hu
  have e2 : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (u • w) = u • w := by
    simp only [actB]
    set P : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E) :=
      ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) with hP
    set c : AE F E := algebraMap (AF F) (AE F E) u with hc
    have hs1 : u • w = c • w := (algebraMap_smul (AE F E) u w).symm
    have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
    have h2' : c • (P - 1) = 0 := hs2 ▸ h2
    have : (c • w) * Pᵀ - c • w = w * (c • (P - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2'] at this
    simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    rw [hs1]
    exact this
  have h3 := hS.impl p (u • w) Φ hΦ
  simp only [Darboux.rho, he, e2] at h3
  exact h3

end GlobalTheory.DblActs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
      IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ (v : Pl (F := F)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) φ φ₁ := by
  first | exact @GlobalTheory.DblActs.dbl_acts | exact GlobalTheory.DblActs.dbl_acts | (intros; apply GlobalTheory.DblActs.dbl_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}


variable (G) in
abbrev spX (i j : ℕ) : HSp D := GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)


variable (G) in
def latX (i j : ℕ) : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E) :=
  GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1))) (G.Λ (.grid (i + 1) j))


variable (G) in
def homLatA (i j : ℕ) : AddSubgroup (WO (spW G i j) (spX G i j)) :=
  latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) (latX G i j) fun _ => True


variable (G) in
def homLatB (i j : ℕ) : AddSubgroup (WO (spW₁ G i j) (spX G i j)) :=
  latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) (latX G i j) fun _ => True


variable (G) in
def orderingsOnSpW (i j : ℕ) : Set (WO (spW G i j) (spX G i j)) :=
  {x | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) x ∈
      latO (negSp (spW G i j)) (spV G i j) (G.Λ (.grid (i + 1) (j + 1))) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) x) ∈
      latO (spV₁ G i j) (spW G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid (i + 1) (j + 1))) fun _ => True}


variable (G) in
def orderingsOnSpWOne (i j : ℕ) : Set (WO (spW₁ G i j) (spX G i j)) :=
  {y | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) y ∈
      latO (spW₁ G i j) (spV G i j) (G.Λ (.grid i j)) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) y) ∈
      latO (negSp (spV₁ G i j)) (spW₁ G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid i j)) fun _ => True}

section Vac

variable {W : G.Weil} (ρ : RealMatch W) (i j : ℕ)

def vacA : WO (spW G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) (ρ.vX i (j + 1))
    fun y => ρ.vT (i + 1) j (GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) y)

def vacB : WO (spW₁ G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := spW₁ G i j) (A := spV G i j) (B := spV₁ G i j) (ρ.vT i j)
    fun y => ρ.vX i j (GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) y)

theorem datumA_vac (t : T) : datumA W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) = vacA ρ i j := by
  unfold datumA
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

theorem datumB_vac (t : T) : datumB W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) = vacB ρ i j := by
  unfold datumB
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

end Vac

section Coord

variable (B : Frames G) (t : T) (i j : Fin D.R.m)

def frX : GL (Fin (spX G i j).rank) (EAf D) := GlobalTheory.Doubling.blkGL finSumFinEquiv (B.β i (j + 1), -B.β (i + 1) j)


variable (G) in
def colX (w : Pl D.host.E) : Fin (spX G i j).rank ≃ (locGrid G t w).Cols i j :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))


variable (G) in
def ordX (w : Pl D.host.E) :
    (locGrid G t w).Cols i j ≃ Fin ((locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j)) :=
  (stdSplit ((locGrid G t w).rank_square i j)).symm.trans finSumFinEquiv


variable (G) in
abbrev MatA (w : Pl D.host.E) : Type :=
  Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w)


variable (G) in
abbrev MatB (w : Pl D.host.E) : Type := Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w)

def linA (w : Pl D.host.E) (x : WO (spW G i j) (spX G i j)) : MatA G t i j w :=
  reindex (finCongr (rankW G t i j w)) (colX G t i j w)
    ((frMapO (spW G i j) (spX G i j) (B.β (i + 1) (j + 1)) (frX B i j) x).map (cpt w))ᵀ

def linB (w : Pl D.host.E) (y : WO (spW₁ G i j) (spX G i j)) : MatB G t i j w :=
  reindex (finCongr (rankW₁ G t i j w)) (colX G t i j w)
    ((frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) y).map (cpt w))


open Classical in
def prodA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (x : WO (spW G i j) (spX G i j)) : ℂ :=
  if IsHalf ε x then ∏ w ∈ locPl G t, Ξ w (linA B t i j w x) else 0


open Classical in
def prodB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (y : WO (spW₁ G i j) (spX G i j)) : ℂ :=
  if IsHalf (cA D ε) y then ∏ w ∈ locPl G t, Ψ w (linB B t i j w y) else 0

variable {W : G.Weil} (ρ : RealMatch W)

def IsLinA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (F : WO (spW G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) (heisO W.ψ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) ε
    (homLatA G i j) 1 (vacA ρ i j) (prodA B t i j ε Ξ) F

def IsLinB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (F : WO (spW₁ G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (spW₁ G i j) (spX G i j)) (heisO W.ψ (spW₁ G i j) (spX G i j)) (cA D ε)
    (homLatB G i j) 1 (vacB ρ i j) (prodB B t i j ε Ψ) F

end Coord

section Model

variable {i j : ℕ} (e : Num G i j)

def ptA (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

def ptB (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW₁ G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (spW₁ G i j).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

end Model

section Charts

variable (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (w : Pl D.host.E)


variable (G i j) in
abbrev ToA : Type :=
  ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatA G t i j w → ℂ)


variable (G i j) in
abbrev ToB : Type :=
  ((Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatB G t i j w → ℂ)

def IsLinModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (atPl w 1) (ptA e u)} {u | IsHalf (cA D (atPl w 1)) (ptA e u)}
    (fun u => linA B t i j w (ptA e u)) ι

def IsLinModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (cA D (atPl w 1)) (ptB e u)} {u | IsHalf (atPl w 1) (ptB e u)}
    (fun u => linB B t i j w (ptB e u)) ι

def IsMixModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι

def IsMixModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) ι

end Charts

section ZetaNonvanishing₂

variable (G) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)

def zetaA (Ξ : MatA G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  bigP (haarVol (KO (Kw w) _)) (unifAt w) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j) 1 Ξ

def zetaB (Ψ : MatB G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  smallP (haarVol (KO (Kw w) _)) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    ((locGrid G t w).nu i j * 1) Ψ

def levVol : ℝ :=
  (haarVol (KO (Kw w) (Fin ((locGrid G t w).rank (i, j))))).real ((givenLevel G t w (i, j)).map invT : Subgroup _)

end ZetaNonvanishing₂

section Std

variable (B : Frames G) (t : T) {i j : Fin D.R.m} (X : TriG G i j) (w : Pl D.host.E)

def chA : GL (Fin ((locGrid G t w).rank (i + 1, j + 1))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW G t i j w)) (invT ((loc w X.rA.β)⁻¹ * loc w (B.β (i + 1) (j + 1))))

def chB : GL (Fin ((locGrid G t w).rank (i, j))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW₁ G t i j w))
    (Units.map (Matrix.scalar (Fin (spW₁ G i j).rank)).toMonoidHom
        (Units.mk0 (xiAt w) ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)) *
      ((loc w X.rA'.β)⁻¹ * loc w (B.β i j)))

def chX : GL ((locGrid G t w).Cols i j) (Kw w) :=
  GlobalTheory.StepData.reGL (colX G t i j w) ((loc w (frX B i j))⁻¹ * loc w X.rW.β)

def locFst (Z : MatA G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdA ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chA B t X w).val * Z * (invT (chX B t X w)).val))

def locSnd (Y : MatB G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdB ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chB B t X w).val * Y * (chX B t X w).val))

end Std

end GlobalTheory.TopFlip

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
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
namespace GlobalTheory.WeilLocality

theorem comm_off : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a' × Fin (a + a') → AF F,
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')),
      om' (x, 1) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om' (x, 1) Φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v x hx u hu p q Φ hΦ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set w := Γ.M'.co.e.symm (p, q) with hw
  have he : Γ.M'.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) = 0 := hx u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((x, 1) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h0, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using h1
  have h2 := hW.impl (x, 1) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∃ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ GlobalTheory.WeilM.SB _ ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ (S φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v x hx
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set T := om' (x, 1) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (x, 1) Φ hΦ
  have hcomm := comm_off Bs Γ X om om' hTr v x hx
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace Bs.ψ hTr.base.std) hkeep (fun μ hμ Φ hΦ => hW.unit μ hμ (x, 1) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a' × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  refine ⟨fun φ t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)),
    fun φ hφ => ⟨?_, ?_⟩⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a' × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef]
    field_simp
    ring

end GlobalTheory.WeilLocality
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
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
theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∃ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ GlobalTheory.WeilM.SB _ ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ (S φ) := by
  first | exact @GlobalTheory.WeilLocality.locality | exact GlobalTheory.WeilLocality.locality | (intros; apply GlobalTheory.WeilLocality.locality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityW'

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hTr : IsTriple B G X om om') (v : Pl (F := F)) (h : UA σ G.W.J) (hh : h ∈ UAt σ G.W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin a' × Fin (a + a') → AF F)
    (Φ : (Fin a' × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a'))) :
      om' (1, h) (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (om' (1, h) Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set w := G.M'.co.e.symm (p, q) with hw
  have he : G.M'.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat h - 1) = 0 := hh u hu
  have hact : GlobalTheory.WeilM.actAB (cA σ) ((1, h) : UA σ G.V'.J × UA σ G.W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1
  have h2 := hW.impl (1, h) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v h hh φ hφ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set T := om' (1, h) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have hcomm := comm_off B G X om om' hTr v h hh
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (1, h) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a' × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h' := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h'
    exact h'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  refine ⟨fun t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a' × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp

end GlobalTheory.WeilLocalityW'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityW'.locality | exact GlobalTheory.WeilLocalityW'.locality | (intros; apply GlobalTheory.WeilLocalityW'.locality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA (Dinv xi_mem_Dinv int_of_xi)
open GlobalTheory.FunObj.Good (char_int mem_Dinv atPl_mul inc_mul_inc mem_intAE exists_pole isEquiv_Kw valued_alg psiAt_eq_one
  trace_inc_pair cpt_pair)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

namespace CondAA

theorem valued_genAt (w : Pl D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    Valued.v ((genAt w 𝔞 : (Kw w)ˣ) : Kw w) = WithZero.exp (-FractionalIdeal.count D.host.E w 𝔞) := by
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [genAt, Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

theorem exists_mem_valuation_eq (w : Pl D.host.E) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) :
    ∃ c ∈ I, w.valuation D.host.E c = WithZero.exp (-FractionalIdeal.count D.host.E w I) := by
  have hw0 : (w.asIdeal : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  have hIw : I * w.asIdeal ≠ 0 := mul_ne_zero hI hw0
  have hne : ¬ I ≤ I * w.asIdeal := fun h => by
    have := FractionalIdeal.count_mono D.host.E w hI h
    rw [FractionalIdeal.count_mul D.host.E w hI hw0, FractionalIdeal.count_self] at this
    omega
  obtain ⟨c, hc, hc'⟩ := SetLike.not_le_iff_exists.1 hne
  refine ⟨c, hc, le_antisymm ((GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc w) ?_⟩
  by_contra hlt
  push_neg at hlt
  refine hc' ((GlobalTheory.Idele.mem_iff_valuation_le hIw c).2 fun Q => ?_)
  rw [FractionalIdeal.count_mul D.host.E Q hI hw0]
  by_cases hQ : w = Q
  · subst hQ
    rw [FractionalIdeal.count_self]
    rcases eq_or_ne (w.valuation D.host.E c) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0, WithZero.exp_lt_exp] at hlt
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  · rw [FractionalIdeal.count_maximal_coprime D.host.E Q hQ, add_zero]
    exact (GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc Q

end CondAA


open CondAA in
theorem hasConductor_psiAt_AA {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E) :
    HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar) := by
  classical
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have e := isEquiv_Kw w
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero hP D
  have hB : D.host.AAbar ≠ 0 := fun h => by
    have h1 := hP D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hI : D.host.AA * D.host.AAbar ≠ 0 := mul_ne_zero hA hB
  set n := FractionalIdeal.count D.host.E w (D.host.AA * D.host.AAbar) with hn
  have hv : Valued.v (((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ)) : Kw w) = WithZero.exp (-n) := by
    rw [Units.val_mul, map_mul, valued_genAt, valued_genAt, ← WithZero.exp_add, hn,
      FractionalIdeal.count_mul D.host.E w hA hB, neg_add]
  have hint : ∀ y : Kw w, Valued.v y ≤ 1 → finPart D (atPl w y) ∈ intAE D := fun y hy => mem_intAE fun Q => by
    rw [(atPl_spec w y).2]
    by_cases h : Q = w
    · subst h; simpa using hy
    · simp [h]
  intro x
  rw [e x, hv]
  refine ⟨fun h => ?_, fun hx y hy => ?_⟩
  · by_contra hx
    obtain ⟨u, hu, hu1, hu2⟩ := exists_pole w
    refine hu (int_of_xi hP D fun a ha j hj => mem_Dinv.2 fun c => ?_)
    have hx1 : WithZero.exp (-n + 1) ≤ Valued.v x := by
      have h0 : Valued.v x ≠ 0 := fun h0 => hx (h0 ▸ zero_le')
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at hx
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    have haj : w.valuation D.host.E (a * j) ≤ WithZero.exp (-n) :=
      (GlobalTheory.Idele.mem_iff_valuation_le hI (a * j)).1 (FractionalIdeal.mul_mem_mul ha hj) w
    have hn' : D.host.xi0 * (a * j) * c ∈ Dinv D := by
      rw [mul_comm]
      exact (Dinv D).coeToSubmodule.smul_mem c (xi_mem_Dinv hP D ha hj)
    have h1 := (psiAt_eq_one W w _).1 (h (algebraMap D.host.E (Kw w) (a * j * c) * algebraMap D.host.E (Kw w) u) (by
      rw [e, map_mul, valued_alg, valued_alg, map_mul]
      refine le_trans ?_ hx1
      calc _ ≤ WithZero.exp (-n) * 1 * WithZero.exp (1 : ℤ) :=
            mul_le_mul' (mul_le_mul' haj (w.valuation_le_one c)) hu1
        _ = _ := by rw [mul_one, ← WithZero.exp_add]))
    rw [atPl_mul, inc_mul_inc] at h1
    have h2 := char_int W.ψ_std hn' (z := pairA D.host.F 0 1 ⊗ₜ[D.host.F] u - atPl w (algebraMap D.host.E (Kw w) u))
      (by rw [RingHom.map_sub, GlobalTheory.LatVac.infPart_pair, (atPl_spec w _).1, sub_zero]) (mem_intAE fun Q => by
        rw [RingHom.map_sub, RingHom.map_sub, cpt_pair, (atPl_spec w _).2]
        by_cases hQ : Q = w
        · subst hQ; simp
        · rw [Pi.single_eq_of_ne hQ, sub_zero, valued_alg]
          exact hu2 Q hQ)
    rw [← mul_assoc D.host.xi0, ← mul_assoc D.host.xi0] at h1
    rw [← mul_assoc D.host.xi0] at h2
    have h3 : W.ψ (Algebra.trace (AF D.host.F) (AE D)
        (incA D (D.host.xi0 * a * j * c) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u))) = 1 := by
      rw [← sub_add_cancel (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u : AE D) (atPl w (algebraMap D.host.E (Kw w) u)), mul_add,
        map_add, W.ψ.map_add_eq_mul, h1, h2, one_mul]
    rw [trace_inc_pair, one_mul, GlobalTheory.LatVac.char_rat W.ψ_std] at h3
    rwa [show D.host.xi0 * (a * (j * u)) * c = D.host.xi0 * a * j * c * u by ring]
  · obtain ⟨c, hc, hcv⟩ := exists_mem_valuation_eq w hI
    have hy1 : Valued.v y ≤ WithZero.exp (-n) := ((e y x).1 hy).trans hx
    have hξc : D.host.xi0 * c ∈ Dinv D := by
      rw [show Dinv D = _ from (Formalism.L2.Pj.dual_eq hP D).symm, mul_assoc]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hc
    have hvc : Valued.v (algebraMap D.host.E (Kw w) c) = WithZero.exp (-n) := by rw [valued_alg, hcv]
    have h0 : algebraMap D.host.E (Kw w) c ≠ 0 := fun h => by
      rw [h, map_zero] at hvc
      exact WithZero.exp_ne_zero hvc.symm
    rw [psiAt_eq_one, ← mul_inv_cancel_left₀ h0 y, atPl_mul, inc_mul_inc]
    refine char_int W.ψ_std hξc (atPl_spec w _).1 (hint _ ?_)
    rw [map_mul, map_inv₀, hvc]
    calc _ ≤ (WithZero.exp (-n))⁻¹ * WithZero.exp (-n) := mul_le_mul' le_rfl hy1
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdele
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_compFinV (v : HeightOneSpectrum (𝓞 F)) : Continuous (compFin F E v) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd)


end GlobalTheory.ThK.LemF.QuotInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section
namespace GlobalTheory.PureMatch

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def rowB (t : T) (w : Pl D.host.E) (i j : Fin D.R.m) :
    Fin ((locGrid G t w).rank (i, j)) ≃ Fin (spW₁ G i j).rank :=
  finCongr (rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨i.2.le, j.2.le⟩)

def trB (t : T) {w : Pl D.host.E} {v : Pl D.host.F} (hv : w.under (𝓞 D.host.F) = v) {i j : Fin D.R.m} (e : Num G i j)
    (Y : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  Matrix.of fun r c => GlobalTheory.LFun.complMap hv (Y (rowB t w i j r) (GlobalTheory.SquareFlipReach.colE t w e c))

def blockV {i j : Fin D.R.m} (e : Num G i j) : Finset (Fin ((spW G i j).rank + (spW₁ G i j).rank)) :=
  Finset.univ.image fun k => e (Sum.inl k)

end GlobalTheory.PureMatch
end
end

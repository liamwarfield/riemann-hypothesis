module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferAllFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAverageTranslateEqSmulBranchingMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevelP

theorem toMap_shift {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    c.toMap pr f' v h = a⁻¹ * c.toMap pr f v (h * κ) := by
  have h1 := GlobalTheory.ThetaProjEquiv.ext_shift c hc κ hκ a ha f f' hy h
  show pr (c.ext f' h) v = a⁻¹ * pr (c.ext f (h * κ)) v
  rw [← h1, map_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ ha]

theorem toMap_eigen {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0) (b : ℂ)
    (f : Bridge.Gf V → c.W) (hy : ∀ h, (b • f) h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    a⁻¹ * c.toMap pr f v (h * κ) = b * c.toMap pr f v h :=
  (toMap_shift c hc pr κ hκ a ha f (b • f) hy v h).symm.trans
    (congrFun (LinearMap.congr_fun ((c.toMap pr).map_smul b f) v) h)

theorem mem_multT_withP {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (hu : u ∈ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)))
    (hP : ∀ p : P.H, ∃ κ, IsLevelLift V β L p.1 κ ∧ ∀ v h,
      (levChi V β (flagL L) κ)⁻¹ * u v (h * κ) = ((P.chi p : ℂˣ) : ℂ) * u v h) :
    u ∈ MultT θ M (levS V β (withP L P)) (levChi V β (withP L P)) := by
  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hu)
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff]
  refine ⟨hm.aut, hm.cusp, fun v k hk g => ?_, hm.equiv, hm.cont⟩
  have hT : HasType V β (flag1L L) (PiTensorProduct.lift.symm u v) := fun k hk g => hm.lev v k hk g
  refine IsPLevel.hasType (V := V) (β := β) (L := L) (P := P) ⟨hT, fun p => ?_⟩ k hk g
  obtain ⟨κ, hl, hκ⟩ := hP p
  funext h
  exact (level_action_spec hT ⟨κ, hl⟩ κ hl h).trans (hκ (PiTensorProduct.tprod ℂ v) h)

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_lift_eigen (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (a : D.what₂.LL) (hx : (A.fam.R t).r g x = a • x) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ v h,
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ)⁻¹ * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v (h * κ) =
        D.what₂.embLL a * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v h := by
  refine (GlobalTheory.FormAction.act_eq_translate R hred hj t g x).imp fun κ hκ => ⟨hκ.1, ?_⟩
  have h3 : R.jX t ((A.fam.R t).r g x) = D.what₂.embLL a • R.jX t x :=
    (congrArg (R.jX t) hx).trans ((R.jX t).map_smulₛₗ a x)
  have h4 : (R.HX t).e (R.jX t ((A.fam.R t).r g x)) = D.what₂.embLL a • (R.HX t).e (R.jX t x) :=
    (congrArg (R.HX t).e h3).trans ((R.HX t).e.map_smul _ _)
  exact toMap_eigen R.cX hc R.prX κ hκ.1.1 _ (levChi_ne_zero (V := D.sp.X') (β := R.βX) (flagL (R.datXt t)) κ) _ _
    fun h => (congrFun h4 h).symm.trans (hκ.2 h)

theorem mem_CXP_of_good (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (hirr : ∀ χ ∈ A.fam.X, IsAbsIrrChar χ)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T0) (x : (A.fam.R t).S.Forms)
    (hx : x ∈ Formalism.IndefR.Cx.BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ))
    (hu : R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈
      MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))) :
    R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈ CXP R (levPOf R.eG D.what₂.embLL P ψ) t := by
  rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hx
  refine mem_multT_withP R.θ R.MX R.βX (R.datXt t) (levPOf R.eG D.what₂.embLL P ψ) _ hu fun p => ?_
  have hq : R.eG.symm p.1 ∈ P := p.2
  have ha := Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type (A.fam.R t).r A.fam.X hirr P ψ ⟨_, hq⟩ x hx
  refine (exists_lift_eigen R hred hj hc t (R.eG.symm p.1) x _ ha).imp fun κ hκ => ⟨?_, hκ.2⟩
  exact ⟨hκ.1.1, hκ.1.2.1, hκ.1.2.2.trans (R.eG.apply_symm_apply p.1)⟩

end Package

end GlobalTheory.TopLevelP

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem PiLocalization₂.val_autCusp {D : D7} (c : Com D) (s : PiLocalization₂ D) (u : s.CC c) (x : SmT s.M) :
    IsAutFunSm c.θ s.V (PiLocalization₂.val u x) ∧ IsCuspFun s.V (PiLocalization₂.val u x) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D c.θ s.V _ s.M _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  have key : ∀ y : SmT s.M, PiLocalization₂.val u y =
      (PiTensorProduct.lift (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) y := by
    intro y; rw [LinearEquiv.apply_symm_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [key, map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    have e : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := map_add _ _ _
    rw [e]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem rankY_succ {D : D7} (k : ℕ) : D.R.rankY (k + 1) = D.R.rankY k + D.R.t := by
  show D.R.r + (k + 1) * D.R.t = D.R.r + k * D.R.t + D.R.t
  ring

theorem upPar_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, LevFacts D → UpPar D := by
  intro hRD hHowe D _ hND c hc k hk s s' hs hs' p hp u B φ hu v _ hne
  have hlat' := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc (k + 1) hk s' hs').2
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc k hk.le s hs).2
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : IsParamFunV s.V c.S (fun g => conj (y g)) B := (hlat _ B).1 (hu.2 v hy0)
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + D.R.t := by rw [hs'.rank, hs.rank, rankY_succ]
  have hYA := PiLocalization₂.val_autCusp c s u v
  unfold ParFun
  rw [hlat', hconj]
  intro w0 hw0 w h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer hRD D (GlobalTheory.T.sphericalParameterTransfer_all_finitePlaces hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil D.R.t hrank s.ν s.fd
    hs.haar hs.fund w0 (fun w' hw' => GlobalTheory.T.thetaChain_step_chars_unramified_off_S D c hc k hk w0 hw0' w' hw') w h (p.pt φ)
    (GlobalTheory.T.fock_vectors_lattice_vacua_off_finite_set D hND c hc k hk s s' hs hs' p hp φ w0 hw0') y (B w) hYA.1 hYA.2 (hyB w0 hw0 w h) hne'

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferredStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainUpwardLift_heckeParam_transferred : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, LevFacts D → UpPar D := by
  first | exact @GlobalTheory.ChainOnto.upPar_of_transfer | exact GlobalTheory.ChainOnto.upPar_of_transfer | (intros; apply GlobalTheory.ChainOnto.upPar_of_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatios
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatios
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ratio_total_unitRatio_of_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  intro D c v 𝒯 t w S s₀ hIs hCV hkap hcG hscK hTQ hcP n hn s
  obtain ⟨hrefl, hmul, -, hprod⟩ := GlobalTheory.Fam.unitRatio_laws (S s)
  have split : ∀ (f : ℕ → ℂ) (k : ℕ), ∏ j ∈ Finset.range (2 * k), f j =
      ∏ i ∈ Finset.range k, (f (2 * i) * f (2 * i + 1)) := by
    intro f k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Finset.prod_range_succ, mul_assoc]
  have hIs' : ∀ s j, j < D.R.m → (t s).cI j ≠ 0 := fun s j hj => (hIs s).cI j hj
  have hκ : ∀ i, i < n → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s, (t s).cV (2 * i) =
      κ * ((w s).sc (2 * i) * (w s).sc (2 * i + 1)) * (w s).cQ (2 * i) * v.cG (2 * i) * (w s).cT (2 * i) := by
    intro i hi
    by_cases hlast : i + 1 = n
    · refine ⟨1, one_ne_zero, fun s => ?_⟩
      rw [one_mul]
      exact (hCV s).2 (2 * i) (by omega)
    · exact ⟨v.kap (2 * i) (n - i - 2) (by omega), hkap _ _ _, fun s => (hCV s).1 (2 * i) (n - i - 2) (by omega)⟩
  have hB : ∀ i, i < n → UnitRatio (S s)
      ((t s).cV (2 * i) * (t s).cK (2 * i) * (t s).cK (2 * i + 1) / ((t s).cI (2 * i) * (t s).cI (2 * i + 1)))
      ((t s₀).cV (2 * i) * (t s₀).cK (2 * i) * (t s₀).cK (2 * i + 1) / ((t s₀).cI (2 * i) * (t s₀).cI (2 * i + 1))) := by
    intro i hi
    obtain ⟨κ, hκ0, hκs⟩ := hκ i hi
    have hK0 : κ * v.cG (2 * i) ≠ 0 := mul_ne_zero hκ0 (hcG _)
    have hform : ∀ s', (t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) /
        ((t s').cI (2 * i) * (t s').cI (2 * i + 1)) =
        κ * v.cG (2 * i) *
          ((w s').sc (2 * i) * (w s').sc (2 * i + 1) * (w s').cT (2 * i) *
            ((w s').cQ (2 * i) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1))) *
            ((t s').cK (2 * i) * (t s').cK (2 * i + 1))) := by
      intro s'
      rw [hκs s']
      ring
    rw [hform s, hform s₀]
    have hsc1 := (hscK s (2 * i) (by omega)).1
    have hsc2 := (hscK s (2 * i + 1) (by omega)).1
    have homogComponent_comm_first_action := (hscK s (2 * i) (by omega)).2
    have homogComponent_comm_second_action := (hscK s (2 * i + 1) (by omega)).2
    have hcT := (hTQ s (2 * i) (n - i - 1) (by omega)).1
    have hcQ := (hTQ s (2 * i) (n - i - 1) (by omega)).2
    exact (hmul _ _ _ _ (hrefl _ hK0)
      (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hsc1 hsc2).1 hcT).1 hcQ).1
        (hmul _ _ _ _ homogComponent_comm_first_action homogComponent_comm_second_action).1).1).1
  have hq : ∀ s', (t s').cTop n / (t s').cBot = (∏ i ∈ Finset.range n,
      ((t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)))) *
      (t s').cP := by
    intro s'
    unfold Tup.cTop Tup.cBot
    rw [← hn, split (fun j => (t s').cI j) n, Finset.prod_div_distrib]
    ring
  have hall : UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
    rw [hq s, hq s₀]
    exact (hmul _ _ _ _ (hprod ℕ (Finset.range n) _ _ fun i hi => hB i (Finset.mem_range.mp hi)) (hcP s)).1
  have hbot : (t s).cBot ≠ 0 := by
    unfold Tup.cBot
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hIs' s j (Finset.mem_range.mp hj)
  have hne := (hmul _ _ _ _ hall hall).2.2
  refine ⟨fun h0 => hne ?_, hbot, hall⟩
  rw [h0, zero_div]

end GlobalTheory.SeeSaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatiosStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_totalConstant_ratio_of_factor_ratios : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  first | exact @GlobalTheory.SeeSaw.ratio_total_unitRatio_of_parts | exact GlobalTheory.SeeSaw.ratio_total_unitRatio_of_parts | (intros; apply GlobalTheory.SeeSaw.ratio_total_unitRatio_of_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletio
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitInt

variable {D : D7}

theorem mem_latV_iff_at (S : HSp D) (N : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S N P ↔ y ∈ latV S N (· = v) := by
  constructor
  · intro h
    have h2 := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) h
    have e : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy i)
    rwa [e] at h2
  · intro h
    exact GlobalTheory.FinPl.KSplit.latV_mono S N (fun w hw => by subst hw; exact hv) h

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_sec (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  have h := q.sec_pr (a * q.sec b)
  have h2 := q.sec_pr (q.sec b)
  rw [q.pr_sec] at h2
  rw [RingHom.map_mul, q.pr_sec] at h
  rw [h, mul_left_comm, ← h2]

theorem mulVec_sec (q : SplitPt D k) {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (b : Fin n → k) :
    (M *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map q.pr *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => mul_sec q _ _

theorem mem_KO_of_keeps {Y : Type} [Fintype Y] [DecidableEq Y] (x : GL Y k)
    (h : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ ∀ i, (x.val *ᵥ y) i ∈ 𝒪[k]) : x ∈ GlobalTheory.SplitWeil.KO k Y := by
  have h1 : ∀ j i : Y, (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k] := by
    intro j i
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  have hc : ∀ (A : Matrix Y Y k) (i j : Y), (A *ᵥ (Pi.single j (1 : k) : Y → k)) i = A i j := by
    intro A i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hA : ∀ i j, x.val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc x.val i j]; exact (h _).1 (h1 j) i
  have hB : ∀ i j, (x⁻¹).val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc (x⁻¹).val i j]
    refine (h _).2 ?_ i
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact h1 j
  have hinj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix : Matrix Y Y 𝒪[k] → Matrix Y Y k) :=
    fun a b hab => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  let A : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨x.val i j, hA i j⟩
  let B : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨(x⁻¹).val i j, hB i j⟩
  have eA : (algebraMap 𝒪[k] k).mapMatrix A = x.val := rfl
  have eB : (algebraMap 𝒪[k] k).mapMatrix B = (x⁻¹).val := rfl
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext eA⟩
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.mul_inv]
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.inv_mul]

end

theorem mem_KO_of_moves : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (N : Lat S) (P : Pl D → Prop), P q.v → IntIn q S F N → ∀ g : GA D S, Moves S g N N P → ∀ x : GL Y k, (mt S g).map q.pr = F.β * x.val * F.γ → x ∈ GlobalTheory.SplitWeil.KO k Y := by
  intro D k _ _ _ _ q S Y _ _ F N P hP hI g hM x hx
  refine mem_KO_of_keeps x fun y => ?_
  have hs : ∀ (b : Fin S.rank → k) i, (fun i => q.sec (b i)) i ∈ idAt D (· = q.v) := fun b i => q.sec_mem_idAt _
  have e : (Formalism.L2.Theta.mt S g).map q.pr *ᵥ (F.β *ᵥ y) = F.β *ᵥ (x.val *ᵥ y) := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  rw [hI y, hI (x.val *ᵥ y), ← mem_latV_iff_at S N hP _ (hs _), ← mem_latV_iff_at S N hP _ (hs _),
    hM _ (fun i => GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => by subst hw; exact hP) (hs _ i)), mulVec_sec, e]

end GlobalTheory.SplitInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (N : Lat S) (P : Pl D → Prop), P q.v → IntIn q S F N → ∀ g : GA D S, Moves S g N N P → ∀ x : GL Y k, (mt S g).map q.pr = F.β * x.val * F.γ → x ∈ GlobalTheory.SplitWeil.KO k Y := by
  first | exact @GlobalTheory.SplitInt.mem_KO_of_moves | exact GlobalTheory.SplitInt.mem_KO_of_moves | (intros; apply GlobalTheory.SplitInt.mem_KO_of_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassData
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerXCls

variable {D : D7}

abbrev finfF (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GinfC_iff (V : HSp D) (g : GA D V) : g ∈ GinfC V ↔ (Formalism.L2.Theta.mt V g).map (finfF D) = 1 := by
  show finHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfF D) = 1) :
    (x ⬝ m ⬝ y).map (finfF D) = (x ⬝ y).map (finfF D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfF D) = x.map (finfF D) ⬝ m.map (finfF D) ⬝ y.map (finfF D) := by
    rw [Matrix.map_mul (f := finfF D), Matrix.map_mul (f := finfF D)]
  have e2 : (x ⬝ y).map (finfF D) = x.map (finfF D) ⬝ y.map (finfF D) := Matrix.map_mul (f := finfF D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GinfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GinfC A) :
    o.emb (a, 1) ∈ GinfC S := by
  rw [mem_GinfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfF D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfF D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trc_apply {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsm : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact hadd hx hy
  | zero => simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsm (h x) c

theorem ontoUni_of_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (hab : a = b)
    (r : K → ι → Matrix (Fin a) (Fin a) ℂ)
    (hr : OntoUni (fun k τ => (r k τ).reindex (finCongr hab) (finCongr hab))) : OntoUni r := by
  subst hab
  simpa using hr

end GlobalTheory.SeeSaw.PerXCls


open GlobalTheory.SeeSaw.PerXCls in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.SeeSaw.perX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) →
    ClsPinD t → PerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro n h y v
  have hU : OntoUni (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) :=
    ontoUni_of_reindex ρ.hT (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) hρ.uniT
  obtain ⟨_, _, _, ν, hν1, hν2, hcls⟩ := integral_eq_classSum D c.θ c.T ρ.BT hc.inf hU
  obtain ⟨hN, hInt, hBr, hne, hblk⟩ := hρ.low n h
  have hemb : ∀ k : GinfC c.T, (c.oT n h).emb (k.1, 1) ∈ GinfC (c.X n) := fun k => orth_emb_mem_GinfC _ k.2
  let y0 : FrN D (ρ.N n) := ρ.fr n y
  have hdet : ∀ (k : GinfC c.T) τ, IsUnit ((ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ).det) := by
    intro k τ
    rw [Matrix.det_mul]
    have hu := (hρ.uni n h.le).uni ⟨_, hemb k⟩ τ
    exact (Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp hu)).mul (y0.2 τ)
  let yk : GinfC c.T → FrN D (ρ.N n) := fun k => ⟨fun τ => ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ, hdet k⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.unitaryAverage_translate_eq_smul_branchingMap D.what₂.Tau (ρ.N n) ρ.NT hN (fun _ => 1) (fun _ => 1) (ρ.lam n) ρ.sg hInt (ρ.low n h) hBr
    hne (GinfC c.T) ν (fun k => ρ.rT k.1) hρ.uniT y0 yk
    (fun k => ⟨_, fun τ => hblk k.1 k.2 τ, fun τ => rfl⟩) (ρ.J v 1) (hρ.J v).1 (fun k => ρ.J v k.1)
    (fun k z z' hz => (hρ.J v).2 k.1 k.2 z z' hz)
  refine ⟨a, fun s ψ hψ F => ?_⟩
  obtain ⟨⟨A, hA1⟩, B, hB⟩ := hA s
  obtain ⟨hvol, hstab, hsum⟩ := hcls c.volT B.U B.cl B.h hB.reps
  have rdtr := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA1.1 n h.le ψ hψ
  obtain ⟨J, χ, hCT⟩ := (ht s).CT
  have hF : IsContAut c.T (F.1 v) := isContAut_multT (hCT F.2) v
  have key : ∀ β, ∫ h' in c.volT.𝓕, trc ((t s).eT n h β) (F.1 v) h' * (t s).rd n β ψ y ((c.oT n h).emb (h', 1)) ∂c.volT.μ =
      (volLev c.volT B.U : ℂ) * ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        (a * B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
    intro β
    obtain ⟨hr1, -, hr3, hr4⟩ := rdtr β
    rw [hsum]
    · congr 1
      refine Finset.sum_congr rfl fun a' _ => ?_
      congr 1
      have hpt : ∀ k : GinfC c.T, trc ((t s).eT n h β) (F.1 v) (B.h a' * k.1) *
          (t s).rd n β ψ y ((c.oT n h).emb (B.h a' * k.1, 1)) =
          B.ell n h β a' F (ρ.J v k.1) * (fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1))) (yk k) := by
        intro k
        rw [hB.top n h F v β a' k.1 k.2]
        congr 1
        have hm : (c.oT n h).emb (B.h a' * k.1, 1) = (c.oT n h).emb (B.h a', 1) * (c.oT n h).emb (k.1, 1) := by
          rw [← map_mul]; simp
        rw [hm]
        refine hr3 y _ _ _ (hemb k) ?_
        intro τ
        rw [Equiv.apply_symm_apply]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact ha _ (hr4 _) _
    · refine Continuous.mul ?_ ((hr1 y).2.comp ((c.oT n h).continuous_emb.comp (continuous_id.prodMk continuous_const)))
      have : trc ((t s).eT n h β) (F.1 v) = fun x => ∑ g ∈ ((t s).eT n h β).support, (t s).eT n h β g * F.1 v (x * g) :=
        funext fun x => trc_apply _ _ x
      rw [this]
      exact continuous_finsetSum _ fun g _ => continuous_const.mul (hF.2.comp (continuous_mul_const g))
    · intro γ hγ g
      rw [trc_apply, trc_apply]
      congr 1
      · refine Finset.sum_congr rfl fun g' _ => ?_
        rw [mul_assoc, hF.1 γ hγ]
      · have hm : (c.oT n h).emb (γ * g, 1) = (c.oT n h).emb (γ, 1) * (c.oT n h).emb (g, 1) := by
          rw [← map_mul]; simp
        rw [hm, (hr1 y).1 _ ((c.oT n h).emb_mem_GQ hγ (GQ _).one_mem)]
    · intro κ hκ g
      exact hB.inv n h ψ hψ F v y β g κ hκ
  have htl := hB.tail n h ψ hψ F
  unfold Tup.perT
  rw [Finset.sum_congr rfl fun β _ => key β]
  calc _ = a * ((volLev c.volT B.U : ℂ) * ∑ β, ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun a' _ => by ring
    _ = _ := by rw [htl]; ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLastPeriodFactorization_of_classData : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → PerX t := by
  first | exact @GlobalTheory.SeeSaw.perX_of_clsPinD | exact GlobalTheory.SeeSaw.perX_of_clsPinD | (intros; apply GlobalTheory.SeeSaw.perX_of_clsPinD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumDisjointUnion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.IdemSumAdd

theorem idemSum_union : ∀ (D : D7) (a b : AE D) (P Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), Disjoint P Q → (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → IsIdemSum a P → IsIdemSum b (P ∪ Q) → b = a + ∑ PP ∈ Q, es PP := by
  intro D a b P Q es hPQ hQ ha hb
  rw [← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq hb, GlobalTheory.ExportSeries.idem,
    GlobalTheory.ExportSeries.idem, Finset.sum_union hPQ]
  congr 1
  exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.ExportSeries.idemAt_eq (hQ PP hPP)

end GlobalTheory.IdemSumAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.FinPl.SplitHalfSuppImp

theorem mxAt_of_isHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) {m n : ℕ} (x : Mx D m n), IsHalf (q.e + cA D q.e) x → MxAt (· = q.v) x := by
  intro D k _ _ _ _ q m n x hx
  exact GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D k q m n x hx

end GlobalTheory.FinPl.SplitHalfSuppImp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixSupported_splitPlace_of_isHalf_conjSum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) {m n : ℕ} (x : Mx D m n), IsHalf (q.e + cA D q.e) x → MxAt (· = q.v) x := by
  first | exact @GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf | exact GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf | (intros; apply GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesSplit

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc

variable {D : D7}

theorem idem_eq_algebraMap (R : Pl D → Prop) :
    idem D R = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ePl D R)) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

theorem idem_smul_mem (S : HSp D) (L : Lat S) {P : Pl D → Prop} (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : idem D R • y ∈ latV S L (fun p => P p ∧ R p) := by
  classical
  rw [idem_eq_algebraMap]
  exact smul_mem_latV S L (ePl D R) (ePl_int R) (fun v hv => by rw [evalV_ePl, if_neg hv]) hy

theorem idem_smul_eq (S : HSp D) (R : Pl D → Prop) {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D R) :
    idem D R • y = y :=
  funext fun i => (mem_idAt_iff R (y i)).1 (hy i)

theorem mem_latV_iff_all (S : HSp D) (L : Lat S) (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D R) : y ∈ latV S L R ↔ y ∈ latV S L (fun _ => True) := by
  refine ⟨fun h => latV_mono S L (fun _ _ => trivial) h, fun h => ?_⟩
  have h1 := idem_smul_mem S L R h
  rw [idem_smul_eq S R hy] at h1
  exact latV_mono S L (fun _ h => h.2) h1

theorem idem_add_idem (P : Pl D → Prop) {a : AE D} (ha : a ∈ idAt D (fun _ => True)) :
    idem D P * a + idem D (fun p => ¬ P p) * a = a := by
  classical
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, infPart_of_idAt ha, mul_zero, mul_zero, add_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, compAt_idem, compAt_idem]
    by_cases h : P w
    · simp [h]
    · simp [h]

theorem mem_latV_iff_parts (S : HSp D) (L : Lat S) (P : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (fun _ => True)) :
    y ∈ latV S L (fun _ => True) ↔
      idem D (fun p => ¬ P p) • y ∈ latV S L (fun p => ¬ P p) ∧ idem D P • y ∈ latV S L P := by
  constructor
  · intro h
    exact ⟨latV_mono S L (fun _ h => h.2) (idem_smul_mem S L _ h), latV_mono S L (fun _ h => h.2) (idem_smul_mem S L P h)⟩
  · rintro ⟨h1, h2⟩
    have e : y = idem D P • y + idem D (fun p => ¬ P p) • y :=
      funext fun i => (idem_add_idem P (hy i)).symm
    rw [e]
    exact add_mem (latV_mono S L (fun _ _ => trivial) h2) (latV_mono S L (fun _ _ => trivial) h1)

theorem idem_smul_supp (S : HSp D) (R : Pl D → Prop) (y : Fin S.rank → AE D) (i : Fin S.rank) :
    (idem D R • y) i ∈ idAt D R :=
  Ideal.mul_mem_right _ _ (idem_mem_idAt R)

end GlobalTheory.FinPl.MovesSplit


open GlobalTheory.FinPl.MovesSplit GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc in
theorem GlobalTheory.FinPl.moves_iff_moves_on_off : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S)
    (P : GlobalTheory.FinPl.Pl D → Prop), (GlobalTheory.FinPl.Moves S g L L (fun p => ¬ P p) ∧ GlobalTheory.FinPl.Moves S g L L P) ↔
      GlobalTheory.FinPl.Moves S g L L (fun _ => True) := by
  intro D S g L P
  constructor
  · rintro ⟨hn, hp⟩ y hy
    rw [mem_latV_iff_parts S L P hy, mem_latV_iff_parts S L P (mulVec_mem S _ hy), ← Matrix.mulVec_smul,
      ← Matrix.mulVec_smul]
    exact and_congr (hn _ (idem_smul_supp S _ y)) (hp _ (idem_smul_supp S P y))
  · intro h
    have key : ∀ R : GlobalTheory.FinPl.Pl D → Prop, GlobalTheory.FinPl.Moves S g L L R := by
      intro R y hy
      rw [mem_latV_iff_all S L R hy, mem_latV_iff_all S L R (mulVec_mem S _ hy)]
      exact h y fun i => idAt_mono (fun _ _ => trivial) (hy i)
    exact ⟨key _, key _⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_on_off_iff_all_finitePlaces : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop), (GlobalTheory.FinPl.Moves S g L L (fun p => ¬ P p) ∧ GlobalTheory.FinPl.Moves S g L L P) ↔ GlobalTheory.FinPl.Moves S g L L (fun _ => True) := by
  first | exact @GlobalTheory.FinPl.moves_iff_moves_on_off | exact GlobalTheory.FinPl.moves_iff_moves_on_off | (intros; apply GlobalTheory.FinPl.moves_iff_moves_on_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SplitProj

open Formalism.IndefR.Datum Formalism.L2.Theta

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_near (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (n : ℕ) :
    ∃ k : F, Valued.v (c - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set r : v.adicCompletion F := algebraMap F _ (π ^ n) with hr_def
  have hr : Valued.v r = WithZero.exp (-(n : ℤ)) := by
    rw [hr_def]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (π ^ n)).trans ?_
    rw [map_pow, hπ]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hr0 : Valued.v r ≠ 0 := by rw [hr]; exact WithZero.exp_ne_zero
  have hN : {y : v.adicCompletion F | Valued.v (c - y) < Valued.v r} ∈ nhds c := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict r)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => c - y)
    simp only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (c - c) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hr0
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).mem_nhds hN
  exact ⟨k, (le_of_lt hk).trans_eq hr⟩

theorem afIso_one_tmul_apply (a : FiniteAdeleRing (𝓞 F) F) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P = GlobalTheory.AdeleBaseChange.adMap F E a P := by
  have key : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≤
      WithZero.exp (-(n : ℤ)) := fun n => by
    obtain ⟨k, hk⟩ := exists_near (P.under (𝓞 F)) (a (P.under (𝓞 F))) n
    have h1 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P n hk
    have h2 : Valued.v (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) ≤
        WithZero.exp (-(n : ℤ)) := by
      rw [GlobalTheory.AdeleBaseChange.adMap_apply, ← GlobalTheory.AdeleBaseChange.locMap_algebraMap, ← map_sub]
      exact GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk
    have e : GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P =
        (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) -
          (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 h2)
  by_contra hne
  have h0 : Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  have h2 := key (1 - WithZero.log (Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P -
    GlobalTheory.AdeleBaseChange.adMap F E a P))).toNat
  conv_lhs at h2 => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp] at h2
  omega

end Base

variable {D : Formalism.BasicNotions.D7}

theorem toAd_eq_afIso (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.toAd D w = GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x a =>
    rw [GlobalTheory.StdFrames.toAd_spec]
    have e : (x ⊗ₜ[D.host.F] a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, GlobalTheory.Mem.Col2.afIso_tmul_one]
    congr 1
    exact FiniteAdeleRing.ext _ fun P => (afIso_one_tmul_apply a P).symm
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem cpt_eq_adAt (Q : HeightOneSpectrum (𝓞 D.host.E)) (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.cpt Q w = GlobalTheory.Mem.Col2.adAt D.host.F Q w := by
  show Formalism.UG.evalV D.host.E Q (GlobalTheory.StdFrames.toAd D w) = Formalism.UG.evalV D.host.E Q (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w)
  rw [toAd_eq_afIso]

theorem pr_eq_of_adAt : ∀ {D : Formalism.BasicNotions.D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (z : Formalism.L2.Theta.AE D) (x : D.host.E), GlobalTheory.Mem.Col2.adAt D.host.F PP (Formalism.IndefR.Datum.toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x → q.pr z = q.pr (Formalism.L2.Theta.incA D x) := by
  intro D k _ _ _ _ q PP he z x hz
  have hx : GlobalTheory.StdFrames.cpt PP (toEAf D (incA D x)) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)
  have hz' : GlobalTheory.StdFrames.cpt PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans hz
  have h1 : toEAf D (q.e * z) = toEAf D (q.e * incA D x) := by
    rw [RingHom.map_mul, RingHom.map_mul]
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hQ : Q = PP
    · rw [hQ, hx, hz']
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, zero_mul]
  have h2 : q.pr (q.e * z - q.e * incA D x) = 0 :=
    q.pr_eq_zero_of_toEAf he _ (by rw [RingHom.map_sub, h1, sub_self])
  rw [RingHom.map_sub, sub_eq_zero, ← q.sec_pr, ← q.sec_pr, q.pr_sec, q.pr_sec] at h2
  exact h2

end GlobalTheory.SplitProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEqStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq : ∀ {D : Formalism.BasicNotions.D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (z : Formalism.L2.Theta.AE D) (x : D.host.E), GlobalTheory.Mem.Col2.adAt D.host.F PP (Formalism.IndefR.Datum.toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x → q.pr z = q.pr (Formalism.L2.Theta.incA D x) := by
  first | exact @GlobalTheory.SplitProj.pr_eq_of_adAt | exact GlobalTheory.SplitProj.pr_eq_of_adAt | (intros; apply GlobalTheory.SplitProj.pr_eq_of_adAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Doubling GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)

noncomputable section

namespace GlobalTheory.TwBound

theorem hgt_io_eq_prod (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (ha : IsMaj V a) (g : GA D V) (hg : g ∈ GinfC V) :
    (hgt V a (io V (g, 1)) : ℝ) = ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g) := by
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  rw [hgt, hI.hgtAd_eq (isCMExt_host D)]
  have hf : ∀ v, hgtFin D.sp.cm.sig (dblSp V).gram (frameLat V) v (proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1))) = 1 := by
    intro v
    have e : proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1)) = 1 := by
      rw [io, proj_ioH, mem_infPts_iff_forall.1 hg v, map_one, ioH_one]
    rw [e]
    exact hgtH_of_mem (continuous_absEv v) (isCompact_KFin v) (one_mem _)
  simp only [hf, finprod_one, mul_one, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [io, projArch_ioH, map_one]
  rfl

theorem tw_bound : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → ∀ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1) → ∀ P Q, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q)‖ ≤ C * (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g)) ^ ((W.rank : ℝ) / 2) := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hω m X hm f hf a ha hmaj P Q
  have hpr : GlobalTheory.Published.WeilRepresentationUnitaryPair := fun D ψ S T χS χT hψ hS hT rS rT =>
    GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hpr D ψ V W χS χT ω hω
  have hth := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ V W χS χT ω omh hω homh
  have hco := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ V W χS χT ω omh hω hth m X hm
  have h1 := GlobalTheory.T.isFockVec_ptOf_of_isVacVec D V W S S' M M' θ ψ hω.std hθ f hf P
  have h2 := GlobalTheory.T.isFockVec_ptOf_of_isVacVec D V W S S' M M' θ ψ hω.std hθ f hf Q
  have hS := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M τ
  have hT := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M' τ
  have hc := GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact D θ V (cart M) a hθ hS hmaj
  have hb := GlobalTheory.T.doublingSeesawTensorMap_polynomial_fock_vector D ψ θ V W (cart M) (cart M') hω.std hθ _ _ h1 h2
  have hk := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp V) W 1 χT omh _ (cart M') homh hθ hc.1 hT (Khat V a) (isCompact_Khat V a) hc.2 _ hb
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hpr D ψ V W χT omh homh m X hm _ (hth _ _ h1.1 h2.1).1 a hk
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C, hC⟩ := GlobalTheory.Doubling.HasIwasawa.exists_norm_le continuous_absE (isCompact_Khat V a) hI hmem
  refine ⟨C, fun g hg => ?_⟩
  have e1 := (hco _ _ h1.1 h2.1).2 g
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q) =
      swSec V W omh m X (delta V W (ptOf ψ θ M M' f P) (ptOf ψ θ M M' f Q)) (io V (g, 1)) := by
    rw [e1]; rfl
  rw [e2, ← hgt_io_eq_prod D V a ha g hg]
  have ex : (sZero V W).re + (V.rank : ℝ) / 2 = (W.rank : ℝ) / 2 := by
    simp only [sZero, Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]; ring
  have := hC (io V (g, 1))
  rw [ex] at this
  exact this

end GlobalTheory.TwBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realMatrixCoeff_fockVectors_le_doublingHeight_pow : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → ∀ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1) → ∀ P Q, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q)‖ ≤ C * (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g)) ^ ((W.rank : ℝ) / 2) := by
  first | exact @GlobalTheory.TwBound.tw_bound | exact GlobalTheory.TwBound.tw_bound | (intros; apply GlobalTheory.TwBound.tw_bound <;> assumption)
end
end

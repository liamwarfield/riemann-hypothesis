module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelVectorMovedByRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LocalWeilOps

theorem comm_off_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl (F := F)) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a × Fin (a + a') → AF F,
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')),
      om (x, 1) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om (x, 1) Φ) := by
  intro u hu p q Φ hΦ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := Γ.M.co.e.symm (p, q) with hw
  have he : Γ.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) = 0 := hx u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((x, 1) : UA σ Γ.V.J × UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h0, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using h1
  have h2 := hW.impl (x, 1) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem locality_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl (F := F)) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (x, 1)) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (x, 1) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (x, 1) Φ hΦ
  have hcomm := comm_off_V Bs Γ X om om' hTr v x hx
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace Bs.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (x, 1) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.WeilLocality.schr_trans, GlobalTheory.WeilLocality.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  intro φ hφ
  refine ⟨fun t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.WeilLocality.liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
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

theorem read_off {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl (F := F)) (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i) : κ → AF F) := by
    intro u' hu'
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hR := hRi 0 _ hz
  rw [zero_add] at hR
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  exact read_off v R hR0 (hR φ hφ).1 φ₁ φ₂ ((h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ)))

theorem acts_comp {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₁ : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T₁ Φ ∈ GlobalTheory.WeilM.schA F κ)
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T₁ φ φ₁) (h2 : Acts (evFin F v) T₂ φ₁ φ₂) :
    Acts (evFin F v) (T₂ * T₁) φ φ₂ := by
  intro r hr
  have e1 := h1 r hr
  have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, e1 ▸ hT₁ _ hr.2⟩
  rw [Module.End.mul_apply, e1, h2 r hr1]

theorem local_ops : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v Γ _ j hj
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  have hkeep : ∀ g, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om g Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun g Φ hΦ => hW.pres g Φ hΦ
  have hsplit : ∀ g, om (j g) = om ((j g).1, 1) * om (1, (j g).2) := by
    intro g
    rw [← map_mul]
    congr 1
    simp [Prod.mk_mul_mk]
  have hex : ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ := by
    intro g φ
    obtain ⟨φ₁, h₁, a₁⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hTr v (j g).2 (hj g).2 φ φ.2
    obtain ⟨φ₂, h₂, a₂⟩ := locality_V B G X om om' hTr v (j g).1 (hj g).1 φ₁ h₁
    refine ⟨φ₂, h₂, ?_⟩
    rw [hsplit g]
    exact acts_comp v _ _ (hkeep _) a₁ a₂
  choose S hS hA using hex
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  have hRi := (hR 0 (Submodule.zero_mem _)).1
  have hadd : ∀ g (φ φ' : SB (Fin a × Fin (a + a') → Fv F v)), S g (φ + φ') = S g φ + S g φ' := by
    intro g φ φ'
    apply read_off v R hR0 hRi
    have e1 := hA g (φ + φ') R (hR _ (φ + φ').2)
    have e2 := hA g φ R (hR _ φ.2)
    have e3 := hA g φ' R (hR _ φ'.2)
    have t1 : ∀ ψ₁ ψ₂ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (ψ₁ + ψ₂) R = tens (evFin F v) ψ₁ R + tens (evFin F v) ψ₂ R := by
      intro ψ₁ ψ₂; funext x; simp [tens, add_mul]
    rw [← e1, Submodule.coe_add, t1, map_add (f := _), e2, e3, ← t1]
  have hsmul : ∀ g (c : ℂ) (φ : SB (Fin a × Fin (a + a') → Fv F v)), S g (c • φ) = c • S g φ := by
    intro g c φ
    apply read_off v R hR0 hRi
    have e1 := hA g (c • φ) R (hR _ (c • φ).2)
    have e2 := hA g φ R (hR _ φ.2)
    have t2 : ∀ ψ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (c • ψ) R = c • tens (evFin F v) ψ R := by
      intro ψ; funext x; simp [tens, mul_assoc]
    rw [← e1, Submodule.coe_smul, t2, map_smul, e2, ← t2]
  let ωl : Γ → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)) := fun g =>
    { toFun := fun φ => ⟨S g φ, hS g φ⟩
      map_add' := fun φ φ' => Subtype.ext (hadd g φ φ')
      map_smul' := fun c φ => Subtype.ext (hsmul g c φ) }
  have hone : ∀ φ : SB (Fin a × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ
    refine acts_unique v _ φ.2 (hA 1 φ) ?_
    intro r hr
    rw [map_one, map_one]
    rfl
  have hmul : ∀ g h (φ : SB (Fin a × Fin (a + a') → Fv F v)), S (g * h) φ = S g ⟨S h φ, hS h φ⟩ := by
    intro g h φ
    refine acts_unique v _ φ.2 (hA (g * h) φ) ?_
    rw [map_mul, map_mul]
    exact acts_comp v _ _ (hkeep _) (hA h φ) (hA g ⟨S h φ, hS h φ⟩)
  refine ⟨{ toFun := ωl, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact LinearMap.ext fun φ => Subtype.ext (hone φ)
  · intro g h
    exact LinearMap.ext fun φ => Subtype.ext (hmul g h φ)
  · intro g φ φ₁
    constructor
    · intro hφ₁
      exact acts_unique v _ φ.2 hφ₁ (hA g φ)
    · rintro rfl
      exact hA g φ

end GlobalTheory.LocalWeilOps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localWeilOperators_supportedAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  first | exact @GlobalTheory.LocalWeilOps.local_ops | exact GlobalTheory.LocalWeilOps.local_ops | (intros; apply GlobalTheory.LocalWeilOps.local_ops <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfMemLevel
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRankR

theorem exists_lift_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (κ' : GA D (Wc D i)), κ' ∈ levG (Wc D i) (R.βW i) (R.datWp i P) → ∃ g0 : P.H, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0.1 κ' ∧ levChi (Wc D i) (R.βW i) (R.datWp i P) κ' = ((P.chi g0 : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i P κ' hκ
  have hp : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') ∈ P.H := hκ.2.2
  refine ⟨⟨_, hp⟩, ⟨hκ.1, hκ.2.1, rfl⟩, ?_⟩
  have h2 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
      (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi ⟨_, hp⟩ := extendOne_of_mem _ hp
  unfold levChi levFn
  rw [h2]
  have hs : (R.datWp i P).s = 0 := rfl
  have hQ : (R.datWp i P).Q = ∅ := rfl
  rw [hs, hQ]
  simp

end GlobalTheory.LevelRankR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevel
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLevelP


set_option maxHeartbeats 1000000 in
theorem thF_mem_conj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hIs : R.toLevCh.Is A.μ0)
    (hMod : R.IsModels) (hTh : R.IsThP) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (y : (R.HV i t).H)
    (hy : R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P))
      (levChi _ (R.βV i) (RecTie.datVP R i t P))) :
    R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P.conj))
      (levChi _ (R.βW i) (R.datWp i P.conj)) := by
  have hW := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (hTh.thF_mem i t y)
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2 ⟨hW.aut, hW.cusp, fun v k' hk' g => ?_, hW.equiv, hW.cont⟩
  obtain ⟨g0, hl', hc'⟩ := GlobalTheory.LevelRankR.exists_lift_of_mem_level R i P.conj k' hk'
  have hL := (GlobalTheory.StepLifts.lifts_exist R hIs i).1 t
  have hx := hL g0
  clear hL
  rcases hx with ⟨κ, hl⟩
  have h1 := GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter R i t P
  let g1 : P.H := ⟨g0.1, g0.2⟩
  have h3 := h1 g1 κ hl
  clear h1
  have hf0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := Units.ne_zero _
  have hy' : ∀ k ∈ levS (Vc D i) (R.βV i) (RecTie.datVP R i t P), ∀ h,
      R.extV i t y (h * k) = levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) k • R.extV i t y h := hy
  have e1 := hy' κ h3.1
  have e2 := h3.2
  clear hy' hy h3
  have hnum : (((P.chi g1 : ℂˣ) : ℂ))⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
      levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ := by
    rw [e2]
    field_simp
  have hsh : ∀ h, R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
    intro h
    have e3 : R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ • R.extV i t y h :=
      congrFun ((R.extV i t).map_smul _ y) h
    refine e3.trans ?_
    refine Eq.trans ?_ (congrArg (fun w => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) (e1 h).symm)
    refine (congrArg (fun a : ℂ => a • R.extV i t y h) hnum).trans ?_
    exact mul_smul _ _ _
  have key := GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors R hIs hMod hTh i t g0.1 κ k' hl hl' y _ hsh v g
  have hcc : levChi (Wc D i) (R.βW i) (R.datWp i P.conj) k' = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ := by
    rw [hc']
    change (((P.chi⁻¹) g1 : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have e4 : R.thF i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) v g = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ * R.thF i t y v g := by
    have e5 := congrFun (congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) ((R.thF i t).map_smul (((P.chi g1 : ℂˣ) : ℂ))⁻¹ y)) g
    exact e5
  exact key.symm.trans (e4.trans (congrArg (· * R.thF i t y v g) hcc.symm))


set_option maxHeartbeats 1000000 in
theorem thF_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs hMod hTh hv b i t y hy
  rw [GlobalTheory.Proof.LevelCharacterConjugate.liftLevel_fixedEmbedding_eq_conj_rowLevel R F b hv]
  exact thF_mem_conj R hIs hMod hTh i t (R.levR F b) y hy

end GlobalTheory.ThetaLevelP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevelStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_mem_multiplicitySpace_baseLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  first | exact @GlobalTheory.ThetaLevelP.thF_mem_level | exact GlobalTheory.ThetaLevelP.thF_mem_level | (intros; apply GlobalTheory.ThetaLevelP.thF_mem_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumVolShellInterTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.PureMatch.ShellVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open IsDedekindDomain NumberField MeasureTheory Matrix in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.PureMatch.ShellVolume.isOpen_translate {a : ℕ} (u u' : GL (Fin a) k) :
    IsOpen {g : GL (Fin a) k | u * g * u' ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin a)} :=
  _root_.GlobalTheory.SplitFlip.isOpen_KO.preimage
    ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.PureMatch.ShellVolume


open IsDedekindDomain NumberField MeasureTheory Matrix in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv in
open ValuativeRel in
theorem _root_.GlobalTheory.PureMatch.ShellVolume.finsum_vol_shell_inter_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (ϖ : kˣ) (u u' : GL (Fin a) k), _root_.GlobalTheory.SplitFlip.IsUnif ϖ →
    ∑ᶠ m : {m : Fin a → ℤ // Antitone m}, (_root_.GlobalTheory.SplitFlip.haarVol (_root_.GlobalTheory.SplitWeil.KO k (Fin a))).real (_root_.GlobalTheory.SplitFlip.shellSet ϖ m.1 ∩ {g | u * g * u' ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin a)}) = 1 := by
  intro k _ _ _ _ _ _ a ϖ u u' hϖ
  have hv : valuation k ↑ϖ = uniformizer k := hϖ
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := _root_.GlobalTheory.SplitFlip.borel_GL
  set K := _root_.GlobalTheory.SplitWeil.KO k (Fin a) with hK
  set μ := _root_.GlobalTheory.SplitFlip.haarVol K with hμ
  haveI : μ.IsHaarMeasure := _root_.GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO
  haveI : μ.IsMulRightInvariant := _root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar μ
  set S : Set (GL (Fin a) k) := {g | u * g * u' ∈ K} with hS
  have hshell : ∀ m : Fin a → ℤ,
      _root_.GlobalTheory.SplitFlip.shellSet ϖ m = _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ m := by
    intro m
    unfold _root_.GlobalTheory.GLDoubling.cell _root_.GlobalTheory.SplitFlip.shellSet
    congr 1
    apply Units.ext
    simp only [_root_.GlobalTheory.GLDoubling.val_torusElt, _root_.GlobalTheory.SplitFlip.diagGL_val,
      Units.val_zpow_eq_zpow_val]
  simp only [hshell]
  have hSopen : IsOpen S := _root_.GlobalTheory.PureMatch.ShellVolume.isOpen_translate u u'
  have hSeq : S = (fun x => u⁻¹ * x * u'⁻¹) '' (K : Set (GL (Fin a) k)) := by
    ext g
    constructor
    · intro hg
      exact ⟨u * g * u', hg, by group⟩
    · rintro ⟨x, hx, rfl⟩
      show u * (u⁻¹ * x * u'⁻¹) * u' ∈ K
      have hx' : u * (u⁻¹ * x * u'⁻¹) * u' = x := by group
      rw [hx']
      exact hx
  have hScpt : IsCompact S := by
    rw [hSeq]
    exact _root_.GlobalTheory.SplitFlip.isCompact_KO.image
      ((continuous_const.mul continuous_id).mul continuous_const)
  have hμS : μ S = 1 := by
    have : S = (fun g => u * g) ⁻¹' ((fun g => g * u') ⁻¹' (K : Set (GL (Fin a) k))) := by
      ext g; simp [hS, mul_assoc]
    rw [this, measure_preimage_mul, measure_preimage_mul_right]
    exact _root_.GlobalTheory.SplitFlip.haarVol_self _root_.GlobalTheory.SplitFlip.isOpen_KO le_rfl
  obtain ⟨t, ht⟩ := hScpt.elim_finite_subcover
    (fun e : {m : Fin a → ℤ // Antitone m} => _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1)
    (fun e => _root_.GlobalTheory.GLDoubling.isOpen_cell _ _)
    (by rw [_root_.GlobalTheory.GLDoubling.iUnion_cell hv]; exact Set.subset_univ _)
  have hdisj := _root_.GlobalTheory.GLDoubling.pairwise_disjoint_cell (k := k) (N := a) hv
  have hsupp : Function.support (fun e : {m : Fin a → ℤ // Antitone m} =>
      μ.real (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S)) ⊆ ↑t := by
    intro e he
    by_contra het
    apply he
    have hempty : _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S = ∅ := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hge hgS
      obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht hgS)
      have hie : i ≠ e := fun h => het (h ▸ hi)
      exact Set.disjoint_left.mp (hdisj hie) hgi hge
    simp [hempty]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpd : (↑t : Set {m : Fin a → ℤ // Antitone m}).PairwiseDisjoint
      (fun e => _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S) := by
    intro i _ j _ hij
    exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ i ∈ t, MeasurableSet (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ i.1 ∩ S) := fun i _ =>
    (_root_.GlobalTheory.GLDoubling.isOpen_cell _ _).measurableSet.inter hSopen.measurableSet
  have hfin : ∀ i ∈ t, μ (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ i.1 ∩ S) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (by rw [hμS]; exact ENNReal.one_ne_top) (measure_mono Set.inter_subset_right)
  rw [← measureReal_biUnion_finset hpd hmeas hfin]
  have hU : (⋃ e ∈ t, _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S) = S := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun _ _ => Set.inter_subset_right
    · intro g hg
      obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht hg)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hgi, hg⟩
  rw [hU, measureReal_def, hμS, ENNReal.toReal_one]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaSpanHasType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaSpanHasType
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BaseKernelType

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem actL_levelTrace (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (u : U)
    (hu : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) κ) {F : GA D (Wc D i) → ℂ}
    (hF : HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) F) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) (levelTrace R i U ψ F) =
      D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • levelTrace R i U ψ F := by
  have hmul : ∀ g : G, actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u)
      (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F) =
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G) * g)) F := by
    intro g
    have em : R.eG ((u : G) * g) = R.eG u * R.eG g := map_mul _ _ _
    rw [em]
    by_cases hg : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ
    · exact GlobalTheory.ProjComm.levelGroupAction_mul_of_lifts hu hg hF
    · have hn : ¬ ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u * R.eG g) κ := by
        rintro ⟨κ', hκ'⟩
        obtain ⟨κ, hκ⟩ := hu
        have := GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_inv hκ) hκ'
        have e : (R.eG (u : G))⁻¹ * (R.eG (u : G) * R.eG g) = R.eG g := inv_mul_cancel_left _ _
        exact hg ⟨κ⁻¹ * κ', e ▸ this⟩
      have h1 : actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F = 0 := GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hg F
      rw [h1, map_zero]
      exact (GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hn F).symm
  unfold levelTrace gaL
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  refine Fintype.sum_bijective (fun g => (u : G) * g) (Group.mulLeft_bijective (u : G)) _ _ fun g => ?_
  simp only [smul_smul]
  refine congrArg₂ (· • ·) ?_ (hmul g)
  split_ifs with h1 h2 h2
  · rw [← map_mul, ← Units.val_mul,
      show (⟨(u : G) * g, h2⟩ : U) = u * ⟨g, h1⟩ from rfl, map_mul, mul_inv, mul_inv_cancel_left]
  · exact absurd (U.mul_mem u.2 h1) h2
  · exact absurd ((U.mul_mem_cancel_left u.2).1 h2) h1
  · rw [mul_zero]

theorem singleSeries_hasType (hθ : IsInfFam R.θ) {χS χT : (AE D)ˣ →* Circle} {ω : WeilRep D i}
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω)
    (hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ)
    (hfix : ∀ k', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k' → ω (1, k') φ = φ) (h : GA D (Vc D i))
    (w : (R.cV i).W) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) (singleSeries R i ω φ h w v) := by
  intro κ hκ g
  have hl : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ := ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  rw [GlobalTheory.CuspMult.EqCut.levChi_flag1 rfl rfl, one_mul]
  unfold singleSeries Datum.thetaKO
  have e : ((h, g * κ) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (1, κ) := Prod.ext (mul_one h).symm rfl
  rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hω R.θ hθ 1 (one_mem _) κ hκ.1,
    hfix κ hl]
  exact hφ

theorem adForm_sub (x y : Fin (R.nW i) → D.what₂.LL) : adForm R i (x - y) = adForm R i x - adForm R i y := by
  unfold adForm
  rw [map_sub, map_sub]

theorem thetaBase_hasType : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), R.LUnif → FormsDetermined R i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → (∀ u : F.P0, (R.FW i).chi u = 1) → ∀ x ∈ thetaBase R i F.P0 F.ψ0⁻¹ 1 v (ownAt D v), ∀ u : F.P0, (R.FW i).ρ u x = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • x := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hcore i hU hd v hv hmu hval hchi
  have hgen : ∀ u : F.P0, ∀ y ∈ {x | ∃ ω φ, IsKernel R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) (placesOver R (R.mu v) (ownAt D v)) ω φ ∧
      x ∈ seriesSet R i F.P0 F.ψ0⁻¹ 1 ω φ},
      (R.FW i).ρ u y = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • y := by
    rintro u y ⟨ω, φ, hk, h, -, w, -, hy⟩
    obtain ⟨χ, ξR, hker⟩ := GlobalTheory.T.baseTuple_thetaKernel_tameCharacter D G Pl0 T0 A Ks R F hcore i v hv hmu ω φ hk
    have hfix := (GlobalTheory.T.thetaKernel_vector_moved_by_rootsOfUnity D G Pl0 T0 A Ks R F hcore i _ χ ξR _ ω φ hker hval).2
    obtain ⟨cV, hcV⟩ := hcore.lev.βV i
    obtain ⟨cW, hcW⟩ := hcore.lev.βW i
    have hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ :=
      (GlobalTheory.VecTheta.vecThetaSD D).2 _ _ _ _ _ _ (R.ΛV i) (R.ΛW i) _ _ _ _ _ _ _
        (GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hcore.lev.βV i)))
        (GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hcore.lev.βW i))) hcV.1 hcW.1 hker.vec
    have hT : ∀ v', HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) (singleSeries R i ω φ h w v') :=
      fun v' => GlobalTheory.BaseKernelType.singleSeries_hasType hcore.models.inf hker.weil hφ hfix h w v'
    have hρ : ∀ v' : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i ((R.FW i).ρ u y) (fun ρ => v' ρ) =
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) (adForm R i y (fun ρ => v' ρ)) := by
      intro v'
      have e := (hU i (sg0 D A)).2.2 u y
      rw [hchi u, Units.val_one, map_one, one_smul] at e
      exact congrArg (fun T => T (fun ρ => v' ρ)) e
    by_cases hu : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG u) κ
    · refine sub_eq_zero.1 (hd _ fun v' => ?_)
      rw [GlobalTheory.BaseKernelType.adForm_sub, adForm_smul, MultilinearMap.sub_apply, MultilinearMap.smul_apply, hρ v', hy v',
        one_smul, GlobalTheory.BaseKernelType.actL_levelTrace F.P0 F.ψ0⁻¹ u hu (hT v'), sub_self]
    · have h0 : (R.FW i).ρ u y = 0 := hd _ fun v' => by
        rw [hρ v']
        exact GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hu _
      have hy0 : y = 0 := by
        have e := congrArg ((R.FW i).ρ (u : G)⁻¹) h0
        rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at e
      rw [hy0, map_zero, smul_zero]
  intro x hx u
  unfold thetaBase at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen u y hy
  | zero => rw [map_zero, smul_zero]
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, smul_add]
  | smul a y _ hy => rw [LinearMap.map_smul_of_tower, hy, smul_comm]

end GlobalTheory.BaseKernelType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaSpanHasTypeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseTupleThetaSpan_hasType : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), R.LUnif → FormsDetermined R i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → (∀ u : F.P0, (R.FW i).chi u = 1) → ∀ x ∈ thetaBase R i F.P0 F.ψ0⁻¹ 1 v (ownAt D v), ∀ u : F.P0, (R.FW i).ρ u x = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • x := by
  first | exact @GlobalTheory.BaseKernelType.thetaBase_hasType | exact GlobalTheory.BaseKernelType.thetaBase_hasType | (intros; apply GlobalTheory.BaseKernelType.thetaBase_hasType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDet
noncomputable section

namespace GlobalTheory.StabMove

section Adelic

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}


set_option maxHeartbeats 1000000 in
theorem exists_carries {V W : HSp D} (hV : V = W) {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {U : Unf Xo c σ r}
    {dict : GA D V → Σ k, Frame (U.X k).Ψ r} (io : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k))
    (hL : DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io) e F ik φ th x₀)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom)
    {s : Dw.La →ₗ[𝓞 D.host.E] Dw.La} {κ : GA D W}
    (hκ : Induces W l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ io) s κ) (h : GA D W) :
    (Formalism.IndefR.FWT.castDict hV dict h).2 ∈ (U.X (Formalism.IndefR.FWT.castDict hV dict h).1).dom ∧
      ∃ δ, ∃ hc : Carries φ s (Formalism.IndefR.FWT.castDict hV dict h).1 (Formalism.IndefR.FWT.castDict hV dict (h * κ)).1 δ,
        (Formalism.IndefR.FWT.castDict hV dict (h * κ)).2 =
          lact δ (castFr hc.mt.psi (Formalism.IndefR.FWT.castDict hV dict h).2) := by
  subst hV
  subst hr
  change DictLat U V rfl dict io e F ik φ th x₀ at hL
  change Induces V l io s κ at hκ
  refine ⟨hdom h, ?_⟩
  change ∃ δ, ∃ hc : Carries φ s (dict h).1 (dict (h * κ)).1 δ,
      (dict (h * κ)).2 = lact δ (castFr hc.mt.psi (dict h).2)
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0 := fun k k' => (hW k).2.trans (hW k').2.symm
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hf₁⟩ := hL.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hf₂⟩ := hL.2 (h * κ)
  have e₀ : γ₂ * (h * κ) = γ₂ * γ₁⁻¹ * (γ₁ * h) * κ := by group
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))
  obtain ⟨gam, e₁, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _
    (φ _) (φ _) (F.t _) (F.t _) s (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hW _) (hW _) (hL.1.1 _) (hL.1.1 _) δ hδu hδf hκ.2.1 hκ.2.2
    ⟨hΛ₁, hm₁⟩ (by rw [← e₀]; exact ⟨hΛ₂, hm₂⟩)
  have hmt : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ := by
    refine ⟨Finset.ext fun τ => ((hU.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm,
      hxi _ _, fun u v => by rw [hG, hG]; exact hδu u v, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨v, hv⟩
      rw [show v = (φ (dict h).1 a : Fin V.rank → D.host.E) by rw [ha], ← hgam]
      exact (φ _ _).2
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨_, hv⟩
      obtain ⟨b, rfl⟩ := gam.surjective a
      have h1 := congrArg (fun u => (δ⁻¹).1 *ᵥ u) ((hgam b).symm.trans (congrArg Subtype.val ha))
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
      rw [← h1]
      exact (φ _ _).2
  refine ⟨δ, ⟨hmt, by rw [hG, hG], gam, e₁, t₁, hgam⟩, funext fun τ => ?_⟩
  change mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hmt.mem τ⟩
  rw [hf₁, hf₂, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1),
    GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ ⟨τ.1, hmt.mem τ⟩) (hθ τ.1), e₀, (hAr τ.1).2.1, (hAr τ.1).2.1,
    (hAr τ.1).2.2.1 κ hκ.1, hδa τ.1 _ (hθ τ.1), Matrix.mul_one, ← Matrix.mul_assoc]
  rfl


set_option maxHeartbeats 1000000 in
theorem rdU_eq_of_carries_self (T : CoreJ D) (hT : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)}
    {F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1)}
    {ik : (T.U j σ).Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ}
    (hP : HasPeriods φ) {G : Type} [Group G]
    {lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)}
    (hact : ActLev (Xo := T.Q.Xo j) T.Q.c lev) (a : G) {w : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f : Rul (T.Q.Xo j) T.Q.c} (hf : f ∈ sec (T.Q.Xo j) T.Q.c w n)
    (p q : Σ k, Frame ((T.U j σ).X k).Ψ D.R.r) (hp : p.2 ∈ ((T.U j σ).X p.1).dom) {δ : GL (Fin D.R.r) D.host.E}
    (hc : Carries φ (lev a).1 p.1 q.1 δ) (hq : q.2 = lact δ (castFr hc.mt.psi p.2)) (hpq : q.1 = p.1) :
    rdU (T.U j σ) (actLev T.Q.c lev a f) p.1 p.2 = rdU (T.U j σ) f q.1 q.2 := by
  obtain ⟨k, x⟩ := p
  obtain ⟨k', x'⟩ := q
  dsimp only at hp hc hq hpq ⊢
  subst hpq
  rw [hq]
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hU := hT.unf _ hj σ hσ
  have hr := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  obtain ⟨hneg, φD, h1, h2, h3⟩ := GlobalTheory.GeoLevel.model_space_of_lawsJ D T hT j hj σ hσ k'
  obtain ⟨h4, hdet⟩ := GlobalTheory.GeoLevel.four_dvd_finrank_and_det_eq_pm_one D
  obtain ⟨ρ, ν, hρ, hν, -⟩ := mvPt_spec hact.total a ((T.U j σ).un k' ⟨x, hp⟩)
  refine GlobalTheory.T.movedSection_reading_eq_movedFrame_reading D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU
    k' φD h1 h2 h3 hneg δ hc.mt ((hdet _ _ δ hc.mt).imp_right fun h => ⟨h, h4⟩) ρ ν hν.1
    (fun z y' hm => move_eq hσ hr hA hP hc hν z hm) w n hD f hf _
    (actL_mem _ _ _ _ hact.total hact.nat hact.bor _ a hf) (fun y y' hm => ?_) x hp
  have m1 := mvPt_spec hact.total a y
  have m2 : levActR (Xo := T.Q.Xo j) (c := T.Q.c) lev a y y' := ⟨ρ, ν, hρ, hν, hm⟩
  exact (evalAt_actL hact (hT.evalWD _ hj) frMap_trans_id a hf.1 y).trans
    (evalAt_congr_id (hT.evalWD _ hj) frMap_trans_id hf.1 (hact.func a _ y _ _ m1 m2) (hact.func a _ y _ _ m2 m1))

end Adelic

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem phiAt_actLev_of_comp_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, phiAt T i σ hV (fun _ => 1) (actLev T.Q.c (O i).lev2 g f) h = σ y * phiAt T i σ hV (fun _ => 1) f (h * k) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR ht hpb hO i σ hσ hV g k hk y hy p hp f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj σ hσ
  obtain ⟨hr, g₀, e, F, ik, φ, th, hio, -, hth, hL⟩ := h.adPin _ hj σ hσ
  obtain ⟨_, hW⟩ := h.modelW _ hj σ hσ
  have hU := h.unf _ hj σ hσ
  have hK := h.levelK _ hj σ hσ
  rw [← h.pins.2.1.1] at hK
  obtain ⟨hio', hK'⟩ := GlobalTheory.DictMove.cast_level hV hK (T.iota _) hr (rank_Wc i) hio
  obtain ⟨k₀, hk₀, hs⟩ := (hO i).2.lift.lev g
  have hI := GlobalTheory.DictMove.induces_of_lift hio' (hR.βW i)
    (fun k hk => hK' k ((GlobalTheory.LiftLevel.isLift_one_iff_mem_level T R κ v₀ hR ht hpb i σ hσ hV k).1 hk)) hk₀ hk hs
  obtain ⟨hdom, δ, hc, hq⟩ := exists_carries hV hr (rank_Wc i) (T.iota _) hU hW hL hth hd.2.2.2.1 hI p
  have key := rdU_eq_of_carries_self T h hj hσ hL.1.2 (hO i).2.act.1 g (dom_wtA (κ i))
    ((mem_cusp _ _ _ _ _ _).1 hf).1 _ _ hdom hc hq hp
  obtain ⟨y', hy', hy1⟩ := GlobalTheory.GeoLevel.mu_lift hR ht hpb i hσ hV hk
  obtain rfl : y = y' := (algebraMap T.Q.c.F D.what₂.LL).injective (D.what₂.embLL.injective (hy.trans hy'.symm))
  have hmu := h.muUnit _ hj σ hσ
  rw [GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.castDict_mu_mul hmu.1, ← mul_assoc,
    mul_left_comm (σ y), hy1, mul_one]
  unfold GlobalTheory.GeoLevel.frameRead
  rw [key]

end GlobalTheory.StabMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDetStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMove_stabiliser_character_det : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, phiAt T i σ hV (fun _ => 1) (actLev T.Q.c (O i).lev2 g f) h = σ y * phiAt T i σ hV (fun _ => 1) f (h * k) := by
  first | exact @GlobalTheory.StabMove.phiAt_actLev_of_comp_eq | exact GlobalTheory.StabMove.phiAt_actLev_of_comp_eq | (intros; apply GlobalTheory.StabMove.phiAt_actLev_of_comp_eq <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunction
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleIndicatorFunctions
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RowsCongrOfTrivialAtLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DefiniteGroupVacuumPhaseIndependentOfLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaInnerEqConstMulTestInner
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaInnerEqConstMulTestInner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerVacIp

variable {D : D7} {S T : HSp D} (C : Ctx S T)

theorem isONFr_xB (B : C.Bas) (hB : C.IsB B) : IsONFr C.X (C.xB B) := by
  unfold IsONFr
  intro τ
  have h1 : ∀ x y : T.V, star (T.hT x y) = T.hT y x := by
    intro x y
    exact T.herm.eq x y
  have h2 : ∀ x : D.host.E, tauE D (C.m.e.symm τ) (star x) = (starRingEnd ℂ) (tauE D (C.m.e.symm τ) x) := by
    intro x
    unfold tauE
    dsimp only [star, Formalism.BasicNotions.Host.cmStar]
    exact IsCMField.complexEmbedding_complexConj D.host.E (D.host.emb ↑(D.eTau (C.m.e.symm τ))) x
  have key : ∀ i j, (τ : D.host.E →+* ℂ) (C.X.Gm i j) = tauE D (C.m.e.symm τ) (HSpace.gram T i j) := by
    intro i j
    have he := C.m.e_emb (C.m.e.symm τ)
    rw [Equiv.apply_symm_apply] at he
    rw [he, C.m.gT, Matrix.transpose_apply, NumberField.ComplexEmbedding.conjugate_coe_eq, ← h2]
    unfold HSpace.gram
    rw [h1]
  rw [← hB (C.m.e.symm τ)]
  ext a b
  unfold FD.gram mat Ctx.xB hermC FD.col gramAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_conj, Finset.sum_mul, key]
  rw [Finset.sum_comm]

theorem rho_zero_pt (f : WO S T → ℂ) : C.rho 0 f = f := by
  unfold Ctx.rho heisO
  funext w
  simp [symplOH, symplO, hO]

theorem zOf_zero (x : Frame C.X.Ψ T.rank) : C.zOf x 0 = 0 := by
  unfold Ctx.zOf Ctx.realPt zR
  funext k i
  simp [compAt, hermC]
  intro _
  simp only [← Pi.zero_def, Matrix.mulVec_zero, Pi.zero_apply]

theorem ip_vacua : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' →
      ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  intro D S T C μ 𝓕 hμ
  have h0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    simp
  have hg : ∀ x : Frame C.X.Ψ T.rank, gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    intro x
    unfold gaussR
    simp [hx]
  obtain ⟨a, ha, b, -, hdbl⟩ :=
    GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
  obtain ⟨⟨κ, hκ, hk⟩, -⟩ :=
    GlobalTheory.Ker.kZero_onFr_const_entire D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
  refine ⟨a * κ, mul_ne_zero ha (Complex.ofReal_ne_zero.mpr hκ.ne'), ?_⟩
  intro B hB φ φ' hφ hφ'
  obtain ⟨hdom, hk0⟩ := hk _ (isONFr_xB C B hB)
  have h := GlobalTheory.T.innerProduct_translated_vacua_eq_gaussianKernel D S T C μ 𝓕 hμ _ hdom _ hdom φ φ' hφ hφ' 0 0 h0 h0
  rw [rho_zero_pt, rho_zero_pt, zOf_zero, hg] at h
  have hz : (fun k i => (starRingEnd ℂ) ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [hz, hk0, (hdbl φ φ' hφ hφ').1] at h
  rw [h]
  simp only [map_one, one_mul]
  ring

end GlobalTheory.KerVacIp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaInnerEqConstMulTestInnerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vacua_inner_eq_const_mul_testInner : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' → ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  first | exact @GlobalTheory.KerVacIp.ip_vacua | exact GlobalTheory.KerVacIp.ip_vacua | (intros; apply GlobalTheory.KerVacIp.ip_vacua <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DefiniteGroupVacuumPhaseIndependentOfLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.VacPhase

theorem isMov_one {D : D7} {k : ℕ} (L : Lt D.host.E k) :
    IsMov (1 : Matrix (Fin k) (Fin k) (AfE D)) L L := by
  intro u
  simp only [Matrix.one_mulVec]
  exact ⟨fun h => ⟨u, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩

theorem conjI_ne_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) :
    conjI P ≠ ⊥ := by
  intro h
  apply hP
  rw [eq_bot_iff]
  intro b hb
  have h1 : GlobalTheory.SW.Nbr.co b ∈ conjI P := GlobalTheory.SW.Nbr.mem_conjI.2 (by rwa [GlobalTheory.SW.Nbr.co_co])
  rw [h, Ideal.mem_bot] at h1
  rw [Ideal.mem_bot, ← GlobalTheory.SW.Nbr.co_co b, h1, map_zero]

theorem phase_indep : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∃ ep : ℂ, ‖ep‖ = 1 ∧ ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → om (h, 1) (C.Th (C.xB B) (v₀ L)) = ep • (C.Th (C.xB B) (unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)))) := by
  intro D S T C om hom Lv hn M hidem hM hMm v₀ hv₀ B hB h Λ hh htriv hfg hmov
  obtain ⟨w, hw⟩ : ∃ w : Lt D.host.E T.rank → TF S.rank C.g,
      ∀ L, w L = unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)) := ⟨_, fun _ => rfl⟩
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hΛM : Λ ∈ Vset D.host.E S.rank M := (GlobalTheory.T.self_dual_lattices_at_level D S T C).1 M h Λ hM htriv hfg hmov
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := GlobalTheory.SW.stdL_mem_Vset M
  have h6833 := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  have fmt_one : ∀ V : HSp D, fmt V 1 = 1 ∧ fmtC V 1 = 1 := fun V =>
    ⟨(((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 V).2.2.2.1 1 (one_mem _)).1,
      (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 V).2.2.2.1 1 (one_mem _)).2.1⟩
  obtain ⟨μ, 𝓕, hcov⟩ := (GlobalTheory.Ker.ScalarProduct.ip_basic D S T C).1
  obtain ⟨κ, hκ, hipTh⟩ := GlobalTheory.T.exists_vacua_inner_eq_const_mul_testInner D S T C μ 𝓕 hcov
  have hsd : ∀ L ∈ Lv.lats, SelfD C.X (Lv.sh L) := fun L hL => (h6833.2.2.2.1 L hL).1
  have hvac : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens Λ (Lv.sh L)) (w L) := fun L hL => by
    rw [hw L]
    exact GlobalTheory.SW.RecSum.isVac_unitv (D := Lv) C.idx C.sympl C.even hΛM (hsd L hL) (hv₀ L hL)
  have hsbw : ∀ L ∈ Lv.lats, GlobalTheory.SW.IsSB (w L) := fun L hL => (hvac L hL).1
  have hsbv : ∀ L ∈ Lv.lats, GlobalTheory.SW.IsSB (v₀ L) := fun L hL => (hv₀ L hL).1
  have hS1 : ∀ Λ₀ : Lt D.host.E S.rank, IsMov (fmtC S 1) Λ₀ Λ₀ := fun Λ₀ => by
    rw [(fmt_one S).2]
    exact GlobalTheory.Ker.VacPhase.isMov_one Λ₀

  have phase : ∀ L ∈ Lv.lats, ∃ c : ℂ, ‖c‖ = 1 ∧
      om (h, 1) (C.Th (C.xB B) (v₀ L)) = c • C.Th (C.xB B) (w L) := fun L hL =>
    GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hstd _ hΛM _ _ (hsd L hL) (hsd L hL)
      h hh 1 (one_mem _) hmov (by rw [(fmt_one T).1]; exact GlobalTheory.Ker.VacPhase.isMov_one _)
      (v₀ L) (w L) (hv₀ L hL) (hvac L hL) B hB

  have pos : ∀ L ∈ Lv.lats, GlobalTheory.SW.ip (v₀ L) (w L) ≠ 0 ∧
      GlobalTheory.SW.ip (v₀ L) (w L) = ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ) := by
    intro L hL
    obtain ⟨hne, heq⟩ := GlobalTheory.SW.RecSum.unitv_proj (D := Lv) C.idx C.sympl C.even hΛM (hsd L hL)
      (hv₀ L hL) (hvac L hL)
    rw [← hw L] at heq
    refine ⟨hne, ?_⟩
    have h1 : GlobalTheory.SW.ip (w L) (w L) = 1 := (hvac L hL).2.1
    have e : (GlobalTheory.SW.ip (v₀ L) (w L) / ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ)) * GlobalTheory.SW.ip (w L) (w L) =
        GlobalTheory.SW.ip (w L) (w L) := by
      rw [← GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL), ← heq]
    rw [h1, mul_one] at e
    have hn0 : ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
    exact (div_eq_one_iff_eq hn0).1 e
  have hXl : C.X.Λ ∈ Lv.lats := h6833.1
  obtain ⟨ep, hep1, hep⟩ := phase C.X.Λ hXl
  refine ⟨ep, hep1, ?_⟩
  intro g L hg hgtriv hLfg hgmov
  rw [← hw L]
  have hL : L ∈ Lv.lats := ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L hLfg hgmov).2.1 hgtriv
  obtain ⟨c, hc1, hc⟩ := phase L hL
  rw [hc]

  have hXsd : SelfD C.X C.X.Λ := (show SelfD C.X C.X.Λ ∧ _ from hXl).1
  have hXfs : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨hXsd.1, (h6833.2.2.2.1 _ hXl).2.1⟩
  have hinv : fmt T g * fmt T g⁻¹ = 1 := by
    rw [← (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.1 g g⁻¹).2.1, mul_inv_cancel, (fmt_one T).1]
  have hshmov : IsMov (fmt T g) (Lv.sh C.X.Λ) (Lv.sh L) :=
    ((((GlobalTheory.T.finiteAdelicLatticeTransport_laws D T.rank C.X.Λ hXfs).2.2.2 (fmt T g) (fmt T g⁻¹) hinv).2 L hLfg hgmov).2.2.2.2
      Lv.𝔪 (conjI Lv.𝔪) Lv.ne_bot (GlobalTheory.Ker.VacPhase.conjI_ne_bot Lv.ne_bot)).2.1

  obtain ⟨a, ha1, ha⟩ := GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hstd _ hstd _ _
    (hsd _ hXl) (hsd L hL) 1 (one_mem _) g hg (hS1 _) hshmov (v₀ C.X.Λ) (v₀ L) (hv₀ _ hXl) (hv₀ L hL) B hB
  obtain ⟨b, hb1, hb⟩ := GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hΛM _ hΛM _ _
    (hsd _ hXl) (hsd L hL) 1 (one_mem _) g hg (hS1 _) hshmov (w C.X.Λ) (w L) (hvac _ hXl) (hvac L hL) B hB

  have hThX := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx _ (hsbv _ hXl)).1.1
  have hThwX := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx _ (hsbw _ hXl)).1.1
  have hinvar := (((GlobalTheory.Ker.ScalarProduct.ip_basic D S T C).2 μ 𝓕 hcov _ hThX).2.2.2 _ hThwX).2.2.2.2.2
    om hom (1, g)
  rw [ha, hb, ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbv L hL)).2.1 a,
    ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbw L hL)).2.1 b,
    hipTh B hB _ _ (GlobalTheory.SW.TensVac.sb_smul a (hsbv L hL)) (GlobalTheory.SW.TensVac.sb_smul b (hsbw L hL)),
    hipTh B hB _ _ (hsbv _ hXl) (hsbw _ hXl),
    GlobalTheory.SW.TensVac.ip_smul_left _ (hsbv L hL) (GlobalTheory.SW.TensVac.sb_smul b (hsbw L hL)),
    GlobalTheory.SW.TensVac.ip_smul_right _ (hsbv L hL) (hsbw L hL)] at hinvar
  have e1 : a * (conj b * GlobalTheory.SW.ip (v₀ L) (w L)) = GlobalTheory.SW.ip (v₀ C.X.Λ) (w C.X.Λ) :=
    mul_left_cancel₀ hκ hinvar
  obtain ⟨hpL0, hpL⟩ := pos L hL
  obtain ⟨-, hpX⟩ := pos _ hXl
  have hnorm : ‖GlobalTheory.SW.ip (v₀ C.X.Λ) (w C.X.Λ)‖ = ‖GlobalTheory.SW.ip (v₀ L) (w L)‖ := by
    rw [← e1, norm_mul, norm_mul, Complex.norm_conj, ha1, hb1, one_mul, one_mul]
  have e2 : (a * conj b) * GlobalTheory.SW.ip (v₀ L) (w L) = 1 * GlobalTheory.SW.ip (v₀ L) (w L) := by
    rw [mul_assoc, e1, one_mul, hpX, hnorm, ← hpL]
  have hab : a * conj b = 1 := mul_right_cancel₀ hpL0 e2
  have hbb : b * conj b = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    norm_num
  have hab' : a = b := by
    calc a = a * (b * conj b) := by rw [hbb, mul_one]
      _ = (a * conj b) * b := by ring
      _ = b := by rw [hab, one_mul]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha1
    exact zero_ne_one ha1

  have hsq : om (h, 1) (om (1, g) (C.Th (C.xB B) (v₀ C.X.Λ))) =
      om (1, g) (om (h, 1) (C.Th (C.xB B) (v₀ C.X.Λ))) := by
    have e : ((h, 1) : GA D S × GA D T) * (1, g) = (1, g) * (h, 1) := by simp
    have := congrArg (fun p => om p (C.Th (C.xB B) (v₀ C.X.Λ))) e
    simpa only [map_mul, Module.End.mul_apply] using this
  rw [ha, hep, map_smul, map_smul, hc, hb, smul_smul, smul_smul,
    ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbw L hL)).2.1 (a * c),
    ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (hsbw L hL)).2.1 (ep * b)] at hsq
  have hfun := ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ (GlobalTheory.SW.TensVac.sb_smul (a * c) (hsbw L hL))).1 _
    (GlobalTheory.SW.TensVac.sb_smul (ep * b) (hsbw L hL))).2 hsq
  have e3 := congrArg (fun φ => GlobalTheory.SW.ip φ (w L)) hfun
  rw [GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL),
    GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL), (hvac L hL).2.1, mul_one, mul_one,
    hab', mul_comm ep b] at e3
  rw [mul_left_cancel₀ (hab' ▸ ha0) e3]

end GlobalTheory.Ker.VacPhase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DefiniteGroupVacuumPhaseIndependentOfLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_group_vacuum_phase_independent_of_lattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∃ ep : ℂ, ‖ep‖ = 1 ∧ ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → om (h, 1) (C.Th (C.xB B) (v₀ L)) = ep • (C.Th (C.xB B) (unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)))) := by
  first | exact @GlobalTheory.Ker.VacPhase.phase_indep | exact GlobalTheory.Ker.VacPhase.phase_indep | (intros; apply GlobalTheory.Ker.VacPhase.phase_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevelMove

section Lattices

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem full_stdL (E : Type) [Field E] [NumberField E] (r : ℕ) :
    (stdL E r).FG ∧ Submodule.span E (stdL E r : Set (Fin r → E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem full_smul {L : Lt E r} (hL : L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤)
    {𝔠 : Ideal (𝓞 E)} (h : 𝔠 ≠ ⊥) :
    (𝔠 • L).FG ∧ Submodule.span E ((𝔠 • L : Lt E r) : Set (Fin r → E)) = ⊤ := by
  refine ⟨hL.1.of_le Submodule.smul_le_right, ?_⟩
  obtain ⟨c, hc, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [eq_top_iff, ← hL.2, Submodule.span_le]
  intro v hv
  have h1 : (c : E) ≠ 0 := by simpa using h0
  have : v = (c : E)⁻¹ • (c • v) := by
    change v = (c : E)⁻¹ • ((c : E) • v)
    rw [inv_smul_smul₀ h1]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hc hv))

theorem nsmul_mem_tens {n : ℕ} {Λ : Lt E n} {L : Lt E r} {𝔠 𝔪 : Ideal (𝓞 E)} {M : ℕ} (hM : (M : 𝓞 E) ∈ 𝔪)
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ (𝔠 • L)) : M • y ∈ tens Λ (𝔪 • L) := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨v, hv, (M : 𝓞 E) • u,
      Submodule.smul_mem_smul hM (Submodule.smul_le_right hu), ?_⟩
    rw [Nat.cast_smul_eq_nsmul]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, mul_smul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end Lattices

variable {D : D7} {S T : HSp D}

theorem nsmul_mem_hatA {A B : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)} {M : ℕ}
    (h : ∀ y ∈ A, M • y ∈ B) {u : WO S T} (hu : u ∈ hatA S T A) : M • u ∈ hatA S T B := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M • y, h y hy, ?_⟩
    exact (map_nsmul (HatLat.fT D.host.F α) M y).symm
  | zero => simp
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem finW_neg (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : finW S T (-y) = -finW S T y :=
  map_neg (HatLat.fT D.host.F 1) y

theorem actO_neg (h : GA D S) (g : GA D T) (u : WO S T) : actO S T h g (-u) = -actO S T h g u := by
  unfold actO
  rw [Matrix.mul_neg, Matrix.neg_mul]

theorem fmt_mul_inv (V : HSp D) (g : GA D V) : fmt V g * fmt V g⁻¹ = 1 := by
  have : mt V g * mt V g⁻¹ = 1 := by simp [Formalism.L2.Theta.mt]
  rw [fmt, fmt, ← Matrix.map_mul, this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fmtC_mul_inv (V : HSp D) (g : GA D V) : fmtC V g * fmtC V g⁻¹ = 1 := by
  have : mt V g * mt V g⁻¹ = 1 := by simp [Formalism.L2.Theta.mt]
  rw [fmtC, fmtC, cM, cM, ← Matrix.map_mul, ← Matrix.map_mul, this, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem fmtC_one (V : HSp D) : fmtC V 1 = 1 := by
  have : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [fmtC, cM, this, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem heisO_add_two (ψ : AddChar (AF D.host.F) ℂ) (u a : WO S T) (f : WO S T → ℂ)
    (h1 : heisO ψ S T a f = f) (h2 : heisO ψ S T a (heisO ψ S T u f) = heisO ψ S T u f) :
    heisO ψ S T (u + 2 • a) f = heisO ψ S T u f := by
  have h3 : heisO ψ S T a (heisO ψ S T u (heisO ψ S T a f)) = heisO ψ S T u f := by rw [h1, h2]
  rw [FinTranslate.heisO_heisO S T ψ u a] at h3
  have h4 := (FinTranslate.heisL S T ψ a).map_smul (ψ (symplOH S T u a)) (heisO ψ S T (u + a) f)
  change heisO ψ S T a _ = _ • heisO ψ S T a _ at h4
  rw [h4, FinTranslate.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, FinTranslate.symplOH_add_right,
    FinTranslate.symplOH_self, FinTranslate.symplOH_skew S T u a, add_zero, add_neg_cancel,
    AddChar.map_zero_eq_one, one_smul] at h3
  rw [← h3]
  congr 1
  abel

theorem exists_approx (C : Ctx S T) {Λ : Lt D.host.E S.rank} {L : Lt D.host.E T.rank}
    (hΛ : Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) = ⊤)
    (hL : L.FG ∧ Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤)
    {f : WO S T → ℂ} (hf : C.IsTh f) {u : WO S T} (hu : u ∈ hatA S T (tens Λ L)) {M : ℕ} (hM : 0 < M) :
    ∃ y ∈ tens Λ L, ∃ u' ∈ hatA S T (tens Λ L), u = finW S T y + M • u' ∧
      C.rho (-finW S T y) f = C.rho (-u) f := by
  obtain ⟨-, -, h3, h4, -⟩ := HatLat.hatA_tens D S T C Λ L hΛ hL
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨U', hU', hUf'⟩ := (FinTranslate.isThetaFunO_heisO C.std.1.1 C.std.1.2.1 hf (h3 _ (neg_mem hu)).1).level
  obtain ⟨N, hN, hNU⟩ := h4 (U ⊓ U') (hU.inter hU')
  obtain ⟨y, hy, u', hu', e⟩ := (h3 u hu).2 (2 * (N * M)) (by positivity)
  have hm := nsmul_mem hu' M
  have hfin := (h3 _ (nsmul_mem hm N)).1
  refine ⟨y, hy, (2 * N) • u', nsmul_mem hu' _, ?_, ?_⟩
  · rw [e, smul_smul]; congr 2; ring
  · have : -finW S T y = -u + 2 • N • M • u' := by
      rw [e, smul_smul, smul_smul, mul_assoc]; abel
    rw [this]
    exact heisO_add_two _ _ _ _ (hUf _ (hNU _ hm).1 hfin) (hUf' _ (hNU _ hm).2 hfin)

theorem Th_sum (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type} (s : Finset ι)
    (φ : ι → TF S.rank C.g) (hφ : ∀ i, SW.IsSB (φ i)) : C.Th x (∑ i ∈ s, φ i) = ∑ i ∈ s, C.Th x (φ i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx 0 (RecSum.isSB_sum (∅ : Finset ι) φ hφ)).2.1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ (hφ a)).1 _ (RecSum.isSB_sum s φ hφ)).1

theorem Th_sum_heis (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type} [Fintype ι]
    (a : ι → ℂ) (y : ι → Matrix (Fin S.rank) (Fin T.rank) D.host.E) {v : TF S.rank C.g} (hv : SW.IsSB v) :
    C.Th x (∑ i, a i • heisG C.X C.bas (y i) v) = ∑ i, a i • C.rho (-finW S T (y i)) (C.Th x v) := by
  have h := fun i => ((heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 (y i) v hv).1
  rw [Th_sum C hx _ _ fun i => TensVac.sb_smul _ (h i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ (h i)).2.1, ← finW_neg, (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ hv).2.2.1, neg_neg]

theorem om_Th_phi : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∃ (ep : GA D S → ℂ) (c : GA D T → ℂ), ∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖c g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * c g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ)) := by
  intro D S T C om hom Lv hn M hw hM0 hM v₀ hv₀ B hB
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  obtain ⟨hX, -, -, hl, -, hd, -⟩ := level_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  have hS := full_stdL D.host.E S.rank
  have hSV := Base.stdL_mem_Vset (E := D.host.E) S.rank M
  have hX0 : C.X.Λ.FG ∧ _ := ⟨hX.1.1, (hl _ hX).2.1⟩
  have hone : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [fmtC_one]; exact (GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ _ hS).2.1
  have H1 : ∀ h : GA D S, ∃ ep : ℂ, ∀ Λ : Lt D.host.E S.rank, h ∈ GfC S →
      TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ →
      ‖ep‖ = 1 ∧ ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG →
        IsMov (fmt T g) C.X.Λ L → om (h, 1) (C.Th (C.xB B) (v₀ L)) =
          ep • (C.Th (C.xB B) (unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)))) := by
    intro h
    by_cases H : ∃ Λ : Lt D.host.E S.rank, h ∈ GfC S ∧ TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ Λ.FG ∧
        IsMov (fmtC S h) (stdL D.host.E S.rank) Λ
    · obtain ⟨Λ, h1, h2, h3, h4⟩ := H
      obtain ⟨ep, hep⟩ := GlobalTheory.T.definite_group_vacuum_phase_independent_of_lattice D S T C om hom Lv hn M hw hM0 hM v₀ hv₀ B hB h Λ h1 h2 h3 h4
      refine ⟨ep, fun Λ' _ _ h3' h4' => ?_⟩
      rw [(((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ _ hS).2.2.2 _ _ (fmtC_mul_inv S h)).2 Λ h3 h4).2.2.1 Λ' h3' h4']
      exact hep
    · exact ⟨1, fun Λ h1 h2 h3 h4 => (H ⟨Λ, h1, h2, h3, h4⟩).elim⟩
  have H2 : ∀ g : GA D T, ∃ c : ℂ, ∀ L : Lt D.host.E T.rank, g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG →
      IsMov (fmt T g) C.X.Λ L →
      ‖c‖ = 1 ∧ om (1, g) (C.Th (C.xB B) (v₀ C.X.Λ)) = c • C.Th (C.xB B) (v₀ L) := by
    intro g
    by_cases H : ∃ L : Lt D.host.E T.rank, g ∈ GfC T ∧ TrivAt T (C.under Lv) g ∧ L.FG ∧ IsMov (fmt T g) C.X.Λ L
    · obtain ⟨L, h1, h2, h3, h4⟩ := H
      have hL : L ∈ Lv.lats := ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L h3 h4).2.1 h2
      have hm := ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ _ hX0).2.2.2 _ _ (fmt_mul_inv T g)).2 L h3 h4
      have hc : conjI Lv.𝔪 ≠ ⊥ := fun e => Lv.proper (by
        have := Lv.cop
        rwa [e, ← Ideal.zero_eq_bot, isCoprime_zero_right, Ideal.isUnit_iff] at this)
      obtain ⟨c, hc⟩ := GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum D S T C om hom Lv.w Lv.w_int Lv.w_tr hw M _ hSV _ hSV _ _ (hl _ hX).1
        (hl _ hL).1 1 (one_mem _) g h1 hone (hm.2.2.2.2 _ _ Lv.ne_bot hc).2.1 _ _ (hv₀ _ hX) (hv₀ _ hL) B hB
      refine ⟨c, fun L' _ _ h3' h4' => ?_⟩
      rw [hm.2.2.1 L' h3' h4']
      exact hc
    · exact ⟨1, fun L h1 h2 h3 h4 => (H ⟨L, h1, h2, h3, h4⟩).elim⟩
  choose ep hep using H1
  choose c hc using H2
  refine ⟨ep, c, fun h Λ g L h1 h2 h3 h4 g1 g2 g3 g4 => ⟨(hep h Λ h1 h2 h3 h4).1, (hc g L g1 g2 g3 g4).1, ?_⟩⟩
  have hL : L ∈ Lv.lats := ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L g3 g4).2.1 g2
  have hΛ : Λ ∈ Vset D.host.E S.rank M := (GlobalTheory.T.self_dual_lattices_at_level D S T C).1 M h Λ hM0 h2 h3 h4
  have hΛ0 : Λ.FG ∧ _ := ⟨h3, (((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ _ hS).2.2.2 _ _ (fmtC_mul_inv S h)).2 Λ h3 h4).1⟩
  have hm := ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ _ hX0).2.2.2 _ _ (fmt_mul_inv T g)).2 L g3 g4
  have h𝔠 : Ideal.span {2} * conjI Lv.𝔪 ≠ ⊥ := fun e => Lv.proper (by
    have := RecSum.cop_level Lv
    rwa [e, ← Ideal.zero_eq_bot, isCoprime_zero_left, Ideal.isUnit_iff] at this)
  have hL0 := full_smul ⟨g3, hm.1⟩ h𝔠
  have hmov := (GlobalTheory.T.completedTensorLattice_lattice_vacuum_transport D S T C h g _ _ _ _ h4 (hm.2.2.2.2 _ _ h𝔠 h𝔠).1).1
  have hV0 := RecSum.isVac_unitv C.idx C.sympl C.even hSV (hl _ hX).1 (hv₀ _ hX)
  have hV := RecSum.isVac_unitv C.idx C.sympl C.even hΛ (hl _ hL).1 (hv₀ _ hL)
  have e0 : unitv (projA C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) (v₀ C.X.Λ)) = v₀ C.X.Λ := by
    rw [(RecSum.unitv_proj C.idx C.sympl C.even hSV (hl _ hX).1 (hv₀ _ hX) (hv₀ _ hX)).2, (hv₀ _ hX).2.1]
    simp
  have t0 : C.IsTh (C.Th (C.xB B) (v₀ C.X.Λ)) := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx _ (hv₀ _ hX).1).1.1
  have t1 := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx _ hV.1).1.1
  have key : om (h, g) (C.Th (C.xB B) (v₀ C.X.Λ)) = (ep h * c g) •
      C.Th (C.xB B) (unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L))) := by
    rw [show ((h, g) : GA D S × GA D T) = (h, 1) * (1, g) by simp, map_mul, Module.End.mul_apply,
      (hc g L g1 g2 g3 g4).2, map_smul, (hep h Λ h1 h2 h3 h4).2 g L g1 g2 g3 g4, smul_smul, mul_comm]
  haveI := RecSum.finite_J Lv
  haveI : Fintype Lv.J := Fintype.ofFinite _
  obtain ⟨f, f1, f2, f3, -⟩ := RecSum.exists_reps C.idx C.sympl C.even hn hM hSV (RecSum.near_of_mem hX)
  have hu : ∀ i, actO S T h g (finW S T (f i)) ∈ hatA S T (tens Λ ((Ideal.span {2} * conjI Lv.𝔪) • L)) := fun i =>
    (hmov _).2 ⟨_, ((HatLat.hatA_tens D S T C _ _ hS (full_smul hX0 h𝔠)).2.1 _).2 (f1 i), rfl⟩
  choose f' f1' u' hu' eu er using fun i => exists_approx C hΛ0 hL0 t1 (hu i) hM0
  have hcong : ∀ i k, Cong C.X Lv.𝔪 (f' i k) (f i k) := fun i =>
    GlobalTheory.T.rows_congr_of_trivial_at_level D S T C Lv hn M hw hM0 hM h Λ g L h1 h2 h3 h4 g1 g2 g3 g4 _ _ (by
      rw [eu i, sub_add_cancel_left]
      exact neg_mem (nsmul_mem_hatA (fun y hy => nsmul_mem_tens hM hy) (hu' i)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [RecSum.phi_eq_sum C.idx C.sympl C.even hn hM hSV hX v₀ hV0 f f1 f2 f3,
    RecSum.phi_eq_sum C.idx C.sympl C.even hn hM hΛ hL v₀ hV f' f1'
      (fun i j e => f2 i j fun k => RecSum.cong_trans (RecSum.cong_symm (hcong i k))
        (RecSum.cong_trans (e k) (hcong j k)))
      (fun y hy => (f3 y hy).imp fun i e k => RecSum.cong_trans (e k) (RecSum.cong_symm (hcong i k))),
    Th_sum_heis C hx _ _ hV0.1, Th_sum_heis C hx _ _ hV.1, e0, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hom.om_heis h g _ _ t0, key, actO_neg, hd _ _ (hcong i), er i, smul_comm (ep h * c g)]
  congr 1
  exact (FinTranslate.heisL S T C.ψ _).map_smul _ _

end GlobalTheory.Ker.LevelMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPair_levelTrivial_maps_levelVector : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∃ (ep : GA D S → ℂ) (c : GA D T → ℂ), ∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖c g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * c g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ)) := by
  first | exact @GlobalTheory.Ker.LevelMove.om_Th_phi | exact GlobalTheory.Ker.LevelMove.om_Th_phi | (intros; apply GlobalTheory.Ker.LevelMove.om_Th_phi <;> assumption)
end

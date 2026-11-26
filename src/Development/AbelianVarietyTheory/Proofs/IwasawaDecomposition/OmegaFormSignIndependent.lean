module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionFixesLevelVectorUpToUnit
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HostElementIdempotentModTwo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.AtRecord

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 : (H.w0 : E) + cc (H.w0 : E) = 1 := by
    have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
    rw [map_add (f := _), map_one] at this
    exact (congrArg _ (H.bar_eq _).symm).trans this
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

end GlobalTheory.Ker.AtRecord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFinitePointMovesVacuumToProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFinitePointMovesVacuumToProjection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.OneMapRef.SplitProj

open GlobalTheory.Ker GlobalTheory.AdTh.SplitClass

variable {D : D7} {S T : HSp D}

theorem span_of_vset {n : ℕ} {Λ : Lt D.host.E n} (h : Λ ∈ Vset D.host.E n 1) :
    Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ :=
  DualFamily.span_eq_top Λ h.1 fun x => (h.2.1 x).2

theorem exists_selfDualC (hS : S.gram = 1) {Λ : Lt D.host.E S.rank} (h : Λ ∈ Vset D.host.E S.rank 1) :
    ∃ ΛS : Lt D.host.E S.rank, IsSelfDualC S ΛS ∧ ∀ v, v ∈ Λ ↔ star v ∈ ΛS := by
  obtain ⟨ΛS, h1⟩ := exists_conj Λ
  have h1' : ∀ v, v ∈ ΛS ↔ star v ∈ Λ := h1
  have hfg := GlobalTheory.AdTh.LatOf.fg_of_star h.1 h1'
  have hU := (GenLatCmp.unimod_iff Λ).2 h.2.1
  have key : ∀ y : Fin S.rank → D.host.E, y ∈ ΛS ↔
      ∀ x ∈ ΛS, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j := by
    intro y
    have e : ∀ x : Fin S.rank → D.host.E,
        ∑ i, ∑ j, star (x i) * S.gram i j * y j = ∑ j, star ((star y) j) * (star x) j := by
      intro x
      simp [hS, Matrix.one_apply, mul_comm]
    have hy : star y ∈ Λ ↔ ∀ w ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star ((star y) j) * w j := hU (star y)
    rw [h1', hy]
    simp only [e]
    constructor
    · intro H x hx
      exact H _ ((h1' x).1 hx)
    · intro H w hw
      have := H (star w) ((h1' _).2 (by rwa [star_star]))
      rwa [star_star] at this
  exact ⟨ΛS, ⟨Submodule.IsLattice.of_fg D.host.E hfg, key⟩,
    fun v => by rw [h1', star_star]⟩

open scoped ComplexOrder in
theorem cartan_one (hS : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by
    unfold gramAt
    rw [hS]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem fmtC_mul (V : HSp D) (g g' : GA D V) : fmtC V (g * g') = fmtC V g * fmtC V g' := by
  simp only [fmtC, Formalism.L2.Theta.cM, AdelicLatMove.mt_mul, Matrix.map_mul]

theorem fmtC_one (V : HSp D) : fmtC V 1 = 1 := by
  simp only [fmtC, Formalism.L2.Theta.cM, AdelicLatMove.mt_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, AdelicLatMove.mt_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _)]

theorem finW_sub (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : finW S T (y - y') = finW S T y - finW S T y' :=
  map_sub (LatTens.gen S T 1) y y'

theorem good (C : Ctx S T) {w : D.host.E} (hw : IsIntegral ℤ w) (hw1 : w + cc w = 1) {L : Lt D.host.E T.rank}
    (hL : SelfD C.X L) {Λ : Lt D.host.E S.rank} (h : Λ ∈ Vset D.host.E S.rank 1) :
    TensVac.Good C.X w (tens Λ L) := by
  obtain ⟨a1, a2, a3, -⟩ := TensLat.tens_selfDual_semichar_index _ _ C.X C.g C.bas C.idx _ C.sympl C.even _
    hw hw1 L hL 1 _ h
  exact ⟨a1, a2, a3⟩

theorem th_sum (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type} (s : Finset ι)
    {φ : ι → TF S.rank C.g} (h : ∀ i, GlobalTheory.SW.IsSB (φ i)) {v : TF S.rank C.g} (hv : GlobalTheory.SW.IsSB v) :
    GlobalTheory.SW.IsSB (∑ i ∈ s, φ i) ∧ C.Th x (∑ i ∈ s, φ i) = ∑ i ∈ s, C.Th x (φ i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h1 := TensVac.sb_smul 0 hv
    have h2 := (Ctx.th_laws D S T C x hx v hv).2.1 0
    rw [zero_smul] at h1 h2
    rw [zero_smul] at h2
    exact ⟨h1, h2⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih.2]
    exact ⟨(GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ _ _ (h i) ih.1).1, ((Ctx.th_laws D S T C x hx _ (h i)).1 _ ih.1).1⟩

theorem step (C : Ctx S T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO C.ψ S T χS χT om) (hS : S.SigOK) (hT : T.SigOK) {w : D.host.E} (hw : IsIntegral ℤ w)
    (hw1 : w + cc w = 1) (hw2 : IdemTwo w) {B : C.Bas} (hB : C.IsB B) {LT L : Lt D.host.E T.rank}
    (hLT : IsSelfDualC T LT) (hL : SelfD C.X L) (hA : IsAA L LT) {Λ Λ₁ : Lt D.host.E S.rank}
    (hΛ : Λ ∈ Vset D.host.E S.rank 1) (hΛ₁ : Λ₁ ∈ Vset D.host.E S.rank 1) {e : AE D} (he : IsSplitIdem D e)
    {h : GA D S} (hh : SuppAt e S h) {y : (AE D)ˣ} (hy : IsDetAt e S h y) (hm : IsMov (fmtC S h) Λ Λ₁)
    {v : TF S.rank C.g} (hv : IsVac C.X C.bas w (tens Λ L) v) (κ : ℂ) :
    om (h, 1) (C.Th (C.xB B) (κ • v)) = C.Th (C.xB B)
      ((((χT y : Circle) : ℂ)⁻¹ * (Real.sqrt ((tens Λ L).relIndex (tens Λ₁ L) : ℝ) : ℂ)) •
        projA C.X C.bas w (tens Λ₁ L) (κ • v)) := by
  have g0 := good C hw hw1 hL hΛ
  have g1 := good C hw hw1 hL hΛ₁
  obtain ⟨ΛS, d0, s0⟩ := exists_selfDualC C.m.gS hΛ
  obtain ⟨ΛS₁, d1, s1⟩ := exists_selfDualC C.m.gS hΛ₁
  have l0 := LatTens.latO_eq_hatA D S T C ΛS Λ LT L s0 hA
  have l1 := LatTens.latO_eq_hatA D S T C ΛS₁ Λ₁ LT L s1 hA
  obtain ⟨-, hx, hc, -⟩ := (onBasis_frame_period D S T C).2 B hB
  have hLs := TensLat.span_of_selfD C.X hL
  obtain ⟨-, r0, -⟩ := HatLat.hatA_tens D S T C Λ L ⟨hΛ.1, span_of_vset hΛ⟩ ⟨hL.1, hLs⟩
  obtain ⟨-, r1, a1, -⟩ := HatLat.hatA_tens D S T C Λ₁ L ⟨hΛ₁.1, span_of_vset hΛ₁⟩ ⟨hL.1, hLs⟩
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D C.ψ C.θ C.std C.inf S T (fun _ => 1) (C.sB B) hS hT
    (cartan_one C.m.gS) (fun τ => (hc τ).1) ΛS LT d0 hLT
  obtain ⟨t, ht⟩ := (latVac_th_line D S T C w hw hw1 hw2 1 Λ hΛ L hL).2 B hB v hv f hf.2.theta hf.2.fock
    (l0 ▸ hf.2.lat)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    subst ht
    obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
    have := hn p hp
    simp [nrm2] at this
  obtain ⟨v₁, hv₁, -⟩ := g1.vac C.sympl
  have hidx : (tens Λ L).relIndex (tens Λ₁ L) ≠ 0 := by
    intro h0
    have := g1.overlap C.idx C.sympl C.even g0 hv₁ hv
    rw [h0, Nat.cast_zero, zero_mul] at this
    exact zero_ne_one this
  have : ((tens Λ L).addSubgroupOf (tens Λ₁ L)).FiniteIndex := ⟨hidx⟩
  haveI := Fintype.ofFinite (tens Λ₁ L ⧸ (tens Λ L).addSubgroupOf (tens Λ₁ L))
  obtain ⟨R, hR, hRu⟩ := exists_reps (tens Λ L) (fun z => z ∈ tens Λ₁ L) Finset.univ
    (fun q : tens Λ₁ L ⧸ (tens Λ L).addSubgroupOf (tens Λ₁ L) => (q.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))
    fun z hz => ⟨QuotientAddGroup.mk ⟨z, hz⟩, Finset.mem_univ _,
      AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq_iff_sub_mem.1 (QuotientAddGroup.out_eq'
        (QuotientAddGroup.mk ⟨z, hz⟩ : tens Λ₁ L ⧸ (tens Λ L).addSubgroupOf (tens Λ₁ L))).symm)⟩
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.AdTh.VacProj.proj_eq C.idx C.sympl C.even g1 g0 hv R hR hRu
  have hc0 : (0 : ℝ) < R.card := by rw [c1]; exact Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)
  have hc0' : (R.card : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hsq : (Real.sqrt (R.card : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hc0).ne'
  have hp := (g1.proj C.idx C.sympl C.even hv.1 hv₁).1
  have lin := fun φ hφ => (Ctx.th_laws D S T C _ hx φ hφ).2.1
  have hG : ∑ z ∈ R, epsW C.X w z • heisO C.ψ S T (finW S T (-z)) f = C.Th (C.xB B)
      ((t * (Real.sqrt (R.card : ℝ) : ℂ)) • (Real.sqrt (R.card : ℝ) : ℂ) • projA C.X C.bas w (tens Λ₁ L) v) := by
    have hsb : ∀ z, GlobalTheory.SW.IsSB (epsW C.X w z • heisG C.X C.bas z v) := fun z =>
      TensVac.rho_sb C.idx C.sympl C.even z hv.1
    obtain ⟨u1, u2⟩ := th_sum C hx R hsb hv.1
    rw [c2, smul_smul, smul_smul, mul_assoc t, ← Complex.ofReal_mul, Real.mul_self_sqrt hc0.le,
      Complex.ofReal_natCast, mul_inv_cancel_right₀ hc0', lin _ u1, u2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h1 := (Ctx.th_laws D S T C _ hx v hv.1).2.2.1 (-z)
    rw [neg_neg] at h1
    rw [lin (heisG C.X C.bas z v) (GlobalTheory.SW.heisS_laws _ _ _ _ v hv.1).1, ← h1, ht, GlobalTheory.SplitScalar.heisO_smul, smul_comm]
  have hN : hatA S T (tens Λ₁ L) ≤ (hatA S T (tens Λ L)).comap
      (nsmulAddMonoidHom ((tens Λ L).relIndex (tens Λ₁ L))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, z, hz, rfl⟩
    exact AddSubgroup.subset_closure ⟨α, hα, _, AddSubgroup.nsmul_relIndex_mem _ hz,
      (map_nsmul (LatTens.gen S T α) _ z).symm⟩
  have hone : IsMov (fmt T 1) L L := by
    rw [fmt_one]; exact (isMov_laws D _ L ⟨hL.1, hLs⟩).2.1
  have hom := om_eq_smul_sum hW C.inf hS hT (cartan_one C.m.gS) (fun τ => (hc τ).1) d0 d1 hLT he hh hy l0.symm l1.symm
    (GlobalTheory.TensLatMove.hatA_move D S T C h 1 Λ Λ₁ L L hm hone).1 hf R
    (fun z => finW S T (-z)) (epsW C.X w) (fun z hz => (r1 _).2 (neg_mem (hR z hz))) (fun z _ => norm_epsW C.X _ z)
    (fun u hu => by
      obtain ⟨z, hz, u', hu', rfl⟩ := (a1 u hu).2 _ (Nat.pos_of_ne_zero hidx)
      obtain ⟨z', ⟨hz', h3⟩, -⟩ := hRu _ (neg_mem hz)
      refine ⟨z', hz', ?_⟩
      rw [add_sub_right_comm, ← finW_sub]
      refine add_mem ((r0 _).2 ?_) (hN hu')
      convert neg_mem h3 using 1
      abel)
    (fun z hz z' hz' hm => by
      rw [← finW_sub, r0, neg_sub_neg, ← neg_sub, neg_mem_iff] at hm
      exact (hRu z (hR z hz)).unique ⟨hz, by rw [sub_self]; exact zero_mem _⟩ ⟨hz', hm⟩)
    (fun F hF hFl z hz => by
      have := (SignVac.isLatVac_iff D S T C w hw hw1 hw2 1 Λ₁ hΛ₁ L hL F hF).1 hFl _ (neg_mem (hR z hz))
      rwa [epsW_neg] at this)
    (by
      rw [hG]
      refine ((latVac_th_line D S T C w hw hw1 hw2 1 Λ₁ hΛ₁ L hL).1 _ hx _ (TensVac.sb_smul _ c3.1)).2 fun z hz => ?_
      rw [TensVac.heisG_smul, smul_comm, c3.2.2 z hz])
  rw [hG, ht, map_smul, lin _ c3.1, lin _ hp, smul_smul, smul_smul] at hom
  rw [projA_smul C.idx C.sympl C.even g1 _ hv.1, smul_smul, lin _ hp, lin _ hv.1, map_smul,
    ← inv_smul_smul₀ ht0 (om (h, 1) _), hom, smul_smul, smul_smul, ← c1]
  congr 1
  field_simp


open GlobalTheory.AdLat in
theorem mov_split {V : HSp D} {e : AE D} (he : IsSplitIdem D e) {h h' : GA D V}
    (h1 : (e + cA D e) • Formalism.L2.Theta.mt V h' = (e + cA D e) • 1)
    (h2 : (1 - (e + cA D e)) • Formalism.L2.Theta.mt V h' = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V h)
    {Λ₀ Λ' Λ₁ : Lt D.host.E V.rank} (v0 : Λ₀ ∈ Vset D.host.E V.rank 1) (v' : Λ' ∈ Vset D.host.E V.rank 1)
    (v1 : Λ₁ ∈ Vset D.host.E V.rank 1) (m' : IsMov (fmtC V h') Λ₀ Λ') (m : IsMov (fmtC V h) Λ₀ Λ₁) :
    ∀ v ∈ Λ', ∃ x, x ∈ Λ₀ ∧ x ∈ Λ' ∧ v - x ∈ Λ₁ := by
  intro v hv
  have hc : cA D (e + cA D e) = e + cA D e := by rw [RingHom.map_add (f := _), cA_cA, add_comm]
  obtain ⟨-, -, p, ε, ⟨α, rfl, a1, a0⟩, h3⟩ := he
  have hα : ∀ q, α q ∈ q.adicCompletionIntegers D.host.F := fun q => by
    by_cases hq : q = p
    · subst hq
      have : α q = 1 := a1
      rw [this]; exact one_mem _
    · have : α q = 0 := a0 q hq
      rw [this]; exact zero_mem _
  have ht : finPart D (e + cA D e) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by rw [h3]; rfl
  generalize e + cA D e = t at h1 h2 ht hc
  have hst : ∀ (L : Lt D.host.E V.rank), ∀ z ∈ hatV L, finPart D t • z ∈ hatV L :=
    fun L z hz => by rw [ht]; exact tmul_smul_mem _ hα hz
  have hv' : toAf v ∈ hatV Λ' := cap_fv_mem D.host.F _ v hv
  obtain ⟨u, hu, e0⟩ := (m' _).1 hv'
  have key : ∀ (s : AE D) (k k' : GA D V), cA D s = s → s • Formalism.L2.Theta.mt V k = s • Formalism.L2.Theta.mt V k' →
      finPart D s • fmtC V k *ᵥ u = fmtC V k' *ᵥ (finPart D s • u) := fun s k k' hs hM => by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec]
    congr 1
    ext i j
    have := congrArg (fun a => finPart D (cA D a)) (congrFun (congrFun hM i) j)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hs] at this
    exact this
  refine exists_split (F := D.host.F)
    { toIsLattice := Submodule.IsLattice.of_fg D.host.E v0.1, span_eq_top := span_of_vset v0 }
    { toIsLattice := Submodule.IsLattice.of_fg D.host.E v'.1, span_eq_top := span_of_vset v' }
    { toIsLattice := Submodule.IsLattice.of_fg D.host.E v1.1, span_eq_top := span_of_vset v1 }
    (z := finPart D t • toAf v) ?_ (hst _ _ hv') ?_
  · rw [e0, key t h' 1 hc (by rw [h1, AdelicLatMove.mt_one]), fmtC_one, Matrix.one_mulVec]
    exact hst _ _ hu
  · have e1 : toAf v - finPart D t • toAf v = finPart D (1 - t) • toAf v := by
      rw [RingHom.map_sub, RingHom.map_one, sub_smul, one_smul]
    have e2 : finPart D (1 - t) • u ∈ hatV Λ₀ := by
      rw [RingHom.map_sub, RingHom.map_one, sub_smul, one_smul]
      exact sub_mem hu (hst _ _ hu)
    change toAf v - finPart D t • toAf v ∈ hatV Λ₁
    rw [e1, e0, key _ h' h (by rw [RingHom.map_sub, RingHom.map_one, hc]) h2]
    exact (m _).2 ⟨_, e2, rfl⟩

theorem om_th (C : Ctx S T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO C.ψ S T χS χT om) (hS : S.SigOK) (hT : T.SigOK) {w : D.host.E} (hw : IsIntegral ℤ w)
    (hw1 : w + cc w = 1) (hw2 : IdemTwo w) {B : C.Bas} (hB : C.IsB B) {LT L : Lt D.host.E T.rank}
    (hLT : IsSelfDualC T LT) (hL : SelfD C.X L) (hA : IsAA L LT) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) {h : GA D S} (hsupp : SuppAt e S h) {y : (AE D)ˣ} (hdet : IsDetAt e S h y)
    {Λ₁ : Lt D.host.E S.rank} (hΛ₁ : Λ₁ ∈ Vset D.host.E S.rank 1) (hm : IsMov (fmtC S h) (stdL D.host.E S.rank) Λ₁)
    {v : TF S.rank C.g} (hv : IsVac C.X C.bas w (tens (stdL D.host.E S.rank) L) v) (κ : ℂ) :
    om (h, 1) (C.Th (C.xB B) (κ • v)) = C.Th (C.xB B)
      ((((χT y : Circle) : ℂ)⁻¹ * (Real.sqrt ((tens (stdL D.host.E S.rank) L).relIndex (tens Λ₁ L) : ℝ) : ℂ)) •
        projA C.X C.bas w (tens Λ₁ L) (κ • v)) := by
  have hSv : stdL D.host.E S.rank ∈ Vset D.host.E S.rank 1 := Base.stdL_mem_Vset S.rank 1
  obtain ⟨-, m1, -, laws⟩ := isMov_laws D _ _ ⟨hSv.1, span_of_vset hSv⟩
  have hinv : ∀ k : GA D S, fmtC S k * fmtC S k⁻¹ = 1 := fun k => by rw [← fmtC_mul, mul_inv_cancel, fmtC_one]
  have hgood := fun Λ => @good D S T C w hw hw1 L hL Λ
  obtain ⟨ι, Q, es, h1, h2, rfl⟩ := PlaceModelSum.isOrthSum_of_isIdemSum he
  have h3 := he.2
  clear he
  induction Q using Finset.induction_on generalizing h y Λ₁ with
  | empty =>
    rw [Finset.sum_empty] at hsupp hdet
    obtain rfl : h = 1 := mt_inj (by
      have := (suppAt_iff _ _ _).1 hsupp
      rw [RingHom.map_zero, add_zero, zero_smul, eq_comm, sub_eq_zero] at this
      exact this)
    obtain rfl : y = 1 := Units.ext (by
      have : (y : AE D) = _ := hdet
      rw [this, zero_mul, zero_add, sub_zero, Units.val_one])
    rw [fmtC_one] at hm
    obtain rfl : Λ₁ = stdL D.host.E S.rank := ((laws 1 1 (one_mul _)).2 _ hSv.1 m1).2.2.1 _ hΛ₁.1 hm
    rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, AddSubgroup.relIndex_self, map_one,
      projA_smul C.idx C.sympl C.even (hgood _ hSv) _ hv.1, projA_vac C.idx C.sympl C.even (hgood _ hSv) hv]
    simp
  | insert i Q hi ih =>
    rw [Finset.sum_insert hi] at hsupp hdet h3
    have hsp := h1 i (Finset.mem_insert_self _ _)
    have h1' : ∀ j ∈ Q, IsSplitIdem D (es j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2' : ∀ j ∈ Q, ∀ k ∈ Q, k ≠ j → es j * es k = 0 := fun j hj k hk =>
      h2 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have o4 : (∑ j ∈ Q, es j) * (∑ j ∈ Q, es j) = ∑ j ∈ Q, es j :=
      PlaceModelSum.IsOrthSum.idem ⟨ι, Q, es, h1', h2', rfl⟩
    have o7 : es i * ∑ j ∈ Q, es j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => h2 i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        fun hji => hi (hji ▸ hj)
    set a := es i with ha
    set a' := ∑ j ∈ Q, es j with ha'
    have o1 : a * a = a := hsp.1
    have o3 : a * cA D a = 0 := hsp.2.1
    have o2 : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, o1]
    have o5 : cA D a' * cA D a' = cA D a' := by rw [← RingHom.map_mul, o4]
    have o8 : cA D a * cA D a' = 0 := by rw [← RingHom.map_mul, o7, RingHom.map_zero]
    rw [RingHom.map_add (f := _)] at h3
    have o9 : a * cA D a' = 0 := by
      linear_combination (a * cA D a') * h3 - (cA D a' * (cA D a + cA D a')) * o1 -
        (cA D a' * (cA D a + cA D a')) * o7 - a * o8 - a * o5
    have o10 : cA D a * a' = 0 := by
      have := congrArg (cA D) o9
      rwa [RingHom.map_mul, cA_cA, RingHom.map_zero] at this
    have o6 : a' * cA D a' = 0 := by linear_combination h3 - o3 - o9 - o10
    have hε : (a + cA D a) * (a + cA D a) = a + cA D a := by linear_combination o1 + o2 + 2 * o3
    have hcε : cA D (a + cA D a) = a + cA D a := by rw [RingHom.map_add (f := _), cA_cA, add_comm]
    obtain ⟨h₀, e₀⟩ := exists_part S hε hcε h
    obtain ⟨h', e'⟩ := exists_part S (ε := 1 - (a + cA D a)) (by linear_combination hε)
      (by rw [RingHom.map_sub, RingHom.map_one, hcε]) h
    have hsupp' := (suppAt_iff _ _ _).1 hsupp
    rw [RingHom.map_add (f := _)] at hsupp'
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := alg_parts o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 hsupp' e₀ e'
    obtain ⟨y₀, hy₀⟩ := exists_detAt S o1 h₀
    obtain ⟨y', hy'⟩ := exists_detAt S o4 h'
    obtain rfl : y = y₀ * y' := Units.ext (by
      rw [Units.val_mul, show (y : AE D) = _ from hdet, show (y₀ : AE D) = _ from hy₀, show (y' : AE D) = _ from hy', b4])
    obtain ⟨⟨Λ', hf', m'⟩, law⟩ := laws _ _ (hinv h')
    have hΛ' : Λ' ∈ Vset D.host.E S.rank 1 := MovLev.mem_Vset C (h := h') (fun p hp => by
      rw [Nat.cast_one, Ideal.span_singleton_one, top_le_iff] at hp
      exact (p.isPrime.ne_top hp).elim) hf'.1 m'
    have hle := tens_le L (mov_split hsp b5 b6 hSv hΛ' hΛ₁ m' hm)
    clear e₀ e' b4 b5 b6 hsupp' hsupp hdet
    obtain rfl : h = h₀ * h' := mt_inj (b1.trans (AdelicLatMove.mt_mul S h₀ h').symm)
    have ih' := ih hΛ' m' h1' h2' ((suppAt_iff _ _ _).2 b3) hy' o6
    have m₀ : IsMov (fmtC S h₀) Λ' Λ₁ := by
      have := (((isMov_laws D _ _ hf').2.2.2 _ _ (hinv h'⁻¹)).2 _ hSv.1 (law _ hf'.1 m').2.1).2.2.2.1 _ _ hm
      rwa [← fmtC_mul, mul_inv_cancel_right] at this
    obtain ⟨b, hb, -⟩ := (hgood _ hΛ').vac C.sympl
    have hc := step C hW hS hT hw hw1 hw2 hB hLT hL hA hΛ' hΛ₁ hsp ((suppAt_iff _ _ _).2 b2) hy₀ m₀ hb
      ((((χT y' : Circle) : ℂ)⁻¹ * (Real.sqrt ((tens (stdL D.host.E S.rank) L).relIndex (tens Λ' L) : ℝ) : ℂ)) *
        SW.ip (κ • v) b)
    rw [mul_smul _ (SW.ip (κ • v) b), ← ((hgood _ hΛ').proj C.idx C.sympl C.even (TensVac.sb_smul κ hv.1) hb).2, ← ih',
      proj_step C.idx C.sympl C.even (hgood _ hSv) (hgood _ hΛ') (hgood _ hΛ₁) hle hv] at hc
    rw [show ((h₀ * h', 1) : GA D S × GA D T) = (h₀, 1) * (h', 1) from Prod.ext rfl (mul_one _).symm, map_mul,
      map_mul, Circle.coe_mul, mul_inv]
    exact hc

theorem zak_om_split : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → GlobalTheory.Ker.IdemTwo w → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ (LT : Lt D.host.E T.rank) (L : Lt D.host.E r), IsSelfDualC T LT → SelfD X L → GlobalTheory.Ker.IsAA (latW hr L) LT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ h ∈ GfC S, SuppAt e S h → ∀ x : (AE D)ˣ, IsDetAt e S h x → ∀ Λ ∈ Vset D.host.E S.rank 1, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC S h) (stdL D.host.E S.rank) Λ → ∀ v : TF S.rank g, IsVac X bas w (tens (stdL D.host.E S.rank) L) v → ∀ (t : ℂ) (f : WO S T → ℂ), Zak ψ θ hr eT bas idx (frOf hr eT Z) (t • v) f → Zak ψ θ hr eT bas idx (frOf hr eT Z) ((t * (((χT x)⁻¹ : Circle) : ℂ) * ((Real.sqrt (((((Λ ⊓ stdL D.host.E S.rank).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ r : ℕ) : ℝ)) : ℝ) : ℂ)) • projA X bas w (tens Λ L) v) (om (h, 1) f) := by
  intro D S T r g hr ψ θ X eT bas idx hS kS kT χS χT om hW w hw hw1 hw2 Z hZ LT L hLT hL hA e P he h _ hsupp x hdet
    Λ hΛ hm v hv t f hf
  subst hr
  obtain ⟨X', m, hq', bas', idx', hs', π, -, hEF, hh, hfr⟩ :=
    GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T _ g rfl ψ θ X eT bas idx hS _ (Nat.add_sub_cancel' X.p0_le)
  obtain ⟨hB, hz⟩ := hfr Z
  obtain ⟨-, hz, -⟩ := hz hZ
  replace hB := hB.1 hZ
  replace hEF : ∀ u v, EF X' u v = EF X u v := hEF
  replace hh : ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (φ : TF S.rank g),
    heisG X' bas' y φ = heisG X bas y φ := hh
  have hE : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, SW.epsW X' w y = SW.epsW X w y := fun y => by
    simp only [SW.epsW, hEF]
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs' with hC
  have hL' : SelfD C.X L := by
    refine ⟨hL.1, fun u => (hL.2 u).trans ?_⟩
    change _ ↔ ∀ y ∈ L, ∃ k : ℤ, EF X' u y = k
    simp only [hEF]
  have hv' : IsVac C.X C.bas w (tens (stdL D.host.E S.rank) L) v := by
    refine ⟨hv.1, hv.2.1, fun y hy => ?_⟩
    change SW.epsW X' _ y • heisG X' bas' y v = v
    rw [hE, hh]
    exact hv.2.2 y hy
  have hp : projA C.X C.bas w (tens Λ L) v = projA X bas w (tens Λ L) v := by
    change projA X' bas' w (tens Λ L) v = _
    simp only [projA, hE, hh]
  have hx := ((onBasis_frame_period D S T C).2 _ hB).2.1
  have g1 := good C hw hw1 hL' hΛ
  obtain ⟨b, hb, -⟩ := g1.vac C.sympl
  have key := om_th C hW kS kT hw hw1 hw2 hB hLT hL' hA he hsupp hdet hΛ hm hv' t
  obtain ⟨-, -, -, -, -, a4⟩ := TensLat.tens_selfDual_semichar_index _ _ C.X C.g C.bas C.idx _ C.sympl C.even _
    hw hw1 L hL' 1 _ hΛ
  have hi : ((Λ ⊓ stdL D.host.E S.rank).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ T.rank =
      (tens (stdL D.host.E S.rank) L).relIndex (tens Λ L) := by
    rw [a4 _ (Base.stdL_mem_Vset S.rank 1), ← AddSubgroup.inf_relIndex_left]
    rfl
  rw [← (ZakEx.isZak_Th D S T C _ hx _ (TensVac.sb_smul t hv.1)).2 f ((hz _ _).2 hf),
    projA_smul C.idx C.sympl C.even g1 _ hv.1, smul_smul] at key
  rw [← hz, key, hi, ← hp, Circle.coe_inv, mul_assoc, mul_comm t]
  exact (ZakEx.isZak_Th D S T C _ hx _ (TensVac.sb_smul _ (g1.proj C.idx C.sympl C.even hv.1 hb).1)).1

end GlobalTheory.OneMapRef.SplitProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFinitePointMovesVacuumToProjectionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFinitePoint_moves_vacuum_to_projection : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → GlobalTheory.Ker.IdemTwo w → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ (LT : Lt D.host.E T.rank) (L : Lt D.host.E r), IsSelfDualC T LT → SelfD X L → GlobalTheory.Ker.IsAA (latW hr L) LT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ h ∈ GfC S, SuppAt e S h → ∀ x : (AE D)ˣ, IsDetAt e S h x → ∀ Λ ∈ Vset D.host.E S.rank 1, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC S h) (stdL D.host.E S.rank) Λ → ∀ v : TF S.rank g, IsVac X bas w (tens (stdL D.host.E S.rank) L) v → ∀ (t : ℂ) (f : WO S T → ℂ), Zak ψ θ hr eT bas idx (frOf hr eT Z) (t • v) f → Zak ψ θ hr eT bas idx (frOf hr eT Z) ((t * (((χT x)⁻¹ : Circle) : ℂ) * ((Real.sqrt (((((Λ ⊓ stdL D.host.E S.rank).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ r : ℕ) : ℝ)) : ℝ) : ℂ)) • projA X bas w (tens Λ L) v) (om (h, 1) f) := by
  first | exact @GlobalTheory.OneMapRef.SplitProj.zak_om_split | exact GlobalTheory.OneMapRef.SplitProj.zak_om_split | (intros; apply GlobalTheory.OneMapRef.SplitProj.zak_om_split <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Term

open GlobalTheory.Ker GlobalTheory.TensLatMove

variable {D : D7} {S T : HSp D}

theorem exists_half {R W A : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup A] (B : W →+ W →+ A)
    (c : R → R) (hc : ∀ a p q, B (a • p) q = B p (c a • q)) (K : AddSubgroup A) {H : AddSubgroup W}
    (hH : ∀ u ∈ H, ∀ u' ∈ H, B u u' ∈ K) {σ τ : R} {k M : ℕ} (h1 : σ + (2 * k * k : ℕ) * τ = 1)
    (hτ : ∀ u ∈ H, τ • u ∈ H) {x y : W}
    (hk : k • (x - y) ∈ H) (hM : k • M • y ∈ H) (hx : ∃ u ∈ H, σ • x = 2 • u) (hy : ∃ u ∈ H, σ • y = 2 • u)
    (hx' : ∃ u ∈ H, c τ • x = (2 * M) • u) (hy' : ∃ u ∈ H, k • c τ • y = (2 * M) • u) :
    ∃ u ∈ H, x = y + 2 • u ∧ B y u ∈ K := by
  obtain ⟨a, ha, ea⟩ := hx
  obtain ⟨b, hb, eb⟩ := hy
  obtain ⟨a', ha', ec⟩ := hx'
  obtain ⟨d, hd, ed⟩ := hy'
  have dec (z : W) : z = σ • z + (2 * k * k) • τ • z := by
    rw [← Nat.cast_smul_eq_nsmul R, smul_smul, ← add_smul, h1, one_smul]
  have hu : a - b + k • τ • k • (x - y) ∈ H := add_mem (sub_mem ha hb) (nsmul_mem (hτ _ hk) _)
  have e : x - y = 2 • (a - b + k • τ • k • (x - y)) := by
    conv_lhs => rw [dec (x - y), smul_sub, ea, eb]
    rw [smul_comm τ k, smul_add, smul_sub 2, smul_smul 2, smul_smul (2 * k)]
  generalize a - b + k • τ • k • (x - y) = u at hu e
  refine ⟨u, hu, by rw [← e, add_sub_cancel], ?_⟩
  have nl (n : ℕ) (p q : W) : B (n • p) q = B p (n • q) := by
    rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]
  have e2 : B ((2 * k * k) • τ • y) u = B (k • M • y) (2 • (k • a' - d)) := by
    have e3 : k • c τ • (2 • u) = M • 2 • (k • a' - d) := by
      rw [← e, smul_sub, smul_sub, ec, ed, smul_comm k, ← smul_sub, smul_smul M, mul_comm M]
    rw [nl k, nl M, smul_comm M k, ← e3, nl, hc, smul_comm (c τ), smul_comm (c τ), smul_smul k, smul_smul]
    congr 2
    ring
  rw [dec y, map_add (f := _), AddMonoidHom.add_apply, eb, e2]
  exact add_mem (hH _ (nsmul_mem hb 2) _ hu) (hH _ hM _ (nsmul_mem (sub_mem (nsmul_mem ha' k) hd) 2))

theorem heis_congr {ψ : AddChar (AF D.host.F) ℂ} {H : AddSubgroup (WO S T)}
    (hH : ∀ u ∈ H, ∀ u' ∈ H, ψ (symplO S T u u') = 1) {f : WO S T → ℂ} (hf : ∀ u ∈ H, heisO ψ S T (2 • u) f = f)
    {σ τ : Formalism.L2.Theta.AE D} {k M : ℕ} (h1 : σ + (2 * k * k : ℕ) * τ = 1) (hτ : ∀ u ∈ H, τ • u ∈ H) {x y : WO S T}
    (hk : k • (x - y) ∈ H) (hM : k • M • y ∈ H) (hx : ∃ u ∈ H, σ • x = 2 • u) (hy : ∃ u ∈ H, σ • y = 2 • u)
    (hx' : ∃ u ∈ H, cA D τ • x = (2 * M) • u) (hy' : ∃ u ∈ H, k • cA D τ • y = (2 * M) • u) :
    heisO ψ S T x f = heisO ψ S T y f := by
  obtain ⟨u, hu, rfl, hp⟩ := exists_half (LatVac.symplHom S T) (cA D) (SplitScalar.symplO_smul S T)
    (LatVac.kerChar ψ) hH h1 hτ hk hM hx hy hx' hy'
  have hp' : ψ (symplOH S T y (2 • u)) = 1 := by
    rw [two_nsmul, SplitScalar.symplOH_add_right, SplitScalar.symplOH_add_self]
    exact hp
  have := SplitScalar.heisO_heisO ψ S T y (2 • u) f
  rw [hf u hu, hp', one_smul] at this
  exact this.symm

theorem exists_split {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) {k : ℕ} (hk : Nat.Coprime k l.M) (j : ℕ) :
    ∃ s ∈ l.Mb ^ j, ∃ t : 𝓞 D.host.E, H.bar t ∈ l.Mb ^ j ∧ s + (2 * k * k : ℕ) * t = 1 := by
  have hM : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have hMM : (l.M : 𝓞 D.host.E) ∈ l.Mb * Mfr l := l.prod.ge (Ideal.subset_span rfl)
    exact Ideal.mul_le_left hMM
  have c1 : IsCoprime l.Mb (Mfr l) := Ideal.isCoprime_iff_sup_eq.2 l.coprime
  have c2 : IsCoprime l.Mb (Ideal.span {((2 * k * k : ℕ) : 𝓞 D.host.E)}) := by
    have h2 : Nat.Coprime (2 * k * k) l.M :=
      Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.coprime_two_left.2 l.odd) hk) hk
    obtain ⟨a, b, e⟩ : IsCoprime ((2 * k * k : ℕ) : 𝓞 D.host.E) (l.M : 𝓞 D.host.E) := h2.cast
    exact Ideal.isCoprime_iff_exists.2 ⟨_, l.Mb.mul_mem_left b hM, _, Ideal.mem_span_singleton'.2 ⟨a, rfl⟩,
      (add_comm _ _).trans e⟩
  obtain ⟨s, hs, t, ht, e⟩ := Ideal.isCoprime_iff_exists.1 ((c2.mul_right (c1.pow_right (n := j))).pow_left (m := j))
  obtain ⟨t', ht', rfl⟩ := Ideal.mem_span_singleton_mul.1 ht
  refine ⟨s, hs, t', ?_, e⟩
  have h1 : (Mfr l ^ j).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ l.Mb ^ j := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun a ha => LevelPairing.bar_mem_Mb ha) j
  exact h1 (Ideal.mem_map_of_mem _ ht')

theorem smul_mem_of_int {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1) {L : Lt D.host.E T.rank}
    {a : Formalism.L2.Theta.AE D} (ha : finPart D a ∈ Formalism.L2.Theta.intAE D) {u : WO S T} (hu : u ∈ hatA S T (tens Λ L)) :
    a • u ∈ hatA S T (tens Λ L) ∧ cA D a • u ∈ hatA S T (tens Λ L) := by
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens Λ L, (o : D.host.E) • y ∈ tens Λ L := fun o y hy =>
    TensLat.smul_mem_tens hΛ o.isIntegral_coe hy
  have h1 : ∀ z ∈ Formalism.L2.Theta.intAE D, emb D z ∈ SignVac.intAE D ∧ cA D (emb D z) ∈ SignVac.intAE D := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, o, rfl⟩ := hz
      exact ⟨AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩, AddSubgroup.subset_closure
        ⟨α, hα, ⟨cc (o : D.host.E), Base.isIntegral_cc o.isIntegral_coe⟩, rfl⟩⟩
    | zero => rw [map_zero, map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy => rw [map_add (f := _), RingHom.map_add (f := _)]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg, RingHom.map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
  have h2 := emb_mul a 1
  rw [mul_one] at h2
  have h3 : emb D 1 = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have h4 : cA D (emb D 1) = emb D 1 := by
    rw [h3]
    exact congrArg (fun t => pairA D.host.F 0 1 ⊗ₜ[D.host.F] t) (star_one D.host.E)
  have h5 := h1 _ ha
  rw [h2, RingHom.map_mul, h4, h3] at h5
  rw [← SignVac.one_smul_hatA hu, smul_smul, smul_smul]
  exact ⟨SignVac.smul_mem_hatA hA h5.1 hu, SignVac.smul_mem_hatA hA h5.2 hu⟩

noncomputable def colM (S T : HSp D) : (Fin S.rank → Fin T.rank → AfE D) →+ WO S T :=
  AddMonoidHom.mk' (fun u => Matrix.of fun a k => emb D (u k a)) fun _ _ => by
    ext a k
    exact map_add (emb D) _ _

theorem finW_eq_colM (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : finW S T y = colM S T fun b => toAf (y b) := rfl

theorem colM_mem {L : Lt D.host.E T.rank} {u : Fin S.rank → Fin T.rank → AfE D} (hu : ∀ b, u b ∈ hatV L) :
    colM S T u ∈ hatA S T (tens (stdL D.host.E S.rank) L) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single u, map_sum]
  refine sum_mem fun b _ => ?_
  have h1 : (Pi.single b 1 : Fin S.rank → D.host.E) ∈ stdL D.host.E S.rank := Submodule.subset_span ⟨b, rfl⟩
  refine (congrArg (· ∈ hatA S T (tens (stdL D.host.E S.rank) L)) ?_).mpr
    (outer_mem S T _ L _ (LevEig.toAf_mem h1) _ (hu b))
  ext a k
  change emb D ((Pi.single b (u b) : Fin S.rank → Fin T.rank → AfE D) k a) = emb D (u b a * toAf (Pi.single b 1) k)
  by_cases e : k = b
  · subst e
    simp only [toAf, Pi.single_eq_same]
    exact congrArg (emb D) (mul_one _).symm
  · simp only [toAf, Pi.single_eq_of_ne e, TensorProduct.tmul_zero, mul_zero, Pi.zero_apply]

theorem actO_colM (g : GA D T) (u : Fin S.rank → Fin T.rank → AfE D) :
    actO S T 1 g (colM S T u) = colM S T fun b => fmt T g *ᵥ u b := by
  have e : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by rw [inv_one, Formalism.L2.Theta.mt, map_one, Units.val_one]
  rw [actO, e, Matrix.mul_one]
  ext a k
  change ∑ c, Formalism.L2.Theta.mt T g a c * emb D (u k c) = emb D (∑ c, finPart D (Formalism.L2.Theta.mt T g a c) * u k c)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun c _ => (emb_mul _ _).symm

theorem inc_smul_finW (s : D.host.E) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    incA D s • finW S T y = finW S T (s • y) := by
  ext a k
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] s) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem finW_nsmul (n : ℕ) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : finW S T (n • y) = n • finW S T y := by
  rw [← Nat.cast_smul_eq_nsmul D.host.E, ← inc_smul_finW, map_natCast, Nat.cast_smul_eq_nsmul]

theorem finW_mem {L : Lt D.host.E T.rank} {y : Matrix (Fin S.rank) (Fin T.rank) D.host.E} (hy : ∀ b, y b ∈ L) :
    finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) L) := colM_mem fun b => LevEig.toAf_mem (hy b)

theorem nsmul_mem_of_le {Λ Λ' : Lt D.host.E S.rank} {L : Lt D.host.E T.rank} {n : ℕ}
    (h : Ideal.span {(n : 𝓞 D.host.E)} • Λ ≤ Λ') {u : WO S T} (hu : u ∈ hatA S T (tens Λ L)) :
    n • u ∈ hatA S T (tens Λ' L) := by
  refine hatA_le S T Λ L ((hatA S T (tens Λ' L)).comap (nsmulAddMonoidHom n)) (fun v hv w hw => ?_) hu
  change n • outerHom S T v w ∈ hatA S T (tens Λ' L)
  rw [← AddMonoidHom.nsmul_apply, ← map_nsmul]
  refine outer_mem S T Λ' L _ (AddSubgroup.closure_mono ?_
    (LevEig.nsmul_mem_hatV (Ideal.mem_span_singleton_self _) hv)) _ hw
  rintro z ⟨a, ha, x, hx, e⟩
  exact ⟨a, ha, x, h hx, e⟩

theorem isMov_latG (g : GA D T) : IsMov (fmt T g) (latG T 1) (latG T g) := by
  obtain ⟨-, -, -, h4, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D T g
  rw [h5] at h4
  intro u
  exact Iff.trans (Set.ext_iff.1 h4 u) ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩⟩

theorem actO_split (h : GA D S) (g : GA D T) (x : WO S T) : actO S T h g x = actO S T h 1 (actO S T 1 g x) := by
  simp only [actO, Formalism.L2.Theta.mt, inv_one, map_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

theorem actO_smul (h : GA D S) (g : GA D T) (a : Formalism.L2.Theta.AE D) (x : WO S T) :
    actO S T h g (a • x) = a • actO S T h g x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_sub_self {e : Formalism.L2.Theta.AE D} {h : GA D S} (hs : SuppAt e S h) (x : WO S T) :
    actO S T h 1 x - x = actO S T h 1 ((e + cA D e) • x) - (e + cA D e) • x := by
  have h1 : (e + cA D e) • (Formalism.L2.Theta.mt S h - 1) = Formalism.L2.Theta.mt S h - 1 := Matrix.ext hs
  have h2 : Formalism.L2.Theta.mt S h⁻¹ * Formalism.L2.Theta.mt S h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]
  have gen : ∀ {R : Type} [CommRing R] (ε : R) (A B : Matrix (Fin S.rank) (Fin S.rank) R)
      (z : Matrix (Fin T.rank) (Fin S.rank) R), ε • (A - 1) = A - 1 → B * A = 1 →
      z * B - z = (ε • z) * B - ε • z := by
    intro R _ ε A B z h1 h2
    have h3 (w : Matrix (Fin T.rank) (Fin S.rank) R) : w * B - w = -(w * B * (A - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_assoc w B A, h2, Matrix.mul_one, Matrix.mul_one, neg_sub]
    rw [h3, h3, Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_smul, h1]
  have h0 : Formalism.L2.Theta.mt T 1 = 1 := by rw [Formalism.L2.Theta.mt, map_one, Units.val_one]
  rw [actO, actO, h0, Matrix.one_mul, Matrix.one_mul]
  exact gen _ _ _ _ h1 h2

section Rows

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem modN_of_both {a : Dw.La} (h1 : a ∈ (Mfr l • ⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (h2 : a ∈ (l.Mb • ⊤ : Submodule (𝓞 D.host.E) Dw.La)) : ∃ b, a = l.M • b := by
  obtain ⟨b, hb⟩ := DualMark.smul_eq_nsmul (DualMark.prod_le l) (LevelPairing.cSep_spec l).2 h1
  obtain ⟨b', hb'⟩ := DualMark.smul_eq_nsmul ((mul_comm _ _).le.trans (DualMark.prod_le l))
    (LevelPairing.cSep_spec l).1 h2
  exact ⟨b' - b, by rw [smul_sub, ← hb, ← hb', sub_smul, one_smul, sub_sub_cancel]⟩

theorem inv_smul_nsmul {r : ℕ} (v : Fin r → D.host.E) : (l.M : D.host.E)⁻¹ • l.M • v = v := by
  rw [← Nat.cast_smul_eq_nsmul D.host.E, inv_smul_smul₀ (Nat.cast_ne_zero.2 (DualMark.level_ne l))]

theorem nsmul_root_mem {r : ℕ} {L : Lt D.host.E r} {mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)} (hmk : ∀ a, mk a ∈ L)
    {a : Dw.La} (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) {y : Fin r → D.host.E}
    (hy : y - (l.M : D.host.E)⁻¹ • mk a ∈ L) {B : ℕ}
    (hB : (B : 𝓞 D.host.E) • (Submodule.Quotient.mk a : LevQ Dw l) = 0) : B • y ∈ L := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hB
  obtain ⟨c, hc⟩ := modN_of_both (Submodule.smul_mem _ _ ha) hB
  rw [Nat.cast_smul_eq_nsmul] at hc
  have := add_mem (nsmul_mem hy B) (hmk c)
  rwa [smul_sub, smul_comm B, ← map_nsmul, hc, map_nsmul, inv_smul_nsmul, sub_add_cancel] at this

theorem root_cong {g : GA D T} {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : ∀ a, ι a ∈ latG T 1)
    (hm : MarkAd (T := T) rfl l ι g mk) {a a₀ : Dw.La} (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (ha₀ : a₀ ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (e : (Submodule.Quotient.mk a₀ : LevQ Dw l) = Submodule.Quotient.mk a) {y y₀ : Fin T.rank → D.host.E}
    (hy : y - (l.M : D.host.E)⁻¹ • mk a ∈ latG T g) (hy₀ : y₀ - (l.M : D.host.E)⁻¹ • ι a₀ ∈ latG T 1) :
    fmt T g *ᵥ toAf y₀ - toAf y ∈ hatV (latG T g) := by
  obtain ⟨c, hc⟩ := modN_of_both (sub_mem ha₀ ha) ((Submodule.Quotient.eq _).1 e)
  have h0 : y₀ - (l.M : D.host.E)⁻¹ • ι a ∈ latG T 1 := by
    have := add_mem hy₀ (hι c)
    rwa [eq_add_of_sub_eq hc, map_add, map_nsmul, smul_add, inv_smul_nsmul, ← sub_sub, sub_add_eq_add_sub,
      sub_add_cancel] at this
  obtain ⟨w, hw, ew⟩ := hm a ha
  rw [(GlobalTheory.Member.latG_lattice_and_completion D T g).2.2.2.2.1] at hw
  replace ew : toAf (mk a) - fmt T g *ᵥ toAf (ι a) = l.M • w := ew
  set μ : AfE D := (1 : Af D.host.F) ⊗ₜ[D.host.F] (l.M : D.host.E)⁻¹ with hμ
  have t1 (v : Fin T.rank → D.host.E) : toAf ((l.M : D.host.E)⁻¹ • v) = μ • toAf v := by
    funext i
    simp only [toAf, hμ, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have t2 : μ * (l.M : AfE D) = 1 := by
    rw [hμ, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)),
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (DualMark.level_ne l))]
    rfl
  have h1 := (isMov_latG g _).2 ⟨_, LevEig.toAf_mem h0, rfl⟩
  have h2 := LevEig.toAf_mem hy
  rw [LevEig.toAf_sub, t1] at h1 h2
  have gen : ∀ {R : Type} [CommRing R] (A : Matrix (Fin T.rank) (Fin T.rank) R) (μ : R) (M : ℕ)
      (p q s t w : Fin T.rank → R), μ * M = 1 → t - A *ᵥ s = M • w →
      A *ᵥ p - q = A *ᵥ (p - μ • s) - (q - μ • t) - w := by
    intro R _ A μ M p q s t w h1 h2
    have : w = μ • (t - A *ᵥ s) := by rw [h2, ← Nat.cast_smul_eq_nsmul R, smul_smul, h1, one_smul]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    abel
  rw [gen _ μ l.M _ _ _ _ w t2 ew]
  exact sub_mem (sub_mem h1 h2) hw

theorem exists_pow {n r N : ℕ} {L : Lt D.host.E r} {y : Matrix (Fin n) (Fin r) D.host.E}
    (h : ∀ b, ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • y b = (2 * N) • u) :
    ∃ j : ℕ, ∀ j' ≥ j, ∀ s ∈ l.Mb ^ j', ∃ u : Matrix (Fin n) (Fin r) D.host.E, (∀ b, u b ∈ L) ∧
      (s : D.host.E) • y = (2 * N) • u := by
  choose j hj using h
  refine ⟨Finset.univ.sup j, fun j' hj' s hs => ?_⟩
  choose u hu e using fun b => hj b s
    (Ideal.pow_le_pow_right ((Finset.le_sup (Finset.mem_univ b)).trans hj') hs)
  exact ⟨Matrix.of u, hu, funext e⟩

end Rows

theorem isMov_fmt_one (L : Lt D.host.E T.rank) : IsMov (fmt T 1) L L := fun v => by
  simp only [LevEig.fmt_one, Matrix.one_mulVec, exists_eq_right']

theorem heisG_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (y : Matrix (Fin n) (Fin r) E) (a : ℂ) (φ : TF n g) :
    heisG X bas y (a • φ) = a • heisG X bas y φ := by
  funext z
  simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem char_hatA (C : Ctx S T) {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1) {L : Lt D.host.E T.rank}
    (hL : SelfD C.X L) : ∀ u ∈ hatA S T (tens Λ L), ∀ u' ∈ hatA S T (tens Λ L), C.ψ (symplO S T u u') = 1 := by
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens Λ L, (o : D.host.E) • y ∈ tens Λ L := fun o y hy =>
    TensLat.smul_mem_tens hΛ o.isIntegral_coe hy
  refine fun u hu u' hu' => SignVac.char_sympl_hatA C.std.1.1 hA (fun y hy y' hy' => ?_) hu hu'
  obtain ⟨k, hk⟩ := (TensLat.tens_selfDual hΛ hL y).1 hy y' hy'
  rw [← SplitScalar.symplOH_add_self, AddChar.map_add_eq_mul, (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.1, hk, ← Complex.exp_add,
    ← Complex.exp_int_mul_two_pi_mul_I (-k)]
  congr 1
  push_cast
  ring


set_option maxHeartbeats 1600000 in
theorem heis_root (C : Ctx S T) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {h : GA D S} {g : GA D T} {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1)
    (hmv : IsMov (fmtC S h) (stdL D.host.E S.rank) Λ) (hL : SelfD C.X (latG T g)) {f : WO S T → ℂ}
    (hf : ∀ u ∈ hatA S T (tens Λ (latG T g)), heisO C.ψ S T (2 • u) f = f)
    {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : ∀ a, ι a ∈ latG T 1) (hmk : ∀ a, mk a ∈ latG T g)
    (hm : MarkAd (T := T) rfl l ι g mk) {N k B : ℕ} (hN : l.M ∣ N)
    (hN' : Ideal.span {(N : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hk : Nat.Coprime k l.M)
    (hk' : Ideal.span {(k : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hB : B ≠ 0) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hP : ∀ PP ∈ P, (B : 𝓞 D.host.E) ∉ PP.asIdeal) (hs : SuppAt e S h)
    {Y₀ Y : (Fin S.rank → LevQ Dw l) → Matrix (Fin S.rank) (Fin T.rank) D.host.E}
    (hY₀ : IsRoots l (latG T 1) ι l.M Y₀) (hY : IsRoots l (latG T g) mk N Y) {q : Fin S.rank → LevQ Dw l}
    (hq : ∀ b, (B : 𝓞 D.host.E) • q b = 0) :
    heisO C.ψ S T (actO S T h g (finW S T (Y₀ q))) f = heisO C.ψ S T (finW S T (Y q)) f := by
  have hV := Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  have m1 : ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)), actO S T h 1 u ∈ hatA S T (tens Λ (latG T g)) :=
    fun u hu => (mem_hatA_iff S T C.m.gS h 1 _ _ _ _ hmv (isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩
  have m2 : ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T 1)), actO S T h g u ∈ hatA S T (tens Λ (latG T g)) :=
    fun u hu => (mem_hatA_iff S T C.m.gS h g _ _ _ _ hmv (isMov_latG g) _).2 ⟨u, hu, rfl⟩
  choose a ha ea ya using fun b => (hY q b).1
  choose a₀ ha₀ ea₀ ya₀ using fun b => (hY₀ q b).1
  have f1 : actO S T 1 g (finW S T (Y₀ q)) - finW S T (Y q) ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)) := by
    rw [finW_eq_colM, finW_eq_colM, actO_colM, ← map_sub]
    exact colM_mem fun b => root_cong hι hm (ha b) (ha₀ b) ((ea₀ b).trans (ea b).symm) (ya b) (ya₀ b)
  have f2 : ∀ n : ℕ, (∀ b, (n : 𝓞 D.host.E) • q b = 0) →
      n • finW S T (Y q) ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)) := fun n hn => by
    rw [← finW_nsmul]
    exact finW_mem fun b => nsmul_root_mem hmk (ha b) (ya b) (by rw [ea b]; exact hn b)
  have hMb : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have hMM : (l.M : 𝓞 D.host.E) ∈ l.Mb * Mfr l := l.prod.ge (Ideal.subset_span rfl)
    exact Ideal.mul_le_left hMM
  have f3 := f2 l.M fun b => by
    rw [← ea b, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hMb trivial
  have f4 : (e + cA D e) • finW S T (Y q) ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)) := by
    have hB0 : (B : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hB
    have hB1 : (B : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hB
    have i1 : finPart D (e * incA D (B : D.host.E)⁻¹) ∈ Formalism.L2.Theta.intAE D := by
      obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_mul, map_sum]
      refine sum_mem fun PP hPP => ?_
      by_contra hn
      exact hP PP hPP (((hes PP hPP).2 _ hB0).2 hn)
    have i2 : incA D (B : D.host.E)⁻¹ * (B : Formalism.L2.Theta.AE D) = 1 := by
      rw [← map_natCast (incA D), ← RingHom.map_mul, inv_mul_cancel₀ hB1, RingHom.map_one]
    have i3 : cA D (incA D (B : D.host.E)⁻¹) * (B : Formalism.L2.Theta.AE D) = 1 := by
      rw [← map_natCast (cA D), ← RingHom.map_mul, i2, RingHom.map_one]
    obtain ⟨j1, j2⟩ := smul_mem_of_int hV i1 (f2 B hq)
    rw [← Nat.cast_smul_eq_nsmul (Formalism.L2.Theta.AE D), smul_smul] at j1 j2
    rw [mul_assoc, i2, mul_one] at j1
    rw [RingHom.map_mul, mul_assoc, i3, mul_one] at j2
    rw [add_smul]
    exact add_mem j1 j2
  have f5 : k • (actO S T h g (finW S T (Y₀ q)) - finW S T (Y q)) ∈ hatA S T (tens Λ (latG T g)) := by
    have := add_mem (nsmul_mem (m1 _ f1) k) (sub_mem (nsmul_mem (m1 _ f4) k) (nsmul_mem_of_le hk' f4))
    rwa [← nsmul_sub, ← actO_sub_self hs, LevEig.actO_sub, ← actO_split, ← nsmul_add, sub_add_sub_cancel] at this
  obtain ⟨j, hj⟩ := exists_pow fun b => (hY q b).2
  obtain ⟨j₀, hj₀⟩ := exists_pow fun b => (hY₀ q b).2
  obtain ⟨s, hs, t, ht, est⟩ := exists_split l hk (max j j₀)
  have g1 : ∀ s ∈ l.Mb ^ max j j₀, ∃ u ∈ hatA S T (tens Λ (latG T g)),
      incA D (s : D.host.E) • actO S T h g (finW S T (Y₀ q)) = (2 * l.M) • u := fun s hs => by
    obtain ⟨u, hu, eu⟩ := hj₀ _ (le_max_right _ _) s hs
    refine ⟨_, m2 _ (finW_mem hu), ?_⟩
    rw [← actO_smul, inc_smul_finW, eu, finW_nsmul]
    exact map_nsmul (TensLatMove.actHom S T h g) _ _
  have g2 : ∀ s ∈ l.Mb ^ max j j₀, ∃ u ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)),
      incA D (s : D.host.E) • finW S T (Y q) = (2 * N) • u := fun s hs => by
    obtain ⟨u, hu, eu⟩ := hj _ (le_max_left _ _) s hs
    exact ⟨_, finW_mem hu, by rw [inc_smul_finW, eu, finW_nsmul]⟩
  have hbar : cA D (incA D (t : D.host.E)) = incA D (H.bar t : D.host.E) := by rw [H.bar_eq]; rfl
  refine heis_congr (σ := incA D (s : D.host.E)) (τ := incA D (t : D.host.E)) (k := k) (M := l.M)
    (char_hatA C hΛ hL) hf ?_ (fun u hu => (smul_mem_of_int hΛ ?_ hu).1) f5 (nsmul_mem_of_le hk' f3) ?_ ?_ ?_ ?_
  · have := congrArg ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) est
    rwa [RingHom.map_add, RingHom.map_mul, map_natCast, RingHom.map_one] at this
  · exact AddSubgroup.subset_closure ⟨1, intAf_one, t, rfl⟩
  · obtain ⟨u, hu, eu⟩ := g1 s hs
    exact ⟨_, nsmul_mem hu l.M, by rw [eu, mul_nsmul']⟩
  · obtain ⟨u, hu, eu⟩ := g2 s hs
    exact ⟨_, nsmul_mem_of_le hN' hu, by rw [eu, mul_nsmul']⟩
  · rw [hbar]
    exact g1 _ ht
  · obtain ⟨u, hu, eu⟩ := g2 _ ht
    obtain ⟨c, rfl⟩ := hN
    refine ⟨_, nsmul_mem (nsmul_mem_of_le hk' hu) c, ?_⟩
    rw [hbar, eu, ← mul_nsmul', ← mul_nsmul', ← mul_nsmul']
    congr 1
    ring

theorem isRoots_neg {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {n r N : ℕ}
    {L : Lt D.host.E r} {mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) D.host.E} (hY : IsRoots l L mk N Y) :
    IsRoots l L (-mk) N fun q => -Y q := by
  intro q b
  obtain ⟨⟨a, ha, ea, ya⟩, j, hj⟩ := hY q b
  refine ⟨⟨a, ha, ea, ?_⟩, j, fun s hs => ?_⟩
  · have := neg_mem ya
    rw [neg_sub'] at this
    rwa [LinearMap.neg_apply, smul_neg]
  · obtain ⟨u, hu, e⟩ := hj s hs
    exact ⟨-u, neg_mem hu, by rw [smul_neg, ← e, ← smul_neg]; rfl⟩

theorem markAd_zsmul {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {g : GA D T}
    {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hm : MarkAd (T := T) rfl l ι g mk) (ε : ℤ) :
    MarkAd (T := T) rfl l (-(ε • ι)) g (-(ε • mk)) := by
  intro a ha
  have e (f : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) : (-(ε • f)) a = f (-(ε • a)) := by simp
  rw [e, e]
  exact hm _ (neg_mem (zsmul_mem ha ε))

theorem heis_root_zak {r g : ℕ} (hr : T.rank = r) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hS : IsSet ψ θ S T hr X eT bas) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeak ψ S T om)
    {w : D.host.E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) (hw2 : IdemTwo w) {Z : Fam T} (hZ : IsONeg T X.p0 Z)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {h : GA D S} {g' : GA D T} {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1)
    (hmv : IsMov (fmtC S h) (stdL D.host.E S.rank) Λ) {L : Lt D.host.E r} (hL : SelfD X L) (hLG : latW hr L = latG T g')
    {v : TF S.rank g} (hv : IsVac X bas w (tens (stdL D.host.E S.rank) L) v) {a : ℂ} {f : WO S T → ℂ}
    (hf : Zak ψ θ hr eT bas idx (frOf hr eT Z) (a • v) f) {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)}
    (hι : LatEmb T (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι)) (hmk : ∀ a, mk a ∈ L)
    (hm : MarkAd hr l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι) g' mk) {N k B : ℕ} (hN : l.M ∣ N)
    (hN' : Ideal.span {(N : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hk : Nat.Coprime k l.M)
    (hk' : Ideal.span {(k : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hB : B ≠ 0) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hP : ∀ PP ∈ P, (B : 𝓞 D.host.E) ∉ PP.asIdeal) (hs : SuppAt e S h)
    {ε : ℤ} {Y₀ Y : (Fin S.rank → LevQ Dw l) → Matrix (Fin S.rank) (Fin r) D.host.E}
    (hY₀ : IsRoots l (LinearMap.range ι) (ε • ι) l.M Y₀) (hY : IsRoots l L (ε • mk) N Y) {q : Fin S.rank → LevQ Dw l}
    (hq : ∀ b, (B : 𝓞 D.host.E) • q b = 0) :
    heisO ψ S T (actO S T h g' (finR S hr (-Y₀ q))) (om (h, 1) f) = heisO ψ S T (finR S hr (-Y q)) (om (h, 1) f) := by
  subst hr
  obtain rfl : L = latG T g' := hLG
  replace hm : MarkAd (T := T) rfl l ι g' mk := hm
  have hι' : LinearMap.range ι = latG T 1 := hι.2
  rw [hι'] at hY₀
  obtain ⟨X', m, hq', bas', idx', hsy, π, -, hEF, -⟩ := Flip.exists_flip_model D S T _ g rfl ψ θ X eT bas idx hS
    (T.rank - X.p0) (Nat.add_sub_cancel' X.p0_le)
  replace hEF : ∀ u v, EF X' u v = EF X u v := hEF
  have hL' : SelfD X' (latG T g') := ⟨hL.1, by simpa only [hEF] using hL.2⟩
  let C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hsy
  have hz := (GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors D S T _ g rfl ψ θ X eT bas idx hS Z hZ).1
  have hsb := Const.isSB_smul_tf a hv.1
  have hlat : IsLatVac (heisO ψ S T) (hatA S T (tens (stdL D.host.E S.rank) (latG T g'))) f := by
    refine (SignVac.isLatVac_iff D S T C w hw hw' hw2 1 _ (Base.stdL_mem_Vset _ 1) _ hL' f hf.1).2 fun y hy => ?_
    obtain ⟨u1, -, -, -, u5, -⟩ := (hz _ hsb).2 f hf
    have hsb' := ((heisG_laws _ _ X g bas idx S.rank hS.2.2.2.2.2.2.2 hS.2.2.2.1).2.2.2 (-y) _ hsb).1
    have h1 := ((hz _ hsb').2 _ (u5 y)).2.2.1 (SW.epsW X w (-y))
    have h2 : SW.epsW X w (-y) • heisG X bas (-y) (a • v) = a • v := by
      rw [heisG_smul, smul_comm, hv.2.2 _ (neg_mem hy)]
    have h3 : SW.epsW C.X w y = SW.epsW X w (-y) := by
      rw [epsW_neg_rows]
      change SW.epsW X' w y = _
      simp only [SW.epsW, hEF]
    rw [h2] at h1
    rw [h3]
    exact u1 _ h1
  have hlat' := (hatA_move D S T C h 1 _ _ _ _ hmv (isMov_fmt_one _)).2 om hom f hf.1 hlat
  exact heis_root C hΛ hmv hL' hlat'.1 (fun a => neg_mem (zsmul_mem (hι' ▸ LinearMap.mem_range_self ι a) ε))
    (fun a => neg_mem (zsmul_mem (hmk a) ε)) (markAd_zsmul hm ε) hN hN' hk hk' hB he hP hs (isRoots_neg hY₀)
    (isRoots_neg hY) hq

theorem zak_sum {r g : ℕ} {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hS : IsSet ψ θ S T hr X eT bas) {Z : Fam T} (hZ : IsONeg T X.p0 Z) {φ : TF S.rank g} (hφ : SW.IsSB φ)
    {f : WO S T → ℂ} (hf : Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) {Q : Type} [Fintype Q] (W : Q → ℂ)
    (Y : Q → Matrix (Fin S.rank) (Fin r) D.host.E) (c : ℂ) :
    Zak ψ θ hr eT bas idx (frOf hr eT Z) (c • ∑ q, W q • heisG X bas (Y q) φ)
      (c • ∑ q, W q • heisO ψ S T (finR S hr (-Y q)) f) := by
  classical
  have hz := (GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors D S T _ g hr ψ θ X eT bas idx hS Z hZ).1
  have key : ∀ s : Finset Q, SW.IsSB (∑ q ∈ s, W q • heisG X bas (Y q) φ) ∧ Zak ψ θ hr eT bas idx (frOf hr eT Z)
      (∑ q ∈ s, W q • heisG X bas (Y q) φ) (∑ q ∈ s, W q • heisO ψ S T (finR S hr (-Y q)) f) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have := ((hz φ hφ).2 f hf).2.2.1 0
      rw [zero_smul, zero_smul] at this
      exact ⟨isSB_zero, this⟩
    | insert q s hq ih =>
      rw [Finset.sum_insert hq, Finset.sum_insert hq]
      have h1 := ((heisG_laws _ _ X g bas idx S.rank hS.2.2.2.2.2.2.2 hS.2.2.2.1).2.2.2 (Y q) _ hφ).1
      have h2 := ((hz φ hφ).2 f hf).2.2.2.2.1 (-Y q)
      rw [neg_neg] at h2
      have h3 := Const.isSB_smul_tf (W q) h1
      exact ⟨(isSB_algebra_haar_linear ℚ _ _ _ _ h3 ih.1).1,
        ((hz _ h3).2 _ (((hz _ h1).2 _ h2).2.2.1 (W q))).2.2.2.1 _ _ ih.1 ih.2⟩
  exact ((hz _ (key _).1).2 _ (key _).2).2.2.1 c

end GlobalTheory.OneMapRef.Term

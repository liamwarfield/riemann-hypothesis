module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabFlag

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActRow
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut Formalism.L2.SG.PackageTie2 Matrix

namespace Formalism.L2.SG.Pf.Act

section Row

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem isoG_one {u : D.what₂.Word} : isoG (1 : Gam X u) = 1 := by
  apply LinearEquiv.ext
  intro y
  apply inclCrd_inj
  rw [isoG_spec]
  show X.B.I.fmat 1 *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y)
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem one_mem_gamL {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)
    (q : {Λ // Λ ∈ what₂}) : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) ∈ X.B.I.Kset := by
  have e : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) =
      (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ * (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)) := by
    unfold colD; simp
  rw [e]
  exact Formalism.L2.SG.Pf.LatDictK.dict_K X _ _ {y | X.B.I.fmat (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ *ᵥ
    incl X.B.I (X.crd y) ∈ X.B.I.Lf} (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem cmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (c : GQ X u u' F0 F0' Λ Λ') :
    SatGramActR.cmap x β hN hx c = c := by
  subst hx1 hβ1
  by_cases hβ : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')
  · induction c using Quot.ind with
    | mk p =>
      rw [SatGramActR.cmap_pos _ _ _ _ hβ]
      congr 1
      apply Subtype.ext
      show (p.1.1 * (1 : X.B.I.GA)⁻¹, p.1.2 * (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)⁻¹) = p.1
      simp
  · exact SatGramActR.cmap_neg _ _ _ _ hβ c

theorem tmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    (t : GTerm X u u' F0 F0' what₂ rows') : SatGramActR.tmap x β hN hx t = t := by
  obtain ⟨Λ, hΛ, Λ', hΛ', c⟩ := t
  show (⟨Λ, hΛ, Λ', hΛ', SatGramActR.cmap x β hN hx c⟩ : GTerm X u u' F0 F0' what₂ rows') = ⟨Λ, hΛ, Λ', hΛ', c⟩
  rw [cmap_id hN hx hx1 hβ1]

variable {Y : Full X} {u u' : D.what₂.Word}

theorem act_one (q : {Λ // Λ ∈ Y.what₂ u'}) (t : Formalism.L2.SG.PackageTie2.TT Y u u') :
    KernelOfEmbedding.act Y q ⟨1, one_mem_gamL (Y.cs u') q⟩ t = t :=
  tmap_id _ _ rfl isoG_one t

theorem rowFree_of (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) : Formalism.L2.SG.Pf.FibreCounting.RowFree Y := by
  intro u u' s s' h hrow
  obtain ⟨γ, rfl⟩ := KernelOfEmbedding.fib_gam (hN u') h
  have hι := KernelOfEmbedding.iota_act hIR ⟨s.lam', s.mem'⟩ γ s rfl
  have hι2 : iotaOf Y.TR (Y.cs u) (Y.cs u') s =
      iotaOf Y.TR (Y.cs u) (Y.cs u') (KernelOfEmbedding.act Y ⟨s.lam', s.mem'⟩ γ s) := congrArg (fun r => r.2.2) hrow
  rw [hι] at hι2
  have hl : levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1) = 1 := by
    have h3 : iotaOf Y.TR (Y.cs u) (Y.cs u') s * (levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1))⁻¹ =
        iotaOf Y.TR (Y.cs u) (Y.cs u') s * 1 := by rw [mul_one]; exact hι2.symm
    exact inv_eq_one.1 (mul_left_cancel h3)
  have hg : gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ γ =
      gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ ⟨1, one_mem_gamL (Y.cs u') ⟨s.lam', s.mem'⟩⟩ := by
    apply Subtype.ext
    show levi Y.TR (colD _ _) = levi Y.TR (colD _ _)
    have e1 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' γ.1 * (Y.cs u').h ((Y.cs u').base s.lam')) =
        SatGramActL.kB (Y.cs u') s.lam' γ.1 := (aK_eq _ _).symm
    have e2 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' 1 * (Y.cs u').h ((Y.cs u').base s.lam')) = 1 := by
      unfold colD; simp
    rw [e1, e2, hl, levi_one]
  have h1 := (gamL_levi_bij (Y.cs u') Y.TR Y.hK (hN u') ⟨s.lam', s.mem'⟩).1 hg
  rw [h1, act_one]

theorem liftIotaFree (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) (u u' : D.what₂.Word) (s₁ s₂ : Formalism.L2.SG.PackageTie2.TT Y u u') (h : s₁.toTerm = s₂.toTerm)
    (hr : rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂) : s₁ = s₂ :=
  rowFree_of hN hIR u u' s₁ s₂ h hr

end Row

end Formalism.L2.SG.Pf.Act
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolEqPf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem mem_gcS {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) (s : X.B.I.Ginf) :
    s ∈ GcS X u hK c ↔ ∃ γ : X.B.I.GA, γ ∈ X.B.I.GFset ∧ γ.1 = s ∧ γ.1 ∈ X.NinfU u ∧ γ.2 ∈ X.NfinU u ∧
      c⁻¹ * γ.2 * c ∈ X.K2 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨hG, hP⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hP
    obtain ⟨hN, hk⟩ := Subgroup.mem_inf.1 h2
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hk
    refine ⟨γ, hG, rfl, h1, hN, ?_⟩
    have : γ.2 = c * k * c⁻¹ := by rw [← hke]; rfl
    rw [this]
    have : c⁻¹ * (c * k * c⁻¹) * c = k := by group
    rw [this]; exact hk
  · rintro ⟨γ, hG, rfl, h1, hN, hk⟩
    refine ⟨γ, Subgroup.mem_inf.2 ⟨hG, Subgroup.mem_prod.2 ⟨h1, Subgroup.mem_inf.2 ⟨hN, ?_⟩⟩⟩, rfl⟩
    refine Subgroup.mem_map.2 ⟨c⁻¹ * γ.2 * c, hk, ?_⟩
    show c * (c⁻¹ * γ.2 * c) * c⁻¹ = γ.2
    group

theorem noinfEqC_holds : NOinfEqC := by
  intro D X u hK
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩

theorem nocolEqC_holds : NOcolEqC := by
  intro D X Y u ρ
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨x, ratLink_mem X hx, rfl, nLamNinf_holds D X u _ x n hx hn, nLamNfin_holds D X u _ x n hx hn,
      (nilradical_conj_level' D X Y u ρ x n hn hx).1⟩
  · rintro ⟨γ, hG, rfl, hN, hF, hk⟩
    exact Formalism.L2.SG.Pf.SlabCoverPf.nilradical_rational_lattice D X Y u ρ γ (Formalism.L2.SG.Closed.level_subgroup_properties X) hG hN hF hk

theorem gcCountC_holds : GcCountC := by
  intro D X u hK c
  have hR : (RcS X u hK c : Set X.B.I.GA).Countable :=
    (Set.countable_coe_iff.1 (Formalism.MainNotions.LeviCoordinates.rr_GF_countable X.B.I)).mono (fun _ h => (Subgroup.mem_inf.1 h).1)
  have : (GcS X u hK c : Set X.B.I.Ginf).Countable := by
    unfold GcS
    rw [Subgroup.coe_map]
    exact hR.image _
  exact this.to_subtype

theorem conjUC_holds : ConjUC := by
  intro D X u hK g c
  ext x
  simp only [UcS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hN, k, hk, hke⟩
    refine ⟨(g : X.B.I.Gf)⁻¹ * x * (g : X.B.I.Gf), ⟨?_, k, hk, ?_⟩, ?_⟩
    · have := (nfinConj_holds X u g⁻¹ x hN).1
      simp only [InvMemClass.coe_inv, inv_inv] at this
      exact this
    · rw [← hke]; group
    · group
  · rintro ⟨y, ⟨hN, k, hk, hke⟩, rfl⟩
    refine ⟨(nfinConj_holds X u g y hN).1, k, hk, ?_⟩
    rw [← hke]; group

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NHLocHolds
noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

theorem NHLoc_holds : JacobianCoordinates.NHLoc := by
  intro n r k ε e p z z' T T' F hep hpp hzp μN μH hN hH
  have hpz : ∀ a, hJ ε (p a) z = 0 := fun a => hJ_swap0 (hzp a)
  obtain ⟨w, hww, hew, hpw, hzw⟩ := UnitaryIsometries.RI.complement ε F.dim F.sig F.T_pos
    (⟨F.ee, hep, hpp, F.ez, hpz, F.zz⟩ : UnitaryIsometries.RI.Hyp ε e p z (T : ℂ))
  have Fw : Frm ε e p z w T := ⟨F.ee, hep, hpp, F.ez, hpz, F.zz, hew, hpw, hzw, hww, F.T_pos.ne'⟩
  have hdim := F.dim
  have hHc := HG_compact Fw hdim
  have hNH := hN
  obtain ⟨⟨hσN, hneN, hcN, hinvN⟩, hfinN⟩ := hN
  obtain ⟨⟨hσH, hneH, hcH, hinvH⟩, hfinH⟩ := hH
  haveI := hσN
  haveI := hσH
  haveI := hfinN
  haveI := hfinH
  have hmult : Measurable (fun q : UJ ε × UJ ε => q.1 * q.2) := measurable_fst.mul measurable_snd
  set NH : Set (UJ ε × UJ ε) := (NG ε e z : Set (UJ ε)) ×ˢ (HG ε e p z : Set (UJ ε)) with hNHdef
  have hPout : (μN.prod μH) NHᶜ = 0 := by
    rw [hNHdef, Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod]
      have : μN (NG ε e z : Set (UJ ε))ᶜ = 0 := hcN
      rw [this, zero_mul]
    · rw [Measure.prod_prod]
      have : μH (HG ε e p z : Set (UJ ε))ᶜ = 0 := hcH
      rw [this, mul_zero]
  have hHfin : μH (HG ε e p z : Set (UJ ε)) < ⊤ := hHc.measure_lt_top
  have hfin : IsFiniteMeasureOnCompacts ((μN.prod μH).map (fun q : UJ ε × UJ ε => q.1 * q.2)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hmult hK.measurableSet]
    have hsub : (fun q : UJ ε × UJ ε => q.1 * q.2) ⁻¹' K ⊆
        ((K * (HG ε e p z : Set (UJ ε))⁻¹) ×ˢ (HG ε e p z : Set (UJ ε))) ∪ NHᶜ := by
      intro q hq
      by_cases hq' : q ∈ NH
      · left
        refine ⟨⟨q.1 * q.2, hq, q.2⁻¹, by simpa using hq'.2, by group⟩, hq'.2⟩
      · right; exact hq'
    refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
    rw [hPout, add_zero, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hK.mul hHc.inv).measure_lt_top hHfin
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, hfin⟩
  · haveI := hfin
    infer_instance
  · intro h0
    have := congrArg (fun m : Measure (UJ ε) => m Set.univ) h0
    simp only [Measure.map_apply hmult MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply, ← Set.univ_prod_univ, Measure.prod_prod] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hneN (Measure.measure_univ_eq_zero.1 h1)
    · exact hneH (Measure.measure_univ_eq_zero.1 h1)
  · rw [Measure.map_apply hmult (show MeasurableSet (SLoc ε e z)ᶜ from
      (UnitaryIsometries.RI.SG_closed ε e z).measurableSet.compl)]
    refine measure_mono_null (s := (fun q : UJ ε × UJ ε => q.1 * q.2) ⁻¹' (SLoc ε e z)ᶜ) (t := NHᶜ)
      (fun q hq hqNH => hq ?_) hPout
    exact (UnitaryIsometries.RI.SG ε e z).mul_mem (NG_le_SG ε e z hqNH.1) (HG_le_SG ε e p z hqNH.2)
  · obtain ⟨m0, hm0, h0, hh0, rfl⟩ := mem_NH Fw hdim hs
    have hf : μN.map (fun x => m0 * conjH h0 x) = μN := by
      have : (fun x => m0 * conjH h0 x) = (fun x => m0 * x) ∘ conjH h0 := rfl
      rw [this, ← Measure.map_map (measurable_const_mul m0) (conjH h0).continuous.measurable,
        conj_haar_eq Fw hdim hNH hh0, hinvN m0 hm0]
    have hg : μH.map (fun x => h0 * x) = μH := hinvH h0 hh0
    have hfm : Measurable (fun x => m0 * conjH h0 x) := (conjH h0).continuous.measurable.const_mul m0
    have hgm : Measurable (fun x : UJ ε => h0 * x) := measurable_const_mul h0
    haveI : SFinite (μN.map (fun x => m0 * conjH h0 x)) := by rw [hf]; infer_instance
    haveI : SFinite (μH.map (fun x => h0 * x)) := by rw [hg]; infer_instance
    have hfun : (fun x => m0 * h0 * x) ∘ (fun q : UJ ε × UJ ε => q.1 * q.2) =
        (fun q : UJ ε × UJ ε => q.1 * q.2) ∘ Prod.map (fun x => m0 * conjH h0 x) (fun x => h0 * x) := by
      funext q
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, conjH_apply]
      group
    rw [Measure.map_map (measurable_const_mul _) hmult, hfun,
      ← Measure.map_map hmult (hfm.prodMap hgm), ← Measure.map_prod_map μN μH hfm hgm, hf, hg]

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKeyPf
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
open Matrix

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.Pf.Level

variable {D : D7} (X : HidaSetting D)

theorem isId_rat {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (t : GTerm X u u (X.Fu u) (X.Fu u) what₂ what₂) (ht : t.isId) :
    (∀ a : Fin D.R.rS, t.lin (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1})) ∧
      t.lin (X.zu u) - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX) := by
  have hin := Formalism.L2.SG.FourParts.isInS_of_isIdT ht
  have hS : Formalism.L2.SG.FourParts.InSF (lf D (X.Fu u)) t.frame :=
    (Formalism.L2.SG.FourParts.isInS_mk (Λ := t.lam) (F := lf D (X.Fu u))
      (P := Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u)
      (PI.InSClassConstW.inSFun_all _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩).1 hin
  have hfr : t.frame.fl = mapFlag t.rep.1.2 t.rep.2.2.1 (lf D (X.Fu u)).fl := by
    show (mapLF t.rep.1.2 (lf D (X.Fu u))).fl = _
    simp only [mapLF, dite_eq_left t.rep.2.2.1]
  refine ⟨fun a => ?_, ?_⟩
  · have h := hS.1 a
    have e1 : t.frame.fl.e a = t.lin (X.eX a) := by
      rw [hfr]
      show t.rep.1.2 ((X.Fu u).e a) = t.rep.1.2 (X.eX a)
      rw [X.Fu_e u]
    have e2 : (lf D (X.Fu u)).fl.e a = X.eX a := by
      show (X.Fu u).e a = _
      rw [X.Fu_e u]
    have e3 : Xflag (lf D (X.Fu u)) a.val = Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1}) := rfl
    rw [e1, e2, e3, X.Fu_e u] at h
    exact h
  · have h := hS.2
    have e1 : t.frame.fl.z = t.lin (X.zu u) := by
      rw [hfr]
      show t.rep.1.2 ((X.Fu u).z) = t.rep.1.2 (X.zu u)
      rw [X.flagZVector u]
    have e2 : (lf D (X.Fu u)).fl.z = X.zu u := by
      show (X.Fu u).z = _
      rw [X.flagZVector u]
    have e3 : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range (X.Fu u).e) := rfl
    rw [e1, e2, e3, X.Fu_e u] at h
    exact h

theorem pt_srat {u : D.what₂.Word} {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (he : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}))
    (hz : n (X.zu u) - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX)) : x ∈ Srat X u := by
  have hmem := ratLink_mem X hx
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  have hE : ∀ a : Fin D.R.rS, ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.eR a ∈
      Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
    intro a
    have := crd_span' X (he a)
    rw [Set.image_image] at this
    show _ *ᵥ X.crd (X.eX a) ∈ _
    rw [mcrd X h3]
    exact this
  have hZ : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.zR u ∈
      Submodule.span X.B.I.E (Set.range X.eR) := by
    have := crd_span' X hz
    rw [← Set.range_comp] at this
    show _ *ᵥ X.crd (X.zu u) ∈ _
    rw [mcrd X h3]
    exact this
  have transfer {R : Type} [CommRing R] (j : X.B.I.E →+* R)
      (ι : (Fin X.B.I.n → X.B.I.E) →+ (Fin X.B.I.n → R))
      (hs : ∀ c x, ι (c • x) = j c • ι x)
      (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) R)
      (hG : ∀ y, G *ᵥ ι y = ι (M *ᵥ y))
      (S : Set (Fin D.R.rS)) (y : Fin X.B.I.n → X.B.I.E)
      (hy : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ y ∈ Submodule.span X.B.I.E (X.eR '' S)) :
      (G - 1) *ᵥ ι y ∈ Submodule.span R ((fun b => ι (X.eR b)) '' S) := by
    have hspan : ∀ {z}, z ∈ Submodule.span X.B.I.E (X.eR '' S) →
        ι z ∈ Submodule.span R (ι '' (X.eR '' S)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha => rw [hs]; exact Submodule.smul_mem _ _ ha
    have hh := hspan hy
    rw [Set.image_image] at hh
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hG, ← map_sub]
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hh
  let rmap (v : InfinitePlace X.B.I.F) : (Fin X.B.I.n → X.B.I.E) →+ (Fin X.B.I.n → ℂ) :=
    { toFun := rv X.B.I v
      map_zero' := by
        unfold rv
        have : (fun i => X.B.I.φ v ((0 : Fin X.B.I.n → X.B.I.E) i)) = 0 := by funext i; simp
        rw [this, Matrix.mulVec_zero]
      map_add' := by
        intro x y
        unfold rv
        rw [← Matrix.mulVec_add]
        congr 1
        funext i; simp }
  have rsmul (v : InfinitePlace X.B.I.F) (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
      rmap v (c • x) = X.B.I.φ v c • rmap v x := by
    change rv X.B.I v (c • x) = X.B.I.φ v c • rv X.B.I v x
    unfold rv
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i; simp
  let imap : (Fin X.B.I.n → X.B.I.E) →+ VA X.B.I :=
    { toFun := incl X.B.I
      map_zero' := by funext i; simp [incl]
      map_add' := by intro x y; funext i; simp [incl] }
  have ismul (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
      imap (c • x) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) c • imap x := by
    funext i
    simp [imap, incl]
  refine Subgroup.mem_inf.2 ⟨hmem, Subgroup.subset_closure ⟨fun v => ?_, ?_⟩⟩
  · have hG : ∀ y, uMat (x.1 v) *ᵥ rmap v y =
        rmap v ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
      intro y
      change uMat (x.1 v) *ᵥ rv X.B.I v y = rv X.B.I v (M *ᵥ y)
      rw [h1 v]
      exact rv_mulVec X v _ y
    refine ⟨fun a => ?_, ?_⟩
    · exact transfer (X.B.I.φ v) (rmap v) (rsmul v) _ hG _ _ (hE a)
    · have := transfer (X.B.I.φ v) (rmap v) (rsmul v) _ hG Set.univ _
        (by rw [Set.image_univ]; exact hZ)
      unfold spanLt
      rw [← range_eq_image_lt]
      rwa [Set.image_univ] at this
  · have hG : ∀ y, X.B.I.fmat x.2 *ᵥ imap y =
        imap ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
      intro y
      change X.B.I.fmat x.2 *ᵥ incl X.B.I y = incl X.B.I (M *ᵥ y)
      rw [h2]
      exact incl_mulVec X _ y
    refine ⟨fun a => ?_, ?_⟩
    · exact transfer _ imap ismul _ hG _ _ (hE a)
    · have := transfer _ imap ismul _ hG Set.univ _
        (by rw [Set.image_univ]; exact hZ)
      rwa [Set.image_univ] at this

theorem lin_eq_of_fst {x y : X.B.I.GA} {m n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m)
    (hy : RatLink X y n) (h : x.1 = y.1) : m = n := by
  obtain ⟨M, -, h1, -, h3⟩ := hx
  obtain ⟨N, -, k1, -, k3⟩ := hy
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hP : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have e3 : ∀ A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
      X.B.I.P v * ((X.B.I.P v)⁻¹ * A * X.B.I.P v) * (X.B.I.P v)⁻¹ = A := by
    intro A
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hP]
  have e : (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v =
      (X.B.I.P v)⁻¹ * (N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v := by
    rw [← h1 v, ← k1 v, h]
  have e2 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) =
      (N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) := by
    rw [← e3 ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)),
      ← e3 ((N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)), e]
  have hMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N := by
    ext i j
    exact (X.B.I.φ v).injective (congrFun (congrFun e2 i) j)
  refine LinearEquiv.ext fun p => ?_
  rw [← toV_crd X (m p), ← toV_crd X (n p), h3, k3, hMN]

end Formalism.L2.SG.Pf.IdMeet

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.Pf.Level

theorem idMeetKeyC_holds : IdMeetKeyC := by
  intro D X Y u hNeat ρ ρ' t ht hM
  obtain ⟨-, -, hk⟩ := hM
  obtain ⟨he, hz⟩ := isId_rat X t ht
  have hs : t.pt ∈ Srat X u := pt_srat X t.rep.2.1 he hz
  have hg : (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u) ∈ X.K2 := hk
  obtain ⟨hs1, hs2⟩ := sratComp_holds X u t.pt hs
  obtain ⟨ν, η, hνη, hνG, hν1, hν2, hη⟩ :=
    Formalism.L2.SG.Pf.ratLevi_holds X u t.pt (Subgroup.mem_inf.1 hs).1 hs1 hs2
  obtain ⟨ηg, hηg⟩ : ∃ ηg : Gam X u, ηg = ⟨η, hη⟩ := ⟨_, rfl⟩
  have hs2e : t.pt.2 = ν.2 * η.2 := by rw [hνη]; rfl
  obtain ⟨hn1, -⟩ := nfinConj_holds X u ((Y.cs u).h ρ)⁻¹ ν.2 hν2
  have hLD := Formalism.L2.SG.Pf.Level.levelDec_of_psiDd (X := X) (u := u) (Formalism.L2.SG.Pf.psiDd_holds X)
  obtain ⟨h1, hh1⟩ : ∃ h1 : Hfin X u, h1 = ((Y.cs u).h ρ)⁻¹ * iotaF X u ηg * (Y.cs u).h ρ' := ⟨_, rfl⟩
  have e1 : (X.xu u)⁻¹ * ((((Y.cs u).h ρ)⁻¹ : Hfin X u) * ν.2 * ((((Y.cs u).h ρ)⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
      (h1 : X.B.I.Gf)) * X.xu u =
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u) := by
    rw [hs2e, hh1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, iotaF_coe, hηg]
    group
  have hh1K : (X.xu u)⁻¹ * (h1 : X.B.I.Gf) * X.xu u ∈ X.K2 := (hLD _ hn1 h1 (e1 ▸ hg)).1
  have hρρ : ρ = ρ' := by
    refine (Y.colReps u ((Y.cs u).h ρ')).unique ⟨ηg⁻¹, ⟨h1, hh1K⟩, ?_⟩ ⟨1, 1, by simp⟩
    show (Y.cs u).h ρ' = iotaF X u ηg⁻¹ * (Y.cs u).h ρ * h1
    rw [map_inv, hh1]
    group
  subst hρρ
  have hmem : ((Y.cs u).h ρ)⁻¹ * iotaF X u ηg * (Y.cs u).h ρ ∈ Ku X u Y.hK := by
    rw [← hh1]; exact hh1K
  have hη1 : ηg = 1 := hNeat ((Y.cs u).h ρ) ηg hmem
  have hη1' : η = 1 := by
    have := congrArg Subtype.val hη1
    rw [hηg] at this
    exact this
  have hsν : t.pt = ν := by rw [hνη, hη1', mul_one]
  have hsN := nilradical_rational_lattice D X Y u ρ t.pt (Formalism.L2.SG.Closed.level_subgroup_properties X)
    (by rw [hsν]; exact hνG) (by rw [hsν]; exact hν1) (by rw [hsν]; exact hν2) hg
  obtain ⟨x, n, hx, hx1, hn⟩ := hsN
  refine ⟨rfl, ?_⟩
  have hl : t.lin = n := lin_eq_of_fst X t.rep.2.1 hx hx1
  rw [hl]
  exact hn

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviSteps
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeviStabFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    ∃ T : Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      (∀ τ ∈ T, τ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap τ Λ = Λ ∧ ∃ t : X.B.I.GA, RatLink X t τ ∧ t ∈ Srat X u') ∧
      ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA), RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ = Λ →
        ∃ τ ∈ T, ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), (τ⁻¹ * σ) x - x ∈ Xsp (lf D (X.Fu u'))

def Usp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u'})

def Wsp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  orth (VS D) (Usp X u')

def LeviPosC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word), ∀ w ∈ Wsp X u', w ≠ 0 →
    0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)

def SratZC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (s : X.B.I.GA)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ → s ∈ Srat X u' →
      σ (X.zu u') - X.zu u' ∈ Xsp (lf D (X.Fu u'))

def piWL {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (X.fY a)).smulRight (X.eX a) - ∑ a, ((VS D).hT (X.eX a)).smulRight (X.fY a) -
    ((VS D).hT (X.zu u')).smulRight (((VS D).hT (X.zu u') (X.zu u'))⁻¹ • X.zu u')

def hW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    Wsp X u' →ₗ⋆[D.host.E] Wsp X u' →ₗ[D.host.E] D.host.E :=
  ((VS D).hT.comp (Wsp X u').subtype).compl₂ (Wsp X u').subtype

def LW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Submodule (𝓞 D.host.E) (Wsp X u') :=
  ((Λ ⊓ (orth (VS D) (Xsp (lf D (X.Fu u')))).restrictScalars (𝓞 D.host.E)).map
    ((piWL X u').restrictScalars (𝓞 D.host.E))).comap ((Wsp X u').subtype.restrictScalars (𝓞 D.host.E))

def LeviWFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    Set.Finite {g : Wsp X u' ≃ₗ[D.host.E] Wsp X u' | g ∈ Formalism.HermitianLatticesTheory.isom (hW X u') ∧ Formalism.HermitianLatticesTheory.gmap g (LW X u' Λ) = LW X u' Λ}

theorem srat_flag {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {u' : D.what₂.Word} {s : X.B.I.GA}
    {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : RatLink X s σ) (hS : s ∈ Srat X u') :
    ∀ j, ∀ x ∈ Xflag (lf D (X.Fu u')) (j + 1), σ x - x ∈ Xflag (lf D (X.Fu u')) j := by
  have hX : ∀ j : ℕ, Xflag (lf D (X.Fu u')) j = Submodule.span D.host.E (X.eX '' {b | b.1 < j}) := by
    intro j
    unfold Formalism.MainNotions.S.Lat.Xflag Formalism.MainNotions.S.FlagG.Xa
    simp only [Formalism.MainNotions.S.lf, X.Fu_e]
  intro j x hx
  rw [hX (j + 1)] at hx
  rw [hX j]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have h := Formalism.L2.SG.Pf.RegroupPf.StabFlagPf.flag_e (X := X) hs hS b
    refine Submodule.span_mono ?_ h
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_of_lt_of_le hc (Nat.lt_succ_iff.mp hb), rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _), add_sub_add_comm]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hy

private theorem gmap_mul_lemma {D : D7} (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (L : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

private theorem gmap_one_explicit_D {D : D7} (L : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.coe_one, id_eq, exists_eq_right]

private theorem gmap_inv_of_gmap_eq {D : D7} (a : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (L M : Submodule (𝓞 D.host.E) (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap a L = M) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ M = L := by
  rw [← h, ← gmap_mul_lemma, inv_mul_cancel, gmap_one_explicit_D]

theorem leviFinC_of (h : LeviStabFinC) : LeviFinC := by
  intro D X Y u'
  let P : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V → Prop := fun Λ₁ Λ₂ =>
    Λ₂ ∈ Y.what₂ u' ∧ ∃ (σ₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s₀ : X.B.I.GA), RatLink X s₀ σ₀ ∧
      σ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ s₀ ∈ Srat X u' ∧ Formalism.HermitianLatticesTheory.gmap σ₀ Λ₂ = Λ₁
  refine ⟨fun Λ₁ Λ₂ => if hP : P Λ₁ Λ₂ then
      (h D X Y u' Λ₂ hP.1).choose.image (fun τ => hP.2.choose * τ) else ∅, ?_⟩
  intro Λ₁ _ Λ₂ hΛ₂ σ s hs hσ hS hmap
  have hP : P Λ₁ Λ₂ := ⟨hΛ₂, σ, s, hs, hσ, hS, hmap⟩
  simp only [dif_pos hP]
  obtain ⟨s₀, hs₀, hσ₀, hS₀, hmap₀⟩ := hP.2.choose_spec
  obtain ⟨hT1, hT2⟩ := (h D X Y u' Λ₂ hP.1).choose_spec
  generalize hP.2.choose = σ₀ at hs₀ hσ₀ hmap₀ ⊢
  generalize (h D X Y u' Λ₂ hP.1).choose = T at hT1 hT2 ⊢

  have hρL : RatLink X (s₀⁻¹ * s) (σ₀⁻¹ * σ) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hs₀) hs
  have hρI : σ₀⁻¹ * σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hσ₀) hσ
  have hρS : s₀⁻¹ * s ∈ Srat X u' := (Srat X u').mul_mem ((Srat X u').inv_mem hS₀) hS
  have hρΛ : Formalism.HermitianLatticesTheory.gmap (σ₀⁻¹ * σ) Λ₂ = Λ₂ := by
    rw [gmap_mul_lemma, hmap]
    exact gmap_inv_of_gmap_eq σ₀ Λ₂ Λ₁ hmap₀
  obtain ⟨τ, hτ, hτo⟩ := hT2 (σ₀⁻¹ * σ) (s₀⁻¹ * s) hρL hρI hρS hρΛ
  obtain ⟨hτI, hτΛ, t, ht, htS⟩ := hT1 τ hτ
  refine ⟨σ₀ * τ, Finset.mem_image.mpr ⟨τ, hτ, rfl⟩, ?_⟩
  have heq : (σ₀ * τ)⁻¹ * σ = τ⁻¹ * (σ₀⁻¹ * σ) := by
    rw [mul_inv_rev, mul_assoc]
  rw [heq]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hτI) hρI, ?_⟩, ?_, hτo⟩
  · rw [gmap_mul_lemma, hρΛ]
    exact gmap_inv_of_gmap_eq τ Λ₂ Λ₂ hτΛ
  · exact srat_flag X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X ht) hρL)
      ((Srat X u').mul_mem ((Srat X u').inv_mem htS) hρS)

end Formalism.L2.SG.Pf.SlabCount
end
end

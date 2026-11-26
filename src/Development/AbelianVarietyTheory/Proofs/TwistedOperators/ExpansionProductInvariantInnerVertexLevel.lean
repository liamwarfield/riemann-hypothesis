module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatOIffOfSt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjComponentIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjComponentIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemPairCpt

open GlobalTheory.StdFrames

theorem cpt_sg_eq_one_of_cP_mem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∈ P) : cpt (D := D) w (sg D (toEAf D e)) = 1 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (1 - toEAf D e) = 0 := by
    rw [map_sub, map_one, GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, sub_self]
  have h2 := cpt_sg_eq_zero h1
  rw [map_sub, map_one, map_sub, map_one] at h2
  exact (sub_eq_zero.mp h2).symm

theorem cpt_sg_eq_zero_of_cP_notMem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∉ P) : cpt (D := D) w (sg D (toEAf D e)) = 0 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (toEAf D e) = 0 := by
    rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw]
  exact cpt_sg_eq_zero h1

theorem cpt_add_cA_idemSum : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := by
  intro D e P he w
  have hsplit : GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) =
      cpt (D := D) w (toEAf D e) + cpt (D := D) w (sg D (toEAf D e)) := by
    rw [map_add (f := _), toEAf_cA, map_add (f := _)]
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · rw [hsplit]
    by_cases hw : w ∈ P
    · have hc : GlobalTheory.IdemSupport.cP w ∉ P := fun hc => GlobalTheory.IdemSumBranch.conjPrime_ne he hc hw rfl
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, cpt_sg_eq_zero_of_cP_notMem he w hc, add_zero]
    · have hc : GlobalTheory.IdemSupport.cP w ∈ P := h.resolve_left hw
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw, cpt_sg_eq_one_of_cP_mem he w hc, zero_add]
  · rw [hsplit, GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg h1, cpt_sg_eq_zero_of_cP_notMem he w h2, add_zero]

end GlobalTheory.IdemPairCpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjComponentIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_add_conj_component_indicator : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := by
  first | exact @GlobalTheory.IdemPairCpt.cpt_add_cA_idemSum | exact GlobalTheory.IdemPairCpt.cpt_add_cA_idemSum | (intros; apply GlobalTheory.IdemPairCpt.cpt_add_cA_idemSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix

namespace GlobalTheory.CutProdLev

theorem cutGL_mem_St_of_mem_prodLev : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  intro D n β P n' h K x hx b hb hb0
  apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO
  intro w

  have hc : GlobalTheory.StdFrames.cpt (D := D) w b * GlobalTheory.StdFrames.cpt (D := D) w b = GlobalTheory.StdFrames.cpt (D := D) w b :=
    (map_mul (GlobalTheory.StdFrames.cpt (D := D) w) b b).symm.trans (congrArg _ hb)
  have h01 : GlobalTheory.StdFrames.cpt (D := D) w b = 0 ∨ GlobalTheory.StdFrames.cpt (D := D) w b = 1 := by
    have h' : GlobalTheory.StdFrames.cpt (D := D) w b * (GlobalTheory.StdFrames.cpt (D := D) w b - 1) = 0 := by
      rw [mul_sub, hc, mul_one, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)

  have hconj : (MulAut.conj β⁻¹).toMonoidHom (GlobalTheory.UnitaryIdemCut.cutGL b hb x) =
      GlobalTheory.UnitaryIdemCut.cutGL b hb ((MulAut.conj β⁻¹).toMonoidHom x) :=
    (GlobalTheory.UnitaryIdemCut.cutGL_conj b hb β⁻¹ x).symm
  have hloc : ∀ y : GL (Fin n) (Lev.EAf D), GlobalTheory.StdFrames.loc w (GlobalTheory.UnitaryIdemCut.cutGL b hb y) =
      GlobalTheory.UnitaryIdemCut.cutGL _ hc (GlobalTheory.StdFrames.loc w y) := fun y =>
    GlobalTheory.UnitaryIdemCut.bc_cutGL (GlobalTheory.StdFrames.cpt w) b hb _ hc rfl y
  rcases h01 with h0 | h1
  ·
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = 1 := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h0]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = 1 := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1, map_one]
    rw [e]
    exact one_mem _
  ·

    unfold GlobalTheory.FunObj.prodLev at hx
    have hx2 := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_iInf] at hx2
    have hx3 := hx2 w
    rw [Subgroup.mem_iInf] at hx3
    have hxw := Subgroup.mem_comap.mp (hx3 fun PP hPP e => by
      have h2 := hb0 w ⟨PP, hPP, e⟩
      rw [h1] at h2
      exact one_ne_zero h2)
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = g := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h1]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = GlobalTheory.FunObj.inBasis rfl β w x := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1]
    rw [e]
    exact hxw

end GlobalTheory.CutProdLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  first | exact @GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | exact GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | (intros; apply GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.CutStdLat

open GlobalTheory.FunObj Matrix

theorem latO_iff_of_St {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (j : ℕ) (βS : GL (Fin (G.V (.top j)).rank) (Lev.EAf D))
    (βT : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) (hβS : IsFrame βS (colLat (S.N.fr (.top j))))
    (hβT : IsFrame βT (colLat (S.N.fr (.top (j + 1))))) (g : GA D (G.V (.top (j + 1))))
    (hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT) (x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  unfold stdLatO
  exact GlobalTheory.VecInv.mem_latO_iff (S := G.V (.top j)) (T := G.V (.top (j + 1))) hβS hβT (g := 1) (h := g)
    (by rw [map_one]; exact one_mem _) hT x

theorem keep_stdLatO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ g : GA D (G.V (.top (j + 1))),
      Formalism.L2.Theta.mt _ g = (1 - (e + cA D e)) • Formalism.L2.Theta.mt _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) :
        FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) + (e + cA D e) • (1 : Matrix (Fin (G.V (.top (j + 1))).rank)
        (Fin (G.V (.top (j + 1))).rank) (AE D)) →
      ∀ x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)),
        x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he g hg x
  classical
  have hfull {n : ℕ} (B : GL (Fin n) D.host.E) : (colLat B).IsFullLattice D.host.E := by
    letI := GlobalTheory.FunObj.VecEx.isLattice_colLat B
    refine ⟨?_⟩
    rw [colLat, Submodule.span_span_of_tower]
    change Submodule.span D.host.E (Set.range (B : Matrix (Fin n) (Fin n) D.host.E).col) = ⊤
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr B.isUnit)
  obtain ⟨βS, hβS⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top j))) (hfull _)
  obtain ⟨βT, hβT⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top (j + 1)))) (hfull _)
  set a : AE D := e + cA D e with ha
  set b : Lev.EAf D := toEAf D (1 - a) with hbdef
  have hcb : ∀ w, GlobalTheory.StdFrames.cpt (D := D) w b = 1 - GlobalTheory.StdFrames.cpt (D := D) w (toEAf D a) := fun w => by
    rw [hbdef, RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one]
  have hca := GlobalTheory.T.idempotentSum_add_conj_component_indicator he
  have hb : b * b = b := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    by_cases h1 : w ∈ locPl G t ∨ GlobalTheory.IdemSupport.cP w ∈ locPl G t
    · rw [(hca w).1 h1]; ring
    · push_neg at h1; rw [(hca w).2 h1.1 h1.2]; ring
  have hfh : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
      GA D (G.V (.top (j + 1)))) = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    have e0 : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
        GA D (G.V (.top (j + 1)))) = finG (G.V (.top (j + 1))) ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) := rfl
    rw [e0, map_mul, map_mul, map_inv]
  have hfg : Lev.finE (G.V (.top (j + 1))) g = GlobalTheory.UnitaryIdemCut.cutGL b hb
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val, ← hfh, GlobalTheory.VecInv.finE_val, GlobalTheory.VecInv.finE_val, hg]
    ext i l
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add (f := _), RingHom.map_mul, hbdef,
      RingHom.map_sub, RingHom.map_one, Matrix.one_apply]
    split_ifs <;> simp only [RingHom.map_one, RingHom.map_zero] <;> ring
  obtain ⟨Pu, eu, heu, hsu, hoff⟩ := S.N.u_supp (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have hnot : ∀ Q ∈ Pu, ∀ w : Pl D.host.E, w.under (𝓞 D.host.F) = Q.under (𝓞 D.host.F) → w ∉ locPl G t := by
    intro Q hQ w hw hwl
    obtain ⟨h1, h2, -⟩ := S.N.off Q (hoff Q hQ)
    unfold locPl at hwl
    rcases Finset.mem_union.1 hwl with h3 | h3
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h3
      have h4 := G.pl.w_over v hv
      exact h1 ((hw.symm.trans h4) ▸ hv)
    · exact h2 t ht w h3 hw.symm
  have hub : b * toEAf D (eu + cA D eu) = toEAf D (eu + cA D eu) := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    have hu := GlobalTheory.T.idempotentSum_add_conj_component_indicator heu w
    by_cases h1 : w ∈ Pu ∨ GlobalTheory.IdemSupport.cP w ∈ Pu
    · rw [hu.1 h1]
      have hw1 : w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 w rfl
        · exact hnot _ h1 w (GlobalTheory.IdemSupport.under_cP w).symm
      have hw2 : GlobalTheory.IdemSupport.cP w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 _ (GlobalTheory.IdemSupport.under_cP w)
        · exact hnot _ h1 _ rfl
      rw [(hca w).2 hw1 hw2]; ring
    · push_neg at h1; rw [hu.2 h1.1 h1.2, mul_zero]
  have hU : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) = finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val]
    show b • (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val + (1 - b) • 1 = (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val
    rw [GlobalTheory.VecInv.finE_val]
    ext i l
    have h0 := hsu i l
    have h3 : b * toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) =
        toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) := by
      rw [← h0, RingHom.map_mul, ← mul_assoc, hub]
    have h4 : toEAf D ((1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (AE D)) i l) =
        (1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) i l := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.sub_apply, RingHom.map_sub, h4] at h3
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination h3
  have hK : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) ∈ St (S.βp (j + 1)) :=
    GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel _ _ _ _ _ hk b hb fun w ⟨PP, hPP, hw⟩ => by
      rw [hcb]
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hw with rfl | rfl
      · rw [(hca _).1 (Or.inl hPP)]; ring
      · rw [(hca _).1 (Or.inr (by rwa [GlobalTheory.StdFrames.cP_cP]))]; ring
  have hcut : Lev.finE (G.V (.top (j + 1))) g = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) *
      finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    rw [hfg, map_mul, map_mul, map_inv, hU]
  have hp := S.βp_is (j + 1) (by omega)
  have hl := S.N.u_lat (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have keep : ∀ X ∈ St (S.βp (j + 1)), ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))),
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) := by
    intro X hX y hy
    have h1 : (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top (j + 1))) := (hl y).1 hy
    have h2 := ((GlobalTheory.LevSplit.mem_St_iff _ _ hp X).1 hX).1 _ h1
    refine (hl _).2 ?_
    change (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ _ ∈ _
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h2 ⊢
    have e3 : Uu.val * (Uu⁻¹ * X * Uu).val = X.val * Uu.val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec y Uu.val (Uu⁻¹ * X * Uu).val, e3, ← Matrix.mulVec_mulVec y X.val Uu.val]
    exact h2
  have st : ∀ X ∈ St (S.βp (j + 1)),
      (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) ∈ St βT := by
    intro X hX
    refine (GlobalTheory.LevSplit.mem_St_iff _ _ hβT _).2 ⟨keep X hX, fun y hy => ?_⟩
    have h5 := keep _ (inv_mem hX) y hy
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h5 ⊢
    have e1 : (Uu⁻¹ * X * Uu)⁻¹ = Uu⁻¹ * X⁻¹ * Uu := by group
    rw [e1]
    exact h5
  have hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT := by
    rw [hcut]
    exact st _ hK
  exact latO_iff_of_St S j βS βT hβS hβT g hT x

end GlobalTheory.CutStdLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem halfInd_isSBHalf {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
  · by_contra h; exact hx (if_neg fun h' => h h'.2)
  · rw [one_smul]
    have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
      rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
    exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
  · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)

theorem om_base_law {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) {h : GA D T}
    (hh : SuppAt e T h) :
    ∃ c : ℂ, om (1, h) f₀ = c • Tm fun x => halfInd e (latO S T ΛS ΛT fun _ => True) (actO S T 1⁻¹ h⁻¹ x) := by
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have key := GlobalTheory.SplitLinear.splitLinearModel D ψ S T χS χT om hW ΛS ΛT hS hT P e he f₀ hf hv 1 one_ne_zero Tm hTm 1 h
    (GlobalTheory.SplitLinear.suppAt_one e S) hh _ _ (GlobalTheory.VecInv.isDetAt_detAt e he' S 1) (GlobalTheory.VecInv.isDetAt_detAt e he' T h)
    _ (halfInd_isSBHalf e _)
  have h0 : Tm (halfInd e (latO S T ΛS ΛT fun _ => True)) = f₀ := by simpa using hTm.vac
  rw [h0] at key
  refine ⟨(splitFacO χS χT (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac S T (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ), key.trans ?_⟩
  rw [← map_smul]
  rfl

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem compAt_fin {θ : InfFam D} {V : HSp D} {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = 1 := by
  have h1 : Formalism.UG.bc (infPart D) (matHom V h) = 1 := (GlobalTheory.UnitaryIdemCut.mem_GfC_iff V h).1 hh
  have h2 := congrArg Units.val h1
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [compAt, Matrix.map_apply]
  have h4 : infPart D (Formalism.L2.Theta.mt V h i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := h3
  rw [h4, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem actO_one_one {S T : HSp D} (u : WO S T) : actO S T 1 1 u = u := by
  simp [actO, GlobalTheory.AdelicLatMove.mt_one]

theorem om_keep_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (kS : S.SigOK) (kT : T.SigOK) {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f)
    {h : GA D T} (hh : h ∈ GfC T)
    (hk : ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T 1 h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ∃ c : ℂ, om (1, h) f = c • f := by
  have hf' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ 1 h
    (fun τ => by rw [compAt_fin (one_mem _) τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_fin hh τ, Matrix.mul_one, Matrix.one_mul])
    (fun u => ⟨fun hu => ⟨actO S T 1 h⁻¹ u, (hk _).2 (by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]; exact hu),
        by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]⟩,
      fun ⟨u₀, hu₀, e⟩ => e ▸ (hk u₀).1 hu₀⟩) f hf
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hf.1 hθ S T sS sT kS kT cS cT ΛS ΛT hS hT f _ hf hf'
  exact ⟨c, hc⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem exists_cut_hom (V : HSp D) (r : AF D.host.F)
    (hb : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r = algebraMap (AF D.host.F) (AE D) r) :
    ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) r • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) r) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  obtain ⟨κ, hκ⟩ := GlobalTheory.UnitaryIdemCut.exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram r hb
  refine ⟨κ, fun g => ?_⟩
  have := congrArg Units.val (hκ g)
  rw [GlobalTheory.UnitaryIdemCut.cutGL_val] at this
  exact this

theorem actO_cut_half {S T : HSp D} {b e : AE D} (hbe : b * e = 0) {g : GA D T}
    {M : Matrix (Fin T.rank) (Fin T.rank) (AE D)}
    (hg : Formalism.L2.Theta.mt T g = b • M + (1 - b) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) {y : WO S T}
    (hy : IsHalf e y) : actO S T 1 g y = y := by
  have hby : ∀ i j, b * y i j = 0 := fun i j => by rw [← hy i j, ← mul_assoc, hbe, zero_mul]
  have h1 : actO S T 1 g y = (HMul.hMul (Formalism.L2.Theta.mt T g) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    simp [actO, GlobalTheory.AdelicLatMove.mt_one]
  rw [h1, hg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_eq_zero fun k _ => by rw [mul_left_comm, hby, mul_zero], zero_add, sub_mul, one_mul,
    hby, sub_zero]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem cut_mul_cut {n : Type} [Fintype n] [DecidableEq n] {a : AE D} (ha : a * a = a) (M : Matrix n n (AE D)) :
    (a • M + (1 - a) • (1 : Matrix n n (AE D))) * ((1 - a) • M + (1 - (1 - a)) • (1 : Matrix n n (AE D))) = M := by
  have h0 : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
  have h0' : (1 - a) * a = 0 := by rw [mul_comm, h0]
  have h1 : (1 - a) * (1 - a) = 1 - a := by rw [sub_mul, one_mul, h0, sub_zero]
  rw [sub_sub_cancel]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
  simp only [smul_add, smul_smul, h0, h0', ha, h1, zero_smul, zero_add, add_zero]
  rw [← add_smul, sub_add_cancel, one_smul]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_cut_pair (V : HSp D) {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    ∃ κe κo : GA D V →* GA D V, (∀ g, g = κe g * κo g) ∧ (∀ g, SuppAt e V (κe g)) ∧ (∀ g ∈ GfC V, κo g ∈ GfC V) ∧
      (∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
        (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      ∀ (S : HSp D) g (y : WO S V), IsHalf e y → actO S V 1 (κo g) y = y := by
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hec : cA D e * e = 0 := by rw [mul_comm]; exact hc
  obtain ⟨r, hr⟩ := GlobalTheory.PlaceModelSum.exists_add_conj e
  have hr1 : algebraMap (AF D.host.F) (AE D) (1 - r) = 1 - algebraMap (AF D.host.F) (AE D) r := by
    simp only [map_sub, map_one]
  have hrr : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r =
      algebraMap (AF D.host.F) (AE D) r := by
    rw [hr, add_mul, mul_add, mul_add, he, hce, hc, hec, add_zero, zero_add]
  have hrr' : algebraMap (AF D.host.F) (AE D) (1 - r) * algebraMap (AF D.host.F) (AE D) (1 - r) =
      algebraMap (AF D.host.F) (AE D) (1 - r) := by
    rw [hr1, sub_mul, mul_sub, mul_sub, hrr, mul_one, one_mul, mul_one, sub_self, sub_zero]
  have hbe0 : algebraMap (AF D.host.F) (AE D) (1 - r) * e = 0 := by
    rw [map_sub, map_one, hr, sub_mul, add_mul, he, hec, one_mul, add_zero, sub_self]
  have hbe : (1 - algebraMap (AF D.host.F) (AE D) r) * e = 0 := by rw [← hr1]; exact hbe0
  obtain ⟨κe, hκe⟩ := exists_cut_hom V r hrr
  obtain ⟨κo, hκo⟩ := exists_cut_hom V (1 - r) hrr'
  rw [hr1] at hκo
  have hκo' : ∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
      (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun g => by
    rw [hκo, ← hr, sub_sub_cancel]
  refine ⟨κe, κo, fun g => ?_, fun g i j => ?_, fun g hg => ?_, hκo', fun S g y hy => ?_⟩
  · refine Subtype.ext (Units.ext ?_)
    change Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V (κe g * κo g)
    rw [GlobalTheory.AdelicLatMove.mt_mul, hκe, hκo, cut_mul_cut hrr]
  · have e1 : Formalism.L2.Theta.mt V (κe g) - 1 = algebraMap (AF D.host.F) (AE D) r • (Formalism.L2.Theta.mt V g - 1) := by
      rw [hκe, smul_sub, sub_smul, one_smul]; abel
    rw [e1, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hr, hrr]
  · have e1 : matHom V (κo g) = GlobalTheory.UnitaryIdemCut.cutGL _ hrr' (matHom V g) :=
      Units.ext (by rw [GlobalTheory.UnitaryIdemCut.cutGL_val, hr1]; exact hκo g)
    rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, e1]
    exact GlobalTheory.UnitaryIdemCut.bc_cutGL_eq_one _ _ _ ((GlobalTheory.UnitaryIdemCut.mem_GfC_iff _ _).1 hg)
  · exact actO_cut_half hbe (hκo g) hy

theorem halfInd_move {S T : HSp D} {e : AE D} (Λ : AddSubgroup (WO S T)) {h he ho : GA D T} (hs : h = he * ho)
    (hfix : ∀ w, IsHalf e w → actO S T 1 ho w = w) (hfix' : ∀ w, IsHalf e w → actO S T 1 ho⁻¹ w = w) (x : WO S T) :
    halfInd e Λ (actO S T 1⁻¹ he⁻¹ x) = halfInd e Λ (actO S T 1⁻¹ h⁻¹ x) := by
  apply halfInd_congr
  have e0 : actO S T 1⁻¹ (ho⁻¹ * he⁻¹) x = actO S T 1 ho⁻¹ (actO S T 1⁻¹ he⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, one_mul]
  rw [hs, mul_inv_rev, e0]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hfix' _ h2]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e2 := hfix _ h2
    rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one] at e2
    rw [← e2] at h1 h2
    exact ⟨h1, h2⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.ExpansionInvariance

theorem vac_move_low : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      ∃ c : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c • Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t htU Φ β j hj k hk e he Tm hTm
  have hIn : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hDef : GlobalTheory.FunObj.DefPair D.R.m (Pair.top t j : Pair T) := by
    show j + 1 ≤ D.R.m
    omega
  have hW := W.om_is _ hIn
  have hvac := S.Z.vac_is _ hDef
  have hSd : IsSelfDualC (G.pS (.top t j : Pair T)) (S.N.latS (.top t j)) :=
    S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hTd : IsSelfDualC (G.pT (.top t j : Pair T)) (S.N.latT (.top t j)) :=
    S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have kS : (G.pS (.top t j : Pair T)).SigOK := (G.isV (X := .top j) (show j ≤ D.R.m by omega) (by simp)).sigOK
  have kT : (G.pT (.top t j : Pair T)).SigOK :=
    (G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) (by simp)).sigOK
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  obtain ⟨κe, κo, hsplit, hSupp, hFin, hmt, hfix⟩ := GlobalTheory.VacMoveLow.exists_cut_pair (G.V (.top (j + 1))) he' he.2
  set h : GA D (G.V (.top (j + 1))) := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    GA D (G.V (.top (j + 1)))) with hh_def
  have hoLat := GlobalTheory.CutStdLat.keep_stdLatO S htU j hj k hk e he (κo h) (hmt h)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.VacMoveLow.om_keep_vac hW W.θ_is kS kT
    (fun τ => W.cart_is (.top j) (show j ≤ D.R.m by omega) τ)
    (fun τ => W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m by omega) τ) hSd hTd hvac
    (hFin h ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2) hoLat
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.VacMoveLow.om_base_law hW hSd hTd he hvac.2.theta hvac.2.lat hTm (hSupp h)
  refine ⟨c₁ * c₂, ?_⟩
  rw [show ((1 : GA D (G.pS (.top t j : Pair T))), h) = ((1 : GA D (G.pS (.top t j : Pair T))), κe h) * (1, κo h) by
    rw [Prod.mk_mul_mk, mul_one, ← hsplit], map_mul, Module.End.mul_apply, hc₁, map_smul, hc₂, smul_smul]
  congr 2
  funext x
  refine GlobalTheory.VacMoveLow.halfInd_move _ (hsplit h) (fun w hw => hfix _ h w hw) (fun w hw => ?_) x
  rw [← map_inv]
  exact hfix _ h⁻¹ w hw

end GlobalTheory.ExpansionInvariance
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      ∃ c : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c • Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  first | exact @GlobalTheory.ExpansionInvariance.vac_move_low | exact GlobalTheory.ExpansionInvariance.vac_move_low | (intros; apply GlobalTheory.ExpansionInvariance.vac_move_low <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacMoveHigh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_move_high : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      ∃ c : ℂ, W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c • Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hinf : infPart D (e + cA D e) = 0 := by
    rw [RingHom.map_add (f := _), ho.infPart_eq, infPart_cA ho.infPart_eq, add_zero]
  have hgfin : g ∈ GfC (G.V (.top (j + 1))) := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hg1fin : cutPart (e + cA D e) _ g ∈ GfC (G.V (.top (j + 1))) :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF _ hinf (suppAt_cutPart hee hce _ g)
  have hg2fin : cutPart (1 - (e + cA D e)) _ g ∈ GfC (G.V (.top (j + 1))) := by
    have e1 : cutPart (1 - (e + cA D e)) _ g = (cutPart (e + cA D e) _ g)⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← cutPart_mul hf]
    rw [e1]
    exact mul_mem (inv_mem hg1fin) hgfin
  have hΛ : ∀ u, u ∈ stdLatO S (.top t (j + 1)) ↔
      ∃ u₀ ∈ stdLatO S (.top t (j + 1)), u = actO _ _ (cutPart (1 - (e + cA D e)) _ g) 1 u₀ :=
    GlobalTheory.T.offPlacesPart_movedLevel_keeps_standardHomLattice S ht j hj k hk e he
  have hV := G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hV' := G.isV (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ hW W.θ_is _ _ _ _ _ _ _ _ (cutPart (1 - (e + cA D e)) _ g) 1
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg2fin τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ (one_mem _) τ, Matrix.mul_one, Matrix.one_mul]) hΛ _ hvac
  obtain ⟨c₂, -, hc₂⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ hV.sigOK hV'.sigOK
    (W.cart_is _ (show j + 1 ≤ D.R.m by omega)) (W.cart_is _ (show j + 1 + 1 ≤ D.R.m by omega)) _ _ hS hT _ _ hvac hv'
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  refine ⟨c₂ * ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)), ?_⟩
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = c₂ • W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hc₂, map_smul]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        conv_rhs => rw [mul_smul, ← map_smul]
        congr 2
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionProductInvariantInnerVertexLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem product_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}
    {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ (w : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j', movedCol S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) j' (w j')) *
          ∏ i, S.Z.vec (d.2 i) (z i)) =
        τ.sum fun d a => a * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL₀ hde hcc ht hβ hexp hvec j hj k hk w z
  classical
  have hexp' := hexp
  obtain ⟨e, he, hsupp, -⟩ := hexp
  by_cases hτ : τ = 0
  · subst hτ; simp
  obtain ⟨d₀, hd₀⟩ : ∃ d, d ∈ τ.support := by
    obtain ⟨d, hd⟩ := Finsupp.ne_iff.1 hτ
    exact ⟨d, Finsupp.mem_support_iff.2 (by simpa using hd)⟩
  have hmc : ∀ j' : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j')) 1
      (S.Z.vac (.top t j')) Tm := fun j' => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).1 j'
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).1 j').2.1]
    exact hTm
  have hmr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.chi i D.R.m)) 1
      (S.Z.vac (.chi i D.R.m)) Tm := fun i => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).2 i
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).2 i).2.1]
    exact hTm
  choose Tc hTc using hmc
  choose Tr hTr using hmr
  have hvc : ∀ d ∈ τ.support, ∀ j', S.Z.vec (d.1 j') = Tc j' (d.1 j').fn := fun d hd j' =>
    vec_eq_model S _ ((hsupp d hd).1 j').2.2 ((hvec d hd).1 j') _ (by rw [((hsupp d hd).1 j').2.1]; exact hTc j')
  have hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn := fun d hd i =>
    vec_eq_model S _ ((hsupp d hd).2 i).2.2 ((hvec d hd).2 i) _ (by rw [((hsupp d hd).2 i).2.1]; exact hTr i)
  set g : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hg
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent S ht (Φ := Φ) (β := β) j hj k hk e he (Tc ⟨j, by omega⟩) (hTc ⟨j, by omega⟩)
  obtain ⟨c₂, hc₂⟩ := vac_move_high S ht j hj k hk e he (Tc ⟨j + 1, hj⟩) (hTc ⟨j + 1, hj⟩)
  have hla : ∀ X : Node, DefNode D.R.m X → (∀ i, X ≠ .grid 0 i) → X.InRange D.R.m →
      Submodule.IsFullLattice D.host.E (G.Λ X) := fun X _ h0 hX =>
        GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (G.isV hX h0).sd
  have hsb : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsSBHalf e (stdLatO S (.top t j')) (d.1 j').fn := fun d hd j' => by
    have h1 := (d.1 j').sb
    rw [((hsupp d hd).1 j').2.1] at h1
    have hj₀ : (j' : ℕ) ≤ D.R.m := Nat.le_of_lt j'.2
    have hj₁ : (j' : ℕ) + 1 ≤ D.R.m := j'.2
    letI := hla (.top j') hj₀ (by simp) hj₀
    letI := hla (.top (j' + 1)) hj₁ (by simp) hj₁
    letI : Submodule.IsFullLattice D.host.E (S.N.latS (.top t j')) :=
      GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (S.N.selfDual (X := .top j') hj₀)
    letI : Submodule.IsFullLattice D.host.E (S.N.latT (.top t j')) :=
      GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (S.N.selfDual (X := .top (j' + 1)) hj₁)
    exact VecEx.isSBHalf_of_lattices inferInstance inferInstance inferInstance inferInstance
      (GlobalTheory.PlaceDatum.infPart_idemSum he) h1
  have hmv : ∀ d ∈ τ.support, ∀ j', movedCol S d j hj g j' =
      (Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j') •
        Tc j' (movedFn S d j hj g j') := fun d hd j' => by
    rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
    · simp only [movedCol, movedFn, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t (j + 1))) (S.N.latT (.top t (j + 1))) e
        (S.Z.vac (.top t (j + 1))) _ (W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j + 1, hj⟩) _ _ c₂ hc₂ _ (hsb d hd ⟨j + 1, hj⟩)
    rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t j)) (S.N.latT (.top t j)) e
        (S.Z.vac (.top t j)) _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j, by omega⟩) _ _ c₁ hc₁ _ (hsb d hd ⟨j, by omega⟩)
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_of_ne h2, Pi.one_apply, one_smul]
      exact hvc d hd j'
  have hprod : ∏ j' : Fin D.R.m, Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j' =
      c₁ * c₂ := by
    have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := fun h => by simp [Fin.ext_iff] at h
    rw [Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_update_of_mem (by simp [hne])]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    ring
  let X : Fin D.R.m ⊕ Fin D.R.m → Type := Sum.elim (fun j' => WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
    fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  let Tt : ∀ a, (X a → ℂ) →ₗ[ℂ] (X a → ℂ) := fun a => match a with
    | .inl j' => Tc j'
    | .inr i => Tr i
  let F : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => (d.1 j').fn
    | .inr i => (d.2 i).fn
  let F' : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => movedFn S d j hj g j'
    | .inr i => (d.2 i).fn
  let yy : ∀ a, X a := fun a => match a with
    | .inl j' => w j'
    | .inr i => z i
  have key := sum_prod_map_congr Tt τ.support τ.support (fun d => τ d) (fun d => τ d * (c₁ * c₂)) F F' (fun x => by
    have := GlobalTheory.T.unfoldingExpansion_productFunction_localInvariant S hL₀ hde hcc ht hβ hexp' j hj k hk e he (fun d hd j' => ((hsupp d hd).1 j').2.1) _ _ (hTc ⟨j, by omega⟩)
      (hTc ⟨j + 1, hj⟩) c₁ c₂ hc₁ hc₂ (fun j' => x (.inl j')) (fun i => x (.inr i))
    simp only [Finsupp.sum] at this
    simp only [Fintype.prod_sum_type]
    refine (Finset.sum_congr rfl fun d _ => ?_).trans (this.trans (Finset.sum_congr rfl fun d _ => ?_))
    · exact (mul_assoc _ _ _).symm
    · exact mul_assoc _ _ _) yy
  simp only [Fintype.prod_sum_type] at key
  have hL : (∑ d ∈ τ.support, τ d * (∏ j', movedCol S d j hj g j' (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * (c₁ * c₂) * ((∏ j', Tc j' (movedFn S d j hj g j') (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by
      simp only [hmv d hd, hvr d hd, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, hprod]; ring
  have hR : (∑ d ∈ τ.support, τ d * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * ((∏ j', Tc j' (d.1 j').fn (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by simp only [hvc d hd, hvr d hd]; ring
  simp only [Finsupp.sum]
  rw [hL, hR]
  exact key

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionProductInvariantInnerVertexLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_product_invariant_inner_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}
    {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ (w : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j', movedCol S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) j' (w j')) *
          ∏ i, S.Z.vec (d.2 i) (z i)) =
        τ.sum fun d a => a * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i) := by
  first | exact @GlobalTheory.ExpansionInvariance.product_invariant | exact GlobalTheory.ExpansionInvariance.product_invariant | (intros; apply GlobalTheory.ExpansionInvariance.product_invariant <;> assumption)
end

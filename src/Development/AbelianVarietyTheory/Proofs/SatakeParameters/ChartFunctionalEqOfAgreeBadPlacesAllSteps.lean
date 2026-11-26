module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeVectorLocalMemDualBaseCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeVectorLocalMemDualBaseCompletion
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

open Formalism.MainNotions.G.KAat Matrix

namespace GlobalTheory.CompanLocal

theorem mem_latS_dual_of_mem_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  intro R F E _ _ _ _ _ _ N sp J crd a x hx hJ Lb hfin hspan hint v u hu
  set y := bc (prV (E := E) v) x with hy_def
  simp only [latCo, mvL, Submodule.mem_map] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  let locV : (Fin N → E) → (Fin N → E ⊗[F] v.adicCompletion F) := fun z i => inclE (F := F) (v.adicCompletion F) (z i)
  have hcomp : (fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x)
      (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) l)) =
      ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ locV w := by
    have h1 : pullV (F := F) (ratA F crd * x)
        (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) =
        ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
          (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (w i)) := by
      unfold pullV
      rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv]
      congr 1
      have := bc_mulVec (F := F) crd⁻¹ (toLE crd w)
      refine this.trans ?_
      funext i
      show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (toLE crd⁻¹ (toLE crd w) i) = _
      rw [toLE_inv_apply']
    rw [h1, GlobalTheory.LocCarry.prV_mulVec, ← GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  have hL : Submodule.IsFullLattice E (latAd x Lb) := by
    rw [hlat]; exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hLb : Submodule.IsFullLattice E Lb := {
    toIsLattice := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.mp hfin)
    span_eq_top := hspan }
  have hyU : y ∈ UPts sp.cm.sig J (v.adicCompletion F) := Formalism.UG.P.afsplit_bc_mem _ J v x hx
  have hyl := fun z => GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v z
  have hdm := GlobalTheory.DualCompletion.dual_move F E sp.cm.sig N J v (latAd x Lb) Lb y hJ hL hLb hyU hyl
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono (fun z hz => Submodule.subset_span (hint z hz)))
  have hmem : ∀ (Λ : Submodule (𝓞 E) (Fin N → E)) z, z ∈ Λ → locV z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ :=
    fun Λ z hz => Submodule.subset_span ⟨z, hz, rfl⟩
  simp only [compan] at hw
  obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
  have hw2' : w2 ∈ Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J (latAd x Lb) := Submodule.smul_le_right hw2
  have hadd : locV (w1 + w2) = locV w1 + locV w2 := by funext i; simp [locV, map_add (f := _)]
  have key : ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ
      locV (w1 + w2) ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) := by
    rw [hadd, Matrix.mulVec_add]
    exact add_mem (hsub ((hyl _).1 (hmem _ _ hw1))) ((hdm _).1 (hmem _ _ hw2'))
  exact ⟨⟨_, key⟩, hcomp.symm⟩

end GlobalTheory.CompanLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeVectorLocalMemDualBaseCompletionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionLatticeVector_local_mem_dualBaseCompletion : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  first | exact @GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | exact GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | (intros; apply GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllSteps
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwV.FnlAwayCpl

section Loc
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem f_eq_on_at {d d₁ : Deco E n ST SG} (hd : d.Ok) (hd₁ : d₁.Ok) (P : ST) (hat : d₁.at P.1 = d.at P.1)
    (h : ∀ w ∈ d.N, w ∈ d₁.N → d₁.f P w = d.f P w) : ∀ y ∈ d.at P.1, d₁.f P y = d.f P y := by
  intro y hy
  have hy₁ : y ∈ d₁.at P.1 := hat ▸ hy
  obtain ⟨s, hs, hsy⟩ := (mem_locP P.1 d.N y).1 hy
  obtain ⟨s₁, hs₁, hsy₁⟩ := (mem_locP P.1 d₁.N y).1 hy₁
  have hw : (s * s₁) • y ∈ d.N := by
    rw [mul_comm, mul_smul]; exact d.N.smul_mem s₁ hsy
  have hw₁ : (s * s₁) • y ∈ d₁.N := by
    rw [mul_smul]; exact d₁.N.smul_mem s hsy₁
  have e := h _ hw hw₁
  rw [hd₁.f_smul P _ y hy₁, hd.f_smul P _ y hy] at e
  have hne : Ideal.Quotient.mk P.1.asIdeal (s * s₁) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hm => (P.1.isPrime.mem_or_mem hm).elim hs hs₁
  letI := Ideal.Quotient.field P.1.asIdeal
  exact mul_left_cancel₀ hne e
end Loc

section Pull
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem prV_pullV_congr (v : HeightOneSpectrum (𝓞 F)) {g g₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : bc (prV (E := E) v) g₁ = bc (prV (E := E) v) g) (u : Fin N → E) :
    (fun l => prV (E := E) v (pullV (F := F) g₁ u l)) = fun l => prV (E := E) v (pullV (F := F) g u l) := by
  have h' : bc (prV (E := E) v) g₁⁻¹ = bc (prV (E := E) v) g⁻¹ := by rw [map_inv, map_inv, h]
  funext l
  unfold pullV
  rw [RingHom.map_mulVec, RingHom.map_mulVec]
  have h2 : ((g₁⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) =
      ((g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := congrArg Units.val h'
  rw [h2]
end Pull
end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV.FnlAwayCpl
section Z
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem exists_latS_pullV (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (hint : ∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb)
    (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E) (hu : u ∈ latCo sp J crd a x Lb) :
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) :=
  GlobalTheory.T.companionLatticeVector_local_mem_dualBaseCompletion sp J crd a x hx hJ Lb hfin hspan hint v u hu
end Z
end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV.FnlAwayCpl

theorem exists_place {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    {A : AdData t u μ St} {dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt} {a : 𝓞 D.host.E}
    (hTie : AdTie A dtU a) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) ∧
      (∀ j (hj : j ≤ D.R.m), (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) ∧ v ∈ plUnder D.host.F (ssRec t u μ) := by
  classical
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Primes.vT divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : (((D.mem u).A.T : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.T_rec u, ← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    have := (mem_seamP t.seam P.1 _).2 hT
    rwa [map_natCast] at this
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [← t.T_rec u]
    exact_mod_cast (t.pr_ok.T_prime (t.word u)).ne_zero
  have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hTQ
  refine ⟨⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _,
    fun h0 => hT0 (by rw [h0] at hTv; exact (Submodule.mem_bot _).1 hTv)⟩, rfl, fun j hj => ?_, ?_⟩
  · rw [hTie.T_eq j hj]; exact hTv
  · have hSS : P.1 ∈ (t.rd u μ).SS := by
      rw [((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1]
      exact Finset.mem_union_left _ P.2
    exact ⟨_, (mem_ssRec t u μ P.1).2 hSS, rfl⟩

end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV

open _root_.Formalism.L2.Forms


set_option maxHeartbeats 2000000 in
open FnlAwayCpl in
theorem fnl_eq_of_away_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hag P hat
  obtain ⟨v, hov, hTv, hvU⟩ := exists_place hTie P
  have hfnl := hp.fnl P v (hTv j hj) hov
  have hfnl₁ := hp₁.fnl P v (hTv j hj) hov
  refine f_eq_on_at p.deco.2 p₁.deco.2 P hat fun w hw hw₁ => ?_
  have hu : (fun l => t.seam.iE (w l)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x.1 ((St j hj).K β).lev.Lb := by
    rw [← hp.lat]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  obtain ⟨z, hz⟩ := exists_latS_pullV D.sp (gramN D j hj) (A.crd j hj) a x.1 x.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) ((St j hj).K β).lev.Lb
    ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hu
  have hg : bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd j hj) * x₁.1) = bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd j hj) * x.1) := by
    rw [map_mul, map_mul, hag v hvU]
  rw [hfnl₁ w hw₁ z (hz.trans (prV_pullV_congr v hg _).symm), hfnl w hw z hz]

end GlobalTheory.TwV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllStepsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_badPlaces_allSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  first | exact @GlobalTheory.TwV.fnl_eq_of_away_cpl | exact GlobalTheory.TwV.fnl_eq_of_away_cpl | (intros; apply GlobalTheory.TwV.fnl_eq_of_away_cpl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwist
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SelfTwWeak

theorem trace_of_charpoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (N : Matrix (Fin a) (Fin a) (Qbar l))
    (S : Multiset ℂ) (h : N.charpoly.map ι.toRingHom = (S.map fun b => X - C b).prod) : ι N.trace = S.sum := by
  have h1 := congrArg Polynomial.nextCoeff h
  rw [nextCoeff_map ι.injective, multiset_prod_X_sub_C_nextCoeff] at h1
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, map_neg]
  change -(ι.toRingHom N.charpoly.nextCoeff) = _
  rw [h1, neg_neg]

theorem algSat_mul (n q : ℕ) (B : Multiset ℂˣ) (e : ℂˣ) :
    (UpperTheory.V.Af.algSat n q (B.map (· * e))).sum = (e : ℂ) * (UpperTheory.V.Af.algSat n q B).sum := by
  simp only [UpperTheory.V.Af.algSat]
  simp
  simp only [mul_assoc, Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]
  ring

theorem selfTw_mul_trace_inv (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a)
    (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Weak π ι r) (η : HChar K)
    (hη : UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
      IsPlaceOver A v → IsFrob A (normV v) σ →
        (η.val v : ℂ) * ι (r σ⁻¹).val.trace = ι (r σ⁻¹).val.trace := by
  obtain ⟨-, -, hev⟩ := hr
  filter_upwards [hev, hη] with v hv1 hv2 A σ hA hσ
  obtain ⟨B, hB, hF⟩ := hv1
  obtain ⟨-, B', hB', hBη⟩ := hv2
  have hBB : B' = B := hB'.unique hB
  subst hBB
  have ht := trace_of_charpoly ι _ _ ((hF A hA).2 σ hσ)
  rw [ht]
  conv_rhs => rw [← hBη]
  rw [algSat_mul]

theorem ne_one_of_moves (Ω : Type) [Field Ω] (K : Type) [Field K] [Algebra K Ω] (M : Type) [Field M] [Algebra M Ω]
    [Algebra K M] [IsScalarTower K M Ω] [FiniteDimensional K M] [IsGalois K M] (hp : (Module.finrank K M).Prime)
    (χ : G K Ω →* ℂˣ) (hne : χ ≠ 1)
    (h3 : ∀ g : G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1) (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : χ g ≠ 1 := by
  classical
  let ρ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hfix : ∀ k : G K Ω, ρ k = 1 → ∀ x : M, k (algebraMap M Ω x) = algebraMap M Ω x := by
    intro k hk x
    have := AlgEquiv.restrictNormal_commutes k M x
    rw [← this]
    change algebraMap M Ω (ρ k x) = _
    rw [hk]; rfl
  haveI : Fact (Nat.card (M ≃ₐ[K] M)).Prime := ⟨by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hp)
      | (convert hp using 1; rw [Nat.card_eq_fintype_card]; convert IsGalois.card_aut_eq_finrank K M)⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((χ.ker).map ρ) with hH | hH
  · intro hχg
    obtain ⟨x, hx⟩ := hg
    have : ρ g ∈ (χ.ker).map ρ := ⟨g, hχg, rfl⟩
    rw [hH, Subgroup.mem_bot] at this
    exact hx (hfix g this x)
  · exfalso
    apply hne
    ext k
    have : ρ k ∈ (χ.ker).map ρ := by rw [hH]; trivial
    obtain ⟨k', hk', hkk⟩ := this
    have h1 : χ (k * k'⁻¹) = 1 := h3 _ (hfix _ (by rw [map_mul, map_inv, hkk, mul_inv_cancel]))
    rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk', inv_one, mul_one] at h1
    simp [h1]

theorem inv_moves {Ω K M : Type} [Field Ω] [Field K] [Algebra K Ω] [Field M] [Algebra M Ω] (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : ∃ x : M, g⁻¹ (algebraMap M Ω x) ≠ algebraMap M Ω x := by
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, fun h => hx ?_⟩
  have e : (g * g⁻¹) (algebraMap M Ω x) = algebraMap M Ω x := by rw [mul_inv_cancel]; rfl
  rw [AlgEquiv.mul_apply, h] at e
  exact e

theorem trace_eq_zero_of_selfTw : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] [IsGalois K M], (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ η : HChar K, UpperTheory.V.Published.IsNormChar M η → UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η → ∀ g : G K Ω, (∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) → (r g).val.trace = 0 := by
  intro Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ _ hp l _ ι a π r hr η hη hst g hg
  obtain ⟨χ, hχo, hχ1, hχf⟩ :=
    GlobalTheory.HeckeToGal.exists_galChar_of_finite_order Ω K η (Module.finrank K M) hp.pos hη.2.1
  have hχne : χ ≠ 1 := fun h => hη.1 (hχ1 h)
  have h3 := GlobalTheory.trivial_on_ext_of_frob_eq_normChar Ω K M η hη χ hχo hχf
  have hne := ne_one_of_moves Ω K M hp χ hχne h3 g⁻¹ (inv_moves g hg)
  have h1 := selfTw_mul_trace_inv Ω K l ι a π r hr η hst
  have hcont : Continuous r := hr.1
  have hUo : IsOpen {k : G K Ω | χ k ≠ 1} := by
    have hc : IsClosed (χ.ker : Set (G K Ω)) := Subgroup.isClosed_of_isOpen _ hχo
    have : {k : G K Ω | χ k ≠ 1} = (χ.ker : Set (G K Ω))ᶜ := by ext k; simp [MonoidHom.mem_ker]
    rw [this]; exact hc.isOpen_compl
  have hT := Filter.eventually_cofinite.1 (h1.and hχf)
  have hD := GlobalTheory.frob_dense_off_finite K Ω _ hT
  have hc : Continuous fun k : G K Ω => (r k⁻¹).val.trace :=
    (Units.continuous_val.comp (hcont.comp continuous_inv)).matrix_trace
  have hZ : IsClosed {k : G K Ω | (r k⁻¹).val.trace = 0} := isClosed_eq hc continuous_const
  have hsub := hD.open_subset_closure_inter hUo hne
  have key : (r g⁻¹⁻¹).val.trace = 0 := by
    refine closure_minimal ?_ hZ hsub
    rintro σ ⟨hσU, v, hv, A, hA, hσ⟩
    simp only [Set.mem_setOf_eq, not_not] at hv
    have e1 := hv.1 A σ hA hσ
    have e2 := hv.2 A σ hA hσ
    have hv1 : (η.val v : ℂ) ≠ 1 := by
      intro h; apply hσU; rw [e2]; exact Units.val_eq_one.1 h
    have : ι (r σ⁻¹).val.trace = 0 := by
      have h0 : ((η.val v : ℂ) - 1) * ι (r σ⁻¹).val.trace = 0 := by rw [sub_mul, e1, one_mul, sub_self]
      exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hv1)
    exact (map_eq_zero_iff ι ι.injective).1 this
  rwa [inv_inv] at key

end GlobalTheory.SelfTwWeak

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwistStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_eq_zero_off_subgroup_of_selfTwist : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] [IsGalois K M], (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ η : HChar K, UpperTheory.V.Published.IsNormChar M η → UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η → ∀ g : G K Ω, (∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) → (r g).val.trace = 0 := by
  first | (exact @GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw) | (exact GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw) | (intros; apply GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw  <;> assumption)
end
end

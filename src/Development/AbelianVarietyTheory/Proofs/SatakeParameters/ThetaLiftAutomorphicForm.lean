module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaRead

open MeasureTheory Formalism.BasicNotions.TH _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
  Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.ThetaTri
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pair

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem ipM_proj (hM : R.IsModels) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) {S U : MMap (R.MW i (sg0 D A))}
    (hS : S ∈ R.Wall i (sg0 D A)) (hU : U ∈ R.Wall i (sg0 D A)) (hfix : ∀ v, R.eWf i (sg0 D A) (S v) = S v) :
    ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S (postOn _ (R.eWf i (sg0 D A)) U) =
      ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S U ∧
    ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S U c := by
  obtain ⟨hinj, hr, hip⟩ := hM.HW i (sg0 D A)
  obtain ⟨a, rfl⟩ : S ∈ LinearMap.range (R.HW i (sg0 D A)).e := hr ▸ hS
  obtain ⟨b, rfl⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := hr ▸ hU
  refine ⟨?_, GlobalTheory.LiftLower.IsMultIP₂ (R.HW i (sg0 D A)) hip a b⟩
  have he : ∀ x, (R.HW i (sg0 D A)).e (GlobalTheory.Hk3.eH R i x) = postOn _ (R.eWf i (sg0 D A)) ((R.HW i (sg0 D A)).e x) :=
    fun x => GlobalTheory.LiftLower.e_projH hM.gW i (sg0 D A) x
  have ha : GlobalTheory.Hk3.eH R i a = a := by
    apply hinj
    rw [he]
    exact MultilinearMap.ext fun v => hfix v
  have h1 : ⟪a, GlobalTheory.Hk3.eH R i b⟫_ℂ = ⟪a, b⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_left, GlobalTheory.LiftScalarL.adjoint_eH R hM hX i, ha]
  rw [hip, hip, he] at h1
  have hN : (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ρ _ => by exact_mod_cast (GlobalTheory.Mem.EasyInputs.dimOK D i (sg0 D A) ρ).ne'
  exact mul_left_cancel₀ hN h1

theorem mult_le_wall (F : Face D A) (b : Bool) (i : Fin D.R.m) :
    Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) ≤ R.Wall i (sg0 D A) :=
  GlobalTheory.PartDims.mult_le R.θ _ fun k hk => by
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.PartDims.mem_levi_flag_of_mem_parabolic (L := R.datWp i R.triv) rfl rfl (R.levL F b (sg0 D A)) hk
    exact ⟨h1, h2.trans h3.symm⟩

end Pair

section Unit

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

abbrev emb : LowT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => (lowT M τ).subtype

theorem integral_kUnit (hne : ∀ τ, lowT M τ ≠ ⊥) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T U : MMap M)
    (h : ∃ c, IsMultIP M μ 𝓕 T U c) :
    ∫ g in 𝓕, star (PiTensorProduct.lift T (emb M (kUnit M)) g) * PiTensorProduct.lift U (emb M (kUnit M)) g ∂μ =
      ipM M μ 𝓕 T U := by
  have hu : ∀ τ, ∃ u : ↥(lowT M τ), ‖((u : M.sm τ) : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 (hne τ)
    have h0 : (u : M.H τ) ≠ 0 := fun h => hu0 (Submodule.coe_eq_zero.1 h)
    refine ⟨((‖(u : M.H τ)‖⁻¹ : ℝ) : ℂ) • ⟨u, hu⟩, ?_⟩
    simp only [Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)
  let v : M.Vec := fun τ =>
    ((Classical.epsilon fun u : ↥(lowT M τ) => ‖((u : M.sm τ) : M.H τ)‖ = 1 : ↥(lowT M τ)) : M.sm τ)
  have hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1 := fun τ => Classical.epsilon_spec (hu τ)
  have hk : emb M (kUnit M) = PiTensorProduct.tprod ℂ v := PiTensorProduct.map_tprod _ _
  rw [hk, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod, (ipM_spec M μ 𝓕 T U h v v).2]
  simp [inner_self_eq_norm_sq_to_K, hv]

theorem emb_eq_zero {τ : D.what₂.Tau} (h : lowT M τ = ⊥) : emb M = 0 := by
  classical
  ext v
  have : (lowT M τ).subtype (v τ) = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (v τ).2)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  exact MultilinearMap.map_coord_zero _ τ this

theorem integral_zero_right (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T U : MMap M) (hU : U = 0) (k : SmT M) :
    ipM M μ 𝓕 T U = ∫ g in 𝓕, star (PiTensorProduct.lift T k g) * PiTensorProduct.lift U k g ∂μ := by
  subst hU
  choose s hs using GlobalTheory.Mem.EasyInputs.smAll D V S M
  have hs0 : ∏ τ, ⟪(s τ : M.H τ), (s τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hs τ (Submodule.coe_eq_zero.1 h)
  have hz : IsMultIP M μ 𝓕 T 0 0 := by
    intro v v'; simp
  rw [hasPeterssonInner_unique _ _ _ _ _ s hs0 (ipM_spec _ _ _ _ _ ⟨_, hz⟩) hz]
  simp

end Unit

theorem lift_post {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (U : MMap M) :
    PiTensorProduct.lift (postOn M L U) = L ∘ₗ PiTensorProduct.lift U := by
  ext v
  simp [postOn]

section Row

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)


set_option maxHeartbeats 1000000 in
theorem ipM_theta {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) (y : D.what₂.Mj (j.1 + 1))
    (T T' : MMap (X.R.MW j (sg0 D X.A))) (hT : PiTensorProduct.lift T = (X.IL.jMj j y).1)
    (hT' : PiTensorProduct.lift T' = (X.IL.jMj j (D.what₂.thetaP μ (j.1 + 1) x)).1) :
    ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) T T' =
      ∫ g in X.R.fdW j, star (PiTensorProduct.lift T (emb _ (kUnit (X.R.MW j (sg0 D X.A)))) g) *
        (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
          (X.R.ptP j (X.tupT μ) (X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A))) (X.fn hμ j x h))) ∂(X.R.νV j (X.tupT μ)))
        ∂(X.R.νW j) := by
  have hM := X.given.core.models
  obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 μ hμ j x
  have hth := X.recR.tied.lift.theta μ hμ j x w (X.fire.1 _ hμ j) hw1 hw2 hw3
  obtain ⟨U, hU, hUw⟩ := hw1
  have hUw' : PiTensorProduct.lift U = w := hUw
  obtain ⟨T₀, hT₀, hT₀y⟩ := (X.IL.jMj j y).2
  have hTT : T₀ = T := PiTensorProduct.lift.injective (hT₀y.trans hT.symm)
  subst hTT
  obtain ⟨hT1, hT2⟩ := (mem_goodPart _ _ _ _ _ _).1 hT₀
  have hT'U : T' = postOn (X.R.MW j (sg0 D X.A)) (X.R.eWf j (sg0 D X.A)) U := by
    apply PiTensorProduct.lift.injective
    rw [hT', hth, ← hUw']
    exact (lift_post (X.R.MW j (sg0 D X.A)) _ U).symm
  have hin : ∀ g, (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
      (X.R.ptP j (X.tupT μ) (X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A))) (X.fn hμ j x h))) ∂(X.R.νV j (X.tupT μ))) =
      PiTensorProduct.lift U (emb _ (kUnit (X.R.MW j (sg0 D X.A)))) g := by
    intro g
    have e1 := (X.fire.1 _ hμ j).eq (X.IL.jMt μ hμ j x) (kUnit (X.R.MW j (sg0 D X.A))) g
    rw [← hw2, ← hUw'] at e1
    exact e1.symm
  obtain ⟨p1, p2⟩ := ipM_proj X.R hM X.given.irr j (mult_le_wall X.R X.F false j hT1) (mult_le_wall X.R X.F false j hU) hT2
  simp only [hin]
  rw [hT'U]
  refine p1.trans ?_
  by_cases hne : ∀ τ, lowT (X.R.MW j (sg0 D X.A)) τ ≠ ⊥
  · exact (integral_kUnit _ hne _ _ _ _ p2).symm
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have h0 := emb_eq_zero _ hτ
    have hw0 : w = 0 := X.fire.2.2 j w ⟨U, hU, hUw⟩
      ((congrArg (fun e => w ∘ₗ e) h0).trans (LinearMap.comp_zero _))
    have hU0 : U = 0 := PiTensorProduct.lift.injective (by rw [hUw', hw0, map_zero])
    exact integral_zero_right (X.R.MW j (sg0 D X.A)) _ _ _ _ hU0 _

end Row

section Forms

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : GlobalTheory.NJoin.RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}

theorem ext_pre {V : HSp D} {n : ℕ} (c : CoefA V) (hc : ∀ h ∈ GfC V, c.ρ h = 1) (PV : principalLevelFrame.RowPsi V n)
    (f : Bridge.Gf V → c.W) : c.ext (fun k => c.ext f (PV.ψ (preF PV k))) = c.ext f := by
  refine congrArg c.ext (funext fun k => ?_)
  have hex : ∃ κ, (finHom V).rangeRestrict (PV.ψ κ) = k := by
    obtain ⟨κ, hκ, e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V k
    obtain ⟨h, rfl⟩ := PV.onto κ hκ
    exact ⟨h, Subtype.ext e⟩
  have hp : (finHom V).rangeRestrict (PV.ψ (preF PV k)) = k := by
    unfold preF
    rw [dite_eq_left hex]
    exact hex.choose_spec
  show c.ρ (PV.ψ (preF PV k))⁻¹ (f ((finHom V).rangeRestrict (PV.ψ (preF PV k)))) = _
  rw [hp, hc _ (inv_mem (PV.into _)), Module.End.one_apply]


set_option maxHeartbeats 1000000 in
theorem ext_real (hV : X.R.models_cV) (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (x : D.what₂.Mt μ (j.1 + 1)) :
    (X.R.cV j).ext (fun k => (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x (A.a j * preF (A.PV j) k))) =
      X.fn hμ j x := by
  obtain ⟨z, hz⟩ : X.fn hμ j x ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := (X.IL.jMt μ hμ j x).2.1
  have hz' : (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e z) = X.fn hμ j x := hz
  have e : (fun k => (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x (A.a j * preF (A.PV j) k))) =
      fun k => X.fn hμ j x ((A.PV j).ψ (preF (A.PV j) k)) := by
    funext k
    refine (LinearEquiv.symm_apply_eq _).2 ((A.real μ hμ j x _).trans ?_)
    rw [inv_mul_cancel_left]
  refine (congrArg (X.R.cV j).ext e).trans ?_
  generalize X.fn hμ j x = φ at hz' ⊢
  subst hz'
  exact ext_pre _ (hV j).1 _ _

theorem ext_real_cast (hV : X.R.models_cV) (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (x : D.what₂.Mt μ k) :
    (X.R.cV j).ext (fun q => (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2).symm
        ((M μ k p1 p2).real x (A.a j * preF (A.PV j) q))) =
      X.fn hμ j (hk.symm ▸ x) := by
  subst hk
  exact ext_real hV A hμ j x

end Forms

section Canon

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)


end Canon

end GlobalTheory.ThetaRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibility
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigGoodTypes

theorem tw_inv_eta {D : D7} (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D) {a : ℕ} (ha : 1 ≤ a)
    (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hC := h4.2.2
  have h := h5.1 [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      show isoLoc D.nd D.naut (twistIso D.nd D.naut (twistIso D.nd D.naut [⟨a, π, 1⟩] D.naut.etaTinv) D.naut.etaT) w = _
      rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC,
        (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2])
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem sig_parC {D : D7} (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D) {i : D.nd.Loc} {P0 : D.naut.AV i}
    {Sig : List (Part D.naut.CG)}
    (hB : IsBCV D.nd D.naut i P0 (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv))
    (hg : goodSig D.nd D.naut Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
    (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
    rankIso D.nd D.naut Sig = D.R.r ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hB
  refine ⟨fun p hp => ?_, ?_, ?_, fun k v => ⟨((hg k).1.1 v).1, ((hg k).1.1 v).2.1⟩⟩
  · have hm : (⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
    obtain ⟨ha, hd, hc⟩ := h1 _ hm
    refine ⟨ha, hd, ?_⟩
    have := D.naut.csd_tw _ _ h0.2.1.1.1 hc
    rwa [tw_inv_eta h0 h4 h5 ha] at this
  · have hinj : Function.Injective (fun p : Part D.naut.CG => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) := by
      rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ h
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨⟨rfl, h⟩, rfl⟩ := h
      cases h
      rfl
    have hn : (Sig ++ [muPart D.nd D.naut i]).Nodup := by
      unfold twistIso at h2
      rw [List.map_map] at h2
      exact List.Nodup.of_map _ h2
    exact (hn.sublist (List.sublist_append_left _ _)).map hinj
  · have e1 : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).map (fun p => p.a * p.d) =
        (Sig ++ [muPart D.nd D.naut i]).map (fun p => p.a * p.d) := by
      unfold twistIso
      rw [List.map_map]
      rfl
    unfold rankIso at h3 ⊢
    rw [e1, List.map_append, List.sum_append] at h3
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at h3
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

theorem onMt_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a)
    (H : D.ntypes.onMt μ b D.ntypes.e0 (h ▸ f) = h ▸ f) : D.ntypes.onMt μ a D.ntypes.e0 f = f := by
  subst h
  exact H

end GlobalTheory.EigGoodTypes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastEqZeroOfDvdCard
namespace GlobalTheory.NormDivisibility

open NumberField IsDedekindDomain

theorem natCast_eq_zero_of_dvd_card {R : Type*} [CommRing R] [IsDomain R] [Finite R] {l : ℕ}
    (hl : l.Prime) (h : l ∣ Nat.card R) : (l : R) = 0 := by
  classical
  have := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R

  obtain ⟨n, hp, hc⟩ := FiniteField.card R (ringChar R)
  rw [Nat.card_eq_fintype_card, hc] at h
  rw [(Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h)]
  exact ringChar.Nat.cast_ringChar

theorem not_dvd_norm_of_not_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : Nat.Prime l)
    (w : HeightOneSpectrum (RingOfIntegers E))
    (hw : (l : RingOfIntegers E) ∉ w.asIdeal) : ¬ l ∣ Formalism.ConjugateSelfDual.normV w := by
  intro h
  have : Finite (RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  unfold Formalism.ConjugateSelfDual.normV at h
  have h0 := natCast_eq_zero_of_dvd_card (R := RingOfIntegers E ⧸ w.asIdeal) hl h
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0

end GlobalTheory.NormDivisibility
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.FrobOps
open Polynomial

theorem not_dvd_normV {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) (w : HeightOneSpectrum (𝓞 E))
    (h : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  first
  | exact @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | (apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem ..)

theorem norm_le_one {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (m : ℤ) (q e : ℕ) (hq : ¬ l ∣ q) :
    ‖ι.symm ((m : ℂ) / (q : ℂ) ^ e)‖ ≤ 1 := by
  rw [map_div₀, map_pow, map_intCast, map_natCast, norm_div, norm_pow]
  have h1 : ‖((q : ℕ) : Qbar l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq
  rw [h1, one_pow, div_one]
  exact IsUltrametricDist.norm_intCast_le_one _ m

theorem trace_pow_of_charpoly {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) (B : Multiset ℂ)
    (h : M.charpoly = (B.map fun b => X - C b).prod) (n : ℕ) : (M ^ n).trace = (B.map (· ^ n)).sum := by
  rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, h, Polynomial.roots_multiset_prod_X_sub_C]

theorem iota_trc {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : Γ →* GL (Fin a) (Qbar l))
    (s : Γ) (n : ℕ) :
    ι (trc r (s ^ n)) = ((((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom) ^ n).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.map_pow, trc, map_pow, Units.val_pow_eq_pow_val, Matrix.trace, Matrix.trace, map_sum]
  rfl

end GlobalTheory.FrobOps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.LabelTransport


open Classical in
theorem coset_transport {G H : Type} [Group G] [Group H] (ψ : G →* H) (T U J : Subgroup G) (K : Set H) (α : H)
    (R : Finset H) (hK : ∀ x, ψ x ∈ K ↔ x ∈ U ∧ x ∈ T) (hKr : ∀ k ∈ K, ∃ x, ψ x = k)
    (hJ : ∀ x ∈ T, x ∈ J ↔ x ∈ U) (pre : H → G) (hpre : ∀ γ ∈ R, ψ (pre γ) = γ ∧ pre γ ∈ T)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : H, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    ∃ Ds : Set G, (∀ x ∈ Ds, x ∈ T) ∧ (∀ x ∈ Ds, ∀ κ ∈ U, κ ∈ T → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧
      {c : G ⧸ J | ∃ x ∈ Ds, (x : G ⧸ J) = c}.Finite ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), (∀ x, ∀ κ ∈ J, κ ∈ T → F (x * κ) = F x) → ∀ g,
        (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ Ds, (x : G ⧸ J) = c then F (g * hc.choose) else 0) = ∑ γ ∈ R, F (g * pre γ) := by
  have hmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := hKr a ha
    obtain ⟨y, rfl⟩ := hKr b hb
    rw [← map_mul, hK]
    exact ⟨mul_mem ((hK x).1 ha).1 ((hK y).1 hb).1, mul_mem ((hK x).1 ha).2 ((hK y).1 hb).2⟩
  let Ds : Set G := {x | x ∈ T ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ψ x = k₁ * α * k₂}
  have hpD : ∀ γ ∈ R, pre γ ∈ Ds := fun γ hγ => ⟨(hpre γ hγ).2, by rw [(hpre γ hγ).1]; exact h1 γ hγ⟩
  have hrel : ∀ γ ∈ R, ∀ x ∈ T, ((pre γ : G ⧸ J) = (x : G ⧸ J) ↔ γ⁻¹ * ψ x ∈ K) := by
    intro γ hγ x hx
    have ht : (pre γ)⁻¹ * x ∈ T := mul_mem (inv_mem (hpre γ hγ).2) hx
    have e : ψ ((pre γ)⁻¹ * x) = γ⁻¹ * ψ x := by rw [map_mul, map_inv, (hpre γ hγ).1]
    rw [QuotientGroup.eq, hJ _ ht, ← e, hK]
    exact (and_iff_left ht).symm
  have hset : ∀ c : G ⧸ J, (∃ x ∈ Ds, (x : G ⧸ J) = c) ↔ c ∈ R.image fun γ => (pre γ : G ⧸ J) := by
    intro c
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 _ hx.2
      exact ⟨γ, hγ, (hrel γ hγ x hx.1).2 e⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨_, hpD γ hγ, rfl⟩
  refine ⟨Ds, fun x hx => hx.1, ?_, ?_, ?_⟩
  · rintro x ⟨hx, a, ha, b, hb, e⟩ κ hκ hκ'
    have hk : ψ κ ∈ K := (hK κ).2 ⟨hκ, hκ'⟩
    refine ⟨⟨mul_mem hx hκ', a, ha, _, hmul b hb _ hk, ?_⟩, ⟨mul_mem hκ' hx, _, hmul _ hk a ha, b, hb, ?_⟩⟩
    · rw [map_mul, e, mul_assoc]
    · rw [map_mul, e]; simp only [mul_assoc]
  · exact (R.image fun γ => (pre γ : G ⧸ J)).finite_toSet.subset fun c hc => (hset c).1 hc
  · intro W _ F hF g
    rw [finsum_eq_sum_of_support_subset (s := R.image fun γ => (pre γ : G ⧸ J))]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun γ hγ => ?_
        have hc : ∃ x ∈ Ds, (x : G ⧸ J) = (pre γ : G ⧸ J) := ⟨_, hpD γ hγ, rfl⟩
        rw [dite_eq_left hc]
        have hj : hc.choose⁻¹ * pre γ ∈ J := QuotientGroup.eq.1 hc.choose_spec.2
        have ht : hc.choose⁻¹ * pre γ ∈ T := mul_mem (inv_mem hc.choose_spec.1.1) (hpre γ hγ).2
        rw [← hF (g * hc.choose) _ hj ht, mul_assoc, mul_inv_cancel_left]
      · intro a ha b hb e
        have ha' : a ∈ R := ha
        have hb' : b ∈ R := hb
        have e1 := (hrel a ha' _ (hpre b hb').2).1 e
        have e2 := (hrel b hb' _ (hpre b hb').2).1 rfl
        rw [(hpre b hb').1] at e1 e2
        exact (h2 b (h1 b hb')).unique ⟨ha', e1⟩ ⟨hb', e2⟩
    · intro c hc
      by_contra hn
      exact hc (dif_neg fun h => hn ((hset c).1 h))

theorem tensCast_under {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (P : HeightOneSpectrum (𝓞 E)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α (P.under (𝓞 F1)) = 1)
    (h0 : ∀ v', v' ≠ P.under (𝓞 F1) → α v' = 0) :
    ∃ α' : FiniteAdeleRing (𝓞 F2) F2,
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' (P.under (𝓞 F2)) = 1 ∧
        ∀ v', v' ≠ P.under (𝓞 F2) → α' v' = 0 := by
  subst h
  exact ⟨α, rfl, h1, h0⟩

theorem idem_mul_iff {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (α : AFplus L) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0)
    (z : AL L) : ((1 : L) ⊗ₜ[maximalRealSubfield L] α) * z = z ↔ ∀ v', v' ≠ v → compAt L v' z = 0 := by
  have hc : ∀ u, compAt L u ((1 : L) ⊗ₜ[maximalRealSubfield L] α) = (1 : L) ⊗ₜ[maximalRealSubfield L] (α u) := by
    intro u
    rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  constructor
  · intro h u hu
    rw [← h, map_mul, hc, h0 u hu, TensorProduct.tmul_zero, zero_mul]
  · intro h
    rw [← sub_eq_zero]
    apply GlobalTheory.AL_eq_zero_of_compAt
    intro u
    rw [map_sub, map_mul, hc]
    by_cases hu : u = v
    · subst hu
      rw [h1, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [h u hu, mul_zero, sub_zero]

theorem conj_supp {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (M : Matrix (Fin m) (Fin m) B)
    (hM : M = β * K * β') (h : ∀ i j, φ * (K - 1) i j = (K - 1) i j) : ∀ i j, φ * (M - 1) i j = (M - 1) i j := by
  have e : M - 1 = β * (K - 1) * β' := by
    rw [hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have e1 : φ • (K - 1) = K - 1 := Matrix.ext h
  have e2 : φ • (β * (K - 1) * β') = β * (K - 1) * β' := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  rw [e]
  exact fun i j => congrFun (congrFun e2 i) j

theorem conj_supp_iff {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (h2 : β' * β = 1)
    (M : Matrix (Fin m) (Fin m) B) (hM : M = β * K * β') :
    (∀ i j, φ * (M - 1) i j = (M - 1) i j) ↔ ∀ i j, φ * (K - 1) i j = (K - 1) i j := by
  refine ⟨conj_supp φ β' M β h2 K ?_, conj_supp φ β K β' h1 M hM⟩
  rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 2000000 in
theorem suppF_iff_trivOutside (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV)
    (e f : Formalism.L2.Theta.AE D) (hef : Formalism.IndefR.Mult.IsPrimeIdem s.w e f) (κ : GAf D.host.E n) :
    Formalism.IndefR.Mult.SuppF V f (PV.ψ κ) ↔ TrivOutside {s.v} κ := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, hα1, hα0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hef
  obtain ⟨α', hT, hw1, hw0⟩ := tensCast_under hF s.w α hα1 hα0
  have hv : s.w.under (𝓞 (maximalRealSubfield D.host.E)) = s.v := HeightOneSpectrum.ext s.w_under
  rw [hv] at hw1 hw0
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  have hfin : Formalism.L2.Theta.finPart D x = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  set K := (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm with hKdef
  set M := (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.finPart D) with hMdef
  have e6 : (Formalism.L2.Theta.mt V (PV.ψ κ) - 1).map (Formalism.L2.Theta.finPart D) = M - 1 := by
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.finPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.finPart D)) (map_one (Formalism.L2.Theta.finPart D))]
  have e2 : ((Formalism.L2.Theta.mt V (PV.ψ κ)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
    have hk := MonoidHom.mem_ker.1 (PV.into κ)
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
    have e3 : (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ κ)).val := rfl
    rw [e3, hk, Units.val_one, sub_self]
  have s1 : Formalism.IndefR.Mult.SuppF V x (PV.ψ κ) ↔ ∀ i j, Formalism.L2.Theta.finPart D x * (M - 1) i j = (M - 1) i j := by
    rw [← e6]
    refine forall_congr' fun i => forall_congr' fun j => ⟨fun h => ?_, fun h => ?_⟩
    · exact ((Formalism.L2.Theta.finPart D).map_mul _ _).symm.trans (congrArg (Formalism.L2.Theta.finPart D) h)
    · rw [← sub_eq_zero]
      apply GlobalTheory.PlaceSupp.AE_eq_zero D
      · have h0 : Formalism.L2.Theta.infPart D ((Formalism.L2.Theta.mt V (PV.ψ κ) - 1) i j) = 0 := congrFun (congrFun e2 i) j
        rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_mul, sub_eq_zero]
        exact h
  have s2 := conj_supp_iff (Formalism.L2.Theta.finPart D x) β K β' h1 h2 M (hm κ)
  have e7 : (K - 1).map (GlobalTheory.NJoin.tensCast hF) = (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1 := by
    rw [Matrix.map_sub _ (map_sub (GlobalTheory.NJoin.tensCast hF)),
      Matrix.map_one _ (map_zero (GlobalTheory.NJoin.tensCast hF)) (map_one (GlobalTheory.NJoin.tensCast hF))]
    congr 1
    exact Matrix.ext fun a b => (GlobalTheory.NJoin.tensCast hF).apply_symm_apply ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b)
  have s3 : ∀ i j, Formalism.L2.Theta.finPart D x * (K - 1) i j = (K - 1) i j ↔
      ∀ v', v' ≠ s.v → compAt D.host.E v' (((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j) = 0 := by
    intro i j
    have e8 : GlobalTheory.NJoin.tensCast hF ((K - 1) i j) = ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j :=
      congrFun (congrFun e7 i) j
    rw [← idem_mul_iff s.v α' hw1 hw0, ← (GlobalTheory.NJoin.tensCast hF).injective.eq_iff, (GlobalTheory.NJoin.tensCast hF).map_mul,
      hfin, hT, e8]
  have e9 : ∀ v', ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1).map (compAt D.host.E v') =
      (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E v') - 1 := fun v' => by
    rw [Matrix.map_sub _ (map_sub (compAt D.host.E v')),
      Matrix.map_one _ (map_zero (compAt D.host.E v')) (map_one (compAt D.host.E v'))]
  rw [s1, s2]
  constructor
  · intro h v' hv'
    rw [← sub_eq_zero, ← e9]
    exact Matrix.ext fun i j => (s3 i j).1 (h i j) v' hv'
  · intro h i j
    refine (s3 i j).2 fun v' hv' => ?_
    have := e9 v'
    rw [h v' hv', sub_self] at this
    exact congrFun (congrFun this i) j


end GlobalTheory.LabelTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormMemOfUnderEq
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.DenseUsable

theorem isSquare_neg_padic (q : ℕ) [hq : Fact q.Prime] (d : ℕ) (a : ℤ)
    (h1 : (q : ℤ) ∣ a ^ 2 + d) (h2 : ¬ (q : ℤ) ∣ 2 * a) : IsSquare (-(d : ℚ_[q])) := by
  let F : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C (d : ℤ)
  have hF : ∀ z : ℤ_[q], Polynomial.aeval z F = z ^ 2 + d := by intro z; simp [F]
  have hF' : ∀ z : ℤ_[q], Polynomial.aeval z (Polynomial.derivative F) = 2 * z := by
    intro z; simp [F]; left; exact map_ofNat _ 2
  have hlt : ‖((a ^ 2 + d : ℤ) : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).2 h1
  have hn : ‖((2 * a : ℤ) : ℤ_[q])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => h2 ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (a : ℤ_[q])) (by
    rw [hF, hF']; push_cast at hn hlt; rw [hn]; simpa using hlt)
  rw [hF] at hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + d : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz]; simp
  push_cast at this
  linear_combination -this

theorem intCast_mem_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (n : ℤ) :
    ((n : 𝓞 E) ∈ w.asIdeal ↔ ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∣ n) := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← ZMod.intCast_zmod_eq_zero_iff_dvd, map_intCast, ← map_intCast e,
    map_eq_zero_iff _ e.injective]

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (y : 𝓞 E) : ∃ a : ℤ, y - (a : 𝓞 E) ∈ w.asIdeal := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  obtain ⟨c, hc'⟩ := e.surjective (Ideal.Quotient.mk w.asIdeal y)
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc', map_intCast, map_intCast, sub_self]

theorem usPl_of_absNorm_prime {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : ImQ E d)
    (w : HeightOneSpectrum (𝓞 E)) (hp : (Ideal.absNorm w.asIdeal).Prime)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (h2d : ((2 * d : ℕ) : 𝓞 E) ∉ w.asIdeal) : UsPl d w := by
  have hf := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp
  refine ⟨GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w hf he, fun q hq hqw => ?_⟩
  have hqw' : ((q : ℤ) : 𝓞 E) ∈ w.asIdeal := by rwa [Int.cast_natCast]
  have hpq : Ideal.absNorm w.asIdeal = q := by
    have := (intCast_mem_iff w hp q).1 hqw'
    exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 this)
  obtain ⟨-, x, hx⟩ := hd
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hx]
    have : -(d : E) = algebraMap ℤ E (-(d : ℤ)) := by simp
    rw [this]; exact isIntegral_algebraMap
  let y : 𝓞 E := ⟨x, hi⟩
  have hy : y ^ 2 = -(d : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact hx
  obtain ⟨a, ha⟩ := exists_int_sub_mem w hp y
  have h1 : ((q : ℤ) : ℤ) ∣ a ^ 2 + d := by
    rw [← hpq]
    refine (intCast_mem_iff w hp _).1 ?_
    have : (((a ^ 2 + d : ℤ)) : 𝓞 E) = (y - a) * (-(y + a)) + (y ^ 2 + d) := by push_cast; ring
    rw [this, hy, neg_add_cancel, add_zero]
    exact w.asIdeal.mul_mem_right _ ha
  have hnd : ¬ (q : ℤ) ∣ 2 * d := by
    intro h
    apply h2d
    have := (intCast_mem_iff w hp (2 * d)).2 (by rw [hpq]; exact h)
    simpa using this
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  haveI : Fact q.Prime := ⟨hq⟩
  refine isSquare_neg_padic q d a h1 fun h => ?_
  rcases hqz.dvd_or_dvd h with h' | h'
  · exact hnd (dvd_mul_of_dvd_left h' _)
  · apply hnd
    refine dvd_mul_of_dvd_right ?_ _
    have h3 : (q : ℤ) ∣ a ^ 2 := dvd_pow h' two_ne_zero
    have := (Int.dvd_add_right h3).1 h1
    exact this

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

theorem natCast_mem_of_dvd {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n M : ℕ}
    (h : n ∣ M) (hn : (n : 𝓞 E) ∈ w.asIdeal) : (M : 𝓞 E) ∈ w.asIdeal := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  exact w.asIdeal.mul_mem_right _ hn

theorem absNorm_mem_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w u : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hu : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem u.asIdeal
  have h' := congrArg HeightOneSpectrum.asIdeal h
  simp only [HeightOneSpectrum.under_asIdeal] at h'
  have hm : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hu
  rw [← h', Ideal.under, Ideal.mem_comap, map_natCast] at hm
  exact hm

end GlobalTheory.DenseUsable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameMove

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem congAt_mono {P : HeightOneSpectrum (𝓞 E)} {m n : ℕ} (hmn : m ≤ n) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : CongAt (F := F) P n k) : CongAt (F := F) P m k := by
  intro a b
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have e0 : (((qOf P : ℕ) : E) ^ m)⁻¹ = algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m)) * (((qOf P : ℕ) : E) ^ n)⁻¹ := by
    rw [map_pow, map_natCast]
    have hn : ((qOf P : ℕ) : E) ^ n = ((qOf P : ℕ) : E) ^ m * ((qOf P : ℕ) : E) ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [hn]
    field_simp
  have e : iA F E (((qOf P : ℕ) : E) ^ m)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
      iA F E (algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ (n - m))) *
        (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) := by
    rw [← mul_assoc, ← map_mul, e0]
  rw [e]
  exact GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int _) (h a b)

end Cong

theorem mem_of_local {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ)
    (k : Sp E n ≃ₗ[E] Sp E n) (hk : ∀ x ∈ stdAt E n P, ((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x) ∈ stdAt E n P)
    (x : Sp E n) (hx : x ∈ stdAt E n P) : k x ∈ stdAt E n P := by
  have hq : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hc : ((qOf P ^ d : ℕ) : E) ≠ 0 := by exact_mod_cast pow_ne_zero d hq
  have e : k x = x + (qOf P ^ d) • (((qOf P ^ d : ℕ) : E)⁻¹ • (k x - x)) := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
  rw [e]
  exact add_mem hx (nsmul_mem (hk x hx) _)

end GlobalTheory.FrameMove

namespace GlobalTheory.FrameMove

theorem frames_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ j hj β x x₁ κ p p₁ hxκ hp hp₁ P dep g hd1 hdD hg hIn
  have hD1 : 1 ≤ (t.cst μ).D P := hd1.trans hdD
  have hu := hp.frame P
  have hu₁ := hp₁.frame P
  unfold NearAt at hu hu₁
  unfold InFrame NearAt at hIn
  rw [hxκ] at hu₁
  set h := (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) with hh
  have hs : h = g⁻¹ * ((frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P) := by
    ext w; rfl
  have key : ratA D.host.F (seamGL t.seam h) =
      ((ratA D.host.F (seamGL t.seam g))⁻¹ *
        ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P)))⁻¹ *
        ratA D.host.F (seamGL t.seam g)) *
      (((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P))⁻¹ * ratA D.host.F (seamGL t.seam g))⁻¹ *
      ((ratA D.host.F (A.crd j hj) * (x.1 * κ) * ratA D.host.F (A.fb j hj β P))⁻¹ *
        ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) := by
    rw [hs]
    simp only [map_mul, map_inv]
    group
  have c1 := GlobalTheory.CplPt.congAt_conj (dep P)
    (congAt_mono hdD (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hD1 hu))
    (fun a b => GlobalTheory.CplPt.seamGL_int t.seam ⟨g, hg⟩ a b)
  have c2 := GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hIn
  have c3 := congAt_mono hdD hu₁
  have hC : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h)) := by
    rw [key]
    exact GlobalTheory.CplPt.congAt_mul _ (GlobalTheory.CplPt.congAt_mul _ c1 c2) c3
  have hCi : CongAt (F := D.host.F) (seamP t.seam P.1) (dep P) (ratA D.host.F (seamGL t.seam h⁻¹)) := by
    rw [map_inv, map_inv]
    exact GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ hd1 hC
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h hC
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local t.seam P.1 (dep P) (D.R.N j) h⁻¹ hCi
  refine ⟨fun w => ⟨fun hw => ?_, fun hw => mem_of_local P.1 (dep P) h l1 w hw⟩, fun w hw => ?_⟩
  · have := mem_of_local P.1 (dep P) h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)) (h w) = w from h.symm_apply_apply w] at this
  · have := l1 w hw
    rwa [Nat.cast_pow] at this

end GlobalTheory.FrameMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrames_mul_adele_at_badPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameMove.frames_mul | exact GlobalTheory.FrameMove.frames_mul | (intros; apply GlobalTheory.FrameMove.frames_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwRat

theorem ratUnitCol : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi γ hγ
  exact GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹)
    (GlobalTheory.unitary_conj_orthonormal D _ _ _ (hP.crd_orth i hi) hγ)

end GlobalTheory.TwRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometryStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  first | exact @GlobalTheory.TwRat.ratUnitCol | exact GlobalTheory.TwRat.ratUnitCol | (intros; apply GlobalTheory.TwRat.ratUnitCol <;> assumption)
end
end

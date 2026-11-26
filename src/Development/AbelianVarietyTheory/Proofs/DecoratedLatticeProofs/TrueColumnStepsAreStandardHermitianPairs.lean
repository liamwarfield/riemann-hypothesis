module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntMemInverseHalfDifferent
open NumberField Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.DgenNe

theorem emb_injective {R : Ranks} (H : Host R) : Function.Injective H.emb := by
  intro g g' h
  have h1 : H.sigmaOf g = H.sigmaOf g' :=
    AlgEquiv.ext fun x => H.φ₀.injective (RingHom.congr_fun h x)
  exact (H.gal).symm.injective h1

theorem embT_injective {R : Ranks} (H : Host R) : Function.Injective (embT H) := fun τ τ' h =>
  Subtype.ext (emb_injective H h)

theorem bb_ne_bot {R : Ranks} (H : Host R) : H.𝔟 ≠ ⊥ := by
  intro h
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem int_mem_inverse_half_different {R : Ranks} (H : Host R) (t : 𝓞 H.E) :
    ((t : H.E)) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := by
  have h0 : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (bb_ne_bot H)
  have h1 : (1 : H.E) ∈ H.AA0 := by
    unfold Host.AA0
    rw [FractionalIdeal.mem_inv_iff h0]
    intro y hy
    obtain ⟨x, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [one_mul]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩
  have h2 : t • (1 : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := Submodule.smul_mem _ t h1
  simpa [Algebra.smul_def] using h2

end GlobalTheory.Mem.Col2.DgenNe

namespace GlobalTheory.Mem.Col2.DgenNe

theorem dgen_ne_zero : ∀ {R : Ranks} (H : Host R) (cD : Tau R → ℂ), Th.IsDgen H (embT H) cD → ∀ τ, cD τ ≠ 0 := by
  intro R H cD hD τ hτ
  classical
  obtain ⟨M, hM, hemb, hgen⟩ := hD
  obtain ⟨s, hs, hell⟩ := hgen τ
  have hs0 : s = 0 := Subtype.ext (hs.trans hτ)
  rw [hs0, Submodule.span_zero_singleton] at hell
  let e : Tau R → H.E →+* M := fun σ => (embT H σ).codRestrict M (hemb σ)
  have hlift : ∀ σ (x : H.E), Formalism.MainNotions.TaylorLogMetric.liftM M (embT H σ x) = e σ x := by
    intro σ x
    simp only [Formalism.MainNotions.TaylorLogMetric.liftM, dif_pos (hemb σ x)]
    rfl
  let f : Tau R → (𝓞 H.E →* M) := fun σ => ((e σ).comp (algebraMap (𝓞 H.E) H.E)).toMonoidHom
  have hf : Function.Injective f := by
    intro σ σ' h
    apply embT_injective H
    have h2 : e σ = e σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 H.E))
      (RingHom.ext fun x => DFunLike.congr_fun h x)
    ext x
    exact congrArg Subtype.val (RingHom.congr_fun h2 x)
  have hli := (linearIndependent_monoidHom (𝓞 H.E) M).comp f hf
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  let N := Th.mmM H (embT H) M
  let P : Submodule M (Tau R → M) :=
    { carrier := {v | ∃ b : 𝓞 M, b ≠ 0 ∧ b • v ∈ N}
      add_mem' := by
        rintro v w ⟨b, hb, hv⟩ ⟨b', hb', hw⟩
        refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
        have : (b * b') • (v + w) = b' • (b • v) + b • (b' • w) := by
          rw [smul_add, mul_smul, mul_smul, smul_comm b b' v]
        rw [this]
        exact N.add_mem (N.smul_mem _ hv) (N.smul_mem _ hw)
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro m v ⟨b, hb, hv⟩
        obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) m
        have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
        have hy1 : algebraMap (𝓞 M) M y ≠ 0 := by
          intro h0
          exact hy0 (IsFractionRing.injective (𝓞 M) M (by rw [h0, map_zero]))
        refine ⟨y * b, mul_ne_zero hy0 hb, ?_⟩
        have : (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) • v) = x • (b • v) := by
          funext σ
          change (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) * v σ) = x • (b • v σ)
          rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
          field_simp
        rw [this]
        exact N.smul_mem _ hv }
  have hP : ∀ t : 𝓞 H.E, (fun σ => e σ t) ∈ P := fun t =>
    ⟨1, one_ne_zero, by
      rw [one_smul]
      exact Submodule.subset_span ⟨(t : H.E), int_mem_inverse_half_different H t, funext fun σ => (hlift σ t).symm⟩⟩
  have hsingle : (Pi.single τ 1 : Tau R → M) ∈ P := by
    have hle : Submodule.span M (Set.range (flip ((fun g : 𝓞 H.E →* M => (g : 𝓞 H.E → M)) ∘ f))) ≤ P := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact hP t
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨b, hb, hbN⟩ := hsingle
  have hmem : algebraMap (𝓞 M) M b ∈ Th.ellT H (embT H) M τ := by
    rw [Th.ellT, Submodule.mem_comap]
    convert hbN using 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp [Algebra.smul_def]
    · simp [h]
  rw [hell, Submodule.mem_bot] at hmem
  exact hb (IsFractionRing.injective (𝓞 M) M (by rw [hmem, map_zero]))

end GlobalTheory.Mem.Col2.DgenNe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.StdStepsT

theorem stdPair_steps_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → (∀ (i : ℕ), i + 1 ≤ B.R.m → StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ) ∧ (I.rec7 l Z).sp.X'.gram = 1 ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ (∀ τ, I.J.cD τ ≠ 0) ∧ ∀ (V : HSp (I.rec7 l Z)) (g : GA (I.rec7 l Z) V), ∃ x, IsDetRoot V g x := by
  intro B X I hI hP l Z ψ θ hψ hθ
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, GlobalTheory.Mem.Col2.Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact GlobalTheory.Mem.Col2.Crd.ortho_pos hs _
  have oX' : GlobalTheory.Mem.Col2.Crd.Ortho B.sp.X' := by rw [hX']; exact GlobalTheory.Mem.Col2.Crd.ortho_pos hs _
  have gX : ∀ j, (B.sp.X j).gram = 1 := fun j => by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.one_apply]
    exact (oX j).1 a b
  have gX' : B.sp.X'.gram = 1 := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.one_apply]
    exact oX'.1 a b
  have hcc : (I.rec7 l Z).host.ccK = ⊤ := B.toPre.ccK_top
  refine ⟨fun i hi => ?_, gX', fun τ => B.fields_embC τ, GlobalTheory.Mem.Col2.DgenNe.dgen_ne_zero B.host I.J.cD hI.amb_ok.dgen,
    fun V g => GlobalTheory.RecDict.exists_isDetRoot _ V g⟩
  have r1 := rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)
  have r2 := rankN (I.rec7 l Z) (i + 1) hi
  refine ⟨hψ, hθ, gX i, gX (i + 1), (I.rec7 l Z).sp.X_sig i, (I.rec7 l Z).sp.X_sig (i + 1), ?_, hcc, I.J.δ_ne_zero,
    GlobalTheory.AdForm.StdSteps.realPlace_cmTrace_zero_element_eq_I_mul_abs _ hcc, GlobalTheory.AdForm.StdSteps.scale_eq (I.rec7 l Z) I.J.δ_ne_zero⟩
  rw [r1, r2]
  exact ⟨Ranks.N_pos _ _, GlobalTheory.AdForm.StdSteps.N_lt_succ _ _, GlobalTheory.AdForm.StdSteps.even_N _ _, GlobalTheory.AdForm.StdSteps.even_N _ _⟩

end GlobalTheory.AdForm.StdStepsT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → (∀ (i : ℕ), i + 1 ≤ B.R.m → StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ) ∧ (I.rec7 l Z).sp.X'.gram = 1 ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ (∀ τ, I.J.cD τ ≠ 0) ∧ ∀ (V : HSp (I.rec7 l Z)) (g : GA (I.rec7 l Z) V), ∃ x, IsDetRoot V g x := by
  first | exact @GlobalTheory.AdForm.StdStepsT.stdPair_steps_all | exact GlobalTheory.AdForm.StdStepsT.stdPair_steps_all | (intros; apply GlobalTheory.AdForm.StdStepsT.stdPair_steps_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepComb

variable {D : D7}

theorem idem_mem_idAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) :
    es ∈ GlobalTheory.FinPl.idAt D (· = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  have h' := h
  obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := h'
  have hw := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D es PP w ε h hε a3
  have hε' := hε
  obtain ⟨α, rfl, -, h0⟩ := hε'
  have hm : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ GlobalTheory.FinPl.idAt D (· = w) :=
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (P := (· = w)) (fun v hv => h0 v hv) 1
  have e1 : es = es * (es + cA D es) := by rw [mul_add, a1, a2, add_zero]
  rw [e1, a3, hw]
  exact Ideal.mul_mem_left _ _ hm

theorem idemSum_mem_idAt {e : AE D} {Z : Finset (Pl D.host.E)} (h : IsIdemSum e Z) :
    e ∈ GlobalTheory.FinPl.idAt D (fun p => ∃ PP ∈ Z, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  exact Ideal.sum_mem _ fun PP hPP =>
    GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => ⟨PP, hPP, hw⟩) (idem_mem_idAt (hes PP hPP))

theorem mxAt_of_mem_half {S T : HSp D} {a : AE D} {P : GlobalTheory.FinPl.Pl D → Prop} (ha : a ∈ GlobalTheory.FinPl.idAt D P)
    {u : WO S T} (hu : u ∈ GlobalTheory.PlaceModel.half S T a) : GlobalTheory.FinPl.MxAt P u := by
  intro i j
  rw [← (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu i j]
  exact Ideal.mul_mem_right _ _ ha

theorem isSBHalf_stepDatumQ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (e : AE D) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsIdemSum e (L.Pg ∪ Q)) :
    IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T =>
      if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
        omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
      else 0) := by
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ (L.Pg ∪ Q)
    (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
        GlobalTheory.PlaceDatum.omegaQ_congr Q L.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)]

theorem comb_add' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_add (f := _)]

theorem comb_smul' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_smul]

theorem comb_zero' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (f : WO S T → ℂ) :
    comb ψ S T 0 f = 0 := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_zero]

theorem comb_single' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u a) f = a • heisO ψ S T u f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, Finsupp.linearCombination_single]

theorem mem_of_mem_support_add {S T : HSp D} {H : Set (WO S T)} {c c' : WO S T →₀ ℂ} (hc : ∀ u ∈ c.support, u ∈ H)
    (hc' : ∀ u ∈ c'.support, u ∈ H) : ∀ u ∈ (c + c').support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  have h2 : c' u = 0 := by
    by_contra h
    exact hn (hc' u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.add_apply, h1, h2, add_zero])

theorem mem_of_mem_support_smul {S T : HSp D} {H : Set (WO S T)} (a : ℂ) {c : WO S T →₀ ℂ}
    (hc : ∀ u ∈ c.support, u ∈ H) : ∀ u ∈ (a • c).support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.smul_apply, h1, smul_zero])


set_option maxHeartbeats 1000000 in
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum in
theorem exists_comb_of_isThetaAt {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (e : AE D) (f₀ Φ f : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : e * e = e) (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ)
    (hθ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    ∃ d : WO S T →₀ ℂ, (∀ u ∈ d.support, u ∈ half S T (e + cA D e)) ∧ f = comb ψ S T d f₀ := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm]
  clear hall
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy]
    refine ⟨Finsupp.single (x + y) (ψ (symplOH S T x y)), fun u hu => ?_, ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
      exact add_mem (GlobalTheory.FinPl.DatumBack.half_le_sum hce hx) (GlobalTheory.FinPl.DatumBack.half_le_sum' hec hy)
    · rw [comb_single']
  | zero =>
    exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), by rw [LinearMap.map_zero, comb_zero']⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, hc, hc'⟩ := hg
    obtain ⟨c', hd, hd'⟩ := hg'
    refine ⟨c + c', mem_of_mem_support_add hc hd, ?_⟩
    rw [LinearMap.map_add (f := _), hc', hd', comb_add']
  | smul a g _ hg =>
    obtain ⟨c, hc, hc'⟩ := hg
    refine ⟨a • c, mem_of_mem_support_smul a hc, ?_⟩
    rw [LinearMap.map_smul, hc', comb_smul']

theorem exists_comb_of_isStepVecOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f → ∃ d : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ LS.Pg ∪ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧ f = comb ψ S T d f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f hS hT _ _ hv
  obtain ⟨hvac, e, he, hθ⟩ := hv
  have hSB := isSBHalf_stepDatumQ S T ΛS ΛT βS βT LS χj ξ Q e hS hT he
  obtain ⟨d, hd, hf⟩ := exists_comb_of_isThetaAt ψ ΛS ΛT e f₀ _ f hvac.1 hS hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hSB hθ
  have hI := idemSum_mem_idAt he
  exact ⟨d, fun u hu => mxAt_of_mem_half (add_mem hI (GlobalTheory.LastOpPf.cA_mem_idAt hI)) (hd u hu), hf⟩

end GlobalTheory.StepComb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f → ∃ d : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ LS.Pg ∪ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧ f = comb ψ S T d f₀ := by
  first | exact @GlobalTheory.StepComb.exists_comb_of_isStepVecOf | exact GlobalTheory.StepComb.exists_comb_of_isStepVecOf | (intros; apply GlobalTheory.StepComb.exists_comb_of_isStepVecOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm.DenseHalf

theorem half_eq_rat_add_nsmul : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ M : ℕ, 0 < M → ∀ w : WO S T, IsHalf e w → ∃ (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ w = z.map (fun r => e * incA D r) + M • v := by
  intro D S T e P he M hM w hw
  obtain ⟨z, v, hv, hvh, h⟩ := GlobalTheory.AdForm.exists_rat_half_approx S T e P he M hM w
  refine ⟨z, -v, neg_mem hv, fun i j => ?_, ?_⟩
  · simp only [Matrix.neg_apply, mul_neg, hvh i j]
  · have hw' : e • w = w := by
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, hw i j]
    rw [h, hw', smul_neg]
    abel

end GlobalTheory.AdForm.DenseHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHomStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ M : ℕ, 0 < M → ∀ w : WO S T, IsHalf e w → ∃ (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ w = z.map (fun r => e * incA D r) + M • v := by
  first | exact @GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul | exact GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul | (intros; apply GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfStdFin

theorem exists_reps_half_stdHom : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  classical
  intro D S T Q E₂ _ k hk
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T (Formalism.L2.Col.stdLat D.host.E S.rank)
    (Formalism.L2.Col.stdLat D.host.E T.rank) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg (fun _ => True) k hk
  rw [coe_colStdLat, coe_colStdLat] at h
  let G : WO S T → Prop := fun r => ∃ u ∈ stdHom S T, IsHalf E₂ u ∧ ∃ w ∈ stdHom S T, u = r + k • w
  let pick : WO S T → WO S T := fun r => if hG : G r then hG.choose else 0
  refine ⟨hR.toFinset.image pick, fun u hu hh => ?_⟩
  obtain ⟨r, hr, w, hw, huw⟩ := h u hu
  have hG : G r := ⟨u, hu, hh, w, hw, huw⟩
  obtain ⟨_, hh₀, w₀, hw₀, hu₀w⟩ := hG.choose_spec
  have hp : pick r = hG.choose := dif_pos hG
  have hdiff : u = hG.choose + k • (w - w₀) := by
    rw [hu₀w, smul_sub, huw]; abel
  exact ⟨pick r, Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hr), w - w₀, sub_mem hw hw₀,
    GlobalTheory.HalfLatFin.isHalf_of_nsmul E₂ hk hh hh₀ hdiff, by rw [hp]; exact hdiff⟩

end GlobalTheory.HalfStdFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_reps_half_standardHom_mod_nsmul : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  first | exact @GlobalTheory.HalfStdFin.exists_reps_half_stdHom | exact GlobalTheory.HalfStdFin.exists_reps_half_stdHom | (intros; apply GlobalTheory.HalfStdFin.exists_reps_half_stdHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryRealMulFiniteDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryRealMulFiniteDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicSplitParts

variable {D : D7}

theorem infMat_eq_map (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    infMat D.sp.cm.sig V.gram θ h = (infHom V h).1.map θ := rfl

theorem split_parts : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ ∀ a ∈ GinfC V, ∀ k ∈ GfC V, Lev.finE V (a * k) = Lev.finE V k ∧ ∀ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, infMat D.sp.cm.sig V.gram θ (a * k) = infMat D.sp.cm.sig V.gram θ a := by
  intro D V
  refine ⟨fun h => ?_, fun a ha k hk => ⟨?_, fun θ => ?_⟩⟩
  · obtain ⟨p, hp⟩ := (GlobalTheory.AdelicSplit.splitEquiv V).surjective h
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, hp.symm⟩
  · have h1 : finE V a = 1 := by
      have : finHom V a = 1 := ha
      simp only [finE, MonoidHom.comp_apply, this, map_one]
    rw [map_mul, h1, one_mul]
  · have h1 : infHom V k = 1 := hk
    rw [infMat_eq_map, infMat_eq_map, map_mul, h1, mul_one]

end GlobalTheory.AdelicSplitParts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryRealMulFiniteDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ ∀ a ∈ GinfC V, ∀ k ∈ GfC V, Lev.finE V (a * k) = Lev.finE V k ∧ ∀ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, infMat D.sp.cm.sig V.gram θ (a * k) = infMat D.sp.cm.sig V.gram θ a := by
  first | exact @GlobalTheory.AdelicSplitParts.split_parts | exact GlobalTheory.AdelicSplitParts.split_parts | (intros; apply GlobalTheory.AdelicSplitParts.split_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruh
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.LocMod.Place

theorem intInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'],
    Place.intInd (k := k) Y Y' ∈ SB (Matrix Y Y' k) := by
  intro k _ _ _ _ Y Y' _ _ _ _
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  set K : Set (Matrix Y Y' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hK
  have hKeq : K = Set.univ.pi fun _ : Y => Set.univ.pi fun _ : Y' => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ r) q (Set.mem_univ q)⟩
  have hKo : IsOpen K := by
    rw [hKeq]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hKc : IsCompact K := by
    rw [hKeq]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  have hcl : IsClosed K := by
    rw [hKeq]
    exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => (Valuation.isClosed_integer (v := valuation k))
  refine ⟨?_, ?_⟩
  · show IsLocallyConstant (K.indicator fun _ => (1 : ℂ))
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · show HasCompactSupport (K.indicator fun _ => (1 : ℂ))
    exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LocMod.Place
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruhStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'], Place.intInd (k := k) Y Y' ∈ SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.LocMod.Place.intInd_mem_SB | exact GlobalTheory.LocMod.Place.intInd_mem_SB | (intros; apply GlobalTheory.LocMod.Place.intInd_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenominatorAvoidingGivenPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenominatorAvoidingGivenPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffDen

theorem exists_den_avoid : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (G : HeightOneSpectrum (𝓞 E) → Prop) (c : ℕ), 0 < c → ∀ x : Formalism.L2.Col.HomE E a b, (c : E) • x ∈ M → (∀ Q : HeightOneSpectrum (𝓞 E), ¬ G Q → x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) → ∃ d : 𝓞 E, d ≠ 0 ∧ (d : E) • x ∈ M ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q := by
  intro E _ _ a b M G c hc x hcx hloc
  classical
  have hsm : ∀ d : 𝓞 E, (d : E) • x = d • x := fun d => by
    rw [← algebraMap_smul E d x]
  set J : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) _ x) with hJ
  have memJ : ∀ d : 𝓞 E, d ∈ J ↔ d • x ∈ M := fun d => by simp [hJ]
  have hc0 : (c : 𝓞 E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcx' : (c : 𝓞 E) • x ∈ M := by
    have hcE : ((c : 𝓞 E) : E) = (c : E) := by simp
    rw [← hsm, hcE]; exact hcx
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | (c : 𝓞 E) ∈ Q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(c : 𝓞 E)}) (by simpa using hc0)).subset ?_
    intro Q hQ
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hQ)
  set S : Set (HeightOneSpectrum (𝓞 E)) := {Q | (c : 𝓞 E) ∈ Q.asIdeal ∧ ¬ G Q} with hS
  have hSfin : S.Finite := hfin.subset fun Q hQ => hQ.1
  have hnot : ¬ ((J : Set (𝓞 E)) ⊆ ⋃ Q ∈ S, (Q.asIdeal : Set (𝓞 E))) := by
    intro hsub
    rcases S.eq_empty_or_nonempty with h0 | ⟨Q₀, _⟩
    · have hm := hsub ((memJ _).2 hcx')
      simp [h0] at hm
    obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime_finite hSfin (f := fun Q => Q.asIdeal) Q₀ Q₀
      (fun Q _ _ _ => Q.isPrime)).1 hsub
    obtain ⟨s, hs, hsx⟩ := hloc Q hQ.2
    exact hs (hle ((memJ s).2 hsx))
  obtain ⟨d, hdJ, hdS⟩ := Set.not_subset.1 hnot
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hdS
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q :=
    fun Q hcQ hdQ => by_contra fun hG => hdS Q ⟨hcQ, hG⟩ hdQ
  by_cases hd0 : d = 0
  · refine ⟨c, hc0, ?_, fun Q hcQ _ => key Q hcQ (hd0 ▸ Q.asIdeal.zero_mem)⟩
    rw [hsm]; exact hcx'
  · exact ⟨d, hd0, by rw [hsm]; exact (memJ d).1 hdJ, key⟩

end GlobalTheory.OffDen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenominatorAvoidingGivenPrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_avoiding_given_primes : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (G : HeightOneSpectrum (𝓞 E) → Prop) (c : ℕ), 0 < c → ∀ x : Formalism.L2.Col.HomE E a b, (c : E) • x ∈ M → (∀ Q : HeightOneSpectrum (𝓞 E), ¬ G Q → x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) → ∃ d : 𝓞 E, d ≠ 0 ∧ (d : E) • x ∈ M ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q := by
  first | exact @GlobalTheory.OffDen.exists_den_avoid | exact GlobalTheory.OffDen.exists_den_avoid | (intros; apply GlobalTheory.OffDen.exists_den_avoid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastTwo

theorem entries_mem_SB : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  intro D c v χ Q α yb
  have hreg := Q.reg
  constructor
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
    refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (hreg.1 Q.s 0 rfl))
      (p := fun x₀ => withCol x₀ (Quotient.out yb)) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
    · unfold withCol; fun_prop
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
    have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
    have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol Q.k Q.ψk Q.ν (-1) Q.cond Q.unitVol hv1 (Q.X (Q.s + 1)) 1 1 _
      (cosetInd_mem_SB Q.c₂ yb)).1
    refine GlobalTheory.FinPl.Comm.prod_mem_SB hreg.2.1 hh
      (p := fun x : Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k => fromCols x.toRows₁ (0 : Matrix Q.Z (Fin 0) Q.k))
      (r := fun x => x (Sum.inr ()))
      (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases j with j | j
        · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
        · exact j.elim0
    · exact continuous_apply _
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases i with i | i
        · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
        · exact (continuous_apply j).comp continuous_snd
    · intro x; ext (i | i) j <;> rfl

end GlobalTheory.QPl.LastTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  first | exact @GlobalTheory.QPl.LastTwo.entries_mem_SB | exact GlobalTheory.QPl.LastTwo.entries_mem_SB | (intros; apply GlobalTheory.QPl.LastTwo.entries_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCombAtReN
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopLocData

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

def reN {N N' : ℕ} (h : N = N') (F : Frame k N Y) : Frame k N' Y := h ▸ F

theorem exists_o {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁ : SB (Matrix Y Y' k), IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hT a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hT

def mkPl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (hu : q.UnitAA)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : SB (Matrix Y Y' k)) (e : WO S T →₀ ℂ)
    (he : (ofSplit q).IsCombAt ψ FS FT e Φ.1) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') : LocPl ψ S T M M' :=
  ⟨k, q, hu, Y, Y', FS, FT, Φ, e, he, Classical.choose (exists_o hψ q FS FT hS hT),
    (Classical.choose_spec (exists_o hψ q FS FT hS hT)).1, (Classical.choose_spec (exists_o hψ q FS FT hS hT)).2⟩

end Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {f : FamCh W u}
  {v : VCom f.c}

theorem isCombAt_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k)
    (ψ : AddChar (AF D.host.F) ℂ) (FT : Frame k D.sp.X'.rank Y) (Ξ : Matrix Y Y' k → ℂ) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y') (e : WO (Yc D (s + 1)) D.sp.X' →₀ ℂ)
      (e' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), HEq e' e → (ofSplit q).IsCombAt ψ F FT e Ξ →
      (ofSplit q).IsCombAt ψ (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) FT e' Ξ := by
  rintro s j rfl F e e' he h
  cases he
  exact h

theorem intIn_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y' : Type} [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y'), IntIn q (Yc D (s + 1)) F (N (s + 1)) →
      IntIn q (Yc D (j + 1)) (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) (N (j + 1)) := by
  rintro s j rfl F h
  exact h

end GlobalTheory.TopLocData

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotent
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.Place

theorem isSBHalf_tensorAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ → ∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ) := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT e he hInt hMap Φ hΦ Ψ hΨ
  classical
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨hΦs, kΦ, hkΦ, hΦi, hΦl⟩ := hΦ
  obtain ⟨N, hN, hΨi, hΨl⟩ := GlobalTheory.SBUnif.uniform k Y Y' Ψ hΨ
  have hud : ∀ u : WO S T, p.up FS FT (p.down FS FT u) = u.map (fun a => p.e * a) := by
    intro u
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    exact p.ι_π _
  have hupn : ∀ (n : ℕ) (X : Matrix Y Y' k), p.up FS FT (n • X) = n • p.up FS FT X :=
    fun n X => map_nsmul (Witness.upH p FS FT) n X
  have hdownn : ∀ (n : ℕ) (u : WO S T), p.down FS FT (n • u) = n • p.down FS FT u :=
    fun n u => map_nsmul (Witness.downH p FS FT) n u
  have hsupp : ∀ t, p.tensorAt FS FT Φ Ψ t ≠ 0 →
      Φ (t - p.up FS FT (p.down FS FT t)) ≠ 0 ∧ Ψ (p.down FS FT t) ≠ 0 := fun t ht =>
    ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * N, Nat.mul_pos hkΦ hN, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hsupp t ht
    have hs := hΦs _ h1
    have hw := Witness.up_half p FS FT (p.down FS FT t)
    intro i j
    have a1 := hs i j
    have a2 := hw i j
    have e1 : t i j = (t - p.up FS FT (p.down FS FT t)) i j + p.up FS FT (p.down FS FT t) i j := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e1]
    linear_combination (1 - p.e) * a1 + (1 - e) * a2 +
      (p.up FS FT (p.down FS FT t) i j + (t - p.up FS FT (p.down FS FT t)) i j) * he
  · set X := p.down FS FT u with hX
    have hXL : p.up FS FT X ∈ stdHom S T := by rw [hX, hud]; exact hMap u hu
    have hXi : ∀ r q, X r q ∈ 𝒪[k] := (hInt X).2 hXL
    have hYi : ∀ r q, (kΦ • X) r q ∈ 𝒪[k] := fun r q => by
      rw [Matrix.smul_apply]; exact nsmul_mem (hXi r q) kΦ
    have hd : p.down FS FT (t + (kΦ * N) • u) = p.down FS FT t + (kΦ * N) • X := by
      rw [Witness.down_add, hdownn]
    have e3 : p.down FS FT t + (kΦ * N) • X = p.down FS FT t + (N : k) • (kΦ • X) := by
      rw [Nat.cast_smul_eq_nsmul, smul_smul, mul_comm N kΦ]
    set w : WO S T := N • (u - p.up FS FT X) with hw
    have e2 : t + (kΦ * N) • u - p.up FS FT (p.down FS FT t + (kΦ * N) • X) =
        (t - p.up FS FT (p.down FS FT t)) + kΦ • w := by
      rw [Witness.up_add, hupn, hw, smul_smul, nsmul_sub]
      abel
    have hwL : w ∈ stdHom S T := nsmul_mem (sub_mem hu hXL) N
    have hwH : IsHalf e w := by
      intro i j
      rw [hw, hX, hud, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, nsmul_eq_mul]
      linear_combination (N : AE D) * hhu i j - (N : AE D) * u i j * he
    show Φ (t + (kΦ * N) • u - p.up FS FT (p.down FS FT (t + (kΦ * N) • u))) * Ψ (p.down FS FT (t + (kΦ * N) • u)) =
      Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)
    rw [hd, e2, e3, hΦi w hwL hwH, hΨi _ _ hYi]
  · obtain ⟨h1, h2⟩ := hsupp t ht
    have a1 := hΦl _ h1
    have a2 : p.up FS FT (N • p.down FS FT t) ∈ stdHom S T := (hInt _).1 fun r q => by
      rw [Matrix.smul_apply, nsmul_eq_mul]; exact hΨl _ h2 r q
    rw [hupn] at a2
    have e1 : (kΦ * N) • t = N • (kΦ • (t - p.up FS FT (p.down FS FT t))) + kΦ • (N • p.up FS FT (p.down FS FT t)) := by
      rw [smul_smul, smul_smul, mul_comm N kΦ, ← nsmul_add, sub_add_cancel]
    rw [e1]
    exact add_mem (nsmul_mem a1 N) (nsmul_mem a2 kΦ)

end GlobalTheory.LocMod.Place
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ → ∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ) := by
  first | exact @GlobalTheory.LocMod.Place.isSBHalf_tensorAt | exact GlobalTheory.LocMod.Place.isSBHalf_tensorAt | (intros; apply GlobalTheory.LocMod.Place.isSBHalf_tensorAt <;> assumption)
end
end

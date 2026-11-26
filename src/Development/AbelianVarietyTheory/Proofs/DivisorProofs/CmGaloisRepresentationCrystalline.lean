module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGL
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistSph

theorem isSpherical_twist_absPow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ), GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a)) →
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
      (CuspSub.isOpen_ker_locDet _ w)).ρ := by
  intro E _ _ _ a w σ s h
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  rw [← hK] at hv
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have h1 : CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w g.1 = 1 := by
    show (GlobalTheory.HeckeGal.Model.absPow E s).loc w (Matrix.GeneralLinearGroup.det g.1) = 1
    rw [GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s) w]
    refine isUnram_absPow _ _ _ ?_
    obtain ⟨u, hu⟩ := g.2
    rw [← hu]
    have h2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation (w.adicCompletion E)).integer (w.adicCompletion E)) u) :
          (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap (ValuativeRel.valuation (w.adicCompletion E)).integer (w.adicCompletion E) u.val.det := by
      rw [RingHom.map_det]; rfl
    rw [h2]
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).1
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  have h3 := hv g
  show ((CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

end GlobalTheory.TwistSph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGLStatement
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_absDetPow_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ), GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a)) →
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
      (CuspSub.isOpen_ker_locDet _ w)).ρ := by
  first | exact @GlobalTheory.TwistSph.isSpherical_twist_absPow | exact GlobalTheory.TwistSph.isSpherical_twist_absPow | (intros; apply GlobalTheory.TwistSph.isSpherical_twist_absPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CsdTwistGal

theorem infChar_conj_of_isCsd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (P : CuspSub E a), P.IsCsd →
    ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), P.HasInfChar τ m →
      P.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  intro E _ _ _ a P hP τ m m' hm hm'
  have h1 : (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
    obtain ⟨T, hT⟩ := hP
    refine ⟨((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm.trans T, fun o φ => ?_⟩
    obtain ⟨φ, rfl⟩ := ((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).surjective φ
    have e : (GlobalTheory.ThetaPull.thetaSub P).op o ((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V φ) =
        (GlobalTheory.ThetaPull.pull E a).submoduleMap P.V (P.op (thetaOp o) φ) :=
      Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
    rw [e]
    exact (congrArg T (((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply _)).trans
      ((hT o φ).trans (congrArg (P.op o)
        (congrArg T (((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply φ)).symm))
  have h2 : (GlobalTheory.ThetaPull.thetaSub P).HasInfChar τ (m'.map Neg.neg) := by
    refine ⟨by rw [Multiset.card_map, hm'.1], ?_⟩
    rintro u _ ⟨φ, hφ, rfl⟩
    change cap τ u (GlobalTheory.ThetaPull.pull E a φ) = _ • GlobalTheory.ThetaPull.pull E a φ
    rw [GlobalTheory.ThetaPull.cap_pull, LinearMap.smul_apply, hm'.2 _ φ hφ, smul_smul, map_smul]
    congr 1
    have e : ((m'.map Neg.neg).map (u + ·)) = (m'.map (-u + ·)).map Neg.neg := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]; ring
    rw [e, Multiset.prod_map_neg, Multiset.card_map, hm'.1]
  have h4 := (h1.hasInfChar h2).unique hm
  rw [← h4, Multiset.map_map]
  simp

theorem rec_twist_absPow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
    (rc : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ),
      rc (GlobalTheory.LocGL.IrrGL.of (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
        (CuspSub.isOpen_ker_locDet _ w)).ρ (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
        (CuspSub.isOpen_ker_locDet _ w)).smooth (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
        (CuspSub.isOpen_ker_locDet _ w)).irred) = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw s := by
  intro E Ω _ _ _ _ _ _ w B h rc hrc a σ s
  obtain ⟨_, _, _, -, H⟩ := hrc
  rw [← H.nu_eq]
  refine congrArg _ ((GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _
    (GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc (GlobalTheory.HeckeGal.Model.absPow E s) w)).symm.trans ?_)
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s) w

theorem exists_galRep_csd_twist : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a))) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  intro hG _ _ _ _ hLL E Ω _ _ _ _ _ _ _ l _ ι a ha P hP m hm hnd f J hJ
  have hτ : ∀ σ : E →+* ℂ, ι.toRingHom.comp (ι.symm.toRingHom.comp σ) = σ := fun σ => by
    ext x; simp
  have hint : ∀ σ : E →+* ℂ, ∀ z ∈ m σ, ∃ k : ℤ, f - z = k := by
    intro σ z hz
    have h1 := hJ (ι.symm.toRingHom.comp σ)
    rw [hτ] at h1
    have h2 : f - z ∈ (m σ).map (fun z => f - z) := Multiset.mem_map_of_mem _ hz
    rw [← h1] at h2
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 h2
    exact ⟨k, hk.symm⟩
  have hfre : f = ((f.re : ℝ) : ℂ) := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨z, hz⟩ : ∃ z, z ∈ m τ0 := Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ0).1]; omega)
    have hc := infChar_conj_of_isCsd E a P hP τ0 _ _ (hm τ0) (hm _)
    have hz' : -z ∈ m (NumberField.ComplexEmbedding.conjugate τ0) := by
      rw [hc]; exact Multiset.mem_map_of_mem _ hz
    obtain ⟨k1, hk1⟩ := hint _ z hz
    obtain ⟨k2, hk2⟩ := hint _ _ hz'
    have e1 := congrArg Complex.im hk1
    have e2 := congrArg Complex.im hk2
    simp only [Complex.sub_im, Complex.intCast_im, Complex.neg_im] at e1 e2
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]; linarith
  set s : ℝ := ((a : ℝ) - 1) / 2 - f.re with hs
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hexpo : ∀ τ, expo (GlobalTheory.HeckeGal.Model.absPow E s) τ = s :=
    (GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s hν
  have hm' : ∀ τ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).HasInfChar τ ((m τ).map (· + (s : ℂ))) := fun τ => by
    have := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rwa [hexpo] at this
  have hinf' : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) :=
    fun τ => CG.HasInfChar.infChar_eq (hm' τ)
  have hr : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf' τ]
    refine ⟨(hnd τ).map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨k, hk⟩ := hint τ y hy
    refine ⟨-k, ?_⟩
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hk + hfre
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι a ha _ _ hr (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s)
  have hHT : ∀ τ, HT τ = J τ := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hinf', hJ τ, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hfre
  refine ⟨r, H.cont, fun hsph => ⟨H.cont, fun PP AI T w A h O _ _ _ Bw hj => ?_⟩, ?_⟩
  · have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := hj.mem_placesOver h
    obtain ⟨σ, hσ, hsp⟩ := hsph w hw
    have HA := H.above PP AI T w A h O Bw hj
    refine ⟨HA.crys _ (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp), fun τ LL' τ' hτ' => ?_⟩
    rw [← hHT]
    exact HA.jumps τ LL' τ' hτ'
  · intro w _ hl σ hσ S hS B g hB hg
    obtain ⟨rc, hrc⟩ := (hLL.1 E Ω B w hB).exists
    have e1 := H.wdOf_eq hl hrc (hσ.twist (GlobalTheory.HeckeGal.Model.absPow E s))
    rw [rec_twist_absPow E Ω w B hB rc hrc a σ s, GlobalTheory.WeilDeligne.WD.lpTw_add] at e1
    rw [GlobalTheory.T.local_langlands_galois_compat E Ω l ι a r H.cont w hl B hB rc hrc σ S hS _ e1 g hg]
    have e2 : ((-(s + (1 - (a : ℝ)) / 2) : ℝ) : ℂ) = f := by
      rw [hfre, hs]; push_cast; ring
    rw [e2]

end GlobalTheory.CsdTwistGal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystallineStatement
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_galois_representation_crystalline : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a))) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  first | exact @GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | exact GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | (intros; apply GlobalTheory.CsdTwistGal.exists_galRep_csd_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinUA

theorem hermA_neg_transpose {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) x y =
      -((fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) ⬝ᵥ
        ((J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) *ᵥ x)) := by
  unfold GlobalTheory.AdLat.hermA
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply,
    TensorProduct.tmul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermA_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (h : (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ *
      (J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) * g =
      J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E))
    (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) (g *ᵥ x) (g *ᵥ y) = GlobalTheory.AdLat.hermA c (-Jᵀ) x y := by
  rw [hermA_neg_transpose, hermA_neg_transpose]
  congr 1
  have e : (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ((g *ᵥ y) b)) =
      (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
    funext b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e]
  conv_rhs => rw [← h]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (Matrix.transpose _),
    Matrix.vecMul_transpose]

theorem isUA_finHom : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : GA D V),
    GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V g
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 (finHom V g).isUnit, fun x y => hermA_mulVec _ _ _ ?_ x y⟩
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1 * JR (AF D.host.F) V.gram * g.1.1
      = JR (AF D.host.F) V.gram := g.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hc : ∀ t, D.sp.cm.sig t = IsCMField.complexConj D.host.E t :=
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.1
  have hφ : ∀ z, φ (sigR (AF D.host.F) D.sp.cm.sig z) =
      GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E) (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [φ, sigR, GlobalTheory.AdLat.sg, hc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hJ : (JR (AF D.host.F) V.gram).map φ =
      V.gram.map fun t => ((1 : Af D.host.F) ⊗ₜ[D.host.F] t : Af D.host.F ⊗[D.host.F] D.host.E) := by
    ext a b
    simp [φ, JR, inclR]
  have h2 := congrArg (fun M => Matrix.map M φ) h
  simp only [Matrix.map_mul] at h2
  rw [hJ] at h2
  have hg : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1).map φ =
      ((g.1.1.map φ).map (GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E)))ᵀ := by
    ext a b
    exact hφ _
  rw [hg] at h2
  exact h2

end GlobalTheory.FinUA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelicStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteUnitaryPart_isInvertibleUnitaryAdelic : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : GA D V),
    GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) := by
  first | exact @GlobalTheory.FinUA.isUA_finHom | exact GlobalTheory.FinUA.isUA_finHom | (intros; apply GlobalTheory.FinUA.isUA_finHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RepsInj
open Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem cc_eq (D : D7) : IsCMField.complexConj D.host.E = GlobalTheory.Member.cF D :=
  AlgEquiv.ext fun x => ((GlobalTheory.Member.latHat_eq_hat_and_gram D D.sp.X').2.2.2.2.2.1 x).symm

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem hermA_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hermA c G (Pi.single i 1) (Pi.single j 1) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G i j := by
  simp [hermA, Pi.single_apply]

theorem hermA_mulVec_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) (i j : Fin n) :
    hermA c G (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1) =
      (gᵀ * G.map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) i j := by
  simp only [hermA, Matrix.mul_apply, Finset.sum_mul, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  rfl

theorem transpose_form' {A : Type} [CommRing A] {m : ℕ} (s : A →+* A) (J g : Matrix (Fin m) (Fin m) A) :
    gᵀ * Jᵀ * g.map s = Jᵀ ↔ Formalism.UG.cT s g * J * g = J := by
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, ← Matrix.mul_assoc, Formalism.UG.cT]

theorem unitary_of_isUA (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsUA c (-Jᵀ) g) :
    Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E)) g * JR (FiniteAdeleRing (𝓞 F) F) J * g =
      JR (FiniteAdeleRing (𝓞 F) F) J := by
  rw [← transpose_form']
  have key : gᵀ * (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
    ext i j
    rw [← hermA_mulVec_single, h.2, hermA_single, Matrix.map_apply]
  have e : (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) = -(JR (FiniteAdeleRing (𝓞 F) F) J)ᵀ := by
    ext i j; simp [JR, inclR, TensorProduct.tmul_neg]
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at key
  exact key

theorem af_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  refine ⟨0, 1, fun h => ?_⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
  exact zero_ne_one h2

theorem incl_inj : Function.Injective (inclR (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
  haveI := af_nontrivial (F := F)
  Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

theorem cT_map_inclR (R : Type) [CommRing R] [Algebra F R] (c : E →ₐ[F] E) (γ : Matrix (Fin n) (Fin n) E) :
    (Formalism.UG.cT (c : E →+* E) γ).map (inclR R) = Formalism.UG.cT (sigR R c) (γ.map (inclR R)) := by
  ext i j
  simp [Formalism.UG.cT, sigR, inclR]

theorem rat_unitary (c : E ≃ₐ[F] E) (J γ : Matrix (Fin n) (Fin n) E) (h : IsUA c (-Jᵀ) (ratM F γ)) :
    γ.det ≠ 0 ∧ Formalism.UG.cT ((c : E →ₐ[F] E) : E →+* E) γ * J * γ = J := by
  have hr : ratM F γ = γ.map (inclR (FiniteAdeleRing (𝓞 F) F)) := rfl
  constructor
  · intro h0
    have hu := h.1
    rw [hr, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
    haveI := af_nontrivial (F := F)
    haveI : Nontrivial (RA F E) := (incl_inj (F := F) (E := E)).nontrivial
    exact not_isUnit_zero hu
  · have hu := unitary_of_isUA c J _ h
    apply Matrix.map_injective (incl_inj (F := F) (E := E))
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
    exact hu

end Gen

theorem gq_of_isUA (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (h : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) γ)) :
    ∃ γ₀ ∈ GQ V, ((finHom V γ₀).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) =
      ratM (maximalRealSubfield D.host.E) γ := by
  rw [cc_eq] at h
  obtain ⟨hd, hu⟩ := rat_unitary _ _ _ h
  let γu : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det γ).2 (Ne.isUnit hd)).unit
  have hU : γu ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hu
  have hm : Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) γu ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT _ (γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) * JR (AF D.host.F) V.gram * γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) =
      JR (AF D.host.F) V.gram
    rw [← cT_map_inclR, JR, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) hU
  refine ⟨⟨_, hm⟩, ⟨γu, hU, rfl⟩, ?_⟩
  ext i j
  rfl

theorem kf_of_isKM (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (κ : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    (h : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M κ) :
    ∃ κA ∈ Kf, ((finHom V κA).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
  rw [cc_eq] at h
  have hu := unitary_of_isUA _ _ _ h.1
  let κu : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ((Matrix.isUnit_iff_isUnit_det κ).2 h.1.1).unit
  have hmem : κu ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := hu
  obtain ⟨κA, hG, hf⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 κu hmem
  refine ⟨κA, (hK κA).2 ⟨hG, ?_⟩, by rw [hf]; rfl⟩
  intro z hz
  rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
  rw [hf]
  exact h.2.1 z hz

theorem reps_inj : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (gA : Comp → GA D V),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ k, (dict (gA k)).1 = k) → ∀ k k',
      GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (gA k)).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
        ((finHom V (gA k')).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) → k = k' := by
  intro D V Comp X dict Kf th M gA hK _ hD hgA k k' hE
  obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
  obtain ⟨γ₀, hγ₀, hγf⟩ := gq_of_isUA D V γ hγ
  obtain ⟨κA, hκA, hκf⟩ := kf_of_isKM D V M Kf hK κ hκ
  have hfin : finHom V (gA k') = finHom V (γ₀ * gA k * κA) := by
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact he.trans (by rw [← hγf, ← hκf])
  have hx : (γ₀ * gA k * κA)⁻¹ * gA k' ∈ GinfC V := by
    show finHom V _ = 1
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
  have hk' : gA k' = γ₀ * gA k * κA * ((γ₀ * gA k * κA)⁻¹ * gA k') := by group
  obtain ⟨h1, h2, ⟨x0, -, h3⟩, -⟩ := hD
  have s3 : (dict (gA k')).1 = (dict (γ₀ * gA k * κA)).1 := by
    obtain ⟨γ', -, e⟩ := h3 (γ₀ * gA k * κA) _ hx
    rw [hk', e]
  have s2 : (dict (γ₀ * gA k * κA)).1 = (dict (γ₀ * gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h2 κA hκA (γ₀ * gA k)
    rw [e]
  have s1 : (dict (γ₀ * gA k)).1 = (dict (gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h1 γ₀ hγ₀ (gA k)
    rw [e]
  rw [← hgA k, ← hgA k', s3, s2, s1]

end GlobalTheory.RepsInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCosetStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentRepresentatives_injective_doubleCoset : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (gA : Comp → GA D V),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ k, (dict (gA k)).1 = k) → ∀ k k',
      GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (gA k)).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
        ((finHom V (gA k')).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) → k = k' := by
  first | exact @GlobalTheory.RepsInj.reps_inj | exact GlobalTheory.RepsInj.reps_inj | (intros; apply GlobalTheory.RepsInj.reps_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GenericEtale

theorem trdeg_eq (k K A B : Type) [CommRing k] [IsDomain k] [Field K] [Algebra k K]
    [IsFractionRing k K] [CommRing A] [Algebra k A] [FaithfulSMul k A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsAlgebraic A B] [Algebra K B] [Algebra k B]
    [IsScalarTower k K B] [IsScalarTower k A B] : Algebra.trdeg K B = Algebra.trdeg k A := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  have : Algebra.IsAlgebraic k K := IsLocalization.isAlgebraic K (nonZeroDivisors k)
  have h₁ := trdeg_add_eq k K (A := B)
  have h₂ := trdeg_add_eq k A (A := B)
  rw [trdeg_eq_zero, zero_add] at h₁
  rw [trdeg_eq_zero (R := A), add_zero] at h₂
  rw [h₁, h₂]

theorem formallySmooth_fractionField (k A L : Type) [CommRing k] [IsDomain k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] [Field L]
    [Algebra A L] [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L] :
    Algebra.FormallySmooth k L ∧ Module.rank L Ω[L⁄k] = Algebra.trdeg k A := by
  let K := FractionRing k
  have hinj : Function.Injective (algebraMap k L) := by
    rw [IsScalarTower.algebraMap_eq k A L]
    exact (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective k A)
  let : Algebra K L := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType k L := .comp k A L
  have : Algebra.EssFiniteType K L := .of_comp k K L
  have : Algebra.FormallySmooth K L := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale k K := .of_isLocalization (nonZeroDivisors k)
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  refine ⟨.comp k K L, ?_⟩
  have hb : Function.Bijective (KaehlerDifferential.map k K L L) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, KaehlerDifferential.map_surjective k K L⟩
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map k K L x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  rw [(LinearEquiv.ofBijective _ hb).rank_eq, rank_kaehler_eq_trdeg, trdeg_eq k K A L]

theorem exists_away (k A : Type) [CommRing k] [IsDomain k] [CharZero k] [IsNoetherianRing k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] {D : ℕ}
    (hd : Algebra.trdeg k A = D) :
    ∃ f : A, f ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension D k (Localization.Away f) := by
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let L := Localization.AtPrime (⊥ : Ideal A)
  have : IsFractionRing A L :=
    (congrArg (fun M : Submonoid A => IsLocalization M L) (Ideal.primeCompl_bot (α := A))).mp
      inferInstance
  have hL : IsField L :=
    (FractionRing.algEquiv A L).symm.toMulEquiv.isField (Field.toIsField (FractionRing A))
  let : Field L := hL.toField
  obtain ⟨h₁, h₂⟩ := formallySmooth_fractionField k A L
  have : Algebra.IsSmoothAt k (⊥ : Ideal A) := h₁
  obtain ⟨f, hf, h⟩ := exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k (⊥ : Ideal A)
    (d := D) (Module.finrank_eq_of_rank_eq (h₂.trans hd))
  exact ⟨f, hf, h⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem trdeg_chart (h : IsArithVar p D) {A : Type} [CommRing A] [Algebra k A]
    (i : Sp A ⟶ X) [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    Algebra.trdeg k A = D := by
  have := h.isDomain
  let K := FractionRing k
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨_, hd⟩ := RegGenSmooth.ringKrullDim_chart h
    (IsPullback.of_hasPullback p (spMap (algebraMap k K))) i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : FaithfulSMul A (K ⊗[k] A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic A (K ⊗[k] A) :=
    IsLocalization.isAlgebraic _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors k))
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)
  have e : d = D := by exact_mod_cast hd₁.symm.trans hd
  rw [← trdeg_eq k K A (K ⊗[k] A), hd₂, e]

theorem exists_etale_coords [IsIntegral X] (h : IsArithVar p D) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have := h.isDomain
  have := h.charZero_base
  have := h.isNoetherianRing
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨f, hf, hs⟩ := exists_away k A (trdeg_chart h i hi)
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hj : j ≫ p = spMap (algebraMap k B) := by
    rw [Category.assoc, hi, IsScalarTower.algebraMap_eq k A B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

end GlobalTheory.GenericEtale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieIndep

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}

theorem lieTie_add {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp C ⟶ S} {ψ : P.A.A.left ⟶ G.left}
    (hψ : IsGrpPullback P.A.A G y ψ) {x x' : LieG P.Gt}
    {u u' : Over.mk (spMap (algebraMap C (DualNumber C)) ≫ y) ⟶ G}
    (h : LieTie P ψ x u.left) (h' : LieTie P ψ x' u'.left) : LieTie P ψ (lieAdd x x') (u * u').left := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  refine ⟨lieAdd xG xG', w * w', h1.mul h1', (hψ.2 _ w w' u u' h2.symm h2'.symm).symm, ?_⟩
  let d : Over.mk ((specO C (DualNumber C)).hom ≫ spMap (algebraMap O C)) ⟶ specO O (DualNumber O) :=
    Over.homMk (spMap (dualMap (algebraMap O C))) (by
      refine (spMap_spMap _ _).trans (Eq.trans (congrArg _ ?_) (spMap_spMap _ _).symm)
      ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  refine (P.gen_pull.2 _ w w' (d ≫ xG.1) (d ≫ xG'.1) h3.symm h3'.symm).symm.trans ?_
  rw [← MonObj.comp_mul]
  rfl

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem lieTie_unique_right {Y : Scheme.{0}} {ψ : P.A.A.left ⟶ Y} {x : LieG P.Gt} {u u' : Sp (DualNumber C) ⟶ Y}
    (h : LieTie P ψ x u) (h' : LieTie P ψ x u') : u = u' := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => (Fact.out : ¬ IsUnit (p : O)) (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have mem_pow {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd (n : ℕ) (x : DualNumber O) :
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hc : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h := (inferInstance : IsAdicComplete (Ideal.span {(p : O)}) O)
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  have e : xG.1 = xG'.1 := (existsUnique_right hp hc x.1).unique h1 h1'
  have e1 : w.left = w'.left :=
    P.gen_pull.1.hom_ext (by rw [h3, h3', e]) ((Over.w w).trans (Over.w w').symm)
  rw [← h2, ← h2', e1]


omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem linearIndependent_evLie {n : ℕ} (x : Fin n → LieG P.Gt)
    (h : ∀ a : Fin n → O, (∀ f : omega P.Gt, ∑ j, a j * f.1 (x j) = 0) → ∀ j, a j = 0) :
    LinearIndependent C (fun j => evLie P (x j)) := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) g
  choose a ha using hb
  have h0 := h a (fun f => P.integers.hom_inj (by
    have h1 := congrArg (fun L : P.OmC →ₗ[C] C => (b : O) • L ((1 : C) ⊗ₜ f)) hg
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_zero, Finset.smul_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ha, ← smul_assoc, smul_eq_mul]
    congr 1
    simp [evLie])) j
  have h2 := ha j
  rw [h0, map_zero, Algebra.smul_def] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_left
    ((map_ne_zero_iff _ P.integers.hom_inj).2 (nonZeroDivisors.ne_zero b.2))

end GlobalTheory.CompHt.TieIndep

namespace GlobalTheory.CompHt


open TieIndep in
theorem linearIndependent_evLie_of_lieTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → LinearIndependent C (fun j => evLie P (x j)) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  have hψ : IsGrpPullback P.A.A Xo.univ.t.G z.x ψ := hz.1 ▸ hP.isGrpPullback
  obtain ⟨N, _, _, w, ρ, -, htan, hcomb, hρ, hsm⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo C z.x
  choose b hb using fun j => (htan _).1 (z.tan τ j)
  have hadd : ∀ {y y' : LieG P.Gt} {m m' : N}, LieTie P ψ y (w m) → LieTie P ψ y' (w m') →
      LieTie P ψ (lieAdd y y') (w (m + m')) := fun {y y' m m'} h h' => by
    obtain ⟨u, h1, h2⟩ := (hcomb 2 ![m, m'] ![1, 1] (w (m + m'))).2 (by simp)
    have e0 : (u 0).left = w m := (h1 0).trans ((hsm 1 m).symm.trans (by rw [one_smul]))
    have e1 : (u 1).left = w m' := (h1 1).trans ((hsm 1 m').symm.trans (by rw [one_smul]))
    rw [← h2, show (List.ofFn u).prod = u 0 * u 1 by simp]
    exact lieTie_add hψ (e0 ▸ h) (e1 ▸ h')
  have hsc : ∀ (a : O) j, LieTie P ψ (AvDefs.lieScale P.Gt a (x j)) (w (algebraMap O C a • b j)) := fun a j => by
    rw [hsm, hb]
    exact (hx j).scale a
  refine linearIndependent_evLie x fun a ha j => ?_
  have h0 := hsc 0 j
  rw [map_zero, zero_smul] at h0
  have hs : ∀ s : Finset (Fin (Dw.mult τ)), ∃ y, LieTie P ψ y (w (∑ i ∈ s, algebraMap O C (a i) • b i)) ∧
      ∀ f : omega P.Gt, f.1 y = ∑ i ∈ s, a i * f.1 (x i) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨_, h0, fun f => by rw [omega_lieScale, zero_mul, Finset.sum_empty]⟩
    | insert i s hi ih =>
      obtain ⟨y, h1, h2⟩ := ih
      rw [Finset.sum_insert hi]
      exact ⟨_, hadd (hsc (a i) i) h1, fun f => by rw [omega_lieAdd, omega_lieScale, h2, Finset.sum_insert hi]⟩
  obtain ⟨y, h1, h2⟩ := hs Finset.univ
  have e : y = AvDefs.lieScale P.Gt 0 (x j) :=
    (Point.omega_free_finite_bijective p C v O (𝓞 E) P).2.2.1 (LinearMap.ext fun f => by
      change f.1 y = f.1 _
      rw [h2, ha, omega_lieScale, zero_mul])
  have e2 := lieTie_unique_right h0 (e ▸ h1)
  have hu : z.u τ = fun i => w (b i) := funext fun i => (hb i).symm
  have e3 := (z.basis τ (w 0) ((htan _).2 ⟨0, rfl⟩) fun t => by rw [← hρ, ← hsm, map_zero, smul_zero]).unique
    (y₁ := fun i => algebraMap O C (a i)) (y₂ := 0) (by rw [hu, hcomb]; exact e2) (by rw [hu, hcomb]; simp)
  exact P.integers.hom_inj ((congrFun e3 j).trans (map_zero _).symm)

end GlobalTheory.CompHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PointGroup

theorem isIntegrallyClosedIn_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_form (hv : v.Integers O) (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate)
    (hζ : Function.Bijective fun a : ℤ_[p] => a • ζ) :
    ∃ B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p], (∀ s χ, pairing G O s χ = B s χ • ζ) ∧
      Function.Bijective B ∧ Function.Bijective B.flip := by
  haveI := isIntegrallyClosedIn_of_integers hv
  let z := LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  refine ⟨(pairing G O).compr₂ z.symm.toLinearMap, fun s χ => (z.apply_symm_apply _).symm, ?_, ?_⟩
  · exact (LinearEquiv.congrRight (M := G.dual.Tate) z.symm).bijective.comp (G.pairing_bijective C)
  · exact (LinearEquiv.congrRight (M := G.Tate) z.symm).bijective.comp (G.pairing_flip_bijective C)

theorem finite_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Finite ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.finite_tate C

theorem free_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Free ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.free_tate C

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O]
  {ε : PreTilt O p} {hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}



variable [Algebra ℤ_[p] O]




end GlobalTheory.PointGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSum
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.RatDegZeros

theorem mem_range_fst : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → x ∈ Set.range (ratFibre.fst p) := by
  intro k _ X p x hx
  let q : Spec (X.residueField x) ⟶ Sp ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (X.residueField x)))
  let y0 := (ratFibre.isPullback p).lift (X.fromSpecResidueField x) q (specZIsTerminal.hom_ext _ _)
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  refine ⟨y0 z, ?_⟩
  have e : (y0 ≫ ratFibre.fst p) z = X.fromSpecResidueField x z := by
    rw [(ratFibre.isPullback p).lift_fst]
  rw [Scheme.Hom.comp_apply] at e
  exact e.trans (X.fromSpecResidueField_apply x z)

end GlobalTheory.RatDegZeros
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

end GlobalTheory.RatFibreClosure
end
end

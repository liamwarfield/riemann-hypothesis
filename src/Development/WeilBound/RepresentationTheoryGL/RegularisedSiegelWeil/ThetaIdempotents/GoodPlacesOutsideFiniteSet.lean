module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.ConjUnitIdeleAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EmbZeroTrivialWittDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.FinPl.LastInhab

open GlobalTheory.Unf.Inhab

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem eventually_charUnramAt (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) :
    ∀ᶠ v : Pl D in Filter.cofinite, CharUnramAt D χ v := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv x h1 h2 h3 h4
  have ha : (x : AE D) - 1 ∈ intAt D (· = v) := by
    refine ⟨Ideal.mem_inf.2 ⟨?_, Submodule.mem_iInf _ |>.2 fun w => ?_⟩, ?_⟩
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, h1, sub_self]
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, GlobalTheory.FinPl.compAt, RingHom.comp_apply, h2 _ w.2, sub_self]
    · rw [RingHom.map_sub, RingHom.map_one]; exact sub_mem h3 (GlobalTheory.HeckeConj.one_mem_intAE D)
  have e : (x : AE D) - 1 = N • (incA D (N : D.host.E)⁻¹ * ((x : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
  obtain ⟨y, hy, hye⟩ : ∃ y, y ∈ intAt D (· = v) ∧ (x : AE D) - 1 = N • y := ⟨_, hv _ ha, e⟩
  refine hker x ⟨h1, h3, h4⟩ ⟨finPart D y, hy.2, ?_⟩
  rw [← RingHom.map_one (finPart D), ← RingHom.map_sub, hye]
  exact (finPart D).toAddMonoidHom.map_nsmul _ _

end GlobalTheory.FinPl.LastInhab

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.SplitPkg
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

structure SplitPkg (D : D7) (v : Pl D) where
  π : Fv D.host.F v ⊗[D.host.F] D.host.E ≃ₐ[Fv D.host.F v] Fv D.host.F v × Fv D.host.F v
  swap : ∀ y, π (sigR (Fv D.host.F v) D.sp.cm.sig y) = (π y).swap
  int : ∀ y, y ∈ intLoc D.host.F D.host.E v ↔
    (π y).1 ∈ v.adicCompletionIntegers D.host.F ∧ (π y).2 ∈ v.adicCompletionIntegers D.host.F

def PlaceEx : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ →
  ∀ r : ℕ, ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, ∃ P : SplitPkg D v,
    (∀ a : Fv D.host.F v, (∀ b ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v (a * b) = 1) ↔
      a ∈ v.adicCompletionIntegers D.host.F) ∧
    (∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 ∈ v.adicCompletionIntegers D.host.F →
      (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 ∈ v.adicCompletionIntegers D.host.F → (P.π u).2 = 1 →
      χ (ideleAt D.host.F D.host.E v u) = 1) ∧
    ∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 = (P.π u).2 → χ (ideleAt D.host.F D.host.E v u) = 1

end PositivityTheory.Rg.Rsw.L.LJPos

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU tensNU_tmul)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

def pkgOf (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : SplitPkg D v where
  π := splitAlgEquiv (isCMExt_host D) τ
  swap := splitAlgEquiv_sigR (isCMExt_host D) τ
  int := fun _ => mem_intLoc_iff_split (isCMExt_host D) τ

theorem sigR_tensNU {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (σ : E →ₐ[F] E) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (y : R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R' σ (tensNU j hj y) = tensNU j hj (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem conjUnit_ideleAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : (Fv F v ⊗[F] E)ˣ) :
    conjUnit σ (ideleAt F E v w) = ideleAt F E v (conjUnit σ w) := by
  refine Units.ext ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) w.1) =
    1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ w.1)
  rw [map_add (f := _), map_sub, map_one, sigR_tensNU, sigR_tensNU, map_one]

theorem resEta_norm {D : D7} {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (x : (AE D)ˣ) :
    χ (x * conjUnit D.sp.cm.sig x) = 1 := by
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  have e : x * conjUnit D.sp.cm.sig x =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) :=
    Units.ext (algebraMap_norm_eq (isCMExt_host D) x.1).symm
  rw [e, h2 η hη, hη.2.2.1, one_pow]

theorem diag_eq_norm {D : D7} {v : Pl D} (P : SplitPkg D v) (u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (hu : (P.π u).1 = (P.π u).2) : ∃ w, u = w * conjUnit D.sp.cm.sig w := by
  have h1 : (P.π u).1 * (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 = 1 := by
    rw [← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one]
  refine ⟨⟨P.π.symm ((P.π u).1, 1), P.π.symm ((P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1, 1), ?_, ?_⟩,
    Units.ext (P.π.injective ?_)⟩
  · rw [← map_mul, Prod.mk_mul_mk, h1, mul_one]; exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_comm, h1, mul_one]; exact map_one _
  · change _ = P.π (P.π.symm ((P.π u).1, 1) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (P.π.symm ((P.π u).1, 1)))
    rw [map_mul, P.swap, AlgEquiv.apply_symm_apply]
    exact Prod.ext (by simp) (by simp [hu])

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : HeightOneSpectrum (𝓞 F)}

omit [NumberField E] in
theorem snd_tensNU_mem {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => AddSubgroup.subset_closure ⟨singleFin v a, fun w => ?_, x, rfl⟩) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · by_cases hw : w = v
    · subst hw; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne hw]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

omit [NumberField E] in
theorem snd_ideleAt_mem {u : (Fv F v ⊗[F] E)ˣ} (hu : u.1 ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1 ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  rw [ideleAt, val_extUnit, map_add (f := _), map_sub, map_one]
  exact add_mem (sub_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, rfl⟩)
    (snd_tensNU_mem (one_mem _))) (snd_tensNU_mem hu)

omit [NumberField E] in
theorem eval_snd_ideleAt {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1) = 1 := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  exact map_extUnit_zero _ (inFin v) (inFin_mul v) (fun a => evalV_singleFin_ne hw a) u

omit [NumberField E] in
theorem fst_ideleAt (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (ideleAt F E v u).1 = 1 :=
  map_extUnit_zero _ _ _ (fun _ => rfl) u

end Gen

theorem unram_ideleAt {D : D7} {χ : (AE D)ˣ →* Circle} {v : Pl D} (h : CharUnramAt D χ v)
    {u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ} (hu : u.1 ∈ intLoc D.host.F D.host.E v)
    (hu' : (u⁻¹).1 ∈ intLoc D.host.F D.host.E v) : χ (ideleAt D.host.F D.host.E v u) = 1 := by
  refine h _ (fst_ideleAt u) (fun w hw => eval_snd_ideleAt hw u) (snd_ideleAt_mem hu) ?_
  rw [← MonoidHom.map_inv]
  exact snd_ideleAt_mem hu'

theorem placeEx : PlaceEx := by
  classical
  intro D ψ hψ χ hχ r hr S
  have hev := (GlobalTheory.T.character_conductor_condition D.host.F ψ hψ).and (GlobalTheory.FinPl.LastInhab.eventually_charUnramAt D χ hχ.1)
  obtain ⟨v, hv, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem (isCMExt_host D) (S ∪ (Filter.eventually_cofinite.1 hev).toFinset)
  rw [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  refine ⟨v, hv.1, pkgOf D v τ, hv.2.1, fun u h1 h2 h3 => ?_, fun u hu => ?_⟩
  · refine unram_ideleAt hv.2.2 (((pkgOf D v τ).int _).2 ⟨h1, by rw [h3]; exact one_mem _⟩)
      (((pkgOf D v τ).int _).2 ⟨h2, ?_⟩)
    have e : ((pkgOf D v τ).π u).2 * ((pkgOf D v τ).π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).2 = 1 := by
      rw [← Prod.snd_mul, ← map_mul, Units.mul_inv, map_one, Prod.snd_one]
    rw [h3, one_mul] at e
    rw [e]; exact one_mem _
  · obtain ⟨w, rfl⟩ := diag_eq_norm _ u hu
    rw [map_mul, ← conjUnit_ideleAt]
    exact resEta_norm hr _

end PositivityTheory.Rg.Rsw.L.LJPos

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.Jp

theorem PositivityTheory.Rg.Rsw.exists_tau {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    (σ : E →ₐ[F] E) (π : Fv F v ⊗[F] E ≃ₐ[Fv F v] Fv F v × Fv F v) (hs : ∀ y, π (sigR (Fv F v) σ y) = (π y).swap) :
    ∃ τ : E →ₐ[F] Fv F v, (∀ y, splitProj τ y = (π y).1) ∧ ∀ y, splitProj (τ.comp σ) y = (π y).2 := by
  let τ : E →ₐ[F] Fv F v :=
    ((AlgHom.fst (Fv F v) (Fv F v) (Fv F v)).restrictScalars F).comp
      (((π : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v × Fv F v).restrictScalars F).comp
        Algebra.TensorProduct.includeRight)
  have hτ : ∀ x, τ x = (π ((1 : Fv F v) ⊗ₜ[F] x)).1 := fun x => rfl
  have hx : ∀ x, (π ((1 : Fv F v) ⊗ₜ[F] σ x)).1 = (π ((1 : Fv F v) ⊗ₜ[F] x)).2 := by
    intro x
    have h0 := congrArg Prod.fst (hs ((1 : Fv F v) ⊗ₜ[F] x))
    simpa [sigR] using h0
  have e : ∀ (a : Fv F v) (x : E), (a ⊗ₜ[F] x : Fv F v ⊗[F] E) = a • ((1 : Fv F v) ⊗ₜ[F] x) := by
    intro a x
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨τ, fun y => ?_, fun y => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [splitProj, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
      rw [e a x, map_smul, Prod.smul_fst, smul_eq_mul, hτ]
    | add y z hy hz => simp only [map_add (f := _), Prod.fst_add, hy, hz]
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [splitProj, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply]
      rw [e a x, map_smul, Prod.smul_snd, smul_eq_mul, hτ, hx]
    | add y z hy hz => simp only [map_add (f := _), Prod.snd_add, hy, hz]

set_option maxHeartbeats 1000000 in
theorem PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound : GoodPlacesOutsideFiniteSet := by
  intro D r ψ hψ χ hχ hr S
  obtain ⟨v, hvS, P, hP1, hP2, hP3⟩ := PositivityTheory.Rg.Rsw.L.LJPos.placeEx D ψ hψ χ hχ r hr S
  obtain ⟨τ, hτ1, hτ2⟩ := PositivityTheory.Rg.Rsw.exists_tau v D.sp.cm.sig P.π P.swap
  refine ⟨v, hvS, ⟨fun a ha => ?_, fun ϖ hϖ => ?_⟩, τ, fun a hnorm => ?_⟩
  · have h := (hP1 a).2 ha 1 (one_mem _)
    rwa [mul_one] at h
  · have hne : (ϖ : Fv D.host.F v) ≠ 0 := by
      intro h0
      apply hϖ.ne_zero
      exact Subtype.ext h0
    have hnot : (ϖ : Fv D.host.F v)⁻¹ ∉ v.adicCompletionIntegers D.host.F := by
      intro hin
      apply hϖ.not_isUnit
      refine isUnit_iff_exists_inv.2 ⟨⟨_, hin⟩, Subtype.ext ?_⟩
      simp [mul_inv_cancel₀ hne]
    have h := (hP1 (ϖ : Fv D.host.F v)⁻¹).not.2 hnot
    push Not at h
    obtain ⟨b, hb, hb1⟩ := h
    refine ⟨⟨b, hb⟩, ?_⟩
    rwa [div_eq_inv_mul]
  · rw [hτ1, hτ2] at hnorm
    have hprod : P.π (a : Fv D.host.F v ⊗[D.host.F] D.host.E) *
        P.π ((a⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h1 : (P.π a).1 * (P.π ((a⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : _)).1 = 1 := by
      have := congrArg Prod.fst hprod
      rwa [Prod.fst_mul, Prod.fst_one] at this
    have h2 : (P.π a).2 * (P.π ((a⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : _)).2 = 1 := by
      have := congrArg Prod.snd hprod
      rwa [Prod.snd_mul, Prod.snd_one] at this
    have hα : (P.π a).1 ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hβ : (P.π a).2 ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have hn : ‖(P.π a).1‖₊ = ‖(P.π a).2‖₊ := by
      apply NNReal.eq
      rw [coe_nnnorm, coe_nnnorm]
      exact hnorm
    have hq1 : (P.π a).1 / (P.π a).2 ∈ v.adicCompletionIntegers D.host.F :=
      nnnorm_le_one_iff_mem.1 (le_of_eq (by rw [nnnorm_div, hn, div_self (nnnorm_ne_zero_iff.2 hβ)]))
    have hq2 : (P.π a).2 / (P.π a).1 ∈ v.adicCompletionIntegers D.host.F :=
      nnnorm_le_one_iff_mem.1 (le_of_eq (by rw [nnnorm_div, hn, div_self (nnnorm_ne_zero_iff.2 hβ)]))
    let u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ :=
      { val := P.π.symm ((P.π a).1 / (P.π a).2, 1)
        inv := P.π.symm ((P.π a).2 / (P.π a).1, 1)
        val_inv := by
          rw [← map_mul, Prod.mk_mul_mk, div_mul_div_comm, mul_comm ((P.π a).1), div_self (mul_ne_zero hβ hα),
            mul_one, Prod.mk_one_one, map_one]
        inv_val := by
          rw [← map_mul, Prod.mk_mul_mk, div_mul_div_comm, mul_comm ((P.π a).2), div_self (mul_ne_zero hα hβ),
            mul_one, Prod.mk_one_one, map_one] }
    have hu : P.π (u : Fv D.host.F v ⊗[D.host.F] D.host.E) = ((P.π a).1 / (P.π a).2, 1) :=
      P.π.apply_symm_apply _
    have hu' : P.π ((u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) =
        ((P.π a).2 / (P.π a).1, 1) :=
      P.π.apply_symm_apply _
    have hχu : χ (ideleAt D.host.F D.host.E v u) = 1 := by
      refine hP2 u ?_ ?_ ?_
      · rw [hu]
        exact hq1
      · rw [hu']
        exact hq2
      · rw [hu]
    have hχw : χ (ideleAt D.host.F D.host.E v (u⁻¹ * a)) = 1 := by
      refine hP3 _ ?_
      rw [Units.val_mul, map_mul, hu', Prod.fst_mul, Prod.snd_mul, div_mul_cancel₀ _ hα, one_mul]
    rw [← mul_inv_cancel_left u a, map_mul, map_mul, hχu, hχw, mul_one]

end

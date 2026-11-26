module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiesOnRamOfInvariant
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} {q : Unif k}

theorem oneOrbit : OneOrbit k n c q := by
  have h1 : ∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
      ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂ := by
    intro L₁ L₂ f₁ f₂ g₁ g₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) (glue g₁) (glue g₂)
    refine ⟨g, by rw [← glue_ker g₁, ← Pair.smul_ker, hg, glue_ker], ?_⟩
    have := (glue_hasVal g₁).gl_smul g
    rwa [hg, Pair.hasVal_one_iff (glue_hasVal g₂), glue_ker] at this
  refine ⟨h1, fun L₀ _ Q h₀ e h => ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu, L'', f'', hG, H⟩
    obtain ⟨g, hg, hg'⟩ := h1 _ _ _ _ (Pair.isGlue Q.hasVal_vec) hG
    refine ⟨u * embX c g, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩),
      (u * embX c g * h₀)⁻¹ * h, ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, mul_smul, mul_smul, e, embX_smul_gluedS, hg, H,
      gluedS_congr hg']
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    obtain ⟨g, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
    refine ⟨_, Radical.conj_mem g hu, g • Q.ker, g • Q.vec, ?_, ?_⟩
    · simpa using Pair.isGlue (Q.hasVal_vec.gl_smul g)
    · rw [← embX_smul_gluedS, ← e, mul_smul _ κ, show κ • L₀ = L₀ from hκ]
      simp only [mul_smul, inv_smul_smul]

instance isLattice_interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [hL : L.IsFullLattice k] : (interX L).IsLattice k := by
  apply Submodule.IsLattice.of_fg k
  exact Submodule.fg_of_fg_map_injective (inX k n c)
    (fun x y h => funext fun r => congrFun h (Sum.inl r))
    (hL.fg.of_le (Submodule.map_comap_le _ _))

variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]

end GlobalTheory.LevelUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.VacSecondPf

variable {D : D7}

theorem latO_of_none (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (hP : ∀ v, ¬ P v) : latO S T LS LT P = ⊥ := by
  rw [eq_bot_iff, latO, AddSubgroup.closure_le]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    ext v : 1
    exact hα v (hP v)
  subst h0
  rw [SetLike.mem_coe, AddSubgroup.mem_bot]
  have hp : pairA D.host.F 0 0 = 0 := rfl
  ext i j
  simp [hp]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem vac_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ P hP f hf h₁ hh₁ h₂ hh₂
  have hflat : ∀ Q : Pl D → Prop, IsFlatFB s Q (flatFB s) := fun Q => (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ Q).2 σ J B s
  have htheta : IsThetaFunO ψ J.W B.V (s.om (h₁, h₂) f) := s.weil.om_pres _ _ hf.1
  have hth0 : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (h₁, h₂) f)) := (hflat P).Heisenberg₂.theta _ htheta
  by_cases hne : ∃ v, P v
  · obtain ⟨v₀, hv₀⟩ := hne
    have a₀ := (hP v₀ hv₀).1
    have hT : ∀ v, P v → Tame D v := fun v hv => (hP v hv).1.tame
    have L1 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW a₀.sdV a₀.sdW P hT
    have L0 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ a₀.sdV₀ a₀.sdW₀ P hT
    have hg : Vac ψ J.W B.V LV LW P (s.om (h₁, h₂) f) := (L1 f).2.1 hf h₁ hh₁ h₂ hh₂
    have hgv := ((L1 _).1.mp hg).2
    refine (L0 _).1.mpr ⟨hth0, fun v hv => ?_⟩
    exact (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B s LV LV₀ LW LW₀ v (hP v hv).1 (hP v hv).2 (flatFB s) (hflat (· = v))
      ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B s) _ (hgv v hv)).1
  · push_neg at hne
    have hbot := latO_of_none J.W₀ B.V₀ (LV₀ : Set _) (LW₀ : Set _) P hne
    refine ⟨hth0, ?_, ?_⟩
    · intro u hu
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [two_nsmul, add_zero, heisO_zero]
    · intro e _ u hu _
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [heisO_zero]

end GlobalTheory.VacSecondPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondFlatMap_vacuum_translate_isVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  first | exact @GlobalTheory.VacSecondPf.vac_second | exact GlobalTheory.VacSecondPf.vac_second | (intros; apply GlobalTheory.VacSecondPf.vac_second <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem GlobalTheory.FinPl.flatFB_om_shift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LW : Lat B.V) (v : Pl D), IsSelfDualC J.W LV → IsSelfDualC B.V LW → Tame D v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ (x : GA D B.V) (κ : GA D B.V), InK B.V LW (· = v) κ → flatFB s (s.om (1, n * x * κ) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s (s.om (1, x) f) := by
  intro D ψ σ J B s LV LW v hLV hLW hv hu f hf n hn hnv x κ hκ
  have hmul : s.om (1, n * x * κ) f = s.om (1, n) (s.om (1, x) (s.om (1, κ) f)) := by
    have : ((1 : GA D J.W), n * x * κ) = (1, n) * (1, x) * (1, κ) := by simp
    rw [this, map_mul, map_mul]; rfl
  have hκf : s.om (1, κ) f = f := by
    refine GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hLV hLW (· = v) ?_ f hf 1 κ ?_ hκ
    · rintro w rfl; exact ⟨hv, hu.1, hu.2⟩
    · refine ⟨one_mem _, ?_⟩
      intro y _
      simp
  have hth : IsThetaFunO ψ J.W B.V (s.om (1, x) f) := s.weil.om_pres _ _ hf.1
  have h := ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B s).equiv _ hth n hn hnv 1 (one_mem _)
  have he : B.o.emb (1, 1) = 1 := map_one B.o.emb
  have he₀ : s.om₀ ((1 : GA D J.W₀), (1 : GA D B.V₀)) = 1 := map_one s.om₀
  rw [map_one, mul_one, he, he₀, Module.End.one_apply] at h
  rw [hmul, hκf, h]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondFlatMap_unipotent_stabilizer_translate_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LW : Lat B.V) (v : Pl D), IsSelfDualC J.W LV → IsSelfDualC B.V LW → Tame D v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ (x : GA D B.V) (κ : GA D B.V), InK B.V LW (· = v) κ → flatFB s (s.om (1, n * x * κ) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s (s.om (1, x) f) := by
  first | exact @GlobalTheory.FinPl.flatFB_om_shift | exact GlobalTheory.FinPl.flatFB_om_shift | (intros; apply GlobalTheory.FinPl.flatFB_om_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepVanishTargetCoreLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), IsStdChar D ψ (-1) → UnrAt s₁ p.v → UnrAt s₂ p.v → ∀ (M₀ : Lat B.V₀) (M₁ : Lat J.W₀) (M : Lat B'.V₀) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)) (P : Pair k n') (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k], IsSelfDualC B.V₀ M₀ → IsSelfDualC J.W₀ M₁ → IsSelfDualC B'.V₀ M → GluedCore B M₀ q α α₀ P → β.IsLat M₁ Q.lat → IsSumFrame B'.o B'.ζ γ γ₀ → (γ₀.IsLat M (lastKer Λ) ∨ γ₀.IsLat M (lastPair q Λ).lat) → ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ M₀ M₁ (· = p.v) Ξ₁ → Vac ψ J.W₀ B'.V₀ M₁ M (· = p.v) Ξ₂ → ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0 := by
  intro D k _ _ _ _ p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL hψ hs₁ hs₂ M₀ M₁ M α α₀ β γ γ₀ P Q Λ _ hM₀ hM₁ hM hG hβ hγ hγ₀ Ξ₁ Ξ₂ hΞ₁ hΞ₂ φ hφ
  obtain ⟨χ, hχ, -, -, hcond⟩ := (GlobalTheory.T.exists_splitPoint_frame_character D).2 k p |>.2 ψ hψ
  have hc := hcond hG.unit
  have hVex := GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place D k p q ψ χ hc hχ
  have hV := (Classical.choose_spec hVex).2
  have hO := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have h₁ := (hO k p n (n' ⊕ Fin 1) ψ hψ B.V₀ J.W₀ α₀ β M₀ M₁ hM₀ hM₁ Ξ₁ hΞ₁).2.2 hG.unit _ _ hG.lat hβ
  have hO₂ := hO k p (n'' ⊕ Fin 1) n ψ hψ J.W₀ B'.V₀ β γ₀ M₁ M hM₁ hM Ξ₂ hΞ₂
  refine (hV n n' n'' σ B J B' s₁ s₂ l vL hs₁ hs₂ α α₀ β γ γ₀ hG.sum hγ P P Q).2 Λ M₀ M₁ M₁ M Ξ₁ Ξ₁ Ξ₂ Ξ₂ h₁ ?_ φ hφ
  exact hγ₀.elim (fun h => Or.inl (hO₂.2.2 hG.unit _ _ hβ h))
    (fun h => Or.inr (hO₂.2.2 hG.unit _ _ hβ h))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
namespace GlobalTheory.FinPl

theorem emb_map_eq_one {D : D7} {S A L : HSp D} (o : OrthDec S A L) {R : Type} [CommRing R] (f : AE D →+* R)
    {a : GA D A} (ha : (Formalism.L2.Theta.mt A a).map f = 1) : (Formalism.L2.Theta.mt S (o.emb (a, 1))).map f = 1 := by
  rw [OrthDec.mt_emb]
  have h1 : Formalism.L2.Theta.mt L (1 : GA D L) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1]
  have hs := congrArg (fun M : Mx D S.rank S.rank => M.map f) o.sum_eq_one
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f)] at hs ⊢
  rw [ha, Matrix.mul_one, Matrix.mul_one, hs]

theorem emb_mem_grpAt {D : D7} {S A L : HSp D} (o : OrthDec S A L) (P : Pl D → Prop) {a : GA D A}
    (ha : a ∈ grpAt A P) : o.emb (a, 1) ∈ grpAt S P := by
  simp only [grpAt, congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at ha ⊢
  have ha' : (Formalism.L2.Theta.mt A a).map (Ideal.Quotient.mk (idAt D P)) = 1 := by
    have := congrArg Units.val ha
    simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using this
  have key := emb_map_eq_one o (Ideal.Quotient.mk (idAt D P)) ha'
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using key

end GlobalTheory.FinPl

theorem GlobalTheory.FinPl.emb_gl_sumFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  intro D k _ _ _ _ p n _ _ σ B β β₀ hsum g
  obtain ⟨hgrp, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨hgrpA, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
  have hmem : B.o.emb (β.gl g, 1) ∈ grpAt B.V₀ (· = p.v) := emb_mem_grpAt B.o _ ((hgrpA _).2 ⟨g, rfl⟩)
  obtain ⟨h, hh⟩ := (hgrp _).1 hmem
  rw [hh]
  congr 1
  set M := (Formalism.L2.Theta.mt B.V₀ (B.o.emb (β.gl g, 1))).map p.pr with hMdef
  have hM : M = β₀.b * h.val * β₀.b' := by rw [hMdef, hh, β₀.gl_mat]

  have hY : (replicateCol (Fin 1) fun i => p.pr (ratV (vecB B.o B.ζ) i)) =
      B.o.jB.map p.pr * replicateCol (Fin 1) fun j => p.pr (ratV B.ζ j) := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat, map_sum, map_mul]
  have hA : M * B.o.jA.map p.pr = B.o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : M * B.o.jB.map p.pr = B.o.jB.map p.pr := by
    have h1 : Formalism.L2.Theta.mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jB, h1, Matrix.mul_one]
  have hemb : ((embX 1 g : GL (n ⊕ Fin 1) k) : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
  have key : M * β₀.b = β₀.b * (embX 1 g).val := by
    rw [hsum, hemb, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hY]
    congr 1
    · rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one,
        Matrix.mul_zero, add_zero, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hB, Matrix.mul_zero, zero_add, Matrix.mul_one]
  apply Units.ext
  calc h.val = β₀.b' * (β₀.b * h.val * β₀.b') * β₀.b := by
        simp only [Matrix.mul_assoc, β₀.b'b, Matrix.mul_one]
        rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
    _ = β₀.b' * (M * β₀.b) := by rw [← hM, Matrix.mul_assoc]
    _ = β₀.b' * (β₀.b * (embX 1 g).val) := by rw [key]
    _ = (embX 1 g).val := by rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  first | exact @GlobalTheory.FinPl.emb_gl_sumFrame | exact GlobalTheory.FinPl.emb_gl_sumFrame | (intros; apply GlobalTheory.FinPl.emb_gl_sumFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedSplitPlaceLineCoordinateIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedSplitPlaceLineCoordinateIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.GluedInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec' (p : SplitPt D k) {S : HSp D} (h : GA D S) (u : Fin S.rank → k) :
    mt S h *ᵥ (fun i => p.sec (u i)) = fun i => p.sec (((mt S h).map p.pr *ᵥ u) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec]

theorem cAe_smul (p : SplitPt D k) {r : ℕ} (z : Fin r → AE D) :
    cA D p.e • z = fun i => cA D (p.sec (p.pr (cA D (z i)))) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, p.sec_pr, map_mul, cA_cA]

def form (p : SplitPt D k) (S : HSp D) (x w : Fin S.rank → k) : k :=
  ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * w j

theorem form_eq (p : SplitPt D k) (S : HSp D) (x : Fin S.rank → k) (c : Fin S.rank → D.host.E) :
    form p S x (fun j => p.pr (cA D (incA D (c j)))) =
      x ⬝ᵥ fun i => p.pr (incA D ((star (S.gram *ᵥ c)) i)) := by
  unfold form
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.star_apply, Matrix.mulVec, dotProduct, star_sum, map_sum, star_mul', map_mul]
  rfl

theorem row_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    star (S.gram *ᵥ vecB o ζ) ᵥ* o.iA = 0 ∧ star (S.gram *ᵥ vecB o ζ) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
  have hr : star (S.gram *ᵥ vecB o ζ) = star ζ ᵥ* (o.iBᴴ * S.gram) := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_mul, gram_conjTranspose]
  rw [hr]
  constructor
  · rw [Matrix.vecMul_vecMul, o.orth, Matrix.vecMul_zero]
  · rw [vecB, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem form_frame (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (hs : IsSumFrame B.o B.ζ β β₀) (y : n ⊕ Fin 1 → k) :
    form p B.V₀ (β₀.b *ᵥ y) (fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j))) =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := by
  obtain ⟨h1, h2⟩ := row_orth B.o B.ζ
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  set r := star (B.V₀.gram *ᵥ vecB B.o B.ζ) with hr
  change form p B.V₀ _ (fun j => p.pr (cA D (incA D (vecB B.o B.ζ j)))) = _
  rw [form_eq, ← hr, hs, Matrix.fromCols_mulVec, add_dotProduct]
  have hA : (⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) = 0 := by
    funext a
    have hm : B.o.jA.map p.pr = B.o.iA.map ι := by
      rw [OrthDec.jA, rat, Matrix.map_map]; rfl
    rw [hm, ← RingHom.map_vecMul, h1]
    simp
  have e1 : ((B.o.jA.map p.pr * β.b) *ᵥ (y ∘ Sum.inl)) ⬝ᵥ (fun i => p.pr (incA D (r i))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
    change ((⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) ᵥ* β.b) ⬝ᵥ _ = 0
    rw [hA, Matrix.zero_vecMul, zero_dotProduct]
  have e2 : (replicateCol (Fin 1) (fun i => p.pr (ratV (vecB B.o B.ζ) i)) *ᵥ (y ∘ Sum.inr)) =
      y (Sum.inr 0) • (⇑ι ∘ vecB B.o B.ζ) := by
    funext i
    simp [Matrix.mulVec, dotProduct, replicateCol, mul_comm, ratV, hι]
  rw [e1, zero_add, e2, smul_dotProduct, smul_eq_mul, mul_comm]
  congr 1
  change (⇑ι ∘ vecB B.o B.ζ) ⬝ᵥ (⇑ι ∘ r) = ι _
  rw [← RingHom.map_dotProduct, dotProduct_comm, h2]

end GlobalTheory.FinPl.GluedInt

open GlobalTheory.FinPl.GluedInt in
theorem GlobalTheory.FinPl.glued_last_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ _ hyp x hx
  have hu := hg.unit.2 B.V₀ L₀
  have hz := cAe_smul p (ratV (vecB B.o B.ζ))
  set zk : Fin B.V₀.rank → k := fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j)) with hzk
  have hN : ∀ y : n ⊕ Fin 1 → k, form p B.V₀ (β₀.b *ᵥ y) zk =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := form_frame p B β β₀ hg.sum
  have hvN := hg.norm
  set N := p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) with hNdef
  have hq0 : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact q.ne_zero
  have hmem : (fun i => cA D (p.sec (zk i))) ∈ latV B.V₀ L₀ (· = p.v) := by
    rw [FrameLat.csec_mem_iff hsd]
    intro x' hx'
    have hb : β₀.b *ᵥ (β₀.b' *ᵥ x') = x' := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    have hy : β₀.b' *ᵥ x' ∈ gluedS q 1 P.ker P.vec := (hg.lat _).2 (by rw [hb]; exact hx')
    rw [← gluedLat_one, mem_gluedLat] at hy
    obtain ⟨s, -, hs⟩ := hy
    have h0 := (hs 0).2.1 rfl
    change form p B.V₀ x' zk ∈ 𝒪[k]
    rw [← hb, hN, h0, Valuation.mem_integer_iff, map_mul, map_mul, hvN, Unif.inv, map_inv₀, ← mul_assoc,
      mul_inv_cancel₀ hq0, one_mul]
    exact s.2
  have hA : cA D p.e • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by rw [hu, hz]; exact hmem
  have h1 := hyp (cA D p.e) hA
  rw [hu, hz, FrameLat.mt_csec] at h1
  rw [mt_sec' p] at hx
  have h2 := (FrameLat.csec_mem_iff hsd _).1 h1 _ hx
  rw [FrameLat.pairing_inv] at h2
  change form p B.V₀ (β₀.b *ᵥ x) zk ∈ 𝒪[k] at h2
  rw [hN, Valuation.mem_integer_iff, map_mul, hvN] at h2
  rw [Valuation.mem_integer_iff, map_mul]
  exact h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedSplitPlaceLineCoordinateIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedSplitPlace_lineCoordinate_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.glued_last_integral | exact GlobalTheory.FinPl.glued_last_integral | (intros; apply GlobalTheory.FinPl.glued_last_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulGluedLatticeFirstPositionCases
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulGluedLatticeFirstPositionCases
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

noncomputable section
namespace GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}

theorem eq_gluedS_of_mem (q : Unif k) {M : Submodule 𝒪[k] (n ⊕ Fin 1 → k)}
    (hq : ∀ x ∈ M, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) {m : n ⊕ Fin 1 → k} (hm : m ∈ M)
    (hm1 : m (Sum.inr 0) = q.inv) : M = gluedS q 1 (interX M) (m ∘ Sum.inl) := by
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  ext y
  rw [GlobalTheory.LevelUnfold.mem_gluedS]
  constructor
  · intro hy
    refine ⟨⟨_, hq y hy⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · have e : inX k n 1 (y ∘ Sum.inl - (⟨_, hq y hy⟩ : 𝒪[k]) • (m ∘ Sum.inl)) =
          y - (⟨_, hq y hy⟩ : 𝒪[k]) • m := by
        ext (j | j)
        · rfl
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - (q.1 : k) * y (Sum.inr 0) * m (Sum.inr 0)
          rw [hm1, mul_right_comm, hqi, one_mul, sub_self]
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hm)
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
      rw [← mul_assoc, mul_comm q.inv, hqi, one_mul]
  · rintro ⟨s, hs, h⟩
    have e : y = inX k n 1 (y ∘ Sum.inl - s • (m ∘ Sum.inl)) + s • m := by
      ext (j | j)
      · change y (Sum.inl j) = (y (Sum.inl j) - (s : k) * m (Sum.inl j)) + (s : k) * m (Sum.inl j)
        ring
      · have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        change y (Sum.inr 0) = 0 + (s : k) * m (Sum.inr 0)
        rw [(h 0).1 rfl, hm1, zero_add, mul_comm]
    rw [e]
    exact add_mem hs (M.smul_mem _ hm)

theorem gluedS_zero_eq_lastPair_lat [Fintype n] (q : Unif k) (L : Submodule 𝒪[k] (n → k))
    [L.IsFullLattice k] :
    gluedS q 1 L 0 = (lastPair q L).lat := by
  change _ = (glue (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last q L)).lat
  rw [glue_lat]
  refine le_antisymm (GlobalTheory.LevelUnfold.gluedS_le_iff.2 ⟨fun y hy => ?_, ?_, fun i hi => absurd hi (by omega)⟩)
    (sup_le (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
  · refine Submodule.mem_sup_left (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa [inX] using hy, ?_⟩)
    simp [inX]
  · rw [map_zero, add_zero]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · obtain ⟨h1, h2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
    refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨⟨(q.1 : k) * y (Sum.inr 0), mul_mem q.1.2 h2⟩, by simpa using h1,
      fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
    rw [← mul_assoc, mul_comm q.inv, GlobalTheory.LevelUnfold.mul_inv_q, one_mul]
  · have := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) L (0 : n → k)
    rwa [map_zero, add_zero] at this

theorem smul_gluedS_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k),
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec →
    (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) →
    (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨
      h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨
    ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  intro k _ _ _ _ n _ _ q P h hz hq
  have hML : (h • gluedS q 1 P.ker P.vec).IsFullLattice k := inferInstance
  generalize h • gluedS q 1 P.ker P.vec = M at hz hq hML ⊢
  have : (interX M).IsFullLattice k := by
    refine { toIsLattice := Submodule.IsLattice.of_fg k ?_, span_eq_top := ?_ }
    · exact Submodule.fg_of_fg_map_injective (inX k n 1)
        (fun x y e => funext fun i => congrFun e (Sum.inl i))
        (hML.fg.of_le (Submodule.map_comap_le _ _))
    · refine eq_top_iff.2 fun x _ => ?_
      have hx : inX k n 1 x ∈ Submodule.span k (M : Set (n ⊕ Fin 1 → k)) :=
        hML.span_eq_top ▸ Submodule.mem_top
      obtain ⟨y, hy, d, hd⟩ := (IsLocalization.mem_span_iff (M := nonZeroDivisors 𝒪[k])).1 hx
      have hdx : (d : 𝒪[k]) • x ∈ interX M := by
        change inX k n 1 ((d : 𝒪[k]) • x) ∈ M
        rw [map_smul, hd, ← IsScalarTower.algebraMap_smul k (d : 𝒪[k]), smul_smul,
          IsLocalization.mk'_spec', map_one, one_smul]
        simpa only [Submodule.span_eq] using hy
      have h := (Submodule.span k (interX M : Set (n → k))).smul_mem
        (IsLocalization.mk' k 1 d) (Submodule.subset_span hdx)
      rwa [← IsScalarTower.algebraMap_smul k (d : 𝒪[k]), smul_smul,
        IsLocalization.mk'_spec, map_one, one_smul] at h
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  by_cases hO : ∀ x ∈ M, x (Sum.inr 0) ∈ 𝒪[k]
  · refine Or.inl ⟨interX M, inferInstance, Or.inl ?_⟩
    ext y
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    constructor
    · intro hy
      refine ⟨?_, hO y hy⟩
      have e : inX k n 1 (y ∘ Sum.inl) = y - (⟨_, hO y hy⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hz)
    · rintro ⟨h1, h2⟩
      have e : y = inX k n 1 (y ∘ Sum.inl) + (⟨_, h2⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change y (Sum.inr 0) = 0 + y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      rw [e]
      exact add_mem h1 (M.smul_mem _ hz)
  · push Not at hO
    obtain ⟨m₀, hm₀, hm₀'⟩ := hO
    have ht : IsUnit (⟨_, hq m₀ hm₀⟩ : 𝒪[k]) := by
      by_contra ht
      obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((IsLocalRing.mem_maximalIdeal _).2 ht)
      apply hm₀'
      have h' : (q.1 : k) * m₀ (Sum.inr 0) = (q.1 : k) * s := congrArg Subtype.val hs
      rw [mul_left_cancel₀ q.ne_zero h']
      exact s.2
    obtain ⟨u, hu⟩ := ht
    have hu' : ((u : 𝒪[k]) : k) = (q.1 : k) * m₀ (Sum.inr 0) := congrArg Subtype.val hu
    have hinv : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * ((u : 𝒪[k]) : k) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      exact this
    set m : n ⊕ Fin 1 → k := ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • m₀
    have hm : m ∈ M := M.smul_mem _ hm₀
    have hm1 : m (Sum.inr 0) = q.inv := by
      change ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * m₀ (Sum.inr 0) = (q.1 : k)⁻¹
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← hinv, hu']
      ring
    have hMeq := eq_gluedS_of_mem q hq hm hm1
    have hqf : q.1 • (m ∘ Sum.inl) ∈ interX M := by
      have e : inX k n 1 (q.1 • (m ∘ Sum.inl)) = q.1 • m - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · change (q.1 : k) * m (Sum.inl j) = (q.1 : k) * m (Sum.inl j) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inl j)
          simp
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = (q.1 : k) * m (Sum.inr 0) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          rw [hm1, hqi]
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem (M.smul_mem _ hm) hz
    by_cases hf : m ∘ Sum.inl ∈ interX M
    · refine Or.inl ⟨interX M, inferInstance, Or.inr ?_⟩
      calc M = gluedS q 1 (interX M) (m ∘ Sum.inl) := hMeq
        _ = gluedS q 1 (interX M) 0 := GlobalTheory.LevelUnfold.gluedS_congr (by simpa using hf)
        _ = (lastPair q (interX M)).lat := gluedS_zero_eq_lastPair_lat q _
    · refine Or.inr ?_
      have hG : IsGlue (interX M) (m ∘ Sum.inl) := (isGlue_iff q).2 ⟨inferInstance, hf, hqf⟩
      obtain ⟨g, hg1, hg2⟩ := (GlobalTheory.LevelUnfold.oneOrbit (k := k) (n := n) (c := 1) (q := q)).1 P.ker (interX M)
        P.vec (m ∘ Sum.inl) (Pair.isGlue P.hasVal_vec) hG
      refine ⟨g, ?_⟩
      rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, hg1, GlobalTheory.LevelUnfold.gluedS_congr hg2]
      exact hMeq

end GlobalTheory.GluedOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulGluedLatticeFirstPositionCasesStatement
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_gluedLatticeFirstPosition_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k), (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec → (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) → (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨ h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨ ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  exact @GlobalTheory.GluedOrbit.smul_gluedS_cases
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

namespace GlobalTheory.FinPl

theorem sec_mul_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) (a : AE D) (u : k) : p.sec (p.pr a * u) = a * p.sec u := by
  have h1 : p.sec (p.pr a * u) = p.sec (p.pr (a * p.sec u)) := by rw [map_mul p.pr, p.pr_sec]
  have h2 : p.e * p.sec u = p.sec u := by rw [← p.sec_pr, p.pr_sec]
  rw [h1, p.sec_pr, mul_left_comm, h2]

theorem mulVec_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) {r : ℕ} (m : Matrix (Fin r) (Fin r) (AE D)) (u : Fin r → k) :
    m *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((m.map p.pr *ᵥ u) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, sec_mul_sec]

theorem single_mem_gluedS {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) :
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec := by
  refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨q.1, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
  · have h0 : (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
      funext j
      simp
    rw [h0, zero_sub]
    exact neg_mem (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Pi.single_eq_same, Unif.inv, inv_mul_cancel₀ q.ne_zero]

theorem zero_col_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), GluedCore B L₀ q β β₀ P → ∀ γ : GA D B.V₀, (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i)) ∈ latV B.V₀ L₀ (· = p.v) := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hg γ hpres
  have he : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have hvec : p.sec 1 • ratV (vecB B.o B.ζ) =
      fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, he, mulVec_single_one, hg.sum]
    simp [p.sec_pr]
  have hmem : p.sec 1 • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by
    rw [hg.unit.2, hvec, ← hg.lat]
    exact single_mem_gluedS q P
  have := hpres _ hmem
  rwa [hg.unit.2, hvec] at this

theorem orbitGlued (D : D7) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ)
      (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1))
      (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P →
      ∀ γ ∈ grpAt B.V₀ (· = p.v),
        (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) →
          mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) →
        (∃ a ∈ grpAt B.A (· = p.v), ∃ κ, InK B.V₀ L₀ (· = p.v) κ ∧ γ = B.o.emb (a, 1) * κ) ∨
        ∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k),
          β₀.IsLatMoved γ L₀ (lastKer Λ) ∨ β₀.IsLatMoved γ L₀ (lastPair q Λ).lat := by
  intro k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ hγ hpres
  obtain ⟨hF1, -, -, hF4, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨h, rfl⟩ := (hF1 γ).1 hγ
  have key : ∀ x, mt B.V₀ (β₀.gl h)⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) ↔
      x ∈ h • gluedS q 1 P.ker P.vec := by
    intro x
    rw [← map_inv, mulVec_sec, β₀.gl_mat, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, β₀.b'b,
      Matrix.mul_one, ← mulVec_mulVec, ← hg.lat, GlobalTheory.LatPair.mem_smul_iff]
    rfl
  have hz := (key _).1 (zero_col_mem D k p n q σ B L₀ β β₀ P hg _ hpres)
  have hint : ∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] :=
    fun x hx => GlobalTheory.T.gluedSplitPlace_lineCoordinate_integral D k p n q σ B L₀ β β₀ P hsd hg _ hγ hpres x ((key x).2 hx)
  rcases GlobalTheory.T.smul_gluedLatticeFirstPosition_cases k n q P h hz hint with ⟨Λ, hΛ, hM | hM⟩ | ⟨g, hM⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inl fun x => by rw [← hM]; exact (key x).symm⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inr fun x => by rw [← hM]; exact (key x).symm⟩
  · obtain ⟨hA1, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hF4 L₀ hsd
    have hΛG : Λ₀ = gluedS q 1 P.ker P.vec := Submodule.ext fun x => (hΛ₀ x).trans (hg.lat x).symm
    refine Or.inl ⟨β.gl g, (hA1 _).2 ⟨g, rfl⟩, β₀.gl ((embX 1 g)⁻¹ * h), ?_, ?_⟩
    · rw [hK, hΛG, mul_smul, hM, inv_smul_smul]
    · rw [GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal D k p n σ B β β₀ hg.sum g, ← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlaceStatement
alias GlobalTheory.T.threeOrbits_gluedCore_atPlace := GlobalTheory.FinPl.orbitGlued
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.DoubleStep

theorem hand0_smul_snd_of_bessel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) (c : ℂ), hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂) = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ := by
  intro D ψ σ B J B' s₁ s₂ l vL φ Ξ₁ Ξ₂ c
  funext h₁
  simp only [hand0, handFB, pairKer, contractT, thPair, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    MeasureTheory.integral_const_mul]

end GlobalTheory.DoubleStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDoubleStep_linear_in_secondDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) (c : ℂ), hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂) = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ := by
  first | exact @GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | exact GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | (intros; apply GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamified
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

theorem suppSecond_holds : ∀ D : D7, SuppSecond D := by
  intro D k _ _ _ _ ι p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL Λ P a b a' sh sd₂ Φ₁ Φ₂ hΦ₁ hΦ₂
  have tameP : ∀ v, P v → Tame D v := fun v hv => (sh.good v hv).tame
  refine ⟨?_, fun h₁ hh₁ => ⟨?_, ?_⟩⟩
  · exact GlobalTheory.T.vacuum_fixed_by_levelPair_at_selfDualPlaces D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ P
      (fun v hv => ⟨(sh.good v hv).sdW, sd₂, tameP v hv, (sh.unr v hv).2.1, (sh.unr v hv).2.2⟩) Φ₂ hΦ₂
  · intro h₂ hh₂
    exact GlobalTheory.T.secondFlatMap_vacuum_translate_isVacuum D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ P (fun v hv => ⟨sh.adapt v hv, (sh.unr v hv).2⟩) Φ₂ hΦ₂
      h₁ hh₁ h₂ hh₂
  · intro g hg φ hφ h₂ hne
    have key := GlobalTheory.T.placewise_to_adelicDecomposition_forall D B'.V Λ.L₂ P sd₂ (besGrp B'.d B'.o) h₂ ?_
    · exact key
    intro v hv
    obtain ⟨hv', hhv, h', hh', rfl⟩ := GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace D B'.V h₂ v
    refine ⟨hv', hhv, h', hh', rfl, ?_⟩
    have gd := sh.good v hv
    have ad := sh.adapt v hv
    have sdL₁ : IsSelfDualC J.W Λ.L₁ := gd.sdW

    have hΦ₂v : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) Φ₂ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ P tameP Φ₂).1.mp hΦ₂).2 v hv
    set f := s₂.om (h₁, h') Φ₂ with hfdef
    have hf : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) f :=
      (GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ (· = v)
        (fun w hw => hw ▸ gd.tame) Φ₂).2.1 hΦ₂v h₁ (GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone D J.W P (· = v) (fun w hw => hw ▸ hv) hh₁) h' hh'

    set Ξ₁ := flatBF s₁ (s₁.om (g, h₁) Φ₁) with hΞ₁def
    have hΞ₁P : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ :=
      ((GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all D ψ (σ + 1) B J s₁ Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ P (fun w hw => sh.good w hw)
        (fun w hw => (sh.unr w hw).1) sdL₁ Φ₁ hΦ₁).2 g hg).2 h₁ hh₁
    have hΞ₁ : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ (· = v) Ξ₁ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V₀ J.W₀ s₁.χV s₁.χW s₁.om₀ s₁.weil₀ Λ.M₀ Λ.M₁ gd.sdV₀ gd.sdW₀ P tameP Ξ₁).1.mp
        hΞ₁P).2 v hv

    have hom : s₂.om (h₁, hv' * h') Φ₂ = s₂.om (1, hv') f := by
      rw [hfdef, show ((h₁, hv' * h') : GA D J.W × GA D B'.V) = (1, hv') * (h₁, h') by simp, map_mul]
      rfl
    have hand_eq : Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (hv' * h') =
        hand0 s₁ s₂ l vL φ Ξ₁ (flatFB s₂ (s₂.om (1, hv') f)) := by
      simp only [Chain.hand, hand0, hom, hΞ₁def]
    rw [hand_eq] at hne
    have hne' : flatFB s₂ (s₂.om (1, hv') f) ≠ 0 := by
      intro h0
      apply hne
      rw [h0, show (0 : WO J.W₀ B'.V₀ → ℂ) = (0 : ℂ) • (0 : WO J.W₀ B'.V₀ → ℂ) by simp, GlobalTheory.T.besselDoubleStep_linear_in_secondDatum, zero_smul]
    obtain ⟨nn, hnF, hnv, γ, hγ, κ, hκ, hdec, hγp⟩ :=
      (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v ad (sh.unr v hv).2 (flatFB s₂)
        ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B' s₂) ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B' s₂) f hf).2 hv' hhv hne'
    by_cases hgl : ∃ i, v = (p i).v
    · obtain ⟨i, rfl⟩ := hgl
      rcases GlobalTheory.T.threeOrbits_gluedCore_atPlace D k (p i) n'' q σ B' Λ.M₂ (a'.α i) (a'.α₀ i) (a'.P i) ad.sdW₀ (sh.gl' i) γ hγ hγp with
        ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ | ⟨Λ₀, hΛ₀, hmov⟩
      · obtain ⟨r, hr, hrv, κ', hκ', heq⟩ :=
          GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B' Λ.L₂ Λ.M₂ (p i).v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
        exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩
      · exfalso
        apply hne
        obtain ⟨M, sdM, hMov, hvacM⟩ :=
          GlobalTheory.T.secondFlatMap_moved_core_lattice_vacuum D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ (p i).v ad (sh.unr _ hv).2 f hf γ hγ
        have hlat : (a'.α₀ i).IsLat M (lastKer Λ₀) ∨ (a'.α₀ i).IsLat M (lastPair q Λ₀).lat := by
          rcases hmov with h | h
          · exact Or.inl (GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
          · exact Or.inr (GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
        obtain ⟨φf, hφf, hφP⟩ := hφ.2 i
        have hz := GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice D k (p i) n n' n'' q ψ σ B J B' s₁ s₂ l vL s₂.weil.std (sh.unr _ hv).1
          (sh.unr _ hv).2 Λ.M₀ Λ.M₁ M (a.α i) (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (a.P i) (b.Q i) Λ₀ gd.sdV₀ gd.sdW₀
          sdM (sh.gl i) (sh.mid i) (sh.gl' i).sum hlat Ξ₁ _ hΞ₁ hvacM φf hφf
        rw [hφP] at hz
        rw [hdec, GlobalTheory.T.secondFlatMap_unipotent_stabilizer_translate_scalar D ψ σ J B' s₂ Λ.L₁ Λ.L₂ (p i).v sdL₁ sd₂ gd.tame (sh.unr _ hv).2 f hf nn hnF hnv _ κ hκ,
          GlobalTheory.T.besselDoubleStep_linear_in_secondDatum, hz, smul_zero]
    · obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split D σ B' Λ.M₂ v gd.tame ad.sdW₀
        (sh.split v hv fun i h => hgl ⟨i, h⟩) γ hγ hγp
      obtain ⟨r, hr, hrv, κ', hκ', heq⟩ := GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B' Λ.L₂ Λ.M₂ v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
      exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamifiedStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBessel_second_step_flat_support_ramified : ∀ D : D7, GlobalTheory.FinPl.SuppSecond D := by
  first | exact @GlobalTheory.FinPl.suppSecond_holds | exact GlobalTheory.FinPl.suppSecond_holds | (intros; apply GlobalTheory.FinPl.suppSecond_holds <;> assumption)
end

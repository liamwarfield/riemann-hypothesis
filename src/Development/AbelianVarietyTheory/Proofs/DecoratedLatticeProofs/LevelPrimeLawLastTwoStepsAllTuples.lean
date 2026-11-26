module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensColPhiOneCharIndSmul
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

section Translate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_phiOne_charInd_smul (χ : AddChar 𝓀[k] ℂ) (P₁ : Pair k n') (Q : Pair k n) (g : GL n k)
    (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol (phiOne P₁ Q) (charInd χ Q) ((g⁻¹ : GL n k).val * x) =
      tensCol (phiOne P₁ (g • Q)) (charInd χ (g • Q)) x := by
  have hcol : (fun i => ((g⁻¹ : GL n k).val * x) i (Sum.inr 0)) = (g⁻¹ : GL n k) • (fun i => x i (Sum.inr 0)) := rfl
  have hsub : ((g⁻¹ : GL n k).val * x).submatrix id Sum.inl = (g⁻¹ : GL n k).val * x.submatrix id Sum.inl := rfl
  have hphi : ∀ z : Matrix n n' k, phiOne P₁ (g • Q) z = phiOne P₁ Q ((g⁻¹ : GL n k).val * z) := by
    intro z
    have h := phiOne_smul (P := P₁) (Q := Q) (x := z) (1 : GL n' k) g
    rw [one_smul] at h
    rw [h, Units.val_one, Matrix.mul_one]
  have hchi : ∀ y : n → k, charInd χ (g • Q) y = charInd χ Q ((g⁻¹ : GL n k) • y) := by
    intro y
    unfold charInd vecInd
    rw [Pair.smul_lat, mem_smul_iff]
    split_ifs with hy
    · have hv := Pair.hasVal_ev (P := g • Q) (x := y) (by rw [Pair.smul_lat, mem_smul_iff]; exact hy)
      rw [Pair.smul_hasVal] at hv
      rw [hv.ev_eq]
    · simp
  unfold tensCol
  rw [hsub, hcol, hphi, hchi]

end Translate

end GlobalTheory.FinPl

namespace GlobalTheory.FinPl

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem SmallPl.exists_card_withLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] :
    ∃ N : ℕ, 0 < N ∧ ∀ Q : Pair k n, (withLat Q.lat).card = N := by
  by_cases h : Nonempty (Pair k n)
  · obtain ⟨Q₀⟩ := h
    refine ⟨(withLat Q₀.lat).card, Finset.card_pos.2 ⟨Q₀, mem_withLat.2 rfl⟩, fun Q => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
    refine Finset.card_nbij' (fun P => g⁻¹ • P) (fun P => g • P) ?_ ?_ ?_ ?_
    · intro P hP
      have hP' : P.lat = g • Q₀.lat := mem_withLat.1 hP
      refine Finset.mem_coe.2 (mem_withLat.2 ?_)
      rw [Pair.smul_lat, hP', inv_smul_smul]
    · intro P hP
      have hP' : P.lat = Q₀.lat := mem_withLat.1 hP
      refine Finset.mem_coe.2 (mem_withLat.2 ?_)
      rw [Pair.smul_lat, Pair.smul_lat, hP']
    · intro P _
      exact smul_inv_smul g P
    · intro P _
      exact inv_smul_smul g P
  · exact ⟨1, one_pos, fun Q => (h ⟨Q⟩).elim⟩

theorem SmallPl.liftA_contAut {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V₀ A L S : HSp D} (o : OrthDec V₀ A L)
    (hA : CoCpt A) {χV χW : (AE D)ˣ →* Circle} {om : Om V₀ S} (hW : IsWeilDatumO ψ V₀ S χV χW om) (vA : Vol A)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) {Ξ : WO V₀ S → ℂ} (hΞ : IsThetaFunO ψ V₀ S Ξ) :
    IsContAut S fun h => liftA o om vA φ Ξ h 0 := by
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hlift : (fun h => liftA o om vA φ Ξ h 0) = fun h =>
      ∫ h₀ in vA.𝓕, φ h₀ * om (o.emb (h₀, 1), h) Ξ 0 ∂vA.μ := by
    funext h
    simp only [liftA]
    congr 1
    funext h₀
    rw [show ((0 : WO A S), (0 : WO L S)) = 0 from rfl, map_zero]
  rw [hlift]
  have jc := GlobalTheory.Unf.jointCont_all D ψ V₀ S χV χW om hW Ξ hΞ
  have hK₂c : Continuous (Function.uncurry fun (x : GA D A) (h : GA D S) => φ x * om (o.emb (x, 1), h) Ξ 0) := by
    have hmap : Continuous fun z : GA D A × GA D S => ((o.emb (z.1, 1), z.2), (0 : WO V₀ S)) :=
      ((o.continuous_emb.comp (continuous_fst.prodMk continuous_const)).prodMk continuous_snd).prodMk
        continuous_const
    exact (hφ.2.comp continuous_fst).mul (jc.comp hmap)
  have hK₂a : ∀ γ ∈ GQ A, ∀ (x : GA D A) (h : GA D S),
      φ (γ * x) * om (o.emb (γ * x, 1), h) Ξ 0 = φ x * om (o.emb (x, 1), h) Ξ 0 := by
    intro γ hγ x h
    have e : o.emb (γ * x, 1) = o.emb (γ, 1) * o.emb (x, 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    have hq := GlobalTheory.Unf.om_rat_mul D ψ V₀ S _ _ om hW Ξ hΞ (o.emb (γ, 1))
      (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (x, 1)) h 0
    rw [one_mul] at hq
    rw [hφ.1 γ hγ x, e, hq, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨fun γ hγ h => ?_,
    (GlobalTheory.CocompactParam.continuous_integral_param D A hA vA (GA D S) _ hK₂c hK₂a).2.1⟩
  dsimp only
  congr 1
  funext x
  have hq := GlobalTheory.Unf.om_rat_mul D ψ V₀ S _ _ om hW Ξ hΞ 1 (one_mem _) γ hγ (o.emb (x, 1)) h 0
  rw [one_mul] at hq
  rw [hq, Matrix.mul_zero, Matrix.zero_mul]

theorem SmallPl.integral_sum_translates {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hS : CoCpt S)
    {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T χS χT om) (vS : Vol S) {Φ₂ : WO S T → ℂ}
    (hθ : IsThetaFunO ψ S T Φ₂) {ι : Type} (s : Finset ι) (b : ι → GA D S) (hfix : ∀ i ∈ s, om (b i, 1) Φ₂ = Φ₂)
    {G : GA D S → ℂ} (hG : IsContAut S G) (c : ℂ) (h' : GA D T) :
    (∫ h in vS.𝓕, om (h, h') Φ₂ 0 * (c * ∑ i ∈ s, G (h * b i)) ∂vS.μ) =
      c * s.card * ∫ h in vS.𝓕, om (h, h') Φ₂ 0 * G h ∂vS.μ := by
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hHc : Continuous fun h => om (h, h') Φ₂ 0 :=
    (hW.om_cont Φ₂ hθ 0).comp (continuous_id.prodMk continuous_const)
  have hHa : ∀ γ ∈ GQ S, ∀ h, om (γ * h, h') Φ₂ 0 = om (h, h') Φ₂ 0 := by
    intro γ hγ h
    have hq := GlobalTheory.Unf.om_rat_mul D ψ S T _ _ om hW Φ₂ hθ γ hγ 1 (one_mem _) h h' 0
    rw [one_mul] at hq
    rw [hq, Matrix.mul_zero, Matrix.zero_mul]
  have hHb : ∀ i ∈ s, ∀ h, om (h * b i, h') Φ₂ 0 = om (h, h') Φ₂ 0 := by
    intro i hi h
    have : ((h * b i, h') : GA D S × GA D T) = (h, h') * (b i, 1) := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [this, map_mul, Module.End.mul_apply, hfix i hi]
  obtain ⟨K, hK⟩ : ∃ K : GA D S → ℂ, K = fun h => om (h, h') Φ₂ 0 * G h := ⟨_, rfl⟩
  have hKc : Continuous K := hK ▸ hHc.mul hG.2
  have hKa : ∀ γ ∈ GQ S, ∀ h, K (γ * h) = K h := fun γ hγ h => by
    rw [hK]
    dsimp only
    rw [hHa γ hγ h, hG.1 γ hγ h]
  have hint : ∀ i ∈ s, IntegrableOn (fun h => c * K (h * b i)) vS.𝓕 vS.μ := by
    intro i _
    refine (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun h _ => c * K (h * b i)) ?_ ?_).1 ()
    · exact (continuous_const.mul (hKc.comp (continuous_mul_const _))).comp continuous_fst
    · intro γ hγ h _
      rw [mul_assoc γ h, hKa γ hγ]
  calc (∫ h in vS.𝓕, om (h, h') Φ₂ 0 * (c * ∑ i ∈ s, G (h * b i)) ∂vS.μ)
      = ∫ h in vS.𝓕, ∑ i ∈ s, c * K (h * b i) ∂vS.μ := by
        refine integral_congr_ae (ae_of_all _ fun h => ?_)
        dsimp only
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hK]
        dsimp only
        rw [hHb i hi h]
        ring
    _ = ∑ i ∈ s, c * ∫ h in vS.𝓕, K h ∂vS.μ := by
        rw [integral_finsetSum _ hint]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund K hKa]
    _ = _ := by
        rw [hK, Finset.sum_const, nsmul_eq_mul]
        ring

theorem smallOne : ∀ D : D7, SmallOne D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ hχ
  obtain ⟨r₀, e, hr₀, hsrc⟩ := GlobalTheory.T.gluedPlaceSourceConstant_proof D k p n n' q χ hχ
  obtain ⟨N, hN0, hN⟩ := SmallPl.exists_card_withLat k n
  refine ⟨r₀ * N, e, mul_pos hr₀ (Nat.cast_pos.2 hN0), ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hW₁ hWT hV hW hχS hχT vA vS vT α α₀ β hsum P Q s L₁ L₂ L₂' L₃
    f₁ Ξ Ξ' Φ₂ hΞ hΞ' hsd₂ hsd₃ hlat hvac φ₀ hφ₀ F hF
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨χr, hχr⟩ : ∃ χr, χr = resChar χ hχ q := ⟨_, rfl⟩
  rw [← hχr] at hΞ' hsrc ⊢
  have hob := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW₁.std V₀ S α₀ β L₁ L₂ hΞ.1 hΞ.2.1 f₁ hΞ.2.2.1
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  obtain ⟨Ξ'', hΞ'', -⟩ := hob.1 (tensCol (phiOne P (s • Q)) (charInd χr (s • Q)))
    (hsb.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _) (hsb.2.2 _ _))
  have hram := (GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k p n' q χ hχ χr hχr s A α P).2.1 φ hφ
  have hram1 := ((GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k p n' q χ hχ χr hχr 1 A α P).2.1 φ hφ).1
  rw [map_one, Module.End.one_apply] at hram1

  have hmove : liftA o om₁ vA (FFStar q χr φ P) Ξ'' = liftA o om₁ vA (sOp α P q χr s (φ P)) Ξ' := by
    obtain ⟨lS, hlS, hθ⟩ := GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift D k p n n' ψ V₀ A L S o ζ hζ hA vA χV χW om₁ hW₁ α α₀ β hsum
    obtain ⟨θ, hθv, hθe⟩ := hθ L₁ L₂ f₁ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P (s • P)
    have hgs : g ∈ latStab P.lat := by
      change g • P.lat = P.lat
      rw [← Pair.smul_lat, hg, Pair.dia_lat]
    have h1 := hθe g ⟨FFStar q χr φ P, hram1.2.2 P⟩ _ hΞ''.2.2.2.1
    have b2 : (fun x => tensCol (phiOne P (s • Q)) (charInd χr (s • Q)) (x * (SrcGl.blk g).val)) =
        tensCol (phiOne P Q) (charInd χr (s • Q)) := by
      funext x
      rw [SrcGl.tensCol_mul_blk]
      congr 1
      funext x₀
      rw [← SrcGl.phiOne_smul_left, hg, phiOne_dia]
    rw [b2, hθv _ _ _ hΞ', hθv _ _ _ hΞ'', GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' P.lat inferInstance g hgs lS (hlS hW), Units.val_one,
      inv_one, one_smul, SrcGl.caRep_apply] at h1
    rw [hram.2, dia_apply, ← hg, hram1.1 g P]
    exact h1.symm

  obtain ⟨lS, lT, -, hlT, -, -, hlin⟩ := GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ V₀ S χV χW om₁ hW₁
  choose gs hgs using fun Q' : Pair k n => MulAction.exists_smul_eq (GL n k) (s • Q) Q'
  have hstab : ∀ Q' ∈ withLat Q.lat, gs Q' • Q.lat = Q.lat := fun Q' hQ' => by
    rw [← Pair.dia_lat s Q, ← Pair.smul_lat, hgs, mem_withLat.1 hQ', Pair.dia_lat]
  have hfix : ∀ Q' ∈ withLat Q.lat, omT (β.gl (gs Q'), 1) Φ₂ = Φ₂ := by
    intro Q' hQ'
    obtain ⟨-, -, -, hfr, -, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β
    obtain ⟨Λ', -, hΛ', hK⟩ := hfr L₂' hsd₂
    have hΛQ : Λ' = Q.lat := Submodule.ext fun x => (hΛ' x).trans (hlat x).symm
    have hk1 : InK S L₂' (· = p.v) (β.gl (gs Q')) := (hK _).2 (hΛQ ▸ hstab Q' hQ')
    have hk2 : InK T L₃ (· = p.v) 1 := ⟨one_mem _, fun y _ => by simp [Formalism.L2.Theta.mt]⟩
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT omT hWT L₂' L₃ hsd₂ hsd₃ (· = p.v)
      (fun v hv => by subst hv; exact ⟨GlobalTheory.T.isTameFinitePlaceHermitian_all D _, hχS, hχT⟩) Φ₂ hvac _ _ hk1 hk2
  have hOver : ∀ Q' ∈ withLat Q.lat, Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q') (charInd χr Q'))
      (om₁ (1, β.gl (gs Q')) Ξ'') := by
    intro Q' hQ'
    have h0 := hlin n (n' ⊕ Fin 1) α₀ β L₁ L₂ f₁ _ Ξ'' hΞ'' 1 (gs Q')
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n Q.lat inferInstance (gs Q') (hstab Q' hQ') lT (hlT hV)] at h0
    convert (preTransparency := .reducible) h0 using 1
    · funext x
      simp only [map_one, Units.val_one, one_mul, Matrix.mul_one]
      rw [tensCol_phiOne_charInd_smul, hgs]
    · rw [map_one]
  have hfun := hsrc ψ V₀ A L S o ζ hζ hA vA χV χW om₁ hW₁ hV hW α α₀ β hsum P Q.lat L₁ L₂ f₁ Ξ
    (fun Q' => om₁ (1, β.gl (gs Q')) Ξ'') hΞ hOver φ hφ
  have hterm : ∀ (f : GA D A → ℂ) b h,
      liftA o om₁ vA f (om₁ (1, b) Ξ'') h 0 = liftA o om₁ vA f Ξ'' (h * b) 0 := by
    intro f b h
    simp only [liftA]
    congr 1
    funext h₀
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hG := SmallPl.liftA_contAut o hA hW₁ vA (hram1.2.2 P) (hob.2.1 _ _ hΞ'').1
  simp only [smallPair]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun h' => ?_)
  dsimp only
  have key := SmallPl.integral_sum_translates hS hWT vS hvac.1 (withLat Q.lat) (fun Q' => β.gl (gs Q')) hfix hG
    ((r₀ : ℂ) * chrPow χW (p.idele q.unit) e) h'
  rw [hfun, ← hmove]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hterm]
  rw [key, hN]
  push_cast
  ring

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlaceStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPair_pairing_at_one_gluedPlace : ∀ D : D7, GlobalTheory.FinPl.SmallOne D := by
  first | exact @GlobalTheory.FinPl.smallOne | exact GlobalTheory.FinPl.smallOne | (intros; apply GlobalTheory.FinPl.smallOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SmallAllPf

variable {D : D7}

theorem vac_at_place {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}
    {f : WO S T → ℂ} (h : Vac ψ S T LS LT P f) {v : Pl D} (hv : P v) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨α, hα, hP, rest⟩
    exact ⟨α, hα, fun w hw => hP w fun e => hw (e ▸ hv), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem main : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ q χ hχ
  have hSO := GlobalTheory.T.smallPair_pairing_at_one_gluedPlace D
  have hOB := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have hAB := GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D
  choose r e hr hval using fun i => hSO k (p i) n n' q (χ i) (hχ i)
  refine ⟨r, e, hr, ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT hunr vA vS vT a b s L₁ L₂ L₃ hL₁ hL₂ hL₃ hloc
    Ξ Ξ' Φ₂ hΞ hΦ₂ hO φ hφ F hF
  have hstd : IsStdChar D ψ (-1) := hom₁.std
  have hinj : Function.Injective fun i => (p i).v := hP.inj
  have hPi : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  set c : ι → ℂ := fun i => (r i : ℂ) * chrPow χW ((p i).idele q.unit) (e i) with hc
  set Ψ : ι → Matrix n (n' ⊕ Fin 1) k → ℂ :=
    fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (s i • b.Q i)) with hΨ

  have keep : ∀ (l : List ι) (f f' : WO V₀ S → ℂ),
      OverAll ψ a.α₀ b.β L₁ L₂ Ψ l f f' → ∀ i, i ∉ l → Vac ψ V₀ S L₁ L₂ (· = (p i).v) f →
        Vac ψ V₀ S L₁ L₂ (· = (p i).v) f' := by
    intro l
    induction l with
    | nil =>
      intro f f' h i _ hv
      have h' : f' = f := h
      rw [h']
      exact hv
    | cons j l ih =>
      intro f f' h i hi hv
      obtain ⟨g, hg, hOj⟩ := h
      have hgv := ih f g hg i (fun hm => hi (List.mem_cons_of_mem j hm)) hv
      have hij : i ≠ j := fun e => hi (e ▸ List.mem_cons_self)
      exact ((hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hOj.2.2.1).2.1 _ _
        hOj).2 L₁ L₂ _ (fun e => hij (hinj e).symm) hgv
  have val : ∀ l : List ι, l.Nodup → ∀ (Ξ₀ Ξ₁ : WO V₀ S → ℂ),
      (∀ i, Vac ψ V₀ S L₁ L₂ (· = (p i).v) Ξ₀) → OverAll ψ a.α₀ b.β L₁ L₂ Ψ l Ξ₀ Ξ₁ →
      ∀ φ, a.Ram φ → smallPair o om₁ omT vA vS vT φ Ξ₀ Φ₂ F =
        (l.map c).prod * smallPair o om₁ omT vA vS vT (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) Ξ₁ Φ₂ F := by
    intro l
    induction l with
    | nil =>
      intro _ Ξ₀ Ξ₁ _ h φ _
      have h' : Ξ₁ = Ξ₀ := h
      subst h'
      simp [PairDat.sAll]
    | cons j l ih =>
      intro hnd Ξ₀ Ξ₁ h1 h φ hφ
      obtain ⟨g, hg, hOj⟩ := h
      have hj : j ∉ l := (List.nodup_cons.1 hnd).1
      have hgv := keep l Ξ₀ g hg j hj (h1 j)
      rw [ih hnd.tail Ξ₀ g h1 hg φ hφ]
      have hR : a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) :=
        (hAB k ι p q χ hχ s n' A V₀ a hinj l).1.mapsTo hφ
      have hself := (hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hgv).2.2
        (hP.unit j) _ _ (hloc j).2.1 (hloc j).2.2
      obtain ⟨u1, u2, u3, u4⟩ := hunr _ (hPi j)
      have key := hval j ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT u1 u2 u3 u4 vA vS vT
        (a.α j) (a.α₀ j) (b.β j) (hloc j).1 (a.P j) (b.Q j) (s j) L₁ L₂ L₂ L₃ g g Ξ₁ Φ₂ hself hOj hL₂ hL₃
        (hloc j).2.2 (vac_at_place hΦ₂ (hPi j)) _ (hR.2 j) F hF
      have hcons : a.sAll q (fun i => resChar (χ i) (hχ i) q) s (j :: l) φ =
          sOp (a.α j) (a.P j) q (resChar (χ j) (hχ j) q) (s j)
            (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) := rfl
      rw [key, hcons, List.map_cons, List.prod_cons, hc]
      ring
  exact val I hP.nodup Ξ Ξ' (fun i => vac_at_place hΞ (hPi i)) hO φ hφ

end GlobalTheory.FinPl.SmallAllPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPairPairingAllGluedPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  first | exact @GlobalTheory.FinPl.SmallAllPf.main | exact GlobalTheory.FinPl.SmallAllPf.main | (intros; apply GlobalTheory.FinPl.SmallAllPf.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitP
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitP
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharsFromWeil

section Alg

variable {R : Type*} [CommRing R]

theorem alg_key (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) (hab : a * b = 1) :
    (e * a + c e * c b + (1 - e - c e)) * (e * b + c e * c a + (1 - e - c e)) = 1 := by
  have hce : c e * c e = c e := by rw [← map_mul, he1]
  have hcab : c a * c b = 1 := by rw [← map_mul, hab, map_one]
  linear_combination e * e * hab + c e * c e * hcab +
    (a * c a + c b * b - a - b - c b - c a + 2) * hec + (2 - a - b) * he1 + (2 - c b - c a) * hce

theorem alg_conj (c : R →+* R) (hcc : ∀ z, c (c z) = z) (e a b : R) :
    c (e * a + c e * c b + (1 - e - c e)) = e * b + c e * c a + (1 - e - c e) := by
  simp only [map_add (f := _), map_mul, map_sub, map_one, hcc]
  ring

theorem alg_supp (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) :
    (e + c e) * ((e * a + c e * c b + (1 - e - c e)) - 1) = (e * a + c e * c b + (1 - e - c e)) - 1 := by
  have hce : c e * c e = c e := by rw [← map_mul, he1]
  linear_combination (a - 1) * he1 + (c b - 1) * hce + (c b + a - 2) * hec

theorem alg_at (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) :
    e * (e * a + c e * c b + (1 - e - c e)) + (1 - e) = e * a + (1 - e) := by
  linear_combination (a - 1) * he1 + (c b - 1) * hec

theorem alg_prod {e f E x : R} (hef : e * f = 0) (hsum : e + f = E) (hsupp : E * (x - 1) = x - 1) :
    x = (e * x + (1 - e)) * (f * x + (1 - f)) := by
  linear_combination (-(x - 1) ^ 2) * hef - (x - 1) * hsum - hsupp

end Alg

variable {D : D7}

theorem splitFac_eq {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) {e : AE D} (he : IsSplitIdem D e)
    {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) :
    splitFacO χS χT x y = splitFacO χS' χT' x y := by
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [h2 ℓ hℓ f hf] at e1
  have e2 : (r' : ℂ) * (splitFacO χS' χT' x y : ℂ) = r * (splitFacO χS χT x y : ℂ) :=
    mul_right_cancel₀ hne e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, mul_one, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr'.ne') e2).symm

theorem exists_unit_idem {e : AE D} (he : e * e = e) (u : (AE D)ˣ) : ∃ x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) := by
  have hu : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := u.mul_inv
  have hk : (e * u + (1 - e)) * (e * ((u⁻¹ : (AE D)ˣ) : AE D) + (1 - e)) = 1 := by
    linear_combination (2 - (u : AE D) - ((u⁻¹ : (AE D)ˣ) : AE D)) * he + e * e * hu
  exact ⟨⟨_, _, hk, by rw [mul_comm]; exact hk⟩, rfl⟩

theorem isSplitIdem_conj' {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
    by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩

theorem isDetAt_one (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  change (1 : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
  rw [Formalism.IndefR.flipTwoThree.mt_one', Matrix.det_one]
  ring

theorem exists_detUnit {e : AE D} (he : IsSplitIdem D e) (u : (AE D)ˣ) :
    ∃ X : (AE D)ˣ, (X : AE D) * cA D (X : AE D) = 1 ∧ Formalism.IndefR.InjectiveDecompositionAction.SuppAtU D e X ∧
      e * (X : AE D) + (1 - e) = e * u + (1 - e) := by
  have hab : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := u.mul_inv
  have hk := alg_key (cA D) he.1 he.2.1 hab
  refine ⟨⟨_, _, hk, by rw [mul_comm]; exact hk⟩, ?_, alg_supp (cA D) he.1 he.2.1, alg_at (cA D) he.1 he.2.1⟩
  change _ * cA D _ = 1
  rw [alg_conj (cA D) Formalism.L2.Theta.cA_cA]
  exact hk

theorem chiT_agree {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) (hS : 0 < S.rank) {e : AE D}
    (he : IsSplitIdem D e) (u x : (AE D)ˣ) (hx : (x : AE D) = e * u + (1 - e)) : χT x = χT' x := by
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_detUnit he u
  obtain ⟨g, hg, ⟨x', hx'⟩, hdet⟩ := Formalism.IndefR.flipTwoThree.splitDet D S hS e he X hX1 hX2
  have h0 : (x' : AE D) = e * (Formalism.L2.Theta.mt S g).det + (1 - e) := hx'
  have hxx : x' = x := Units.ext (by rw [h0, hdet, hX3, hx])
  subst hxx
  have := splitFac_eq H H' he hg (GlobalTheory.WeilDetermined.suppAt_one e T) hx' (isDetAt_one e T)
  simpa only [splitFacO, map_one, mul_one, _root_.inv_inj] using this

theorem chiS_agree {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) (hT : 0 < T.rank) {e : AE D}
    (he : IsSplitIdem D e) (u y : (AE D)ˣ) (hy : (y : AE D) = e * u + (1 - e)) : χS y = χS' y := by
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_detUnit he u
  obtain ⟨h, hh, ⟨y', hy'⟩, hdet⟩ := Formalism.IndefR.flipTwoThree.splitDet D T hT e he X hX1 hX2
  have h0 : (y' : AE D) = e * (Formalism.L2.Theta.mt T h).det + (1 - e) := hy'
  have hyy : y' = y := Units.ext (by rw [h0, hdet, hX3, hy])
  subst hyy
  have := splitFac_eq H H' he (GlobalTheory.WeilDetermined.suppAt_one e S) hh (isDetAt_one e S) hy'
  simpa only [splitFacO, map_one, inv_one, one_mul] using this

theorem eq_of_comp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ χ' : (AE D)ˣ →* Circle)
    (hag : ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x)
    (x : (AE D)ˣ) (h1 : infPart D (x : AE D) = 1)
    (h2 : ∀ w, w ≠ p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (x : AE D)) = 1) : χ x = χ' x := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hsupp : algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 :=
    (GlobalTheory.VacStabFixed.supp_iff hε _).2 ⟨by rw [map_sub, map_one, h1, sub_self],
      fun w hw => by rw [map_sub, map_sub, map_one, map_one, h2 w hw, sub_self]⟩
  have he : IsSplitIdem D p.e := p.split
  have hce : IsSplitIdem D (cA D p.e) := isSplitIdem_conj' he
  obtain ⟨x1, hx1⟩ := exists_unit_idem he.1 x
  obtain ⟨x2, hx2⟩ := exists_unit_idem hce.1 x
  have hprod : x = x1 * x2 := by
    apply Units.ext
    rw [Units.val_mul, hx1, hx2]
    exact alg_prod he.2.1 hsum hsupp
  rw [hprod, map_mul, map_mul, hag p.e he x x1 hx1, hag _ hce x x2 hx2]

theorem charUnram_transfer {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ χ' : (AE D)ˣ →* Circle)
    (hag : ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ' p.v := by
  intro x h1 h2 h3 h4
  rw [← eq_of_comp p χ χ' hag x h1 h2]
  exact h x h1 h2 h3 h4

theorem charUnram_of_weil : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om → (0 < S.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT' p.v) ∧ (0 < T.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' p.v) := by
  intro D k _ _ _ _ p ψ S T χS χT χS' χT' om H H'
  exact ⟨fun hS => charUnram_transfer p χT χT' fun e he u x hx => chiT_agree H H' hS he u x hx,
    fun hT => charUnram_transfer p χS χS' fun e he u y hy => chiS_agree H H' hT he u y hy⟩

end GlobalTheory.CharsFromWeil

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitPStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om → (0 < S.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT' p.v) ∧ (0 < T.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' p.v) := by
  first | exact @GlobalTheory.CharsFromWeil.charUnram_of_weil | exact GlobalTheory.CharsFromWeil.charUnram_of_weil | (intros; apply GlobalTheory.CharsFromWeil.charUnram_of_weil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.LastStep

theorem chars_unram : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  intro D c v k _ _ _ _ ι o hS j h t hU hK χz χS' χT h1 h2 x hx
  obtain ⟨i, rfl⟩ := (hS.pre.tP x).1 hx
  have hpos : ∀ n, 0 < (c.X n).rank := fun n => by
    apply Nat.pos_of_ne_zero
    intro h0
    have P := o.Q n i
    revert P
    rw [h0]
    intro P
    exact P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have hV : 0 < (c.V (j + 1)).rank := by
    have := (c.jac j 0 h).d.rank_add
    have := hpos (j + 1)
    omega
  obtain ⟨χS₃, χT₃, hW₃, hu₃⟩ := hK (j + 1) (by omega)
  obtain ⟨χS₂, χT₂, hW₂, hu₂⟩ := hU.top j h
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₃ χT₃ χS' (χT * χz⁻¹) (t.kom (j + 1)) hW₃ h1).2 (hpos _) (hu₃ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).1
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₂ χT₂ χS' χT (t.omT j h) hW₂ h2).1 hV (hu₂ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).2

end GlobalTheory.LastStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawLastStage_chars_unramified_at_levelPrime : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  first | exact @GlobalTheory.LastStep.chars_unram | exact GlobalTheory.LastStep.chars_unram | (intros; apply GlobalTheory.LastStep.chars_unram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelDatumInLastLineFrameAtLevelPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.LastKerRep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n₂ : Type} [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂]

theorem hasVal_transport {Q : Pair k n} {R : Pair k n₂} (G : Matrix n₂ n k) (G' : Matrix n n₂ k) (hGG : G * G' = 1)
    {e : n₂ → k} (he : R.HasVal e 1) (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ R.ker) {s : 𝓀[k]ˣ}
    (hs : Q.HasVal (G' *ᵥ e) s) (y : n → k) (a : 𝓀[k]) :
    Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a) := by
  have hGe : ∀ (r : 𝒪[k]) (z : n → k), G *ᵥ (z - r • (G' *ᵥ e)) = G *ᵥ z - r • e := by
    intro r z
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  obtain ⟨r, hr⟩ := residue_surjective (R := 𝒪[k]) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)
  have hsr : residue 𝒪[k] r * (s : 𝓀[k]) = a := by
    rw [hr, mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  constructor
  · intro hy
    have h1 := hy.sub (hs.smul r)
    rw [hsr, sub_self] at h1
    have h2 := Pair.mem_ker.1 ((hker _).1 (Pair.mem_ker.2 h1))
    rw [hGe] at h2
    have h3 := h2.add (he.smul r)
    rw [sub_add_cancel, zero_add, mul_one, hr] at h3
    exact h3
  · intro hy
    have h1 := hy.sub (he.smul r)
    rw [mul_one, hr, sub_self, ← hGe] at h1
    have h2 := Pair.mem_ker.1 ((hker _).2 (Pair.mem_ker.2 h1))
    have h3 := h2.add (hs.smul r)
    rw [sub_add_cancel, zero_add, hsr] at h3
    exact h3

theorem maps_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    Maps (s⁻¹ • P) R (G * x) ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal, inv_inv]
  constructor
  · intro H y a hy
    rw [hT, Matrix.mulVec_mulVec]
    apply H
    rwa [← mul_assoc, Units.mul_inv, one_mul]
  · intro H y a hy
    have := (hT _ _).1 (H y _ hy)
    rwa [← mul_assoc, Units.inv_mul, one_mul, Matrix.mulVec_mulVec] at this

theorem phiOne_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    phiOne (s⁻¹ • P) R (G * x) = phiOne P Q x := by
  classical
  unfold phiOne
  exact if_congr (maps_transport P G s hT x) rfl rfl

section Frames
variable {D : D7} {p : SplitPt D k} {S T : HSp D} {n' : Type} [Fintype n'] [DecidableEq n']

theorem extFun_eq_of (α : Frame p S n') (β : Frame p T n₂) (β' : Frame p T n) (Ψ : Matrix n₂ n' k → ℂ)
    (Ψ' : Matrix n n' k → ℂ) (hΨ : ∀ x, Ψ' ((β'.b' * β.b) * x) = Ψ x) : extFun α β Ψ = extFun α β' Ψ' := by
  funext t
  unfold extFun
  split_ifs
  · rw [← hΨ]
    congr 1
    unfold rd
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
  · rfl

end Frames

section Lists
variable {D : D7} {ι : Type} {p : ι → SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem overAll_of_extFun_eq (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n₂) (β' : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n₂ n' k → ℂ)
    (Ψ' : ι → Matrix n n' k → ℂ) (h : ∀ i, extFun (α i) (β i) (Ψ i) = extFun (α i) (β' i) (Ψ' i))
    (hSB : ∀ i, Ψ' i ∈ SB (Matrix n n' k)) :
    ∀ (l : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ l f f' → OverAll ψ α β' LS LT Ψ' l f f' := by
  intro l f f' hf
  induction l generalizing f' with
  | nil => exact hf
  | cons i l ih =>
    change ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' at hf
    change ∃ g, OverAll ψ α β' LS LT Ψ' l f g ∧ Over ψ (α i) (β' i) LS LT g (Ψ' i) f'
    obtain ⟨g, hg, hov⟩ := hf
    refine ⟨g, ih g hg, ?_⟩
    unfold Over at hov ⊢
    obtain ⟨h1, h2, h3, -, h5⟩ := hov
    refine ⟨h1, h2, h3, hSB i, ?_⟩
    rw [← h i]
    exact h5

end Lists

theorem isLattice_of_lastKer {m : Type} [Fintype m] [DecidableEq m] {Q : Pair k n₂} (G : Matrix (m ⊕ Fin 1) n₂ k)
    (G' : Matrix n₂ (m ⊕ Fin 1) k) (hGG : G * G' = 1) (L : Submodule 𝒪[k] (m → k))
    (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L) :
    L.IsFullLattice k := by
  let e : (m → k) →ₗ[k] (m ⊕ Fin 1 → k) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := by intro x y; ext (i | i) <;> simp
      map_smul' := by intro c x; ext (i | i) <;> simp }
  let f : (m → k) →ₗ[k] (n₂ → k) := (Matrix.mulVecLin G').comp e
  have hGf : ∀ x, G *ᵥ f x = Sum.elim x 0 := by
    intro x
    simp only [f, e, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (G *ᵥ ·) hxy
    simp only [hGf] at this
    funext i
    exact congrFun this (Sum.inl i)
  have hL : L = Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    ext x
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hker, hGf, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    simp
  rw [hL]
  have := GlobalTheory.GoodLat.isLattice_comap Q.ker Q.ker_isLat.toIsLattice f hf
  refine ⟨?_⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx : f x ∈ Submodule.span k (Q.ker : Set (n₂ → k)) := by
    rw [Submodule.IsFullLattice.span_eq_top]
    trivial
  obtain ⟨a, ha, hax⟩ := GlobalTheory.GoodLat.exists_smul_mem Q.ker hx
  have hmem : a • x ∈ Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    change (f.restrictScalars 𝒪[k]) (a • x) ∈ Q.ker
    rw [map_smul]
    exact hax
  have hspan := Submodule.subset_span (R := k) hmem
  have ha' : algebraMap 𝒪[k] k a ≠ 0 := by
    intro hzero
    exact ha (IsFractionRing.injective 𝒪[k] k (hzero.trans (map_zero _).symm))
  rw [← algebraMap_smul k a x] at hspan
  simpa only [inv_smul_smul₀ ha'] using
    (Submodule.span k (Q.ker.comap (f.restrictScalars 𝒪[k]) : Set (m → k))).smul_mem
      (algebraMap 𝒪[k] k a)⁻¹ hspan

end GlobalTheory.LastKerRep


open GlobalTheory.LastKerRep in
theorem GlobalTheory.SeeSaw.lastKernel_reps :
    ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k]
      [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
      c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m),
      ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
        (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧
        Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
          (fun i =>
            haveI := hΛ i
            phiOne (u i • o.Q (j + 1) i)
              (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i)))
          o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have htop := fun i => (hS.pre.topT (j + 1 + 1) h i).2
  choose Λ s hLat hKer hVal using htop
  have hGG : ∀ i, ((o.γ₀ (j + 1 + 1) h i).b' * (o.β (j + 1 + 1) i).b) * ((o.β (j + 1 + 1) i).b' * (o.γ₀ (j + 1 + 1) h i).b) = 1 := by
    intro i
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (o.β (j + 1 + 1) i).b, (o.β (j + 1 + 1) i).bb', Matrix.one_mul, (o.γ₀ (j + 1 + 1) h i).b'b]
  have hΛ : ∀ i, (Λ i).IsFullLattice k := fun i => isLattice_of_lastKer _ _ (hGG i) (Λ i) (hKer i)
  refine ⟨Λ, hΛ, fun i => (s i)⁻¹, hLat, (hv.atT (j + 1)).1, fun f hf => ?_⟩
  refine overAll_of_extFun_eq c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (o.γ₀ (j + 1 + 1) h) _ _ _ _ (fun i => ?_) (fun i => ?_)
    o.I f _ (hS.rep (j + 1) (by omega) f hf)
  · have := hΛ i
    apply extFun_eq_of
    intro x
    exact phiOne_transport _ _ _ (hasVal_transport _ _ (hGG i)
      (glue_hasVal (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last o.q (Λ i)))
      (fun y => (hKer i y).trans (by rw [glue_ker])) (hVal i)) x
  · have := hΛ i
    exact GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeLawLastTwoStepsAllTuples
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.TLastAll

theorem combAt_fin {D : D7} {P : Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ} (h : CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this


set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f → ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ = o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have hPl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, hS.pre.tP, fun i => (hS.pre.char i).2⟩
  have hstd := hc.std
  have hjm : j + 1 < D.R.m := by omega
  have hx0 : IsSelfDualC _ (c.x j).L := (hc.x j (by omega)).sd
  have hx1 : IsSelfDualC _ (c.x (j + 1)).L := (hc.x (j + 1) (by omega)).sd
  have hx2 : IsSelfDualC _ (c.x (j + 1 + 1)).L := (hc.x (j + 1 + 1) (by omega)).sd
  have hpl : Nonempty (Pl D) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := NumberField.RingOfIntegers D.host.F)
    exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField D.host.F)).ne'⟩⟩
  have hM : IsSelfDualC _ (o.M j 0 h) := ((hS.good (Classical.arbitrary _)).bf j 0 h).sdV₀
  obtain ⟨lam, hlam, hlamv⟩ := hS.pre.lam j h
  obtain ⟨ε', hε'⟩ := GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl o.q c.ψ hstd o.χ o.hχ (fun i => (hS.pre.char i).1)
    (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) (Fin c.T.rank) (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1))
    (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (c.bes j 0 h).ζ o.ζ₀ (c.bes j 0 h).line hS.pre.line
    (v.τ j h) lam hlam (fun i => (hlamv i).1) (hS.pre.tau j h)
  obtain ⟨Λ, hΛ, u, hγ, hrep⟩ := GlobalTheory.SeeSaw.lastKernel_reps D c v k ι o hc hv hS j h
  haveI : ∀ i, (Λ i).IsFullLattice k := hΛ
  let ε : ι → 𝓀[k]ˣ := fun i => (ε' i)⁻¹ * u i
  let Q : ι → Pair k (Fin (c.X (j + 1)).rank) := fun i => ε i • o.Q (j + 1) i
  obtain ⟨r, e, hr, hSm⟩ := GlobalTheory.T.smallPairPairingAllGluedPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q o.χ o.hχ
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D
  let Ψ' : ι → Matrix (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) k → ℂ := fun i =>
    tensCol (phiOne (o.Q j i) (o.Q (j + 1) i)) (charInd (resChar (o.χ i) (o.hχ i) o.q) (Q i))
  have hAC1 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) c.ψ hstd
    (c.bes j 0 h).V₀ (c.X (j + 1)) (o.β₀ j 0 h) (o.β (j + 1)) (o.M j 0 h) (c.x (j + 1)).L hM hx1 Ψ'
  obtain ⟨e0, he0⟩ := hAC1.1 fun i => Comm.tensCol_mem (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _) (SBFacts.charInd_mem _ _)
  have hrep' : Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
      (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
    have hf : (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) =
        (fun i => phiOne (u i • o.Q (j + 1) i) (lastPair o.q (Λ i))) := by
      funext i
      simp only [Q, ε, smul_smul, mul_inv_cancel_left]
    rw [hf]
    exact hrep
  obtain ⟨e₁, e₂, he₁, he₂, hE⟩ := hε' (o.β j) (o.β₀ j 0 h) (o.β (j + 1)) o.γ (o.γ₀ (j + 1 + 1) h)
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.pre.topT (j + 1 + 1) h i).1⟩) Q Λ
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) (c.x j).L (c.x (j + 1)).L v.NT (c.x (j + 1 + 1)).L (o.M j 0 h)
    hx0 hx1 hv.sdT hx2 hM (fun i => ⟨hS.pre.latT (j + 1) (by omega) i, hγ i⟩) (v.dT j) (v.dT (j + 1))
    ⟨(hv.atT j).1, hS.rep j (by omega)⟩ hrep'
  have hLO := GlobalTheory.T.lastSeeSaw_combinations_operatorDatum D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
  obtain ⟨op0, hop0, hop0e⟩ := (hLO (· ∈ v.tP)).1 e0 he0.1
  obtain ⟨op, hop, hope⟩ := ((GlobalTheory.T.biVacuumOperator_zero_or_left_invertible D) k ι o.p o.I _ hPl c.ψ hstd _ _ _ op0 hop0).2 e₁ e₂ he₁ he₂
  refine ⟨ε, op, r, e, hr, hop, ?_⟩
  intro t ht hW hU hK Ψ₁ Ψ₂ hΨ₁ hΨ₂
  obtain ⟨χA, χz, χS', χT, omz, omT', omz'', hχV, hwA, hwz, hwX, hwT, hwTi, hwz''⟩ := hW.last j h
  have hunrT := GlobalTheory.T.seesawLastStage_chars_unramified_at_levelPrime D c v k ι o hS j h t hU hK χz χS' χT hwX hwTi
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∈ v.tP)
  have hΞ : Vac c.ψ (c.bes j 0 h).V₀ (c.X (j + 1)) (o.M j 0 h) (c.x (j + 1)).L (· ∈ v.tP) (flatBF (t.sBF j 0 h) Ψ₁) :=
    hFV.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) (v.N j) (o.M j 0 h) (v.N (j + 1)) (c.x (j + 1)).L
      (fun x _ => (hS.good x).bf j 0 h) Ψ₁ hΨ₁
  have hΦ : Vac c.ψ (c.X (j + 1)) c.T (c.x (j + 1)).L v.NT (· ∈ v.tP) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w)) :=
    hFV.2.2 (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d (v.N (j + 1)) (c.x (j + 1)).L v.NT (hv.sd (j + 1) hjm) hx1
      hv.sdT (fun x _ => ((hS.good x).bf j 0 h).monoW) Ψ₂ hΨ₂
  set Ξ := flatBF (t.sBF j 0 h) Ψ₁ with hΞdef
  set Φ₂ : WO (c.X (j + 1)) c.T → ℂ := fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w) with hΦdef
  have hΞ' := he0.2 Ξ hΞ
  obtain ⟨hBV, hEq⟩ := hE Ξ (comb c.ψ _ _ e0 Ξ) Φ₂ hΞ hΞ' hΦ
  have hlst : c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂ = lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) Ξ Φ₂ := rfl
  have hopX : op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) = biComb c.ψ _ _ _ e₁ e₂
      (lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (comb c.ψ _ _ e0 Ξ) Φ₂) := by
    rw [hope, hlst, ← hop0e]
  refine ⟨hopX ▸ hBV, ?_⟩
  intro d d' hd hd' φ hφ f hf
  rw [hopX, ← hEq]
  obtain ⟨N, a, b, hab, hdec⟩ := (hLO (· ∉ v.tP)).2 d d' hd hd'
  rw [hlst, hdec, hdec]
  have hAC2 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin c.T.rank) (Fin (c.X (j + 1)).rank) c.ψ hstd (c.X (j + 1)) c.T
    (o.β (j + 1)) o.γ (c.x (j + 1)).L v.NT hx1 hv.sdT (fun _ _ => 0)
  have hw₁ : IsWeilDatumO c.ψ _ _ (χA * χz) (t.sBF j 0 h).χW (t.sBF j 0 h).om₀ := by
    rw [← hχV]; exact (t.sBF j 0 h).weil₀
  have hSS := GlobalTheory.T.lastSeeSaw_doubleLift_additive D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
    (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt χA χz (t.sBF j 0 h).χW χS' χT (t.sBF j 0 h).om₀
    (t.kom j) omz (t.kom (j + 1)) omT' omz'' hw₁ hwA hwz hwX hwT hwz'' (c.x j).vol (c.x (j + 1)).vol c.volT N
  have hRam : PairDat.Ram (⟨o.β j, o.β₀ j 0 h, o.Q j⟩ : PairDat o.p (c.X j) (c.bes j 0 h).V₀ (Fin (c.X j).rank)) φ := hφ
  have hRam' := (GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι o.p o.q o.χ o.hχ ε (Fin (c.X j).rank) (c.X j) (c.bes j 0 h).V₀
    ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ hS.pre.inj o.I).1.mapsTo hRam
  have L1 := hSS (fun i => comb c.ψ _ _ (a i) Ξ) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1).1, ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) φ f hφ.1 hf
  have L2 := hSS (fun i => comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨GlobalTheory.AvgMid.theta_comb hstd (combAt_fin (hab i).1) (GlobalTheory.AvgMid.theta_comb hstd (combAt_fin he0.1) hΞ.1),
      ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) (o.S (fun _ => ε) j φ) f hRam'.1 hf
  beta_reduce at L1 L2
  unfold Comm.bl
  rw [L1, L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hSm c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) c.T (c.bes j 0 h).o (c.bes j 0 h).ζ
    (c.bes j 0 h).line (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt (t.sBF j 0 h).χV (t.sBF j 0 h).χW
    χS' χT (t.sBF j 0 h).om₀ omT' (t.sBF j 0 h).weil₀ hwT
    (fun x hx => ⟨(hU.bf j 0 h x hx).1, (hU.bf j 0 h x hx).2, (hunrT x hx).1, (hunrT x hx).2⟩)
    (c.x j).vol (c.x (j + 1)).vol c.volT ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ ⟨o.β (j + 1), o.Q (j + 1)⟩ ε (o.M j 0 h)
    (c.x (j + 1)).L v.NT hM hx1 hv.sdT
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.glued j 0 h i).lat, hS.pre.latT (j + 1) (by omega) i⟩)
    (comb c.ψ _ _ (a i) Ξ) (comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (comb c.ψ _ _ (b i) Φ₂)
    (hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1 (hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1
    ((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).2 _ hΞ') φ hRam f hf

end GlobalTheory.FinPl.TLastAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeLawLastTwoStepsAllTuplesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_law_last_two_steps_all_tuples : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f → ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ = o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  first | exact @GlobalTheory.FinPl.TLastAll.main | exact GlobalTheory.FinPl.TLastAll.main | (intros; apply GlobalTheory.FinPl.TLastAll.main <;> assumption)
end

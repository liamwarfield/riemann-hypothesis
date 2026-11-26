module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainCoefficientSupportedPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentMemLevelOfReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentMemLevelOfReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LevAssembly

theorem gAt_mem_levG_of_red : ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank), L.P.H = ⊥ → ∀ (g : GA D S), ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → (∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS → Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) → Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 → gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG S βS L := by
  intro D S βS L hH g PP hPP huniq hQ hSt hred hr
  have hone : ∀ PP' : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) →
      Formalism.L2.DIV.redFn βS PP' (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) = 1 := by
    intro PP' hne
    exact GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS _ PP' hSt (GlobalTheory.AdelicU.proj_emb_ne _ _ hne _)
  refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC S _ _, ?_⟩
  show Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L
  refine ⟨⟨⟨⟨GlobalTheory.LevSplit.finE_mem_UA S _, hSt⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    by_cases h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · rw [huniq PP' hPP' h]; exact hred
    · rw [hone PP' h]; exact Subgroup.one_mem _
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hone PP' (hQ PP' hPP')]; exact Subgroup.one_mem _
  · show Formalism.L2.DIV.rTup βS L _ ∈ L.P.H
    rw [hH, Subgroup.mem_bot]
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP'.1 _) = 1
    by_cases h : PP'.1.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · rw [huniq PP'.1 PP'.2 h]; exact hr
    · rw [hone PP'.1 h]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.LevAssembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentMemLevelOfReductionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPlace_component_mem_level_of_reduction : ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank), L.P.H = ⊥ → ∀ (g : GA D S), ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → (∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS → Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) → Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 → gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG S βS L := by
  first | exact @GlobalTheory.LevAssembly.gAt_mem_levG_of_red | exact GlobalTheory.LevAssembly.gAt_mem_levG_of_red | (intros; apply GlobalTheory.LevAssembly.gAt_mem_levG_of_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainCoefficientSupportedPrincipalLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

noncomputable section

namespace GlobalTheory.TwSuppLev

theorem isSBHalf_twDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  classical
  intro D S T ΛS ΛT βS βT L χ ξ Q Z e hS hT _ _ he
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

theorem eq_of_under_eq {D : D7} {e : AE D} {Z : Finset (Pl D.host.E)} (h : IsIdemSum e Z) {PP PP' : Pl D.host.E}
    (hP : PP ∈ Z) (hP' : PP' ∈ Z) (hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) : PP' = PP := by
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h1 | h1
  · exact h1
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1) (GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hP PP' hP')

theorem gAt_mem_levG_of_supp : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → (∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG S βS L := by
  intro D S T ΛS βS βT L χ ξ e hsd hfr hrk he hP g x hx hx' PP hPP huniq hQu
  obtain ⟨hSt, hB, hR⟩ := GlobalTheory.T.principalPlace_component_stabilises_lattice_twisted D S T ΛS βS βT L χ ξ e hsd hfr hrk he hP g x hx hx' PP hPP huniq
  exact GlobalTheory.T.principalPlace_component_mem_level_of_reduction D S βS L hP g PP hPP (fun PP' hP' hu => huniq PP' (Finset.mem_union_left _ hP') hu) hQu hSt hB hR

theorem supp_at_principal : ∀ D : D7, ForStepQ D fun c w _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ P (g : GA D s.V), coefW p.ω m X (p.pt P) g ≠ 0 → ∀ v ∈ w.S₀, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L := by
  intro D _hgap c w hw k _hk s s' hs hs' p hp m X hX φ g hne v hv
  obtain ⟨hr, hL, hfl⟩ := hs
  obtain ⟨hr', hL', hfl'⟩ := hs'
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hsd' : IsSelfDualC s'.V s'.Λ := hfl'.selfDual
  have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
  have hfr' : Formalism.L2.DIV.IsFrame s'.β s'.Λ := hfl'.frame
  have hrank : s.V.rank ≤ s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hfl.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [h1, h2]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hthf : IsThetaFunO c.ψ s.V s'.V p.f := GlobalTheory.VecTheta.isThetaFunO_stepVec hvec
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  have hQ : s.L.Q = w.Q := by rw [hL]; rfl
  have hPg : s.L.Pg = w.Pg := by rw [hL]; rfl
  have hPH : s.L.P.H = ⊥ := by rw [hL]; rfl
  simp only [Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
  obtain ⟨PP, hPP, rfl⟩ := hv
  by_contra hnot
  have hsupp := fun x hx => by_contra fun h => hnot
    (gAt_mem_levG_of_supp D s.V s'.V s.Λ s.β s'.β s.L (w.chi (k + 1)) w.ξ e hsd hfr hrank (hQ ▸ he) hPH g x
      (by rw [hQ]; exact hx) (by rw [hQ]; exact h) PP (hPg ▸ hPP)
      (fun PP' hP' hu => eq_of_under_eq he (Finset.mem_union_left _ (hPg ▸ hPP)) (hQ ▸ hP') hu)
      fun PP' hP' hu => Finset.disjoint_left.1 hw.disj hPP (by
        have hP'' : PP' ∈ w.Q := hQ ▸ hP'
        have := eq_of_under_eq he (Finset.mem_union_left _ (hPg ▸ hPP)) (Finset.mem_union_right _ hP'') hu
        subst this
        exact hP''))
  have hsb := isSBHalf_twDatum D s.V s'.V s.Λ s'.Λ s.β s'.β s.L (w.chi (k + 1)) w.ξ w.Q (s.L.Pg ∪ w.Q) e hsd hsd' hfr hfr' he
  obtain ⟨n, a, y, hy, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D c.ψ s.V s'.V hw.com.std s.Λ s'.Λ hsd hsd'
    (s.L.Pg ∪ w.Q) e he f₀ _ p.f hsb hth g hsupp
  obtain ⟨H1, -⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hw.com.std hw.com.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n a y (fun i => (hy i).1) φ
  obtain ⟨H2, H0⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hw.com.std hw.com.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n (fun i => conj (a i)) (fun i => actO s.V s'.V g⁻¹ 1 (-(y i))) (fun i => (hy i).2) φ
  have R1 : ∑ i, a i • heisO c.ψ s.V s'.V (y i) (p.pt φ) = p.pt φ := by
    show ∑ i, a i • heisO c.ψ s.V s'.V (y i) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H1, h1]
    rfl
  have R2 : ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i))) (p.pt φ) = 0 := by
    show ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i)))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H2, h2, H0]
  exact hne (GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil m X hX (p.pt φ) (hp.theta φ) g n a y R1 R2)

end GlobalTheory.TwSuppLev

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainCoefficientSupportedPrincipalLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_coefficient_supported_principal_level : ∀ D : D7, ForStepQ D fun c w _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ P (g : GA D s.V), coefW p.ω m X (p.pt P) g ≠ 0 → ∀ v ∈ w.S₀, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L := by
  first | exact @GlobalTheory.TwSuppLev.supp_at_principal | exact GlobalTheory.TwSuppLev.supp_at_principal | (intros; apply GlobalTheory.TwSuppLev.supp_at_principal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralSplitFinitePlaceFubini
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralSplitFinitePlaceFubini
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Core.Rk.FubiniPlace


set_option maxHeartbeats 1000000 in
theorem integral_split_place : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (μ : Measure (GlobalTheory.FinZeta.Gv A v)), μ.IsHaarMeasure → ∀ J : Subgroup (GlobalTheory.FinZeta.Gv A v), IsOpen (J : Set (GlobalTheory.FinZeta.Gv A v)) → μ J = 1 → ∀ E : Set (GA D A), MeasurableSet E → (∀ x y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y ∈ E ↔ x ∈ E) → ∀ (F : GA D A → ℂ) (ζ : GlobalTheory.FinZeta.Gv A v → ℂ), Integrable ζ μ → (∀ y ∈ J, ζ y = 1) → (∀ x ∈ E, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y) = ζ y * F x) → IntegrableOn F (E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) m → IntegrableOn F E m ∧ ∫ g in E, F g ∂m = (∫ y, ζ y ∂μ) * ∫ g in E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}, F g ∂m := by
  intro D A m hm v μ hμ J hJo hJ1 E hE hEr F ζ hζ hζJ hF hFi
  have hec : Continuous (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_emb _ _ v
  have hpc : Continuous (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_proj _ _ v
  have hPm : MeasurableSet {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J} := (hJo.preimage hpc).measurableSet
  have hUm : MeasurableSet (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) := hE.inter hPm
  have hJm : MeasurableSet (J : Set (GlobalTheory.FinZeta.Gv A v)) := hJo.measurableSet

  have hright : ∀ k ∈ J, μ.map (fun y => y * k) = μ := by
    intro k hk
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
    have h2 := congrArg (fun m' : Measure (GlobalTheory.FinZeta.Gv A v) => m' (J : Set (GlobalTheory.FinZeta.Gv A v))) h
    simp only [Measure.coe_nnreal_smul_apply] at h2
    rw [Measure.map_apply (measurable_mul_const _) hJm,
      show (fun x => x * k) ⁻¹' (J : Set (GlobalTheory.FinZeta.Gv A v)) = J from Set.ext fun x => J.mul_mem_cancel_right hk,
      hJ1, mul_one] at h2
    have h3 : Measure.modularCharacterFun k = 1 := by exact_mod_cast h2.symm
    rw [h, h3, one_smul]

  have dec : ∀ x : GA D A, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) = 1 := by
    intro x; rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have dec2 : ∀ x : GA D A, x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x; rw [map_inv, inv_mul_cancel_right]
  have shift : ∀ (x : GA D A) (y : GlobalTheory.FinZeta.Gv A v),
      GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x y
    have hc := (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig A.gram y (dec x)).eq
    calc GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
          rw [mul_assoc, ← dec2]
      _ = _ := by rw [hc, mul_assoc, ← map_mul]
  have hEl : ∀ (y : GlobalTheory.FinZeta.Gv A v) (x : GA D A), GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x ∈ E ↔ x ∈ E := by
    intro y x
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    rw [shift, hEr, h1]
  have key : ∀ x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}), ∀ y, F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x) = F x * ζ (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x hx y
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    have hx' : x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ ∈ E := h1.1 hx.1
    have h2 := hF _ hx' (dec x) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h2
    rw [shift, hF _ hx' (dec x), h2, hζJ _ hx.2, one_mul, mul_comm]
  classical

  let c : GA D A → GlobalTheory.FinZeta.Gv A v := fun x => if GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J then GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x else 1
  have hcm : Measurable c := Measurable.ite hPm hpc.measurable measurable_const
  have hR : MeasurePreserving (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) (m.prod μ) (m.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun x y => y * c x) (MeasurePreserving.id m)
      (measurable_snd.mul (hcm.comp measurable_fst) : Measurable fun p : GA D A × GlobalTheory.FinZeta.Gv A v => p.2 * c p.1)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · simp only [c, if_pos hx]; exact hright _ hx
    · simp only [c, if_neg hx, mul_one, Measure.map_id']
  let g0 : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F q.1 * ζ q.2
  have hg0 : Integrable g0 (m.prod μ) := Integrable.mul_prod ((integrable_indicator_iff hUm).2 hFi) hζ
  let f : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * x)) q.1
  have hfg : f = g0 ∘ (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) := by
    funext q
    by_cases hx : q.1 ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J})
    · have hx2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1 ∈ J := hx.2
      simp only [f, g0, Function.comp_apply, c, if_pos hx2]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, key q.1 hx]
    · simp only [f, g0, Function.comp_apply, Set.indicator_of_notMem hx, zero_mul]
  have hf : Integrable f (m.prod μ) := by
    rw [hfg]; exact (hR.integrable_comp hg0.aestronglyMeasurable).2 hg0
  have hfint : ∫ q, f q ∂(m.prod μ) = ∫ q, g0 q ∂(m.prod μ) := by
    have h := integral_map (μ := m.prod μ) hR.measurable.aemeasurable (f := g0)
      (by rw [hR.map_eq]; exact hg0.aestronglyMeasurable)
    rw [hR.map_eq] at h
    rw [hfg]; exact h.symm

  let T : GA D A × GlobalTheory.FinZeta.Gv A v → GA D A × GlobalTheory.FinZeta.Gv A v := fun q => (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * q.1, q.2)
  have hTp : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2)) (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × GlobalTheory.FinZeta.Gv A v → GlobalTheory.FinZeta.Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : GlobalTheory.FinZeta.Gv A v × GA D A → GA D A × GlobalTheory.FinZeta.Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  let Te : (GA D A × GlobalTheory.FinZeta.Gv A v) ≃ᵐ (GA D A × GlobalTheory.FinZeta.Gv A v) :=
    { toFun := T
      invFun := fun q => ((GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2)⁻¹ * q.1, q.2)
      left_inv := fun q => by simp [T]
      right_inv := fun q => by simp [T]
      measurable_toFun := (((hec.comp continuous_snd).mul continuous_fst).prodMk continuous_snd).measurable
      measurable_invFun := ((((hec.comp continuous_snd).inv).mul continuous_fst).prodMk continuous_snd).measurable }
  have hT : MeasurePreserving Te (m.prod μ) (m.prod μ) := hTp
  let f₂ : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ :=
    fun q => {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) q
  have hf₂T : ∀ q, f₂ (Te q) = f q := by
    rintro ⟨x, y⟩
    have hp : (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y = (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    show {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) =
      (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x)) x
    by_cases h2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∈ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp]; exact J.inv_mem h2
      rw [Set.indicator_of_mem hq]
      by_cases h1 : x ∈ E
      · rw [Set.indicator_of_mem ((hEl y x).2 h1), Set.indicator_of_mem (show x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) from ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (hEl y x).1 h1), Set.indicator_of_notMem (by exact fun h => h1 h.1)]
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∉ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show ¬ (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp, inv_mem_iff]; exact h2
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (by exact fun h => h2 h.2)]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (hT.integrable_comp_emb Te.measurableEmbedding).1 ?_
    have : f₂ ∘ Te = f := funext hf₂T
    rw [this]; exact hf
  have hCm : ∀ a : GlobalTheory.FinZeta.Gv A v, MeasurableSet {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} :=
    fun a => (hJo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : GlobalTheory.FinZeta.Gv A v, μ {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} = 1 := by
    intro a
    rw [← hJ1]
    exact measure_preimage_mul μ a⁻¹ _
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = E.indicator F w := by
    intro w
    have : (fun y => f₂ (w, y)) = {y : GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ J}.indicator (fun _ => E.indicator F w) := by
      funext y; rfl
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hFE : Integrable (E.indicator F) m := by
    have h := hf₂.integral_prod_left
    simp_rw [inner] at h
    exact h
  refine ⟨(integrable_indicator_iff hE).1 hFE, ?_⟩
  calc ∫ g in E, F g ∂m = ∫ w, E.indicator F w ∂m := (integral_indicator hE).symm
    _ = ∫ q, f₂ q ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ q, f₂ (Te q) ∂(m.prod μ) := (hT.integral_comp' f₂).symm
    _ = ∫ q, f q ∂(m.prod μ) := by simp_rw [hf₂T]
    _ = ∫ q, g0 q ∂(m.prod μ) := hfint
    _ = (∫ x, (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F x ∂m) * ∫ y, ζ y ∂μ := integral_prod_mul _ _
    _ = _ := by rw [integral_indicator hUm, mul_comm]

end GlobalTheory.Core.Rk.FubiniPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralSplitFinitePlaceFubiniStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_split_finite_place_fubini : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (μ : Measure (GlobalTheory.FinZeta.Gv A v)), μ.IsHaarMeasure → ∀ J : Subgroup (GlobalTheory.FinZeta.Gv A v), IsOpen (J : Set (GlobalTheory.FinZeta.Gv A v)) → μ J = 1 → ∀ E : Set (GA D A), MeasurableSet E → (∀ x y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y ∈ E ↔ x ∈ E) → ∀ (F : GA D A → ℂ) (ζ : GlobalTheory.FinZeta.Gv A v → ℂ), Integrable ζ μ → (∀ y ∈ J, ζ y = 1) → (∀ x ∈ E, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y) = ζ y * F x) → IntegrableOn F (E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) m → IntegrableOn F E m ∧ ∫ g in E, F g ∂m = (∫ y, ζ y ∂μ) * ∫ g in E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}, F g ∂m := by
  first | exact @GlobalTheory.Core.Rk.FubiniPlace.integral_split_place | exact GlobalTheory.Core.Rk.FubiniPlace.integral_split_place | (intros; apply GlobalTheory.Core.Rk.FubiniPlace.integral_split_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoubling
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw.Peel

theorem qPeel_holds : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  intro hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz hlev
  classical
  have hhaar : s.ν.IsHaarMeasure := by
    obtain ⟨hr, -, hfl⟩ := hs
    exact hfl.haar
  have : BorelSpace (GA D s.V) := ⟨rfl⟩
  obtain ⟨-, hmO, hlevIff, -, -, -⟩ := GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs
  have hmL : MeasurableSet (levSet s) := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs).1
  set F := flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z with hF
  have hloc := GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz
  choose J μ ζ hJo hμ hμJ hζi hζ1 hJiff hζv hFx using hloc

  have hQPg : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => by rw [hw.union]; exact Finset.mem_union_right _ h
  have hQS : ∀ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := fun PP h => Finset.mem_image_of_mem _ (hQPg PP h)
  have hinj := GlobalTheory.LevelPlaces.injOn_under D c hw.com

  let cond : Pl D.host.E → GA D s.V → Prop := fun PP g => gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG s.V s.β s.L
  let ET : Finset (Pl D.host.E) → Set (GA D s.V) := fun T => intOff c s ∩ {g | ∀ PP ∈ T, cond PP g}
  have hET : ∀ T, T ⊆ w.Q → MeasurableSet (ET T) := by
    intro T hT
    have e : {g : GA D s.V | ∀ PP ∈ T, cond PP g} = ⋂ PP ∈ T, {g | cond PP g} := by ext g; simp
    refine hmO.inter ?_
    rw [e]
    refine Finset.measurableSet_biInter T fun PP hPP => ?_
    have e2 : {g : GA D s.V | cond PP g} = (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ⁻¹' (J PP (hT hPP) : Set _) := by
      ext g; exact hJiff PP (hT hPP) g
    rw [e2]
    exact ((hJo PP (hT hPP)).preimage (GlobalTheory.AdelicU.continuous_proj D.sp.cm.sig s.V.gram _)).measurableSet

  have hgAt : ∀ (v v' : HeightOneSpectrum (𝓞 D.host.F)), v' ≠ v → ∀ (x : GA D s.V) y,
      gAt s.V (.inl v') (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = gAt s.V (.inl v') x := by
    intro v v' hne x y
    show GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y)) =
      GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' x)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]
  have hOff : ∀ v ∈ c.S, ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ intOff c s ↔ x ∈ intOff c s := by
    intro v hv x y
    refine forall_congr' fun v' => imp_congr_right fun hv' => ?_
    have hne : v' ≠ v := fun h => hv' (h ▸ hv)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]

  have key : ∀ T : Finset (Pl D.host.E), T ⊆ w.Q → IntegrableOn F (ET w.Q) s.ν →
      IntegrableOn F (ET (w.Q \ T)) s.ν ∧ (z = (D.R.t : ℝ) / 2 → ∫ g in ET (w.Q \ T), F g ∂s.ν =
        (∏ PP ∈ T, blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) * ∫ g in ET w.Q, F g ∂s.ν) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ h; refine ⟨by simpa using h, fun _ => by simp⟩
    | insert PP T hPT ih =>
      intro hsub hint
      have hPP : PP ∈ w.Q := hsub (Finset.mem_insert_self _ _)
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert _ _).trans hsub) hint
      set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hvdef
      have hE' : MeasurableSet (ET (w.Q \ insert PP T)) := hET _ Finset.sdiff_subset
      have hinv : ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ ET (w.Q \ insert PP T) ↔
          x ∈ ET (w.Q \ insert PP T) := by
        intro x y
        refine and_congr (hOff v (hQS PP hPP) x y) (forall₂_congr fun PP' hPP' => ?_)
        have hne : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ v := by
          intro h
          have h1 := Finset.mem_sdiff.1 hPP'
          exact h1.2 (hinj (hQPg PP' h1.1) (hQPg PP hPP) h ▸ Finset.mem_insert_self _ _)
        show gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP'))) (x * _) ∈ _ ↔ gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP'))) x ∈ _
        rw [hgAt v _ hne]
      have hset : ET (w.Q \ insert PP T) ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ J PP hPP} = ET (w.Q \ T) := by
        ext g
        simp only [ET, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun PP' hPP' => ?_⟩
          by_cases he : PP' = PP
          · subst he; exact (hJiff PP' hPP g).2 h3
          · refine h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1, fun h => ?_⟩)
            rcases Finset.mem_insert.1 h with h | h
            · exact he h
            · exact (Finset.mem_sdiff.1 hPP').2 h
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, fun PP' hPP' => h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1,
            fun h => (Finset.mem_sdiff.1 hPP').2 (Finset.mem_insert_of_mem h)⟩)⟩, (hJiff PP hPP g).1 (h2 PP ?_)⟩
          exact Finset.mem_sdiff.2 ⟨hPP, hPT⟩
      have hFx' : ∀ x ∈ ET (w.Q \ insert PP T), GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v x = 1 → ∀ y,
          F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = ζ PP hPP y * F x :=
        fun x hx h1 y => hFx PP hPP x hx.1 h1 y
      have hfub := GlobalTheory.T.integral_split_finite_place_fubini D s.V s.ν hhaar v (μ PP hPP) (hμ PP hPP) (J PP hPP) (hJo PP hPP) (hμJ PP hPP)
        (ET (w.Q \ insert PP T)) hE' hinv F (ζ PP hPP) (hζi PP hPP) (hζ1 PP hPP) hFx' (by rw [hset]; exact ih1)
      refine ⟨hfub.1, fun hz2 => ?_⟩
      rw [hfub.2, hset, ih2 hz2, hζv PP hPP hz2, Finset.prod_insert hPT]
      ring

  have hsub : levSet s ⊆ ET w.Q := fun g hg => ⟨((hlevIff g).1 hg).1, fun PP hPP => ((hlevIff g).1 hg).2 _ (hQS PP hPP)⟩
  have hzero : ∀ g ∈ ET w.Q \ levSet s, F g = 0 := by
    rintro g ⟨⟨h1, h2⟩, h3⟩
    by_contra hne
    apply h3
    refine (hlevIff g).2 ⟨h1, fun v hv => ?_⟩
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    rw [hw.union] at hPP
    rcases Finset.mem_union.1 hPP with hP | hP
    · have hc : coefW p.ω m X (p.pt φ) g ≠ 0 := by
        intro h0
        apply hne
        simp only [hF, flatInt, GlobalTheory.Core.Rk.IP.integrand]
        rw [show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g from rfl, h0, zero_mul, zero_mul]
      exact GlobalTheory.T.twistedChain_coefficient_supported_principal_level D hgap c w hw k hk s s' hs hs' p hp m X hX φ g hc _
        (by simp only [Twist.S₀, Finset.coe_image]; exact Set.mem_image_of_mem _ hP)
    · exact h2 PP hP
  have hintR : IntegrableOn F (ET w.Q) s.ν := hlev.of_forall_diff_eq_zero (hET _ subset_rfl) hzero
  have hR := key w.Q subset_rfl hintR
  have hE0 : ET (w.Q \ w.Q) = intOff c s := by
    ext g; simp [ET]
  rw [hE0] at hR
  refine ⟨hR.1, fun hz2 => ?_⟩
  rw [hR.2 hz2, setIntegral_eq_of_subset_of_forall_diff_eq_zero (hET _ subset_rfl) hsub hzero]
  rfl

end GlobalTheory.ChainTw.Peel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoublingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainTwistPlacesIntegralPeel_of_doubling : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  first | exact @GlobalTheory.ChainTw.Peel.qPeel_holds | exact GlobalTheory.ChainTw.Peel.qPeel_holds | (intros; apply GlobalTheory.ChainTw.Peel.qPeel_holds <;> assumption)
end

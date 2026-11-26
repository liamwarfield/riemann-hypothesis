module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig
open Formalism.L2

theorem not_bad_of_genAt {D : D7} {M : Formalism.L2.MtFam D} (T : Formalism.L2.NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl)
    (i : D.nd.Loc) (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ Formalism.L2.badPl D i := by
  intro hmem
  obtain ⟨w', hover, hw'⟩ := hmem
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, e2]
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  rcases hw' with hQ | ⟨kk, hg⟩ | hpd
  · rw [T.Q_eq j w i h] at hQ
    have hsw : s.w ∈ T.B.Qc j w := T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩
    exact hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    rw [hl] at hpd
    exact Or.inr (Or.inr (hp _ hpd))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro D M HT HR AV NL i hyp P x hcong
  classical
  have tN0 : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
      Formalism.L2.NG.tN (M.loc i).J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
    intro s ϖ k; ext g; simp [Formalism.L2.NG.tN, Formalism.L2.NG.heckeD]
  by_cases hP0 : D.naut.typeV i P = ⊥
  · refine ⟨x, (AV.ptV i P x).2 ?_⟩
    intro v k s ϖ _ _ _ _ _ y hy
    rw [hP0, Submodule.mem_bot] at hy
    subst hy
    rw [map_zero, smul_zero, tN0]
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  let lamF : PlE D.host → ℕ → ℂ := fun v =>
    if hv : SplitOut D.nd i v then Classical.choose (hyp P v hv) else 0
  have hlamF : ∀ v (hv : SplitOut D.nd i v), lamF v = Classical.choose (hyp P v hv) := fun v hv => dif_pos hv
  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hcoef : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → ∃ a : D.nd.O i,
      iotaO D.nd D.naut i a = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) a = IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv hk1 hk2
    obtain ⟨p, hp1, hp2⟩ := hcong v hv
    have e1 := (Classical.choose_spec (hyp P v hv)).1
    rw [← hlamF v hv] at e1
    exact coeff_extract (iotaO D.nd D.naut i) hinjO D.R.nV (normV v) (normV_unit D i v hv.2.1) p (lamF v)
      (fun k => (D.nd.hT i v k : D.nd.X i → D.nd.O i) x) (hp1.trans e1) hp2 k hk1 hk2
  let aF : PlE D.host → ℕ → D.nd.O i := fun v k =>
    if hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then Classical.choose (hcoef v k hv.1 hv.2.1 hv.2.2) else 0
  have haF : ∀ v k (hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV), iotaO D.nd D.naut i (aF v k) = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) (aF v k) =
        IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv
    simp only [aF, dif_pos hv]
    exact Classical.choose_spec (hcoef v k hv.1 hv.2.1 hv.2.2)
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK
  let κ : PlE D.host → ℕ → FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) := fun v k =>
    algebraMap _ _ (NL.phO _ _ i h (aF v k))
  have hκ : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → φ (κ v k) = lamF v k := by
    intro v k hv hk1 hk2
    simp only [κ, hφalg]
    rw [← hiotaC]
    exact (haF v k ⟨hv, hk1, hk2⟩).1
  obtain ⟨e, hene, he⟩ := GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) (D.nd.j_range i).1
    (D.nd.j_range i).2 (D.nd.mu_w i) φ hφ κ y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.T.splitEx_every_datum D v hv.1
      have hbad : s.v ∉ Formalism.L2.badPl D i := not_bad_of_genAt NL _ _ i h v k s hvk hc
      have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (Formalism.L2.badPl D i) (HT.J_hyp i)
        s ϖ k hbad hu
      refine ⟨s, ϖ, hc, hu, ?_, ?_⟩
      · intro c f f'
        show Formalism.L2.NG.tN (M.loc i).J s ϖ k (c • f + f') =
          c • Formalism.L2.NG.tN (M.loc i).J s ϖ k f + Formalism.L2.NG.tN (M.loc i).J s ϖ k f'
        simp only [Formalism.L2.NG.tN]
        rw [heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]
      · rw [hκ v k hv hk1 hk2]
        have e3 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y0 hy0
        rw [← hlamF v hv] at e3
        exact e3)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := pt_of_eigvec (Formalism.L2.heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨NL.phO _ _ i h (aF v k), he v k hvk⟩)
  have hψv : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = NL.phO _ _ i h (aF v k) := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hcls : Formalism.L2.NCov.cls ψ = NL.mx _ _ i := by
    refine (cls_eq_of_residue _ ψ (NL.ptX _ _ i h x).1 ?_).trans (NL.ptX _ _ i h x).2.1
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [hψv v k hvk, ← NL.ptX_hT _ _ i h x v k hvk]
    obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
    exact residue_map_equiv (NL.phO _ _ i h) (haF v k ⟨hv, hk1, hk2⟩).2
  have hW : Formalism.L2.NCov.W (Formalism.L2.heckeAlg NL.B _ _) (Formalism.L2.NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  refine ⟨(NL.ptX _ _ i h).symm ⟨ψ, hcls, hW⟩, (AV.ptV i P _).2 ?_⟩
  intro v k s ϖ hv hc hu hk1 hk2 y hy
  have hvk := (Formalism.L2.genAt_iff NL h v k).1 ⟨hv, hk1, hk2⟩
  have e1 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y hy
  rw [← hlamF v hv] at e1
  rw [e1]
  congr 1
  show lamF v k = iotaO D.nd D.naut i _
  rw [hiotaC, NL.ptX_hT _ _ i h _ v k hvk, Equiv.apply_symm_apply]
  show lamF v k = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
  rw [hψv v k hvk, ← hiotaC]
  exact (haF v k ⟨hv, hk1, hk2⟩).1.symm

end GlobalTheory.PtLocalEig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointLocalEigen_galoisPolynomial_split : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  first | exact @GlobalTheory.PtLocalEig.main | exact GlobalTheory.PtLocalEig.main | (intros; apply GlobalTheory.PtLocalEig.main <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PtLocalPin

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_finset {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i), f ≠ 0 →
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) →
      ∃ S' ∈ t, ∃ g ∈ S', g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert a t ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _), hyfix κ hκ hκt] at e
        exact add_left_cancel e
      by_cases hy0 : y = 0
      · subst hy0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF z hz hf0 hzfix
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨a, Finset.mem_insert_self a t, y, hy, hy0, hyfix⟩
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF f ((sup_le hle le_rfl) hf) hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem fixed_of_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g' : GAf L n → W)
    (hg' : g' ∈ S') (hg0 : g' ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g' = g') :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨T, hT⟩ := hiso
  set g : S := T.symm ⟨g', hg'⟩ with hgdef
  have hTg : T g = ⟨g', hg'⟩ := T.apply_symm_apply _
  refine ⟨g, g.2, fun h => hg0 ?_, fun κ hκ ht => ?_⟩
  · have h0 : g = 0 := Subtype.ext h
    rw [h0, map_zero] at hTg
    exact (congrArg Subtype.val hTg).symm
  · have e := hT κ g ⟨_, hS.stable κ _ g.2⟩ rfl
    rw [hTg] at e
    have e' : T ⟨NG.rt L n κ g, hS.stable κ _ g.2⟩ = T g := by
      rw [hTg]
      exact Subtype.ext (e.trans (hfix κ hκ ht))
    exact congrArg Subtype.val (T.injective e')

theorem exists_fixed_of_isoTyp {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (hS : NG.IsIrrRep ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) (hf0 : f ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g', hg', hg0, hgf⟩ := exists_fixed_of_finset v t ht f hft hf0 hfix
  exact fixed_of_iso hS.1 (ht hS').2 v g' hg' hg0 hgf

end Gen

theorem coeff_eq {N n : ℕ} (hN : N ≠ 0) {c c' : ℕ → ℂ}
    (h : (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c k) * X ^ (n - k) : ℂ[X]) =
      X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c' k) * X ^ (n - k))
    {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : c k = c' k := by
  have key : ∀ d : ℕ → ℂ, (X ^ n + ∑ j ∈ Finset.Icc 1 n,
      C ((-1 : ℂ) ^ j * ((N : ℂ)) ^ (j * (j - 1) / 2) * d j) * X ^ (n - j) : ℂ[X]).coeff (n - k) =
        (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * d k := by
    intro d
    rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro j hj hjk
      rw [Finset.mem_Icc] at hj
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro hk
      exact absurd (Finset.mem_Icc.2 ⟨h1, h2⟩) hk
  have e := congrArg (fun p : ℂ[X] => p.coeff (n - k)) h
  rw [key c, key c'] at e
  have hne : (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hN))
  exact mul_left_cancel₀ hne e

end GlobalTheory.PtLocalPin

end

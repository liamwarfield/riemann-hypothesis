module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.CrysFromGTwo

theorem matRep_twistM {K Γ : Type} [Field K] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) K)
    (χ : Γ →* Kˣ) (g : Γ) (v : Fin k → K) :
    matRep (twistM M χ) g v = ((χ g : Kˣ) : K) • matRep M g v := by
  change (((χ g : Kˣ) : K) • M g).mulVec v = ((χ g : Kˣ) : K) • (M g).mulVec v
  exact Matrix.smul_mulVec _ _ _

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ h

theorem crys_chi (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π))))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π := by
    obtain ⟨e, he⟩ := hD
    exact ⟨e, fun g u => he g u⟩
  exact GlobalTheory.ChiOneEnl.chiOneE_of_isBlockSum hF D i r ρ π hs hc w hw C.LL C.le

theorem twist_mat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K LL : FinExt l)
    {k : ℕ} (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (χ : ↥(GK K) →* (↥LL.1)ˣ)
    (ht : IsTwistRep χ (matRep M) (matRep M')) (hχ : IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ))
    (h : IsCrys (P.PD K) (matRep M)) : IsCrys (P.PD K) (matRep M') :=
  (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI T K LL _ _ _ _ χ ht hχ h).1

theorem crys_tw (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  have := D.nd.lPrime i
  have ht : IsTwistRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
    rw [locC_rTwO]
    exact matRep_twistM _ _ g v
  exact twist_mat (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL _ _ _ ht hχ h

end GlobalTheory.CrysFromGTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
open Formalism.L2.Col

namespace GlobalTheory.TopLaw

theorem blkDet_eq_dB : ∀ {κ : Type} [CommRing κ] {n : ℕ} (β : ℕ → ℕ) (c s t : ℕ), s + t ≤ n → (∀ i, i < n → (β i = c ↔ s ≤ i ∧ i < s + t)) → ∀ (M : btG n κ β) (A : ℕ → ℕ → κ), (∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) → ((blkDet n κ β c M : κˣ) : κ) = GlobalTheory.DatumLaw.dB A s t := by
  intro κ _ n β c s t hn hβ M A hA
  rw [blkDet_val]
  unfold GlobalTheory.DatumLaw.dB
  let e : Fin t ≃ {i : Fin n // β i.1 = c} :=
    { toFun := fun u => ⟨⟨s + u.1, by have := u.2; omega⟩, (hβ _ (by have := u.2; omega)).2 ⟨by simp, by have := u.2; simp⟩⟩
      invFun := fun i => ⟨i.1.1 - s, by have := (hβ _ i.1.2).1 i.2; omega⟩
      left_inv := fun u => Fin.ext (by simp)
      right_inv := fun i => Subtype.ext (Fin.ext (by have := (hβ _ i.1.2).1 i.2; simp only; omega)) }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext u v
  exact (hA (e u).1 (e v).1).symm

end GlobalTheory.TopLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIsoDetGenMNeZero
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

theorem dualIso_det_genM_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem dualIso_cofRel_unique {R : Type} [CommRing R] [IsDomain R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f g') : g = g' :=
  mul_left_cancel₀ (pow_ne_zero _ (dualIso_det_genM_ne_zero R (m + 1))) (h.trans h'.symm)

theorem dualIso_cofRel_add {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g f' g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f' g') :
    CofRel R m ν (f + f') (g + g') := by
  unfold CofRel at *
  rw [mul_add, map_add (f := _), h, h']

theorem dualIso_cofRel_smul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : R) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_smul, h]

theorem dualIso_cofRel_zsmul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : ℤ) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_zsmul, h]

theorem dualIso_map_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    (MvPolynomial.map φ).mapMatrix (genM R n) = genM S n := by
  ext1 a b
  simp [genM]

theorem dualIso_map_cofAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (f : MP R n) :
    MvPolynomial.map φ (cofAct R n f) = cofAct S n (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [cofAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cofAct, aeval_X]
    rw [← dualIso_map_genM φ n, ← RingHom.map_adjugate]
    rfl

theorem dualIso_cofRel_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (h : CofRel R m ν f g) :
    CofRel S m ν (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  unfold CofRel at *
  rw [← dualIso_map_cofAct, ← h, map_mul, map_pow, RingHom.map_det, dualIso_map_genM]

theorem dualIso_nuDual_antitone {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) : Antitone (nuDual ν) := by
  intro i j hij
  have := hν (Fin.rev_le_rev.2 hij)
  simp only [nuDual]
  omega

theorem dualIso_nuDual_last {m : ℕ} (ν : Fin (m + 1) → ℕ) : nuDual ν (Fin.last m) = 0 := by
  simp [nuDual]

theorem dualIso_nuDual_nuDual {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) (hl : ν (Fin.last m) = 0) :
    nuDual (nuDual ν) = ν := by
  funext i
  have := hν (Fin.zero_le i)
  simp only [nuDual, Fin.rev_rev, Fin.rev_zero, hl]
  omega

theorem dualIso_units_smul_smul {M : Type} [AddCommGroup M] (ε : ℤˣ) (x : M) : (ε : ℤ) • (ε : ℤ) • x = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

theorem dualIso_exists_map (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (hl : ν (Fin.last m) = 0) :
    ∃ Ψ : MP K (m + 1) →ₗ[K] MP K (m + 1), ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, CofRel K m ν f (Ψ f) := by
  choose G hG using GlobalTheory.T.exists_cofactorTwist_dualWeyl K m ν hν hl
  let Ψ₀ : dualWeyl K (m + 1) (m + 1) ν →ₗ[K] MP K (m + 1) :=
    { toFun := fun f => G f.1 f.2
      map_add' := fun f g =>
        dualIso_cofRel_unique (hG _ (f + g).2).2 (dualIso_cofRel_add (hG _ f.2).2 (hG _ g.2).2)
      map_smul' := fun c f =>
        dualIso_cofRel_unique (hG _ (c • f).2).2 (dualIso_cofRel_smul c (hG _ f.2).2) }
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend Ψ₀
  refine ⟨Ψ, fun f hf => ?_⟩
  have h1 : Ψ f = G f hf := LinearMap.congr_fun hΨ ⟨f, hf⟩
  rw [h1]
  exact (hG f hf).2

theorem dualIso_lattice (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0)
    (Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1))
    (hΨ : ∀ f ∈ dualWeyl Kf (m + 1) (m + 1) ν, CofRel Kf m ν f (Ψ f))
    (A B : Submodule O (MP O (m + 1))) (hA : A ≤ dualWeyl O (m + 1) (m + 1) ν)
    (hB : B ≤ dualWeyl O (m + 1) (m + 1) (nuDual ν))
    (hAB : ∀ f ∈ A, ∃ g ∈ B, CofRel O m ν f g) (hBA : ∀ g ∈ B, ∃ f ∈ A, CofRel O m (nuDual ν) g f) :
    (A.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap).map (Ψ.restrictScalars O) =
      B.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap := by
  have key : ∀ f ∈ A, ∀ g, CofRel O m ν f g →
      Ψ (MvPolynomial.map (algebraMap O Kf) f) = MvPolynomial.map (algebraMap O Kf) g := fun f hf g hfg =>
    dualIso_cofRel_unique (hΨ _ (dualWeylMap O Kf _ _ _ _ _ (hA hf))) (dualIso_cofRel_map _ hfg)
  apply le_antisymm
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨g, hg, hfg⟩ := hAB f hf
    exact ⟨g, hg, (key f hf g hfg).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hgf⟩ := hBA g hg
    obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive O m (nuDual ν) (dualIso_nuDual_antitone hν) (dualIso_nuDual_last ν)
    have h1 := hε g (hB hg) f hgf
    rw [dualIso_nuDual_nuDual hν hl] at h1
    have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
    rw [dualIso_units_smul_smul] at h2
    have h3 : (ε : ℤ) • f ∈ A := A.toAddSubgroup.zsmul_mem hf _
    exact ⟨_, ⟨_, h3, rfl⟩, key _ h3 g h2⟩

theorem exists_posOk_dual (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0) (e c : ℤ) :
    ∃ Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1),
      PosOk O Kf (m + 1) ν (nuDual ν) e (-(e + ν 0 + c)) c (fun h => (h⁻¹).transpose) Ψ := by
  obtain ⟨Ψ, hΨ⟩ := dualIso_exists_map Kf m ν hν hl
  have hν' := dualIso_nuDual_antitone hν
  have hl' := dualIso_nuDual_last ν
  have hdd := dualIso_nuDual_nuDual hν hl
  refine ⟨Ψ, fun f hf h0 => ?_, ?_, fun h hh f hf => ?_, ?_, ?_⟩
  · obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m ν hν hl
    have h1 := hε f hf _ (hΨ f hf)
    rw [h0] at h1
    have h2 : CofRel Kf m (nuDual ν) 0 0 := by simp [CofRel]
    have h3 := dualIso_cofRel_unique h1 h2
    rw [← dualIso_units_smul_smul ε f, h3, smul_zero]
  · apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨g, hg, hfg⟩ := GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m ν hν hl f hf
      rw [dualIso_cofRel_unique (hΨ f hf) hfg]
      exact hg
    · intro g hg
      obtain ⟨f, hf, hgf⟩ := GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m _ hν' hl' g hg
      obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m _ hν' hl'
      have h1 := hε g hg f hgf
      rw [hdd] at h1 hf
      have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
      rw [dualIso_units_smul_smul] at h2
      have h3 : (ε : ℤ) • f ∈ dualWeyl Kf (m + 1) (m + 1) ν :=
        (dualWeyl Kf (m + 1) (m + 1) ν).toAddSubgroup.zsmul_mem hf _
      exact ⟨_, h3, dualIso_cofRel_unique (hΨ _ h3) h2⟩
  · have h1 := GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant Kf m ν h hh f hf _ (hΨ f hf)
    have h2 := dualIso_cofRel_unique (hΨ _ (dualWeylRowStable Kf _ _ _ h⁻¹ f hf)) h1
    have h3 : (h⁻¹).transpose⁻¹ = h.transpose := by
      rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hh]
    have h4 : (h⁻¹).transpose.det = (h.det)⁻¹ := by
      rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp only [rnd, LinearMap.smul_apply, map_smul, AlgHom.toLinearMap_apply, h2, h3, h4, smul_smul, inv_zpow']
    rw [← zpow_add₀ hh.ne_zero, ← zpow_add₀ hh.ne_zero]
    congr 2
    ring
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ le_rfl le_rfl (GlobalTheory.T.exists_cofactorTwist_dualWeyl O m ν hν hl) fun g hg => ?_
    have := GlobalTheory.T.exists_cofactorTwist_dualWeyl O m _ hν' hl' g hg
    rwa [hdd] at this
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ (weylLeDual O _ _ _ _ hν) (weylLeDual O _ _ _ _ hν')
      (GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m ν hν hl) fun g hg => ?_
    have := GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m _ hν' hl' g hg
    rwa [hdd] at this

end GlobalTheory.ValCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainWideTwistTransport
noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain

section Lattices

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := _root_.GlobalTheory.DegAsm.FrameMove.exists_proj L hfg hsp W

end Lattices


open Classical in
theorem deg_eq {ι : Type} {a b : ℕ} (e : ι × Fin b × Fin a →₀ ℕ) (τ : ι) :
    ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = ∑ β, ∑ α, (e (τ, β, α) : ℤ) := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Nat.cast_sum]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun y : Fin b × Fin a => (τ, y) ∈ e.support))]
  · refine Finset.sum_bij (fun k _ => k.2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, rfl⟩ := Finset.mem_filter.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    · intro k hk k' hk' h
      exact Prod.ext ((Finset.mem_filter.1 hk).2.trans (Finset.mem_filter.1 hk').2.symm) h
    · intro y hy
      exact ⟨(τ, y), Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).2, rfl⟩, rfl⟩
    · intro k hk
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hk
      rfl
  · intro y _ hy
    have : (τ, y) ∉ e.support := fun h => hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [show (τ, y.1, y.2) = (τ, y) from rfl, Finsupp.notMem_support_iff.1 this, Nat.cast_zero]

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Ties

variable {D : D7} {EX : ErrX D} (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

variable (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)

end Ties

section Statements

variable (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) {δ : ℂ}

end Statements

end GlobalTheory.ColPeriodCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralDetOfStable
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.RatEqui

namespace GlobalTheory.DetStab

theorem isIntegral_det_of_stable {R E : Type} [CommRing R] [IsNoetherianRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (γ : Matrix (Fin n) (Fin n) E) (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ.det := by
  classical
  let N : Submodule R E := Submodule.span R {x | ∃ w : Fin n → L, x = (Matrix.of fun i => (w i : Fin n → E)).det}
  let M : Submodule R E := ⨆ j : Fin n, L.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hM : M.FG := Submodule.fg_iSup _ fun j => hfg.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hprod : ∀ (s : Finset (Fin n)) (f : Fin n → E), (∀ i, f i ∈ M) → ∏ i ∈ s, f i ∈ M ^ s.card := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty, pow_zero]
      exact Submodule.one_le.1 le_rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      exact Submodule.mul_mem_mul (hf a) ih
  have hle : N ≤ M ^ (Finset.univ : Finset (Fin n)).card := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine Submodule.smul_of_tower_mem _ _ (hprod _ _ fun i => ?_)
    exact Submodule.mem_iSup_of_mem i ⟨_, (w (σ i)).2, rfl⟩
  have hN : N.FG := (hM.pow _).of_le hle
  have hne : N ≠ ⊥ := by
    intro h
    have h0 : (Matrix.detRowAlternating (n := Fin n) (R := E)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ (x : L) => (x : Fin n → E)) (fun _ => ?_) fun w => ?_
      · rw [← hsp]; congr 1; exact Subtype.range_coe
      · have : (Matrix.of fun i => (w i : Fin n → E)).det ∈ N := Submodule.subset_span ⟨w, rfl⟩
        rw [h] at this
        exact this
    have h1 := congrArg (fun f => f (1 : Matrix (Fin n) (Fin n) E)) h0
    have h2 : (1 : Matrix (Fin n) (Fin n) E).det = 0 := h1
    simp at h2
  refine isIntegral_of_smul_mem_submodule N hne hN _ fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun i => ⟨γ.mulVec (w i), hγ _ (w i).2⟩, ?_⟩
    rw [smul_eq_mul, mul_comm, ← Matrix.det_transpose γ, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact N.smul_mem r hx

theorem prod_emb_det_eq_one (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hL : SD D L) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (hu : γ * adj D γ = 1) (hs : ∀ v, v ∈ L ↔ γ.mulVec v ∈ L) : ∏ τ, embT D τ γ.det = 1 := by
  letI := D.host.cmStar
  obtain ⟨hfg, hsp, -⟩ := hL
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := by
    intro x
    haveI := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    rw [Formalism.HC.HostAx.conjE_apply]
    exact IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : γ.det * (adj D γ).det = 1 := by rw [← Matrix.det_mul, hu, Matrix.det_one]
  have hadj : (adj D γ).det = D.host.conj γ.det := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ).symm
  have hz : γ.det ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar, ← hadj]
    exact ⟨by rw [mul_comm, hd], hd⟩
  have i1 := isIntegral_det_of_stable L hfg hsp γ fun v hv => (hs v).1 hv
  have i2 := isIntegral_det_of_stable L hfg hsp (adj D γ) fun v hv => (hs _).2 (by
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]; exact hv)
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i1
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i2
  have hspan : Submodule.span (𝓞 D.host.E) {γ.det} = Submodule.span (𝓞 D.host.E) {(1 : D.host.E)} := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def, ha, mul_one]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨b, by rw [Algebra.smul_def, hb, mul_comm, hd]⟩
  have e1 := hχ.2 ⟨γ.det, hz⟩
  have e2 := hχ.2 1
  have e3 : ∏ τ, (embT D τ γ.det)⁻¹ = 1 := by
    have e1' : χ (Submodule.span (𝓞 D.host.E) {γ.det}) = ∏ τ, (embT D τ γ.det)⁻¹ := e1
    have e2' : χ (Submodule.span (𝓞 D.host.E) {(1 : D.host.E)}) = ∏ τ, (embT D τ 1)⁻¹ := e2
    rw [← e1', hspan, e2']
    simp
  rwa [Finset.prod_inv_distrib, inv_eq_one] at e3

end GlobalTheory.DetStab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

namespace GlobalTheory.DetFields

open GlobalTheory.Mem.Col2.JetEx.VacEqPf

theorem iE_det {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    s.iE ((LinearEquiv.det γ : X.Eˣ) : X.E) = (matOf s γ).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  rw [show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from
    RingHom.map_det (s.iE : X.E →+* D.host.E) _]
  congr 1

theorem det_of_stab : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  intro D X s χ hok hχ n N' hL γ hγ
  have hd := iE_det s γ.1
  have hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N') := hL
  have hfg : (s.lat N').FG := hL.1
  have hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := hL.2.1
  have hU := matOf_unitary s hok γ
  set M := matOf s γ.1 with hM

  have hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1 := by
    letI := D.host.cmStar
    have e : star M = GlobalTheory.RatEqui.adj D M := by
      ext i j
      simp [GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]
    rw [← e]
    exact ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
  have hadj : M * GlobalTheory.RatEqui.adj D M = 1 := hMM.2

  have hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N' := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (mem_lat s N' v).1 hv
      refine (mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩
      rw [← hγ]
      exact ⟨x, hx, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := (mem_lat s N' _).1 hv
      rw [← hγ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : M.mulVec (vec s x) = M.mulVec v := by
        rw [← hyv]
        exact matOf_mulVec s γ.1 x
      have hinj : vec s x = v := by
        have := congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'
        simpa only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec] using this
      rw [← hinj]
      exact (mem_lat s N' _).2 ⟨x, hx, rfl⟩

  have hdet : M.det * D.host.conj M.det = 1 := by
    have h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det := by
      unfold GlobalTheory.RatEqui.adj
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm
    rw [← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]
  refine ⟨?_, ?_, ?_⟩
  · apply s.iE.injective
    rw [map_mul, hok.2, hd, map_one]
    exact hdet
  · have i1 := GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv
    have i2 : IsIntegral ℤ M.det := isIntegral_trans (R := ℤ) _ i1
    have i3 := map_isIntegral_int s.iE.symm.toRingHom i2
    rw [← hd] at i3
    simpa using i3
  · rw [hd]
    exact GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs

end GlobalTheory.DetFields
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  first | exact @GlobalTheory.DetFields.det_of_stab | exact GlobalTheory.DetFields.det_of_stab | (intros; apply GlobalTheory.DetFields.det_of_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpSNegSumBivariatePairIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogSubstExpSubOne
noncomputable section

namespace GlobalTheory.SubringSeries

open MvPowerSeries Formalism.FG.InjVAux

variable {K : Type} [Field K] {κ : Type}

def intS (A : Subring K) (κ : Type) : Subring (MvPowerSeries κ K) where
  carrier := {F | ∀ n, coeff n F ∈ A}
  mul_mem' := by
    classical
    intro a b ha hb n
    rw [coeff_mul]
    exact A.sum_mem fun x _ => A.mul_mem (ha _) (hb _)
  one_mem' := by
    classical
    intro n
    rw [coeff_one]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  add_mem' := fun ha hb n => by rw [map_add (f := _)]; exact A.add_mem (ha n) (hb n)
  zero_mem' := fun n => by rw [map_zero]; exact A.zero_mem
  neg_mem' := fun ha n => by rw [map_neg]; exact A.neg_mem (ha n)

variable {A : Subring K}

theorem finsum_mem' {ι : Type} {f : ι → K} (h : ∀ i, f i ∈ A) : ∑ᶠ i, f i ∈ A :=
  finsum_induction (fun x => x ∈ A) A.zero_mem (fun _ _ => A.add_mem) h

theorem subst_mem {ι : Type} {a : ι → MvPowerSeries κ K} (ha : HasSubst a) (hA : ∀ i, a i ∈ intS A κ)
    {E : MvPowerSeries ι K} (hE : E ∈ intS A ι) : subst a E ∈ intS A κ := by
  intro n
  rw [coeff_subst ha]
  refine finsum_mem' fun d => ?_
  rw [smul_eq_mul]
  refine A.mul_mem (hE d) (((intS A κ).prod_mem fun i _ => (intS A κ).pow_mem (hA i) _) n)

section Frob

variable {p : ℕ} {hp : p ≠ 0} {σ : K →+* K}

end Frob

end GlobalTheory.SubringSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasSubstPairPadicComplexOfConstantCoeffZero
noncomputable section

namespace GlobalTheory.ThBe0.Inhab

open MvPowerSeries Formalism.FG.InjVAux GlobalTheory.SubringSeries Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric GlobalTheory.ThBe0

variable {l : ℕ} [hl : Fact l.Prime] {κ : Type}

theorem coeff_logF_cases (n : ℕ) : (PowerSeries.coeff n (logF l) = 0 ∧ ∀ j, n ≠ l ^ (2 * j)) ∨
    ∃ j, n = l ^ (2 * j) := by
  by_cases h : ∃ j, n = l ^ (2 * j)
  · exact Or.inr h
  · push Not at h
    refine Or.inl ⟨?_, h⟩
    rw [logF, PowerSeries.coeff_mk]
    exact Finset.sum_eq_zero fun j _ => if_neg (h j)

theorem coeff_zero_logF : PowerSeries.coeff 0 (logF l) = 0 := by
  rcases coeff_logF_cases (l := l) 0 with h | ⟨j, h⟩
  · exact h.1
  · exact absurd h.symm (pow_ne_zero _ hl.out.ne_zero)

theorem cc_logF : PowerSeries.constantCoeff (logF l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_logF]

theorem hasSubst_pair_padicComplex_of_constantCoeff_zero {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (fun i : Fin 2 => if i = 0 then x else y) :=
  hasSubst_of_constantCoeff_zero fun i => by split_ifs <;> assumption

theorem subst_powerSeriesEvalTwoGroups {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (E : MvPowerSeries (Fin 2) ℂ_[l]) : subst a (at2 E x y) = at2 E (subst a x) (subst a y) := by
  rw [at2, at2, subst_comp_subst_apply (hasSubst_pair_padicComplex_of_constantCoeff_zero hx hy) ha]
  congr 1
  funext i
  split_ifs <;> rfl

theorem subst_psubst {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (f : PowerSeries ℂ_[l]) :
    subst a (f.subst x) = f.subst (subst a x) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hx).const ha f

theorem cc_lg (k : κ) : constantCoeff (lg k : MvPowerSeries κ ℂ_[l]) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X k) _ cc_logF

section Frob

variable {σ : ℂ_[l] →+* ℂ_[l]}

end Frob

end GlobalTheory.ThBe0.Inhab
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OrbitPair

open MvPowerSeries

theorem expS_neg_sum_bivariate_pair_integral : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} [NeZero n'] (om om' : Fin (n' / 2) → ℂ_[p]) (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ om om' s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → Formalism.MainNotions.GL3Theta.SimeqW (MvPowerSeries.subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) → ∃ V : MvPowerSeries (ZMod n') ℂ_[p], Formalism.MainNotions.GL3Theta.IntegralW V ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) := by
  intro p _ σ n' _ om om' b0 bv t x _hb0 hbv ht hx hlaS htx hsim
  classical
  have hxS : HasSubst x := hasSubst_of_constantCoeff_zero fun r => (hx r).2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have hzcc : ∀ s : ZMod n', constantCoeff (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = 0 := by
    intro s
    rw [← hlaS s]
    exact constantCoeff_subst_eq_zero htS ht (GlobalTheory.BeProps.constantCoeff_laS s)
  have hzS : HasSubst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) := hasSubst_of_constantCoeff_zero hzcc
  have hzOm : ∀ s : ZMod n', subst x (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = GlobalTheory.ThStr.laS p n' s := by
    intro s
    rw [← hlaS s, subst_comp_subst_apply htS hxS]
    have : (fun r => subst x (t r)) = (X : ZMod n' → MvPowerSeries (ZMod n') ℂ_[p]) := funext htx
    rw [this, subst_self]
    rfl
  have hFx : subst x (subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) = subst (GlobalTheory.ThStr.laS p n') bv := by
    rw [subst_comp_subst_apply hzS hxS]
    congr 1
    funext s
    exact hzOm s
  have hGx : subst x (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) =
      ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hxS, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coe_substAlgHom hxS, GlobalTheory.ThBe0.Inhab.subst_powerSeriesEvalTwoGroups hxS (GlobalTheory.ThBe0.Inhab.cc_lg _) (GlobalTheory.ThBe0.Inhab.cc_lg _)]
    simp only [GlobalTheory.ThBe0.lg]
    rw [GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _), GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _),
      subst_X hxS, subst_X hxS]
  obtain ⟨hD0, hDint⟩ := hsim
  set F := subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv with hF
  set G := ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r)) with hG
  have ccL : constantCoeff (subst (GlobalTheory.ThStr.laS p n') bv) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => GlobalTheory.BeProps.constantCoeff_laS s)
      (fun s => GlobalTheory.BeProps.constantCoeff_laS s) hbv
  have ccD : constantCoeff (subst x (F - G)) = 0 := constantCoeff_subst_eq_zero hxS (fun r => (hx r).2) hD0
  have hneg : -(subst x G) = subst x (F - G) + -(subst (GlobalTheory.ThStr.laS p n') bv) := by
    rw [subst_sub hxS, hFx]
    ring
  refine ⟨subst x (Formalism.MainNotions.TaylorLogMetric.expMv (F - G)), ?_, ?_⟩
  · exact GlobalTheory.SubringSeries.subst_mem (A := Formalism.MainNotions.GL3Theta.Wp p) hxS (fun r => (hx r).1) hDint
  · rw [← hGx, hneg]
    show PowerSeries.subst _ (PowerSeries.exp ℂ_[p]) = _ * PowerSeries.subst _ (PowerSeries.exp ℂ_[p])
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ccD (by rw [map_neg, ccL, neg_zero]), GlobalTheory.BeProps.expMv_eq_subst hD0,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp x (fun r => (hx r).2) hD0]

end GlobalTheory.OrbitPair
end
end

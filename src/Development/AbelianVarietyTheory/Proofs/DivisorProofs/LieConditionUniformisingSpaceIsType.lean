module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDerivAt0CompLinearIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpDerEigenIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

def expDer (he : IsExp y e) (w : Fin g → ℂ) : epsPt y ⟶ G := (he.2.2.2.1 w).exists.choose

variable (he : IsExp y e)
include he

theorem expDer_spec (w : Fin g → ℂ) : IsDerivAt0 (fun z => (e z).left) w (expDer he w).left :=
  (he.2.2.2.1 w).exists.choose_spec

theorem exp_zero : e 0 = 1 := by
  have h := he.1 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_eq_iff (w : Fin g → ℂ) (v : epsPt y ⟶ G) :
    IsDerivAt0 (fun z => (e z).left) w v.left ↔ expDer he w = v :=
  ⟨fun hv => Over.OverMorphism.ext
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he w) hv), fun hv => hv ▸ expDer_spec he w⟩

theorem expDer_base (w : Fin g → ℂ) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (1 : Over.mk y ⟶ G).left := by
  rw [(expDer_spec he w).1]; show (e 0).left = _; rw [exp_zero he]

theorem expDer_injective : Function.Injective (expDer he) := by
  intro w w' h
  have h1 := expDer_spec he w
  have h2 := expDer_spec he w'
  rw [← h] at h2
  have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (e 0).left := h1.1
  exact (he.2.2.2.2 _ hb).unique h1 h2

theorem expDer_surj (v : epsPt y ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left) :
    ∃ w, expDer he w = v := by
  obtain ⟨w, hw, -⟩ := he.2.2.2.2 v (by rw [hv, exp_zero he])
  exact ⟨w, (expDer_eq_iff he w v).1 hw⟩

theorem expDer_add (w w' : Fin g → ℂ) : expDer he (w + w') = expDer he w * expDer he w' :=
  (expDer_eq_iff he _ _).1 (GlobalTheory.UnifCompare.isDerivAt0_mul (by rw [exp_zero he]) (expDer_spec he w)
    (expDer_spec he w'))

theorem expDer_zero : expDer he 0 = 1 := by
  have h := expDer_add he 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_smul (c : ℂ) (w : Fin g → ℂ) :
    (expDer he (c • w)).left = spMap (epsScale c) ≫ (expDer he w).left :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he _)
    (GlobalTheory.UnifCompare.isDerivAt0_smul (expDer_spec he w) c)

theorem expDer_prod {n : ℕ} (f : Fin n → Fin g → ℂ) :
    (List.ofFn fun j => expDer he (f j)).prod = expDer he (∑ j, f j) := by
  induction n with
  | zero => simp [expDer_zero he]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => f j.succ), Fin.sum_univ_succ, expDer_add he]

theorem expDer_mulVec (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (w : Fin g → ℂ) : expDer he (M *ᵥ w) = expDer he w ≫ φ := by
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (expDer_spec he w) φ.left
  have h2 : (fun z => (e z).left ≫ φ.left) = fun z => (e (Matrix.mulVecLin M z)).left := by
    funext z; rw [Matrix.mulVecLin_apply, hM z, Over.comp_left]
  rw [h2, GlobalTheory.ThetaWitness.isDerivAt0_comp_linear_iff (fun z => (e z).left) he.2.2.1] at h1
  exact (expDer_eq_iff he _ _).1 h1

theorem expDer_eigen_iff (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (c : ℂ) (w : Fin g → ℂ) :
    (expDer he w ≫ φ).left = spMap (epsScale c) ≫ (expDer he w).left ↔ M *ᵥ w = c • w := by
  rw [← expDer_mulVec he M φ hM, ← expDer_smul he]
  constructor
  · intro h
    exact expDer_injective he (Over.OverMorphism.ext h)
  · intro h
    rw [h]

end GlobalTheory.UPel.HT.LieType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieTypeOfUnif
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.LieEigenspaceFinrank

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

theorem isLieEigen_iff (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (w : Fin g → ℂ) :
    IsLieEigen act y τ' (expDer he w) ↔ w ∈ eigSp φ τ := by
  rw [mem_eigSp]
  constructor
  · intro h c
    rw [hτ]
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).1 (h.2 c)
  · intro h
    refine ⟨expDer_base he w, fun c => ?_⟩
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).2 (by rw [← hτ]; exact h c)

theorem comb_iff (he : IsExp y e) {n : ℕ} (w : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (z : Fin g → ℂ) :
    (∃ u : Fin n → (epsPt y ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (expDer he (w i)).left) ∧
      expDer he z = (List.ofFn u).prod) ↔ z = ∑ i, c i • w i := by
  constructor
  · rintro ⟨u, hu, hz⟩
    have hu' : u = fun i => expDer he (c i • w i) := by
      funext i
      exact Over.OverMorphism.ext (by rw [hu i, expDer_smul he])
    rw [hu', expDer_prod he (fun i => c i • w i)] at hz
    exact expDer_injective he hz
  · intro hz
    refine ⟨fun i => expDer he (c i • w i), fun i => expDer_smul he _ _, ?_⟩
    rw [expDer_prod he (fun i => c i • w i), hz]

theorem finrank_eigSp (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (n : ℕ) (h : LieMult act y τ' n) :
    Module.finrank ℂ (eigSp φ τ) = n := by
  obtain ⟨v, hv, hb⟩ := h
  choose w hw using fun i => expDer_surj he (v i) (hv i).1
  obtain rfl : v = fun i => expDer he (w i) := funext fun i => (hw i).symm
  have hwm : ∀ i, w i ∈ eigSp φ τ := fun i => (isLieEigen_iff he φ act hM τ τ' hτ _).1 (hv i)
  have key : ∀ z ∈ eigSp φ τ, ∃! c : Fin n → ℂ, z = ∑ i, c i • w i := by
    intro z hz
    have := hb _ ((isLieEigen_iff he φ act hM τ τ' hτ z).2 hz)
    simpa only [comb_iff he w] using this
  let L : (Fin n → ℂ) →ₗ[ℂ] eigSp φ τ := Fintype.linearCombination ℂ (fun i => (⟨w i, hwm i⟩ : eigSp φ τ))
  have hL : ∀ c, (L c : Fin g → ℂ) = ∑ i, c i • w i := by
    intro c
    simp [L, Fintype.linearCombination_apply]
  have hbij : Function.Bijective L := by
    rw [Function.bijective_iff_existsUnique]
    intro z
    obtain ⟨c, hc, hu⟩ := key z.1 z.2
    refine ⟨c, Subtype.ext (by rw [hL]; exact hc.symm), fun c' hc' => hu c' ?_⟩
    exact (congrArg Subtype.val hc').symm.trans (hL c')
  rw [← (LinearEquiv.ofBijective L hbij).finrank_eq]
  simp

theorem lie_type_of_unif (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ))
    (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ))
    (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ (o.fam h hL).A))
    (hU : UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 (Sp ℂ)) e) (τ : Fin D.a → D.F →+* ℂ)
    (hτ : ∀ (i : Fin D.a) (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) :
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
      ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
        u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  have he : IsExp (G := o.A) (𝟙 (Sp ℂ)) e := hU.2.2.1
  have hM : ∀ (a : D.O) z, e (ρ a *ᵥ z) = e z ≫ o.act.act a := hU.2.2.2.2.1
  have hx : 𝟙 (Sp ℂ) ≫ spMap σ = spMap σ := Category.id_comp _
  have hM' : ∀ (c : 𝓞 D.F) z, e ((ρ.comp (algebraMap (𝓞 D.F) D.O)) c *ᵥ z) = e z ≫ (o.act.toF D).act c :=
    fun c z => hM _ z
  refine ⟨fun i => ?_, fun u hu => ?_⟩
  · exact finrank_eigSp (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _
      (o.lieRank ℂ (𝟙 _) σ hx i)
  · obtain ⟨v, hv, hprod⟩ := o.lie ℂ σ (𝟙 _) hx (expDer (G := o.A) he u)
      ⟨expDer_base he u, (expDer_eigen_iff (G := o.A) he _ _ (hM _) (σ b.ρ) u).2 hu⟩
    choose w hw using fun i => expDer_surj (G := o.A) he (v i) (hv i 0).1
    obtain rfl : v = fun i => expDer (G := o.A) he (w i) := funext fun i => (hw i).symm
    have hu' : u = ∑ i, w i := expDer_injective he (hprod.trans (expDer_prod he w))
    rw [hu']
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
    exact (isLieEigen_iff (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _).1
      ⟨(hv i 0).1, fun c => (hv i c).2⟩

end GlobalTheory.LieEigenspaceFinrank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

open GlobalTheory.UPel.HT

theorem lieEigen_rank_cover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e,
    UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∀ τ : Fin D.a → (D.F →+* ℂ),
    (∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) →
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
    ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
      u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  first
  | exact @_root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif
  | exact _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif
  | (apply _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> assumption)
  | (intros; apply _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LieEigenspaceFinrank.lie_type_of_unif ..)

end GlobalTheory.UPel.HT.LieType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_dimension_of_uniformization : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∀ τ : Fin D.a → (D.F →+* ℂ), (∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) → (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧ ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u → u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  first | exact @GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | exact GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | (intros; apply GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

theorem eigSp_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  intro F _ _ g φ s τ hτ
  let ρ : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)).toRingEquiv.toRingHom.comp φ
  have hcomm : ∀ a b : 𝓞 F, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : 𝓞 F => ρ a)
    (fun i j m => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) m)
  let χ : (F →+* ℂ) → (𝓞 F → ℂ) := fun σ c => σ (c : F)
  have hχ : Function.Injective χ := by
    intro σ₁ σ₂ he
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact congrFun he c
  have hle : ∀ σ : F →+* ℂ, eigSp φ σ ≤ ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (χ σ c) := by
    intro σ u hu
    rw [Submodule.mem_iInf]
    intro c
    apply (Module.End.genEigenspace (ρ c) (χ σ c)).mono le_top
    rw [Module.End.mem_eigenspace_iff]
    have := hu c
    simpa [ρ, χ, Matrix.toLin'_apply] using this
  have hnot : χ τ ∉ (χ '' (s : Set (F →+* ℂ))) := by
    rintro ⟨σ, hσ, he⟩
    exact hτ (hχ he ▸ hσ)
  have hd := h.disjoint_biSup hnot
  refine (hd.mono_left (hle τ)).mono_right ?_
  refine iSup₂_le fun σ hσ => (hle σ).trans ?_
  exact le_iSup₂_of_le (f := fun (x : 𝓞 F → ℂ) (_ : x ∈ χ '' (s : Set (F →+* ℂ))) => ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (x c)) (χ σ) ⟨σ, hσ, rfl⟩ le_rfl

end GlobalTheory.UPel.HT.LieType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  first | exact @GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | exact GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | (intros; apply GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionUniformisingSpaceIsType
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

theorem exists_ext (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    ∃ τ' : F →+* ℂ, ∀ c : 𝓞 F, τ' (c : F) = τ c := by
  have hinj : Function.Injective τ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker τ) hne (by simpa [RingHom.mem_ker] using hx)
      (Algebra.IsIntegral.isIntegral x)
    apply hI
    rw [eq_bot_iff]
    intro n hn
    simp only [Ideal.mem_comap, RingHom.mem_ker, map_intCast] at hn
    simpa using hn
  refine ⟨IsFractionRing.lift hinj, fun c => ?_⟩
  exact IsFractionRing.lift_algebraMap hinj c

theorem root_cases {r z : ℂ} {tr nm : ℤ} (hd : tr ^ 2 - 4 * nm < 0) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (z ≠ r ↔ (starRingEnd ℂ) z = r) := by
  have hc : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hfac : ∀ x : ℂ, x ^ 2 - tr * x + nm = 0 → x = r ∨ x = tr - r := by
    intro x hx
    have : (x - r) * (x - (tr - r)) = 0 := by linear_combination hx - hr
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    have him : r.im = 0 := Complex.conj_eq_iff_im.1 h
    have hre := congrArg Complex.re hr
    have himr : r = (r.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [himr] at hre
    simp [sq] at hre
    have : ((2 * r.re - tr) ^ 2 : ℝ) = (tr : ℝ) ^ 2 - 4 * nm := by linear_combination 4 * hre
    have h2 : ((tr : ℝ) ^ 2 - 4 * nm) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * r.re - tr)]
  have hcr : (starRingEnd ℂ) r = tr - r := (hfac _ hc).resolve_left hne
  constructor
  · intro h
    have : z = tr - r := (hfac z hz).resolve_left h
    rw [this, ← hcr]; simp
  · intro h hzr
    rw [hzr] at h
    exact hne h

theorem lie_isType : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → b.IsType σ ρ := by
  intro p _ D R _ b N σ ρ o h hL D' t Q e hU
  classical
  choose τ hτ using fun i => exists_ext D.F (σ.comp (b.t i))
  have hτ' : ∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c) := fun i c => hτ i c
  obtain ⟨hrank, hcov⟩ := GlobalTheory.T.eigenspace_dimension_of_uniformization p D R b N σ ρ o h hL D' t Q e hU τ hτ'
  have hsum := GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul p D D' ρ Q hU.2.1
  set r := σ b.ρ with hrdef
  have hr : r ^ 2 - D.tr * r + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hω : (D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hτω : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ^ 2 - D.tr * τ' (D.ω : D.F) + D.nm = 0 := by
    intro τ'
    have := congrArg (fun x : 𝓞 D.F => τ' (x : D.F)) hω
    simpa using this
  have key : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ≠ r ↔ ((starRingEnd ℂ).comp τ') (D.ω : D.F) = r :=
    fun τ' => root_cases D.disc_neg hr (hτω τ')

  have hinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have h1 := hτ' i x
      have h2 := hτ' j x
      rw [hij] at h1
      simp [RingHom.mem_ker, ← h1, ← h2]
    rw [b.comax i j hne] at hle
    have : (1 : R) ∈ RingHom.ker σ := hle Submodule.mem_top
    simp [RingHom.mem_ker] at this
  have hτA : ∀ i, τ i (D.ω : D.F) = r := fun i => by rw [hτ', b.t_ω]
  set d : (D.F →+* ℂ) → ℕ := fun τ' => Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ') with hd

  have hzero : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) = r → τ' ∉ Finset.univ.image τ → d τ' = 0 := by
    intro τ' h1 h2
    have hbot : eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ' = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu' : ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = r • u := by
        have := hu D.ω
        rw [h1] at this
        exact this
      have hmem := hcov u hu'
      have hle : (⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) ≤ ⨆ τ'' ∈ Finset.univ.image τ, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'' := by
        refine iSup_le fun i => ?_
        exact le_biSup (fun τ'' => eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'') (Finset.mem_image_of_mem τ (Finset.mem_univ i))
      have := (GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) _ τ' h2).le_bot ⟨hu, hle hmem⟩
      simpa using this
    simp [hd, hbot]
  have hA : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ i, (D.m : ℂ) * σ (b.t i c) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hA' : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) =
      ∑ i, (D.m : ℂ) * (starRingEnd ℂ) (σ (b.t i c)) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hconj : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) := by
    intro c
    refine Finset.sum_nbij' (fun τ' => (starRingEnd ℂ).comp τ') (fun τ' => (starRingEnd ℂ).comp τ') ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have := (key x).1 (by simpa using hx)
      simpa using this
    · intro x hx
      have hx' : x (D.ω : D.F) = r := by simpa using hx
      have : ¬ ((starRingEnd ℂ).comp x) (D.ω : D.F) = r := by
        exact fun h => (key x).2 h hx'
      simpa using this
    · intro x _; ext; simp
    · intro x _; ext; simp
    · intro x _; simp
  intro c
  have htr : (ρ (algebraMap (𝓞 D.F) D.O c)).trace = ∑ τ' : D.F →+* ℂ, (d τ' : ℂ) * τ' (c : D.F) := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) c
  rw [htr, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r)]
  have hB : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), ((D.m : ℂ) * D.n * τ' (c : D.F) -
        (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F)) := by
    refine Finset.sum_congr rfl fun τ' _ => ?_
    have := hsum τ'
    have h' : (d τ' : ℂ) + d ((starRingEnd ℂ).comp τ') = D.m * D.n := by exact_mod_cast this
    linear_combination τ' (c : D.F) * h'
  rw [hB, Finset.sum_sub_distrib, hconj c, hA c, hA' c]
  have e1 : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.m : ℂ) * D.n * τ' (c : D.F) =
      D.m * ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.n : ℂ) * τ' (c : D.F) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  simp only [← Finset.mul_sum]
  ring

end GlobalTheory.UPel.HT.LieType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionUniformisingSpaceIsTypeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieCondition_uniformisingSpace_isType : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → b.IsType σ ρ := by
  first | exact @GlobalTheory.UPel.HT.LieType.lie_isType | exact GlobalTheory.UPel.HT.LieType.lie_isType | (intros; apply GlobalTheory.UPel.HT.LieType.lie_isType <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroup
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoinStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem exists_aut_comp_eq_of_normal {E L : Type} [Field E] [CharZero E] [Normal ℚ E] [Field L]
    (f f' : E →+* L) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, f' x = f (σ x) := by
  haveI : CharZero L := (RingHom.charZero_iff f.injective).1 inferInstance
  letI : Algebra E L := f.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by
    change _ = f (algebraMap ℚ E q)
    simp
  obtain ⟨σ, hσ⟩ := (Normal.algHomEquivAut ℚ L E).symm.surjective f'.toRatAlgHom
  refine ⟨σ, fun x => ?_⟩
  have := DFunLike.congr_fun hσ x
  exact this.symm

theorem exists_letter_of_local_embedding : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), ∃ g : D.R.GG, (∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) = Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))) ∧ (Br.EmbTypeU D.nbr i w hw τ ↔ g ∈ D.R.Psi) := by
  intro D i w hw τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨σ, hσ⟩ := exists_aut_comp_eq_of_normal
    (((Br.toLLK (D.nbr i w hw)).comp (D.nd.embK i)).comp D.embE)
    ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw))
  obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
  have hg' : D.host.sigmaOf g = σ := hg
  have key : ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
      Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x))) := by
    intro x
    rw [hg']
    exact hσ x
  have hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := fun x =>
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  refine ⟨g, key, ?_, ?_⟩
  · rintro ⟨-, φ, hφ, h⟩
    have : D.host.emb g = φ := RingHom.ext fun x => by
      rw [← hemb x]
      exact h x _ (key x).symm
    exact ((factEmb D.R D.host).2 g).1 (this ▸ hφ)
  · intro hgP
    refine ⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, ((factEmb D.R D.host).2 g).2 hgP, ?_⟩
    intro x y hy
    have hy' : y = D.embE (D.host.sigmaOf g x) :=
      (D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))
    rw [hy', hemb]

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNeTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNeTypePrime
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertNotType

theorem main : ∀ (D : D7) (l : ℕ) (k : Fin 2), TwistedPlaces.InertK D l → l ≠ D.host.g k := by
  intro D l k h heq
  subst heq
  have h1 := D.ntypes.g_cond k
  have hdvd : 4 * D.host.d ∣ D.host.QS * D.host.q * D.host.d :=
    Nat.mul_dvd_mul_right (((by decide : 4 ∣ 16).trans D.host.sixteen_dvd_QS).mul_right _) _
  have hd1 : D.host.g k % (4 * D.host.d) = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k) hdvd, h1]
    exact Nat.mod_eq_of_lt (by have := D.host.hyp.2.1.two_le; omega)
  have h21 : D.host.g k % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k) (⟨2 * D.host.d, by ring⟩ : 2 ∣ 4 * D.host.d), hd1]
  have hodd : Odd (D.host.g k) := Nat.odd_iff.2 h21
  have hJ : jacobiSym (-(D.host.d : ℤ)) (D.host.g k) = 1 := by
    rw [jacobiSym.mod_right _ hodd]
    have : (-(D.host.d : ℤ)).natAbs = D.host.d := by simp
    rw [this, hd1, jacobiSym.one_right]
  unfold TwistedPlaces.InertK Host.cls primeClass at h
  split_ifs at h <;> simp_all

end GlobalTheory.InertNotType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNeTypePrimeStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_prime_ne_typePrime : ∀ (D : D7) (l : ℕ) (k : Fin 2), TwistedPlaces.InertK D l → l ≠ D.host.g k := by
  first | exact @GlobalTheory.InertNotType.main | exact GlobalTheory.InertNotType.main | (intros; apply GlobalTheory.InertNotType.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct
open TensorProduct

noncomputable section

namespace GlobalTheory.HTW

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a := by
  rw [FilV, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem algebraTensorModule_map_id_eq_rTensor (f : V →ₗ[LL] V') (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = (f.restrictScalars Qp).rTensor BdR x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem comap_ker_sub_eq_ker_sub_of_injective_intertwining {M M' : Type} [AddCommGroup M] [Module LL M] [AddCommGroup M'] [Module LL M']
    (F : M →ₗ[LL] M') (hF : Function.Injective F) (A B : M →ₗ[LL] M) (A' B' : M' →ₗ[LL] M')
    (hA : ∀ x, A' (F x) = F (A x)) (hB : ∀ x, B' (F x) = F (B x)) :
    (LinearMap.ker (A' - B')).comap F = LinearMap.ker (A - B) := by
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, hA, hB,
    ← map_sub]
  exact map_eq_zero_iff F hF

private theorem mem_filV_iff_of_isScalarTower {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    (a : ℤ) (y : W ⊗[Qp] BdR) :
    y ∈ FilV PD (LL := LL) (V := W) a ↔ (((PD.Fil a).restrictScalars Qp).mkQ.lTensor W) y = 0 := by
  have e : ∀ z, AlgebraTensorModule.map (LinearMap.id : W →ₗ[LL] W) ((PD.Fil a).restrictScalars Qp).subtype z =
      (((PD.Fil a).restrictScalars Qp).subtype.lTensor W) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [← LinearMap.mem_ker, lTensor_mkQ, FilV, LinearMap.mem_range, LinearMap.mem_range]
  simp only [e]

private theorem filV_comap_tensorMap_of_injective (f : V →ₗ[LL] V') (hf : Function.Injective f) (a : ℤ) :
    (FilV PD (LL := LL) (V := V') a).comap (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FilV PD (LL := LL) (V := V) a := by
  ext x
  rw [Submodule.mem_comap, mem_filV_iff_of_isScalarTower, mem_filV_iff_of_isScalarTower, algebraTensorModule_map_id_eq_rTensor]
  have hc : ((PD.Fil a).restrictScalars Qp).mkQ.lTensor V' ((f.restrictScalars Qp).rTensor BdR x) =
      (f.restrictScalars Qp).rTensor _ (((PD.Fil a).restrictScalars Qp).mkQ.lTensor V x) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [hc]

  exact map_eq_zero_iff _ (Module.Flat.rTensor_preserves_injective_linearMap (f.restrictScalars Qp) hf)

private theorem injective_algebraTensorModule_map_id_of_injective (f : V →ₗ[LL] V') (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  intro x y hxy
  rw [algebraTensorModule_map_id_eq_rTensor, algebraTensorModule_map_id_eq_rTensor] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (f.restrictScalars Qp) hf hxy

private theorem ddRE_comap_tensorMap_eq_of_injective_equivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) :
    (DdRE PD ρ' τ).comap (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) = DdRE PD ρ τ := by
  have hF := injective_algebraTensorModule_map_id_of_injective f hf (Qp := Qp) (BdR := BdR)
  rw [DdRE, DdRE, Submodule.comap_inf, DdR, DdR, Submodule.comap_iInf, Submodule.comap_iInf]
  congr 1
  · refine iInf_congr fun g => comap_ker_sub_eq_ker_sub_of_injective_intertwining _ hF _ _ _ _ ?_ (fun x => rfl)
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, he]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · refine iInf_congr fun c => comap_ker_sub_eq_ker_sub_of_injective_intertwining _ hF _ _ _ _ ?_ ?_
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    · intro x
      simp

theorem FildR_eq_comap (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FildR PD ρ' τ a).comap
      (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  rw [FildR, FildR, Submodule.comap_inf, ddRE_comap_tensorMap_eq_of_injective_equivariant PD ρ ρ' f hf he τ, filV_comap_tensorMap_of_injective PD f hf a]

end

theorem isJumpV_of_injective : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V'), Function.Injective f → (∀ g v, f (ρ g v) = ρ' g (f v)) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD ρ τ a → IsJumpV PD ρ' τ a := by
  intros
  rename_i ρ ρ' f hf he τ a hJ
  unfold IsJumpV at hJ ⊢
  intro h
  apply hJ
  rw [FildR_eq_comap _ _ _ _ hf he, FildR_eq_comap _ _ _ _ hf he, h]

end GlobalTheory.HTW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

open TensorProduct Module

noncomputable section

namespace GlobalTheory.CrysSub

section Alg

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem rTensor_act (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PD ρ g x) =
      actVB PD σ g (AlgebraTensorModule.rTensor Qp B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) : Dcris PD ρ →ₗ[LL] Dcris PD σ :=
  (AlgebraTensorModule.rTensor Qp B f).restrict (fun x hx => by
    rw [mem_Dcris] at hx ⊢
    intro g
    rw [← rTensor_act PD ρ σ f hf, hx])

theorem coe_Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (x : Dcris PD ρ) :
    (Dmap PD ρ σ f hf x : W ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B f x := rfl

theorem rTensor_eq (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exact_Dmap (ρ : Representation LL G V) (σ : Representation LL G W)
    (τ : Representation LL G U) (f : V →ₗ[LL] W) (q : W →ₗ[LL] U)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hq : ∀ g v, q (σ g v) = τ g (q v))
    (hi : Function.Injective f) (he : Function.Exact f q) (hs : Function.Surjective q) :
    LinearMap.ker (Dmap PD σ τ q hq) ≤ LinearMap.range (Dmap PD ρ σ f hf) := by
  intro x hx
  have h0 : (q.restrictScalars Qp).rTensor B (x : W ⊗[Qp] B) = 0 := by
    rw [← rTensor_eq, ← coe_Dmap PD σ τ q hq, LinearMap.mem_ker.mp hx]
    rfl
  have hex : Function.Exact ((f.restrictScalars Qp).rTensor B) ((q.restrictScalars Qp).rTensor B) :=
    rTensor_exact B (f := f.restrictScalars Qp) (g := q.restrictScalars Qp) he hs
  have hinj : Function.Injective ((f.restrictScalars Qp).rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  obtain ⟨y, hy⟩ := (hex _).mp h0
  rw [← rTensor_eq] at hy
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  rw [mem_Dcris]
  intro g
  apply hinj
  rw [← rTensor_eq, ← rTensor_eq, rTensor_act PD ρ σ f hf, hy]
  exact (mem_Dcris PD σ _).mp x.2 g

theorem finrank_le_of_ker_le {A₁ A₂ A₃ : Type} [AddCommGroup A₁] [Module LL A₁]
    [AddCommGroup A₂] [Module LL A₂] [AddCommGroup A₃] [Module LL A₃]
    [Module.Finite LL A₁] [Module.Finite LL A₃] (f : A₁ →ₗ[LL] A₂) (q : A₂ →ₗ[LL] A₃)
    (h : LinearMap.ker q ≤ LinearMap.range f) :
    Module.Finite LL A₂ ∧ finrank LL A₂ ≤ finrank LL A₁ + finrank LL A₃ := by
  have hk : Module.Finite LL (LinearMap.ker q) := Submodule.finiteDimensional_of_le h
  have hq : Module.Finite LL (A₂ ⧸ LinearMap.ker q) :=
    Module.Finite.equiv (q.quotKerEquivRange).symm
  have h2 : Module.Finite LL A₂ := Module.Finite.of_submodule_quotient (LinearMap.ker q)
  refine ⟨h2, ?_⟩
  have h3 := q.finrank_range_add_finrank_ker
  have h4 := Submodule.finrank_mono h
  have h5 := f.finrank_range_le
  have h6 := (LinearMap.range q).finrank_le
  omega

def piRep {m : ℕ} (ρ : Fin m → Representation LL G V) : Representation LL G (Fin m → V) where
  toFun g := LinearMap.pi fun a => (ρ a g).comp (LinearMap.proj a)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem piRep_apply {m : ℕ} (ρ : Fin m → Representation LL G V) (g : G) (v : Fin m → V)
    (a : Fin m) : piRep ρ g v a = ρ a g (v a) := rfl

theorem sum_le_finrank_piRep {m : ℕ} (ρ : Fin m → Representation LL G V)
    [Module.Finite LL (Dcris PD (piRep ρ))] :
    ∑ a, finrank LL (Dcris PD (ρ a)) ≤ finrank LL (Dcris PD (piRep ρ)) := by
  have hp : ∀ a g v, (LinearMap.proj a : (Fin m → V) →ₗ[LL] V) (piRep ρ g v) =
      ρ a g ((LinearMap.proj a : (Fin m → V) →ₗ[LL] V) v) := fun a g v => rfl
  have hs : ∀ a g v, (LinearMap.single LL (fun _ : Fin m => V) a) (ρ a g v) =
      piRep ρ g (LinearMap.single LL (fun _ : Fin m => V) a v) := by
    intro a g v
    funext b
    rw [piRep_apply]
    by_cases h : b = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  let F : Dcris PD (piRep ρ) →ₗ[LL] (∀ a, Dcris PD (ρ a)) :=
    LinearMap.pi fun a => Dmap PD _ _ _ (hp a)
  have key : ∀ (a b : Fin m) (x : V ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.proj b : (Fin m → V) →ₗ[LL] V)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.single LL (fun _ : Fin m => V) a) x) =
        if a = b then x else 0 := by
    intro a b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      by_cases h : a = b
      · subst h; simp
      · simp [h, Pi.single_eq_of_ne (Ne.symm h)]
    | add x y hx hy =>
      simp only [map_add (f := _), hx, hy]
      split_ifs <;> simp
  have hF : Function.Surjective F := by
    intro y
    refine ⟨∑ a, Dmap PD _ _ _ (hs a) (y a), ?_⟩
    funext b
    apply Subtype.ext
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, LinearMap.pi_apply, coe_Dmap, Submodule.coe_sum, map_sum, key]
    simp
  have h1 : Module.Finite LL (∀ a, Dcris PD (ρ a)) := Module.Finite.of_surjective F hF
  have h2 : ∀ a, Module.Finite LL (Dcris PD (ρ a)) := fun a =>
    Module.Finite.of_surjective (LinearMap.proj a : (∀ a, Dcris PD (ρ a)) →ₗ[LL] _)
      (LinearMap.proj_surjective a)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_surjective hF

end Alg

theorem isCrys_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], Formalism.MainNotions.LocalSituation.fontCore PD → GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)), (∀ x, Continuous (Ms x)) → IsSubOfSums A.ρ (fun x g => Ms x g) → (∀ x, IsCrys PD (matRep (Ms x))) → IsCrys PD A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ O _ _ hF hO A ι k Ms
    hc hsub hcr
  obtain ⟨m, xs, j, hj, hjg⟩ := hsub
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let σ : Representation LL G (Fin m → Fin k → LL) := piRep fun a => matRep (Ms (xs a))
  have hσ : ∀ g v a, σ g v a = (Ms (xs a) g).mulVec (v a) := by
    intro g v a
    simp [σ, piRep_apply, matRep, Matrix.toLinAlgEquiv'_apply]
  have hjσ : ∀ g v, j (A.ρ g v) = σ g (j v) := by
    intro g v
    rw [hjg]
    funext a
    rw [hσ]
  have hst : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (σ g) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨A.ρ g v, hjσ g v⟩
  have hσc : ∀ v, Continuous fun g => σ g v := by
    intro v
    refine continuous_pi fun a => ?_
    simp only [hσ]
    exact (hc (xs a)).matrix_mulVec continuous_const
  let τ := σ.quotient (LinearMap.range j) hst
  have hτ : ∀ g v, (LinearMap.range j).mkQ (σ g v) = τ g ((LinearMap.range j).mkQ v) :=
    fun g v => rfl
  have : ContinuousSMul LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) :=
    IsModuleTopology.toContinuousSMul _ _
  let Q : GRep G Qp LL O :=
    { V := (Fin m → Fin k → LL) ⧸ LinearMap.range j
      ρ := τ
      cont := by
        intro x
        obtain ⟨v, rfl⟩ := (LinearMap.range j).mkQ_surjective x
        simp only [← hτ]
        exact continuous_quot_mk.comp (hσc v) }
  obtain ⟨⟨fA, lA⟩, -⟩ := hF LL O hO A
  obtain ⟨⟨fQ, lQ⟩, -⟩ := hF LL O hO Q
  have fQ' : Module.Finite LL (Dcris PD τ) := fQ
  have lQ' : finrank LL (Dcris PD τ) ≤
    finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) := lQ
  obtain ⟨fS, lS⟩ := finrank_le_of_ker_le _ _
    (exact_Dmap PD A.ρ σ τ j (LinearMap.range j).mkQ hjσ hτ hj
      (LinearMap.exact_map_mkQ_range j) (LinearMap.range j).mkQ_surjective)
  have h1 := sum_le_finrank_piRep PD (fun a => matRep (Ms (xs a)))
  have h2 : ∀ a, finrank LL (Dcris PD (matRep (Ms (xs a)))) = finrank Qp K₀ * k := by
    intro a
    have := hcr (xs a)
    rw [IsCrys] at this
    rw [this]
    simp
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h3 := (LinearMap.range j).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hj] at h3
  have h4 : finrank LL (Fin m → Fin k → LL) = m * k := by
    simp [Module.finrank_pi_fintype]
  have h5 : m * (finrank Qp K₀ * k) =
      finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) +
        finrank Qp K₀ * finrank LL A.V := by
    rw [← mul_add, h3, h4]; ring
  have h6 : finrank LL (Dcris PD (piRep fun a => matRep (Ms (xs a)))) = finrank LL (Dcris PD σ) := rfl
  rw [IsCrys]
  omega

end GlobalTheory.CrysSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbedding
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem size_not_thick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  intro D L C g j hR hnt
  obtain ⟨-, hw100, hwη, hwb, hbT, -⟩ := hR
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρe : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  have hfl : (⌊(hcAt D g).e j⌋ : ℝ) = wj D (j.1 + 1) ρ := by
    rw [hw]
    show (⌊(D.hc ρ).e j⌋ : ℝ) = (((D.hc ρ).e j : ℚ) : ℝ)
    rw [hz, Int.floor_intCast]; push_cast; rfl
  rw [hfl]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb' : 0 < L.sc.b' := by linarith
  have hq : 0 < L.sc.b' / L.sc.x := div_pos hb' hx
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hnt' : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρe]; exact hnt
  by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
    obtain ⟨a1, a2⟩ := L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm
    have a3 := L.bT_ge ⟨t, ht'⟩
    have a4 := hbT ⟨t, ht'⟩
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := L.win_thin _ (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hnt'⟩
    constructor <;> linarith

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbeddingStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.floor_size_bounds_not_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  first | exact @GlobalTheory.HTW.size_not_thick | exact GlobalTheory.HTW.size_not_thick | (intros; apply GlobalTheory.HTW.size_not_thick <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open TensorProduct

namespace GlobalTheory.SubSumJumps

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_mem_DdRE (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR)
    (hx : x ∈ DdRE PD ρ τ) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ DdRE PD ρ' τ := by
  have h1 : ∀ (g : G) (y : V ⊗[Qp] BdR),
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, hf]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have h2 : ∀ (c : K) (y : V ⊗[Qp] BdR),
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c
        (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)
          (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y) := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  simp only [DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  refine ⟨fun g => ?_, fun c => ?_⟩
  · rw [h1, hx.1 g]
  · rw [h2, hx.2 c, map_smul]

theorem FilV_anti (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

end

theorem jumpsInV_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (τ : K →ₐ[Qp] LL) (J : Set ℤ), IsSubOfSums ρ (fun x g => Ms x g) → (∀ x, JumpsInV PD (matRep (Ms x)) τ J) → JumpsInV PD ρ τ J := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ ι k Ms τ J
    hsub hJ a ha
  by_contra haJ
  apply ha
  obtain ⟨m, xs, j, hj, hje⟩ := hsub
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
  have hrv : ∀ v, r (j v) = v := fun v => LinearMap.congr_fun hr v
  apply le_antisymm
  · exact inf_le_inf_left _ (FilV_anti PD a)
  intro x hx
  refine ⟨hx.1, ?_⟩
  let p : Fin m → (V →ₗ[LL] (Fin k → LL)) := fun b => (LinearMap.proj b).comp j
  let s : Fin m → ((Fin k → LL) →ₗ[LL] V) := fun b =>
    r.comp (LinearMap.single LL (fun _ : Fin m => Fin k → LL) b)
  have hdec : ∀ y : V ⊗[Qp] BdR, y = ∑ b, AlgebraTensorModule.map (s b)
      (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.sum_tmul]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [s, p, LinearMap.comp_apply, ← map_sum]
      conv_lhs => rw [← hrv v]
      congr 1
      exact (Finset.univ_sum_single (j v)).symm
    | add y z hy hz =>
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← hy, ← hz]
  rw [hdec x]
  refine Submodule.sum_mem _ fun b _ => map_mem_FilV PD (s b) (a + 1) _ ?_
  have heq : FildR PD (matRep (Ms (xs b))) τ (a + 1) = FildR PD (matRep (Ms (xs b))) τ a := by
    by_contra h
    exact haJ (hJ (xs b) a h)
  have hm : AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FildR PD (matRep (Ms (xs b))) τ a := by
    refine ⟨map_mem_DdRE PD ρ _ (p b) (fun g v => ?_) τ x hx.1, map_mem_FilV PD (p b) a x hx.2⟩
    simp [p, hje, matRep, Matrix.toLinAlgEquiv'_apply]
  rw [← heq] at hm
  exact hm.2

end GlobalTheory.SubSumJumps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbedding
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.SizeThick

theorem size_thick {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hT : Thick D.host g) :
    L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hmem : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces := by
    rw [hρ, Equiv.apply_symm_apply]; exact hT
  have h := L.win_thick (j.1 + 1) (by omega) j.2 ρ hmem
  rw [hw] at h
  have hc : hcAt D g = D.hc ρ := rfl
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  rw [hc, hz, Int.floor_intCast]
  rw [hz] at h
  push_cast at h ⊢
  exact h

end GlobalTheory.HTW.SizeThick
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbeddingStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.floor_size_bounds_at_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m), Thick D.host g → L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  first | exact @GlobalTheory.HTW.SizeThick.size_thick | exact GlobalTheory.HTW.SizeThick.size_thick | (intros; apply GlobalTheory.HTW.SizeThick.size_thick <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizeBoundWindow
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_window : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C →
    L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (bHat L : ℝ) ∧
      (bHat L : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1 := by
  intro D L C h
  obtain ⟨hC, _, hw, hwb, -, hb⟩ := h
  obtain ⟨s, hs⟩ := D.R.t_odd
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hts : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) + 1 := by
    rw [hs]; push_cast; ring
  have hb'pos : 0 < L.sc.b' := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hfac : (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb' : L.sc.b' ≤ L.sc.b := by nlinarith
  have htb : (D.R.t : ℝ) + 2 ≤ L.sc.b := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hdiv : (D.R.t + 1) / 2 = s + 1 := by omega
  have hb0 : 0 ≤ L.sc.b := by linarith
  have hc1 := Nat.le_ceil L.sc.b
  have hc2 := Nat.ceil_lt_add_one hb0
  have hle : s + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((s + 1 : ℕ) : ℝ) ≤ ⌈L.sc.b⌉₊ := by
      have : (D.R.t : ℝ) = 2 * s + 1 := by rw [hs]; push_cast; ring
      push_cast; nlinarith
    exact_mod_cast this
  have hval : (bHat L : ℝ) = (⌈L.sc.b⌉₊ : ℝ) - ((s : ℝ) + 1) := by
    unfold bHat
    rw [hdiv, Nat.cast_sub hle]
    push_cast; ring
  rw [hval, hts]
  constructor <;> linarith

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.DecompCard

theorem card_stabilizer_eq_locDeg : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l →
    Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  intro l _ E _ _ _ v w hv hw
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have := v.isPrime
  have := w.isPrime
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), R ∈ placesOver E l →
      R.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hR)
  have := hover v hv
  have := hover w hw
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) (Ideal.span {(l : ℤ)}) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E), locDeg]

end GlobalTheory.DecompCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegreeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_decomposition_group_eq_local_degree : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l → Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  first | exact @GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | exact GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | (intros; apply GlobalTheory.DecompCard.card_stabilizer_eq_locDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_degW {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N)
    (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) :
    Br.DegW nbr i w hw := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl (N.l i) := (nbr i w hw).j.comp (algebraMap H.E N.Om)
  have hK : (nbr i w hw).Kw.1 = IntermediateField.adjoin ℚ_[N.l i] (Set.range c) :=
    GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' (N.l i) H.E c (nbr i w hw).Kw.1 (nbr i w hw).j_E (nbr i w hw).Kw.2
      (nbr i w hw).j_dense
  obtain ⟨v, hv, hc⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding (N.l i) H.E c
  have h1 := GlobalTheory.T.finrank_local_field_eq_card_decomposition_group (N.l i) H.E c v hc
  have h2 := GlobalTheory.T.card_decomposition_group_eq_local_degree (N.l i) H.E v w hv hw
  have h3 : Module.finrank ℚ_[N.l i] (nbr i w hw).Kw.1 = locDeg H.E w := by
    rw [hK, h1, h2]
  exact h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertiaStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), Br.DegW nbr i w hw := by
  first | exact @GlobalTheory.bridge_degW | exact GlobalTheory.bridge_degW | (intros; apply GlobalTheory.bridge_degW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefActionReprMemSubfield
open Formalism.L2.DIV Formalism.BasicNotions NumberField

namespace GlobalTheory

private lemma blockAct_map_mem_range_map_of_entries_mem {K : Type} [Field K] (K₀ : Subfield K) {ι : Type} [Fintype ι] {n : ℕ}
    (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ K₀)
    (P : MvPolynomial (ι × Fin n × Fin n) K₀) :
    _root_.Formalism.GradedWeylDivisibility.blockAct K U (MvPolynomial.map K₀.subtype P) ∈ (MvPolynomial.map K₀.subtype).range := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a, ?_⟩
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, MvPolynomial.map_X, _root_.Formalism.L2.DIV.blockAct_X]
    refine mul_mem hp (sum_mem fun b _ => mul_mem ?_ ?_)
    · exact ⟨MvPolynomial.C ⟨U v.1 v.2.1 b, hU _ _ _⟩, by simp⟩
    · exact ⟨MvPolynomial.X (v.1, b, v.2.2), by simp⟩

private lemma actP_mem_range_map_of_entries_mem {K : Type} [Field K] (K₀ : Subfield K) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (g : ι → GL (Fin n) K)
    (hg : ∀ τ a b, (g τ : Matrix (Fin n) (Fin n) K) a b ∈ K₀)
    {F : _root_.Formalism.L2.DIV.Pol K ι n} (hF : F ∈ (MvPolynomial.map K₀.subtype).range) :
    _root_.Formalism.L2.DIV.actP lam g F ∈ (MvPolynomial.map K₀.subtype).range := by
  obtain ⟨P, rfl⟩ := hF
  have hdet : ∀ τ, (g τ : Matrix (Fin n) (Fin n) K).det ∈ K₀ := by
    intro τ
    have hM : (g τ : Matrix (Fin n) (Fin n) K) =
        (Matrix.of fun a b => (⟨(g τ : Matrix _ _ K) a b, hg τ a b⟩ : K₀)).map K₀.subtype := by
      ext a b; rfl
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact SetLike.coe_mem _
  have hd : _root_.Formalism.L2.DIV.detTwK lam g ∈ K₀ := by
    rw [_root_.Formalism.L2.DIV.detTw_eq]
    exact prod_mem fun τ _ => by
      first | exact pow_mem (hdet τ) _ | exact zpow_mem (hdet τ) _
  unfold _root_.Formalism.L2.DIV.actP _root_.Formalism.L2.DIV.trAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul]
  refine mul_mem ⟨MvPolynomial.C ⟨_, hd⟩, by simp⟩ (blockAct_map_mem_range_map_of_entries_mem K₀ _ ?_ P)
  intro τ a b
  exact hg τ b a

theorem _root_.GlobalTheory.coefAction_repr_mem_subfield : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (K₀ : Subfield K) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n), (∀ τ x, emb τ x ∈ K₀) → ∀ (g : GL (Fin n) E) i j, (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoV emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ ∧ (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoVr emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ := by
  intro E K ι _ _ _ _ _ n emb K₀ lam hemb γ i j
  classical
  have hbase : ∀ l, _root_.Formalism.L2.DIV.bVVfun K lam l ∈ (MvPolynomial.map K₀.subtype).range := by
    intro l
    obtain ⟨P, hP⟩ := _root_.Formalism.L2.DIV.bVVfun_int K lam l
    rw [hP]
    exact _root_.Formalism.L2.DIV.fk_int_mem K₀ P
  have key : ∀ x : _root_.Formalism.L2.DIV.VV K lam, (x : _root_.Formalism.L2.DIV.Pol K ι n) ∈ (MvPolynomial.map K₀.subtype).range →
      (_root_.Formalism.L2.DIV.bVV K lam).repr x i ∈ K₀ := by
    intro x hx
    refine _root_.Formalism.L2.DIV.fk_descent K₀ (_root_.Formalism.L2.DIV.bVVfun K lam) (_root_.Formalism.L2.DIV.bVVfun_spec K lam).1 hbase (fun l => (_root_.Formalism.L2.DIV.bVV K lam).repr x l) ?_ i
    have hs := congrArg Subtype.val ((_root_.Formalism.L2.DIV.bVV K lam).sum_repr x)
    rw [Submodule.coe_sum] at hs
    simp only [Submodule.coe_smul, _root_.Formalism.L2.DIV.bVV_coe] at hs
    rw [hs]
    exact hx
  have hj : ((_root_.Formalism.L2.DIV.bVV K lam j : _root_.Formalism.L2.DIV.VV K lam) : _root_.Formalism.L2.DIV.Pol K ι n) ∈
      (MvPolynomial.map K₀.subtype).range := by
    rw [_root_.Formalism.L2.DIV.bVV_coe]; exact hbase j
  constructor
  · apply key
    unfold _root_.Formalism.L2.DIV.rhoV
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.rhoK_coe]
    refine actP_mem_range_map_of_entries_mem K₀ lam _ ?_ hj
    intro τ a b
    rw [_root_.Formalism.L2.DIV.embGL_coe]
    exact hemb τ _
  · apply key
    unfold _root_.Formalism.L2.DIV.rhoVr
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.rhoK_coe]
    refine actP_mem_range_map_of_entries_mem K₀ lam _ ?_ hj
    intro τ a b
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.invTrK_coe, _root_.Formalism.L2.DIV.embGL_inv, _root_.Formalism.L2.DIV.embGL_coe]
    exact hemb τ _

end GlobalTheory
end

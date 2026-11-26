module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLattices
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TiltedDivisibility.TiltDivOfGeneral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaine
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOnto
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOnto
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem extHom_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  intro l _ G _ _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hF
  choose x hx hfx using fun i => hF (b₂ i) (hb₂.1 i)
  have key : ∀ i j, ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m =
      (1 : Matrix (Fin k₂) (Fin k₂) ↥LL.1) i j := by
    intro i j
    have h1 := congrFun (LinearMap.toMatrix_mulVec_repr b₁ b₂ F.f (x j)) i
    rw [hfx j, Module.Basis.repr_self] at h1
    rw [Matrix.one_apply, ← show _ = ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m from rfl.symm]
    refine Eq.trans h1 ?_
    rw [Finsupp.single_apply]
    simp only [eq_comm]
  let X : Matrix (Fin k₁) (Fin k₂) ↥LL'.1 := fun m j => incl hL (b₁.repr (x j) m)
  have hX : extMat hL b₁ b₂ F * X = 1 := by
    refine Matrix.ext fun i j => ?_
    have := congrArg (incl hL) (key i j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_mul] at this
    rw [Matrix.mul_apply]
    refine Eq.trans this ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  intro y hy
  refine ⟨X.mulVec y, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (incl_integral hL (hb₁.2 _ (hx j) i)) (hy j)
  · change (extMat hL b₁ b₂ F).mulVec (X.mulVec y) = y
    rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]

end GlobalTheory.BaseCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOntoStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeHomBaseChange_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  first | exact @GlobalTheory.BaseCoef.extHom_onto | exact GlobalTheory.BaseCoef.extHom_onto | (intros; apply GlobalTheory.BaseCoef.extHom_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterSetMapCoefficientFieldProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterSetMapCoefficientFieldProperties
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem mem_mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL')
    (Sig : Finset (I →* LLˣ)) (x : I →* LL'ˣ) :
    x ∈ mapSig f Sig ↔ ∃ a ∈ Sig, (Units.map (f : LL →* LL')).comp a = x := by
  classical
  unfold mapSig
  exact Finset.mem_image

theorem orbLen_map {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL')
    (I : Subgroup G) (Fr : G) (a b : I →* LLˣ) :
    Formalism.MainNotions.ElementDenominator.orbLen I Fr ((Units.map (f : LL →* LL')).comp a * ((Units.map (f : LL →* LL')).comp b)⁻¹) =
      Formalism.MainNotions.ElementDenominator.orbLen I Fr (a * b⁻¹) := by
  set φ : LLˣ →* LL'ˣ := Units.map (f : LL →* LL') with hφ
  have hinj : Function.Injective φ := by
    intro u v huv
    apply Units.ext
    have := congrArg Units.val huv
    simpa [hφ] using f.injective this
  have hcomp : φ.comp a * (φ.comp b)⁻¹ = φ.comp (a * b⁻¹) := by
    ext x
    simp
  rw [hcomp]
  unfold Formalism.MainNotions.ElementDenominator.orbLen
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, MonoidHom.comp_apply]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => hinj (h g g' hg)⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => congrArg φ (h g g' hg)⟩

theorem mapSig_props : ∀ {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL') (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)), (FrobStable I Fr Sig → FrobStable I Fr (mapSig f Sig)) ∧ Formalism.MainNotions.ElementDenominator.rPrime I Fr (mapSig f Sig) = Formalism.MainNotions.ElementDenominator.rPrime I Fr Sig ∧ (mapSig f Sig).card ≤ Sig.card ∧ (1 ∈ Sig → 1 ∈ mapSig f Sig) := by
  intro G LL LL' _ _ _ f I Fr Sig
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hS a' ha'
    obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig a').1 ha'
    obtain ⟨b, hb, hab⟩ := hS a ha
    refine ⟨(Units.map (f : LL →* LL')).comp b, (mem_mapSig f Sig _).2 ⟨b, hb, rfl⟩, ?_⟩
    intro g h hgh
    simp [hab g h hgh]
  · unfold Formalism.MainNotions.ElementDenominator.rPrime
    apply le_antisymm
    · apply Finset.sup_le
      rintro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig p).1 hpq.1
      obtain ⟨b, hb, rfl⟩ := (mem_mapSig f Sig q).1 hpq.2
      rw [orbLen_map f I Fr a b]
      exact Finset.le_sup (s := Sig ×ˢ Sig)
        (f := fun p : (↥I →* LLˣ) × (↥I →* LLˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹)) (b := (a, b))
        (Finset.mem_product.2 ⟨ha, hb⟩)
    · apply Finset.sup_le
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have := Finset.le_sup (s := mapSig f Sig ×ˢ mapSig f Sig)
        (f := fun p : (↥I →* LL'ˣ) × (↥I →* LL'ˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹))
        (b := ((Units.map (f : LL →* LL')).comp a, (Units.map (f : LL →* LL')).comp b))
        (Finset.mem_product.2 ⟨(mem_mapSig f Sig _).2 ⟨a, hab.1, rfl⟩, (mem_mapSig f Sig _).2 ⟨b, hab.2, rfl⟩⟩)
      simpa only [orbLen_map f I Fr a b] using this
  · classical
    unfold mapSig
    exact Finset.card_image_le
  · intro h1
    exact (mem_mapSig f Sig 1).2 ⟨1, h1, MonoidHom.comp_one _⟩

end GlobalTheory.BaseCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterSetMapCoefficientFieldPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterSetMapCoefficientField_properties : ∀ {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL') (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)), (FrobStable I Fr Sig → FrobStable I Fr (mapSig f Sig)) ∧ Formalism.MainNotions.ElementDenominator.rPrime I Fr (mapSig f Sig) = Formalism.MainNotions.ElementDenominator.rPrime I Fr Sig ∧ (mapSig f Sig).card ≤ Sig.card ∧ (1 ∈ Sig → 1 ∈ mapSig f Sig) := by
  first | exact @GlobalTheory.BaseCoef.mapSig_props | exact GlobalTheory.BaseCoef.mapSig_props | (intros; apply GlobalTheory.BaseCoef.mapSig_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughCharactersLatticeCoefficientExtens
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughCharactersLatticeCoefficientExtens
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.BaseCoefIner

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W : Type} [AddCommGroup W] [Module K W]

theorem extS_mono {S T : Submodule K W} (h : S ≤ T) : CJ.extS L S ≤ CJ.extS L T := by
  have := CJ.extS_inf (L := L) S T
  rw [inf_eq_left.2 h] at this
  rw [this]
  exact inf_le_right

theorem extS_iSup_le {J : Sort*} (S : J → Submodule K W) :
    CJ.extS L (⨆ j, S j) ≤ ⨆ j, CJ.extS L (S j) := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | tmul c s =>
    obtain ⟨s, hs⟩ := s
    rw [LinearMap.baseChange_tmul]
    change c ⊗ₜ[K] s ∈ _
    induction hs using Submodule.iSup_induction' with
    | mem j x hx =>
      exact Submodule.mem_iSup_of_mem j ⟨c ⊗ₜ[K] (⟨x, hx⟩ : S j), by simp [LinearMap.baseChange_tmul]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact Submodule.add_mem _ hx hy

end Ext

section Main

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']

section Tower

variable [Algebra LL LL'] [IsScalarTower Qp LL LL'] {k : ℕ}

theorem comm_act_smul (A : Matrix (Fin k) (Fin k) LL) (β : B →ₗ[Qp] B) (r : LL)
    (x : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] B)) :
    CJ.EE (Qp := Qp) (LL' := LL') B ((PI.CoefExt.actT A β - r • LinearMap.id).baseChange LL' x)
      = (PI.CoefExt.actT (A.map (algebraMap LL LL')) β - (algebraMap LL LL' r) • LinearMap.id :
        (Fin k → LL') ⊗[Qp] B →ₗ[LL'] (Fin k → LL') ⊗[Qp] B) (CJ.EE B x) := by
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.sub_apply, map_sub,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.id_apply, ← algebraMap_smul LL' r x, map_smul]
  congr 1
  exact PI.CoefExt.coefEquiv_comm A β x

theorem dpcris_ext (M : G →* Matrix (Fin k) (Fin k) LL) :
    (CJ.extS LL' (PC.Dpcris (CJ.rep M))).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Dpcris (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) := by
  unfold PotCrysData.Dpcris Dcris
  rw [CJ.extS_iInf]
  simp only [CJ.extS_ker]
  exact CJ.map_iInf_ker _ _ _ (fun g x => CJ.comm_act (BdR := B) (M g) _ x)

theorem eig_ext (M : G →* Matrix (Fin k) (Fin k) LL) (I : Subgroup G) (a : I →* LLˣ) :
    (CJ.extS LL' (PC.Eig (CJ.rep M) I a)).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Eig (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) I
          ((Units.map (algebraMap LL LL' : LL →* LL')).comp a) := by
  unfold PotCrysData.Eig
  rw [CJ.extS_inf, CJ.map_inf_equiv, dpcris_ext, CJ.extS_iInf]
  simp only [CJ.extS_ker]
  congr 1
  exact CJ.map_iInf_ker _ _ _ (fun g x => comm_act_smul (M g) _ _ x)

end Tower

theorem orderOf_comp {I : Type} [Group I] (f : LL →+* LL') (a : I →* LLˣ) :
    orderOf ((Units.map (f : LL →* LL')).comp a) = orderOf a := by
  refine orderOf_eq_orderOf_iff.2 fun n => ?_
  simp only [MonoidHom.ext_iff, MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply]
  refine forall_congr' fun g => ?_
  rw [← map_pow]
  exact map_eq_one_iff _ (Units.map_injective f.injective)

theorem inertiaThrough_mat (f : LL →ₐ[Qp] LL') {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough (CJ.rep M) Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
      (mapSig f.toRingHom Sig) := by
  classical
  let _ : Algebra LL LL' := f.toRingHom.toAlgebra
  have _ : IsScalarTower Qp LL LL' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hf : IsScalarTower.toAlgHom Qp LL LL' = f := AlgHom.ext fun _ => rfl
  have hm : ∀ c, c ∈ mapSig f.toRingHom Sig ↔
      ∃ a ∈ Sig, (Units.map (f.toRingHom : LL →* LL')).comp a = c := fun c => by
    unfold mapSig
    convert Finset.mem_image
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨fun c hc g hg => ?_, fun c hc => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [MonoidHom.comp_apply, h1 a ha g hg, map_one]
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [orderOf_comp]
    exact h2 a ha
  · have hD := dpcris_ext (LL' := LL') PC M
    rw [hf] at hD
    refine hD.symm.le.trans (Submodule.map_le_iff_le_comap.2 ?_)
    refine (extS_mono h3.le).trans ?_
    refine (extS_iSup_le _).trans (iSup_le fun a => (extS_iSup_le _).trans (iSup_le fun ha => ?_))
    refine Submodule.map_le_iff_le_comap.1 ?_
    have hE := eig_ext (LL' := LL') PC M PC.Iner a
    rw [hf] at hE
    refine hE.le.trans ?_
    exact le_iSup₂_of_le ((Units.map (f.toRingHom : LL →* LL')).comp a) ((hm _).2 ⟨a, ha, rfl⟩) le_rfl
  · exact iSup₂_le fun _ _ => inf_le_left

theorem inertiaThrough_basis (f : LL →ₐ[Qp] LL') {k : ℕ}
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (b : Module.Basis (Fin k) LL V)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough ρ Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
          ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)))
      (mapSig f.toRingHom Sig) := by
  refine inertiaThrough_mat _ f _ Sig ?_
  refine (GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ b.equivFun.symm ?_).2 Sig hS
  intro g v
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  change (LinearMap.toMatrix b b (ρ g)).mulVec v = _
  have := LinearMap.toMatrix_mulVec_repr b b (ρ g) (b.equivFun.symm v)
  rw [← Module.Basis.equivFun_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at this
  exact this

end Main


set_option maxHeartbeats 1000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)), (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → (pc Pl h hN hF hS).InertiaThrough (extLat hL T b hb).ρ (mapSig (incl hL).toRingHom Sig) := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb Sig hI
  exact inertiaThrough_basis (pc Pl h hN hF hS) (incl hL) T.ρ b Sig hI

end GlobalTheory.BaseCoefIner
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughCharactersLatticeCoefficientExtensStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)), (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → (pc Pl h hN hF hS).InertiaThrough (extLat hL T b hb).ρ (mapSig (incl hL).toRingHom Sig) := by
  first | exact @GlobalTheory.BaseCoefIner.main | exact GlobalTheory.BaseCoefIner.main | (intros; apply GlobalTheory.BaseCoefIner.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtension
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem bot_emb_factor {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (hL : LL.1 ≤ LL'.1)
    (τ' : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL'.1) :
    ∃ τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1, τ' = (incl hL).comp τ := by
  refine ⟨IntermediateField.inclusion (bot_le : (⊥ : IntermediateField ℚ_[l] _) ≤ LL.1), ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 (show x.1 ∈ (⊥ : IntermediateField ℚ_[l] _) from x.2)
  have hx : x = algebraMap ℚ_[l] _ c := Subtype.ext hc.symm
  rw [hx, AlgHom.commutes, AlgHom.commutes]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jumpsInV_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb U H τ' a ha
  obtain ⟨τ, rfl⟩ := bot_emb_factor hL τ'
  refine H τ a ?_
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr (pc Pl h hN hF hS).PD b.equivFun
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf_equiv b T.ρ) τ a
  have e2 := Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general (pc Pl h hN hF hS).PD (incl hL)
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf b T.ρ) τ a
  exact e1.2 (e2.2 ha)

end GlobalTheory.BaseCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtensionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  first | exact @GlobalTheory.BaseCoef.jumpsInV_extLat | exact GlobalTheory.BaseCoef.jumpsInV_extLat | (intros; apply GlobalTheory.BaseCoef.jumpsInV_extLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtens
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtens
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Algebra Qp LL] [Field LL'] [Algebra Qp LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem isCrys_transport {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have key := PI.CoefExt.finrank_iInf_ker_equiv
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)) (actVB PD ρ) (actVB PD ρ') (fun g x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul v c => simp [actVB, he])
  unfold IsCrys at h ⊢
  rw [← e.finrank_eq, ← h]
  exact key

theorem isCrys_matrix_ext (f : LL →ₐ[Qp] LL') {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (h : IsCrys PD ρ) :
    IsCrys PD (CJ.rep ((f.mapMatrix : Matrix (Fin k) (Fin k) LL →ₐ[Qp]
      Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ))) := by
  letI : TopologicalSpace G := ⊥
  have h1 : IsCrys PD (CJ.rep ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)) := by
    refine isCrys_transport PD b.equivFun (fun g v => ?_) h
    change _ = (LinearMap.toMatrix b b (ρ g)).mulVec (b.repr v)
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  exact PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange PD f _ h1

end Gen

theorem isPotCrys_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb hT
  exact isCrys_matrix_ext (pc Pl h hN hF hS).PD' (incl hL) b ((pc Pl h hN hF hS).resH T.ρ) hT

end GlobalTheory.BaseCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtensStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  first | exact @GlobalTheory.BaseCoef.isPotCrys_extLat | exact GlobalTheory.BaseCoef.isPotCrys_extLat | (intros; apply GlobalTheory.BaseCoef.isPotCrys_extLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientField
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.CoefDescent

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {E E' : Type} [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
    {O O' : Type} [CommRing O] [Algebra O E] [CommRing O'] [Algebra O' E']

theorem blochKatoCocycle_comp_equivariant_map
    {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
    [Module O V] [IsScalarTower O E V] {ρ : Representation E G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul E V]
    {V' : Type} [AddCommGroup V'] [Module E' V'] [Module Qp V'] [IsScalarTower Qp E' V']
    [Module O' V'] [IsScalarTower O' E' V'] {ρ' : Representation E' G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul E' V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O') ρ') (φ : V →ₗ[Qp] V')
    (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (hc : Continuous φ) (hT : ∀ x ∈ L.T, φ x ∈ L'.T)
    (c : G → V) (h : c ∈ latticeFiniteCocycles PD L) : (fun g => φ (c g)) ∈ latticeFiniteCocycles PD L' := by
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, -, x, hx⟩ := h
  have hz : (fun g => φ (c g)) ∈ continuousCocycles ρ' := by
    refine ⟨hc.comp hc1, fun g h => ?_⟩
    change φ (c (g * h)) = φ (c g) + ρ' g (φ (c h))
    rw [hc2, map_add (f := _), he]
  refine ⟨⟨hz, fun g _ => hT _ (hc3 g (Set.mem_univ g))⟩, hz, LinearMap.rTensor B φ x, fun g => ?_⟩
  have key : ∀ y : V ⊗[Qp] B, LinearMap.rTensor B φ (actVB PD ρ g y) =
      actVB PD ρ' g (LinearMap.rTensor B φ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← key, ← map_sub, ← hx, LinearMap.rTensor_tmul]

theorem liftF_of_retract
    {V₁ : Type} [AddCommGroup V₁] [Module E V₁] [Module Qp V₁] [IsScalarTower Qp E V₁]
    [Module O V₁] [IsScalarTower O E V₁] {ρ₁ : Representation E G V₁}
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul E V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module E V₂] [Module Qp V₂] [IsScalarTower Qp E V₂]
    [Module O V₂] [IsScalarTower O E V₂] {ρ₂ : Representation E G V₂}
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul E V₂]
    {W₁ : Type} [AddCommGroup W₁] [Module E' W₁] [Module Qp W₁] [IsScalarTower Qp E' W₁]
    [Module O' W₁] [IsScalarTower O' E' W₁] {σ₁ : Representation E' G W₁}
    [TopologicalSpace W₁] [ContinuousAdd W₁] [ContinuousConstSMul E' W₁]
    {W₂ : Type} [AddCommGroup W₂] [Module E' W₂] [Module Qp W₂] [IsScalarTower Qp E' W₂]
    [Module O' W₂] [IsScalarTower O' E' W₂] {σ₂ : Representation E' G W₂}
    [TopologicalSpace W₂] [ContinuousAdd W₂] [ContinuousConstSMul E' W₂]
    {L₁ : Lattice (O := O) ρ₁} {L₂ : Lattice (O := O) ρ₂}
    {M₁ : Lattice (O := O') σ₁} {M₂ : Lattice (O := O') σ₂}
    (F : LatHom L₁ L₂) (F' : LatHom M₁ M₂)
    (ι : V₂ →ₗ[Qp] W₂) (R₁ : W₁ →ₗ[Qp] V₁) (R₂ : W₂ →ₗ[Qp] V₂)
    (ιe : ∀ g x, ι (ρ₂ g x) = σ₂ g (ι x)) (ιc : Continuous ι) (ιT : ∀ x ∈ L₂.T, ι x ∈ M₂.T)
    (R₁e : ∀ g x, R₁ (σ₁ g x) = ρ₁ g (R₁ x)) (R₁c : Continuous R₁) (R₁T : ∀ x ∈ M₁.T, R₁ x ∈ L₁.T)
    (R₂e : ∀ g x, R₂ (σ₂ g x) = ρ₂ g (R₂ x)) (R₂T : ∀ x ∈ M₂.T, R₂ x ∈ L₂.T)
    (hret : ∀ x, R₂ (ι x) = x) (hF : ∀ x, R₂ (F'.f x) = F.f (R₁ x))
    (e : ℕ) (h : F'.LiftF PD e) : F.LiftF PD e := by
  intro c hc
  have h1 := h _ (blochKatoCocycle_comp_equivariant_map PD L₂ M₂ ι ιe ιc ιT c hc)
  obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨y, hy, rfl⟩, hsum⟩ := Submodule.mem_sup.1 h1
  refine Submodule.mem_sup.2 ⟨_, ⟨_, blochKatoCocycle_comp_equivariant_map PD M₁ L₁ R₁ R₁e R₁c R₁T d hd, rfl⟩, _,
    ⟨R₂ y, R₂T y hy, rfl⟩, ?_⟩
  funext g
  have h2 := congrArg R₂ (congrFun hsum g)
  change R₂ (F'.f (d g) + (σ₂ g y - y)) = R₂ (((PD.p : O') ^ e) • ι (c g)) at h2
  change F.f (R₁ (d g)) + (ρ₂ g (R₂ y) - R₂ y) = ((PD.p : O) ^ e) • c g
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, hret, map_add (f := _), map_sub, hF, R₂e] at h2
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, h2]

end General

section Maps
variable {Qp E E' : Type} [Field Qp] [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
  {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module Qp V'] [IsScalarTower Qp E V']
  {k k' : ℕ}

def emb (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) : V →ₗ[Qp] (Fin k → E') :=
  LinearMap.pi fun i => j.toLinearMap ∘ₗ (b.coord i).restrictScalars Qp

theorem emb_apply (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (v : V) (i : Fin k) :
    emb j b v i = j (b.repr v i) := rfl

def ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) : (Fin k → E') →ₗ[Qp] V :=
  (b.equivFun.symm.toLinearMap.restrictScalars Qp) ∘ₗ LinearMap.compLeft r (Fin k)

theorem ret_apply (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') :
    ret r b w = ∑ i, r (w i) • b i := by
  simp [ret, Module.Basis.equivFun_symm_apply]

theorem repr_ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') (i : Fin k) :
    b.repr (ret r b w) i = r (w i) := by
  rw [ret_apply]; simp [Finsupp.single_apply]

theorem ret_emb (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x) (h1 : r 1 = 1)
    (b : Module.Basis (Fin k) E V) (v : V) : ret r b (emb j b v) = v := by
  refine b.ext_elem fun i => ?_
  have := hr (b.repr v i) 1
  rw [mul_one, h1, mul_one] at this
  rw [repr_ret, emb_apply, this]

theorem emb_map (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (v : V) :
    emb j b' (f v) = ((LinearMap.toMatrix b b' f).map j).mulVec (emb j b v) := by
  funext i
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f v) i
  rw [emb_apply, ← this]
  simp [Matrix.mulVec, dotProduct, emb_apply]

theorem ret_map (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x)
    (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (w : Fin k → E') :
    ret r b' (((LinearMap.toMatrix b b' f).map j).mulVec w) = f (ret r b w) := by
  refine b'.ext_elem fun i => ?_
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f (ret r b w)) i
  rw [repr_ret, ← this]
  simp [Matrix.mulVec, dotProduct, repr_ret, hr]

end Maps


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem liftF_descends : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {K₀ K B BdR : Type} [Field K₀] [Field K] [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B] [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR] (PD : PeriodData G ℚ_[l] K₀ K B BdR) (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1), (∀ a x, r (incl hL a * x) = a * r x) → r 1 = 1 → (∀ x ∈ OL LL', r x ∈ OL LL) → Continuous r → ∀ e : ℕ, (extHom hL hb₁ hb₂ F).LiftF PD e → F.LiftF PD e := by
  intro l _ G _ _ K₀ K B BdR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PD LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr h1
    hint hrc e h
  have hincl : Continuous (incl hL) := continuous_subtype_val.subtype_mk _
  have retT : ∀ {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ} {b : Module.Basis (Fin k) ↥LL.1 T.V},
      IsLatBasis T b → ∀ x ∈ intVec LL' k, ret r b x ∈ T.L.T := by
    intro T k b hb x hx
    rw [ret_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := T.L.T.smul_mem (⟨r (x i), hint _ (hx i)⟩ : ↥(OL LL)) (hb.1 i)
    rwa [← algebraMap_smul ↥LL.1] at this
  refine liftF_of_retract PD F (extHom hL hb₁ hb₂ F) (emb (incl hL) b₂) (ret r b₁) (ret r b₂)
    (fun g x => emb_map (incl hL) b₂ b₂ (T₂.ρ g) x) ?_ ?_
    (fun g x => ret_map (incl hL) r hr b₁ b₁ (T₁.ρ g) x) ?_ (retT hb₁)
    (fun g x => ret_map (incl hL) r hr b₂ b₂ (T₂.ρ g) x) (retT hb₂)
    (ret_emb (incl hL) r hr h1 b₂) (fun x => ret_map (incl hL) r hr b₁ b₂ F.f x) e h
  · exact continuous_pi fun i => hincl.comp (IsModuleTopology.continuous_of_linearMap (b₂.coord i))
  · intro x hx i
    exact incl_integral hL (hb₂.2 x hx i)
  · have hc : Continuous (b₁.equivFun.symm.toLinearMap) := IsModuleTopology.continuous_of_linearMap _
    exact hc.comp (continuous_pi fun i => hrc.comp (continuous_apply i))

end GlobalTheory.CoefDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientFieldStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftable_descends_from_larger_coefficientField : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {K₀ K B BdR : Type} [Field K₀] [Field K] [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B] [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR] (PD : PeriodData G ℚ_[l] K₀ K B BdR) (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1), (∀ a x, r (incl hL a * x) = a * r x) → r 1 = 1 → (∀ x ∈ OL LL', r x ∈ OL LL) → Continuous r → ∀ e : ℕ, (extHom hL hb₁ hb₂ F).LiftF PD e → F.LiftF PD e := by
  first | exact @GlobalTheory.CoefDescent.liftF_descends | exact GlobalTheory.CoefDescent.liftF_descends | (intros; apply GlobalTheory.CoefDescent.liftF_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLatticeBasisLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLatticeBasisLocal
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem lattice_basis_exists : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V), IsLatBasis T b := by
  intro l _ G _ _ LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI hfr : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI := T.L.free
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let e0 := Module.Free.chooseBasis ↥(OL LL) ↥T.L.T
  let e := e0.reindex (Fintype.equivFin _)
  let v : Fin (Fintype.card (Module.Free.ChooseBasisIndex ↥(OL LL) ↥T.L.T)) → T.V := fun i => (e i : T.V)
  have hliO : LinearIndependent ↥(OL LL) v := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ↥LL.1 v := (LinearIndependent.iff_fractionRing ↥(OL LL) ↥LL.1).1 hliO

  have hexp : ∀ (x : T.V) (hx : x ∈ T.L.T), x = ∑ i, (((e.repr ⟨x, hx⟩ i : ↥(OL LL)) : ↥LL.1)) • v i := by
    intro x hx
    have h1 := e.sum_repr ⟨x, hx⟩
    have h2 := congrArg (fun y : ↥T.L.T => (y : T.V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ↥LL.1 (e.repr ⟨x, hx⟩ i) (v i)).symm
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range v) := by
    rw [← T.L.span]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨_, Module.Basis.mk hli hsp, fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (e i).2
  · have h3 : (Module.Basis.mk hli hsp).repr x = fun j => (((e.repr ⟨x, hx⟩ j : ↥(OL LL)) : ↥LL.1)) := by
      conv_lhs => rw [hexp x hx]
      simp_rw [← Module.Basis.mk_apply hli hsp]
      exact (Module.Basis.mk hli hsp).repr_sum_self _
    rw [h3]
    exact (e.repr ⟨x, hx⟩ i).2

end GlobalTheory.BaseCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLatticeBasisLocalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralLatticeBasisLocal : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V), IsLatBasis T b := by
  first | exact @GlobalTheory.BaseCoef.lattice_basis_exists | exact GlobalTheory.BaseCoef.lattice_basis_exists | (intros; apply GlobalTheory.BaseCoef.lattice_basis_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem thmT_descend : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  intro l _ Pl K' h hN hF hS LL LL' hL C hT
  intro T₁ T₂ F N η H U Sig Fr hp1 hp2 hon hFr hFS h1 hcard h2N hI1 hI2 hU h0U hUc hη hηH hJ1 hJ2 hl
  obtain ⟨k₁, b₁, hb₁⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₁
  obtain ⟨k₂, b₂, hb₂⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₂
  obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.exists_integral_retraction_finiteExtension_ql l LL LL' hL
  obtain ⟨hFS', hrP, hcard', h1'⟩ := GlobalTheory.T.characterSetMapCoefficientField_properties (incl hL).toRingHom (pc Pl h hN hF hS).Iner Fr Sig
  have key := hT (extLat hL T₁ b₁ hb₁) (extLat hL T₂ b₂ hb₂) (extHom hL hb₁ hb₂ F) N η H U
    (mapSig (incl hL).toRingHom Sig) Fr
    (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ hp1) (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ hp2)
    (GlobalTheory.T.latticeHomBaseChange_onto l LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hon) hFr (hFS' hFS) (h1' h1) (hcard'.trans hcard) h2N
    (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ Sig hI1) (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ Sig hI2)
    hU h0U hUc hη hηH
    (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ _ hJ1) (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ _ hJ2) hl
  rw [hrP] at key
  exact ⟨key.1, GlobalTheory.T.liftable_descends_from_larger_coefficientField l _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr1 hr2 hr3 (by haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2; exact LinearMap.continuous_of_finiteDimensional r) _ key.2⟩

end GlobalTheory.BaseCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficientsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremT_descend_smaller_coefficients : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  first | exact @GlobalTheory.BaseCoef.thmT_descend | exact GlobalTheory.BaseCoef.thmT_descend | (intros; apply GlobalTheory.BaseCoef.thmT_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescen
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescen
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoeff

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l,
    (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  intro l _ a e _ h1 h2 LL
  refine ⟨?_, fun hU => ?_⟩
  · have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have : FiniteDimensional ℚ_[l] ↥(Kunr l a) := (unrExt l a).2
    exact ⟨⟨LL.1 ⊔ Kunr l a, inferInstance⟩, le_sup_left, ⟨le_sup_right⟩⟩
  · obtain ⟨_, ω, hω, -, -⟩ := exists_gen l a
    have hlt := one_lt_pow_l l a
    have hmem : ω ∈ LL.1 := HasUnr.le (a := a) (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
      rw [← Nat.sub_add_cancel hlt.le, pow_succ, hω.pow_eq_one, one_mul]))
    have he : e = l ^ a - 1 := by omega
    exact
      { succ_eq := h1
        not_dvd := h2
        finite := LL.2
        prim := ⟨⟨ω, hmem⟩, he ▸ (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val)
          Subtype.val_injective).1 hω⟩ }

end GlobalTheory.TameCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescenStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l, (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  first | exact @GlobalTheory.TameCoeff.main | exact GlobalTheory.TameCoeff.main | (intros; apply GlobalTheory.TameCoeff.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaine
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTClosing

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_of_le {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  intro hBS hFB C hC D HW F _ l _ K' h hN hF hS LL
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  obtain ⟨a, ha⟩ : ∃ a, a = (l - 1).factorial := ⟨_, rfl⟩
  haveI : NeZero a := ⟨by rw [ha]; exact Nat.factorial_ne_zero _⟩
  have hla : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (by omega)
  obtain ⟨e, he⟩ : ∃ e, e + 1 = l ^ a := ⟨l ^ a - 1, by omega⟩
  haveI : NeZero e := ⟨by
    intro h0
    rw [h0, zero_add] at he
    omega⟩
  have hnd : ¬ l ∣ a := by
    rw [ha, hlp.dvd_factorial]
    omega
  obtain ⟨⟨LL', hle, hUnr⟩, -⟩ := GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL
  haveI := hUnr
  haveI : TameDescentExponentData ↥LL'.1 l e a := (GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL').2 hUnr
  refine GlobalTheory.T.theoremT_descend_smaller_coefficients l (D.loc l) K' h hN hF hS LL LL' hle C ?_
  have ϖ : PiSys l e := Classical.arbitrary _
  have hStd : IsStd (D.loc l) (D.locA l) := IsStd.of_tied (D.locT l)
  intro T₁ T₂ g N η H U Sig Fr hP1 hP2 hOnto hFr hFS h1 hcard h2N hIT1 hIT2 hUr hU0 hUc hη hηH hJ1 hJ2 hl
  have hp : (pc (D.loc l) h hN hF hS).PD.p = l := (D.loc l).PD_p _
  have hlarge : 40 * (H * N ^ 2 + N ^ 3) < l := lt_of_le_of_lt (Nat.mul_le_mul_right _ hC) hl
  have hNl : N < l := by
    have : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
    omega
  have hcop : ∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l := fun χ hχ => by
    have := hIT1.2.1 χ hχ
    rwa [hp] at this
  obtain ⟨Sig', hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd ha
    K' h hN hF hS Sig Fr N hFr hFS h1 hcard hNl hIT1.1 hcop
  obtain ⟨c1, t1⟩ := hS5 T₁ hP1 hIT1
  obtain ⟨c2, t2⟩ := hS5 T₂ hP2 hIT2
  have hnum : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig' U :=
    ⟨hS1, hS2, hS3, h2N, hUr, hU0, hUc, hη, hηH, hlarge⟩
  have hcore := GlobalTheory.T.lift_surjection_good_crystalline_lattices hBS hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd N η H Sig' U hnum T₁ T₂ g hOnto
    ⟨c1, t1, hJ1⟩ ⟨c2, t2, hJ2⟩
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hlp (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) he Sig' N hS1 hS2 hS3 h2N
  rw [hS4] at hcore horb
  refine ⟨horb.2.1, ?_⟩
  exact liftF_of_le _ g hcore (Nat.mul_le_mul_right _ (by omega))

end GlobalTheory.TheoremTClosing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaineStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingStep_theoremT_of_bhattScholze_fontaine : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  first | exact @GlobalTheory.TheoremTClosing.main | exact GlobalTheory.TheoremTClosing.main | (intros; apply GlobalTheory.TheoremTClosing.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAll
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAll
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmAllRecords

section ArtinSchreierWitt
open Polynomial
open scoped NNReal

private theorem exists_root_OC (l : ℕ) [Fact l.Prime] (c b : OC l) :
    ∃ z : OC l, z ^ l - c * z - b = 0 := by
  classical
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  let p : (OC l)[X] := X ^ l - (C c * X + C b)
  have hdeg : (C c * X + C b).degree < (X ^ l : (OC l)[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast (show 1 < l by omega))
  have hmon : p.Monic := (monic_X_pow l).sub_of_left hdeg
  have hnat : p.natDegree = l := by
    apply natDegree_eq_of_degree_eq_some
    rw [degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]
  let q : ℂ_[l][X] := p.map (algebraMap (OC l) ℂ_[l])
  have hq : q.degree ≠ 0 := by
    rw [degree_eq_natDegree (hmon.map _).ne_zero, (hmon.natDegree_map _), hnat]
    exact_mod_cast (show l ≠ 0 by omega)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hq
  have hx' : eval₂ (algebraMap (OC l) ℂ_[l]) x p = 0 := by
    rw [← eval_map]
    exact hx
  have hint : IsIntegral (OC l) x := ⟨p, hmon, hx'⟩
  have hmem : x ∈ PadicComplexInt l := (PadicComplexInt.integers l).mem_of_integral hint
  refine ⟨⟨x, hmem⟩, ?_⟩
  apply Subtype.ext
  have h2 : eval₂ (algebraMap (OC l) ℂ_[l]) x p = x ^ l - ((c : ℂ_[l]) * x + (b : ℂ_[l])) := by
    simp only [p, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C]
    rfl
  rw [h2] at hx'
  show x ^ l - (c : ℂ_[l]) * x - (b : ℂ_[l]) = 0
  rw [sub_sub]
  exact hx'

private theorem rootModP_holds : PI.ArtSch.RootModP := by
  intro l _ c b
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, hz⟩ := exists_root_OC l c' b'
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [← map_pow, ← map_mul, ← map_sub, ← map_sub, hz, map_zero]

private theorem coeff_zero_nilpotent {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*}
    [CommRing O] [Algebra O K] (hv : v.Integers O) {p : ℕ} [Fact p.Prime]
    [Fact (¬ IsUnit (p : O))] (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ N : ℕ, PreTilt.coeff 0 e ^ N = 0 := by
  by_cases h0 : PreTilt.coeff 0 e = 0
  · exact ⟨1, by rw [pow_one, h0]⟩
  have hval : PreTilt.val K v O hv p e = ModP.preVal K v O p (PreTilt.coeff 0 e) := by
    change PreTilt.valAux K v O p e = _
    rw [PreTilt.valAux_eq hv h0, pow_zero, pow_one]
  obtain ⟨E, hE⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff 0 e)
  have hE0 : (Ideal.Quotient.mk (Ideal.span {(p : O)}) E : ModP O p) ≠ 0 := by
    rw [hE]; exact h0
  have hvE : v (algebraMap O K E) < 1 := by
    rw [← ModP.preVal_mk hv hE0, hE, ← hval]; exact he
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one hp hvE
  refine ⟨N, ?_⟩
  have hEN : (Ideal.Quotient.mk (Ideal.span {(p : O)}) (E ^ N) : ModP O p) = 0 := by
    by_contra h
    have h1 := (ModP.v_p_lt_val hv).2 h
    rw [map_pow, v.map_pow] at h1
    exact lt_asymm h1 hN
  rw [← hE, ← map_pow]; exact hEN

private theorem tiltSmall : PI.ArtSch.TiltSmall := by
  intro l _ e he
  have hp : 0 < (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) := by
    rw [PadicComplex.valuation_p l]
    have : (0 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  obtain ⟨N, hN⟩ := coeff_zero_nilpotent (PadicComplexInt.integers l) hp e he
  exact ⟨PI.UnitaryGroupMassFormula.ASSmall.solPerf (R := ModP (OC l) l) (p := l) e hN,
    PI.UnitaryGroupMassFormula.ASSmall.solPerf_spec (R := ModP (OC l) l) (p := l) e hN⟩

end ArtinSchreierWitt

theorem _root_.GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt :
    Formalism.MainNotions.ElementDenominator.ArtinSchreierWittOnto := fun l _ x =>
  PI.ArtSch.main_of PI.ArtSch.WittLiftWork.wittLift
    (PI.ArtSch.Glue.tiltGlue rootModP_holds PI.ArtSch.tiltDiv_of_general tiltSmall) l x

theorem localLifting_admittedHypotheses_all_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm2 D HW F := by
  intro hBK hTD hEC D HW F _
  exact ⟨GlobalTheory.T.restriction_corestriction_H1f D HW F, GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D,
    GlobalTheory.Per.StrictAdm.strict_adm D, GlobalTheory.T.crystalline_restrict_finite_extension_jumps D, GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt⟩

end GlobalTheory.AdmAllRecords
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAllStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_admittedHypotheses_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm2 D HW F := by
  first | exact @GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | exact GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | (intros; apply GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeForty
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.InertiaEigenvalues.theoremT_all_records :
    GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal →
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  intro hBS hFon hBK hTD hEC D HW F Cm C hC
  exact GlobalTheory.T.liftingStep_theoremT_of_bhattScholze_fontaine (GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices hBS) hFon C hC D HW F (GlobalTheory.T.localLifting_admittedHypotheses_all hBK hTD hEC D HW F Cm)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeFortyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  first | exact @GlobalTheory.InertiaEigenvalues.theoremT_all_records | exact GlobalTheory.InertiaEigenvalues.theoremT_all_records | (intros; apply GlobalTheory.InertiaEigenvalues.theoremT_all_records <;> assumption)
end

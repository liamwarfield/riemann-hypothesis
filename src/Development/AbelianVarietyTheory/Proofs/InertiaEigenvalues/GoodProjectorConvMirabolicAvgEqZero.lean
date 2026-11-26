module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvolutionSingleFactorGoodProjectorEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvolutionSingleFactorGoodProjectorEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem conv_single_prod_eq_zero {ι : Type} [Fintype ι] {Γ : ι → Type} [∀ i, Group (Γ i)]
    [∀ i, Finite (Γ i)] (G : Type) [Group G] [Fintype G] (eR : G ≃* (∀ i, Γ i)) (i0 : ι)
    (M : MonoidAlgebra ℂ (Γ i0)) (E : ∀ i, MonoidAlgebra ℂ (Γ i)) (hM : M * E i0 = 0) (x : G) :
    ∑ y : G, (open Classical in if ∀ i, i ≠ i0 → eR y i = 1 then M.coeff (eR y i0) else 0) *
      ∏ i, (E i).coeff (eR (y⁻¹ * x) i) = 0 := by
  classical
  haveI : Fintype (Γ i0) := Fintype.ofFinite _
  have hinj : Function.Injective (fun z : Γ i0 => eR.symm (Pi.mulSingle i0 z)) :=
    eR.symm.injective.comp (Pi.mulSingle_injective i0)
  rw [← Fintype.sum_of_injective (fun z : Γ i0 => eR.symm (Pi.mulSingle i0 z)) hinj
    (fun z => (M.coeff z * (E i0).coeff (z⁻¹ * eR x i0)) *
      ∏ i ∈ Finset.univ.erase i0, (E i).coeff (eR x i))]
  · rw [← Finset.sum_mul]
    have h := MonoidAlgebra.coeff_mul_apply_left M (E i0) (eR x i0)
    rw [hM, Finsupp.sum_fintype _ _ (by simp)] at h
    rw [← h]; simp
  · intro y hy
    rw [if_neg, zero_mul]
    intro h
    apply hy
    refine ⟨eR y i0, ?_⟩
    simp only
    rw [MulEquiv.symm_apply_eq]
    funext i
    by_cases hi : i = i0
    · subst hi; simp
    · rw [Pi.mulSingle_eq_of_ne hi, h i hi]
  · intro z
    rw [if_pos, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), mul_assoc]
    · congr 1
      · simp
      · congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          have hi' := Finset.ne_of_mem_erase hi
          simp [Pi.mulSingle_eq_of_ne hi']
    · intro i hi
      simp [Pi.mulSingle_eq_of_ne hi]

theorem conv_single_goodProj_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (eR : G ≃* G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k),
    haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    ∀ M : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))),
    (∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) →
      M * D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf (a kv0)) = 0) → ∀ x : G,
    ∑ y : G, (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then M.coeff (eR y kv0) else 0) *
      D.ntypes.e0.coeff (eR (y⁻¹ * x)) = 0 := by
  intro D G _ _ eR kv0 M hM x
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))) :=
    Fintype.ofFinite _
  have he : ∀ g : G0g D.nd, D.ntypes.e0.coeff g =
      ∑ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0) := by
    intro g
    rw [← finsum_eq_sum_of_fintype]
    rfl
  simp only [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with ha
  · haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    have := conv_single_prod_eq_zero (Γ := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      G eR kv0 M (fun kv => D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) (hM a ha) x
    convert this
  · simp

end GlobalTheory.DownLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvolutionSingleFactorGoodProjectorEqZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (eR : G ≃* G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k),
    haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    ∀ M : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))),
    (∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) →
      M * D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf (a kv0)) = 0) → ∀ x : G,
    ∑ y : G, (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then M.coeff (eR y kv0) else 0) *
      D.ntypes.e0.coeff (eR (y⁻¹ * x)) = 0 := by
  first | exact @GlobalTheory.DownLift.conv_single_goodProj_eq_zero | exact GlobalTheory.DownLift.conv_single_goodProj_eq_zero | (intros; apply GlobalTheory.DownLift.conv_single_goodProj_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicAverageEqCoeffSinglePlaceElement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicAverageEqCoeffSinglePlaceElement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.MirAvg

theorem bc_ringEquiv_eq_one_iff {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Formalism.UG.bc (e : K →+* K') h = 1 ↔ h = 1 := by
  refine ⟨fun H => ?_, fun H => by rw [H, map_one]⟩
  ext i j
  have := congrArg (fun u : GL (Fin r) K' => (u : Matrix (Fin r) (Fin r) K') i j) H
  apply e.injective
  have h1 : ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := rfl
  simp only [h1] at this
  rw [this]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem bc_ringEquiv_mulVec {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K)
    (x : Fin r → K) :
    ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K').mulVec (fun j => e (x j)) =
      fun j => e ((h : Matrix (Fin r) (Fin r) K).mulVec x j) := by
  funext j
  have h1 : ∀ i j, ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := fun _ _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, h1, map_sum, map_mul]

theorem det_bc_ringEquiv {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Matrix.GeneralLinearGroup.det (Formalism.UG.bc (e : K →+* K') h) =
      Units.map (e : K →* K') (Matrix.GeneralLinearGroup.det h) := by
  ext
  exact ((e : K →+* K').map_det (h : Matrix (Fin r) (Fin r) K)).symm

theorem mirSet_iff_bc {g : ℕ} [Fact g.Prime] {r : ℕ} {K' : Type} [CommRing K'] (e : ZMod g ≃+* K')
    (h : GL (Fin r) (ZMod g)) (a : Fin r → K') (b : Bool) :
    (if b then ∀ x, ∃ c : K', ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x - x = c • a
      else ∀ x, a ⬝ᵥ x = 0 → ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x = x) ↔ mirSet (fun j => e.symm (a j)) b h := by
  have hs : Function.Surjective (fun (x : Fin r → ZMod g) j => e (x j)) :=
    fun x => ⟨fun j => e.symm (x j), by funext j; simp⟩
  cases b with
  | true =>
    simp only [mirSet, if_true]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec, e.surjective.exists]
    refine exists_congr fun c => ?_
    simp only [funext_iff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun j => ?_
    rw [← e.injective.eq_iff (a := _ - _), map_sub, map_mul, e.apply_symm_apply]
  | false =>
    simp only [mirSet, Bool.false_eq_true, if_false]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec]
    refine imp_congr ?_ ?_
    · rw [← e.injective.eq_iff (b := 0), map_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_sum, map_mul, e.apply_symm_apply]
    · simp only [funext_iff, e.injective.eq_iff]

theorem mirC_eq_coeff_mirEl : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R eR plg iso hrec i kv0 a b ε y
  haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
  have h1 : (∀ PP', PP' ≠ plg kv0 → R.eG y PP' = 1) ↔ ∀ kv, kv ≠ kv0 → eR y kv = 1 := by
    rw [plg.surjective.forall]
    refine forall_congr' fun kv => imp_congr plg.injective.ne_iff ?_
    rw [hrec]
    exact bc_ringEquiv_eq_one_iff _ _
  have h2 := mirSet_iff_bc (iso kv0) (eR y kv0) a b
  have h3 := det_bc_ringEquiv (iso kv0) (eR y kv0)
  rw [← hrec] at h2 h3
  rw [mirEl_coeff]
  unfold GlobalTheory.DownLift.mirC
  by_cases hA : ∀ kv, kv ≠ kv0 → eR y kv = 1
  · rw [if_pos hA]
    by_cases hB : mirSet (fun j => (iso kv0).symm (a j)) b (eR y kv0)
    · rw [if_pos hB, if_pos ⟨h1.2 hA, h2.2 hB⟩, h3]
      rfl
    · rw [if_neg hB, if_neg fun H => hB (h2.1 H.2)]
  · rw [if_neg hA, if_neg fun H => hA (h1.1 H.1)]

end GlobalTheory.MirAvg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicAverageEqCoeffSinglePlaceElementStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  first | exact @GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | exact GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | (intros; apply GlobalTheory.MirAvg.mirC_eq_coeff_mirEl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CharLabTransport

theorem teich_inv {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (c : (ZMod g)ˣ) :
    L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((c⁻¹ : (ZMod g)ˣ) : ZMod g)) =
      (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (c : ZMod g)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem charLab_of_value {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ)
    (t : (ZMod g)ˣ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = ((θ u : ℂˣ) : ℂ) ∨
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = (((θ u)⁻¹ : ℂˣ) : ℂ)) :
    ∃ c : ZMod g, GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp θ) c ∧
      (c = (t : ZMod g) ∨ c = ((t⁻¹ : (ZMod g)ˣ) : ZMod g)) := by
  by_cases hex : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1
  · obtain ⟨u₀, hu₀⟩ := hex
    have huniq : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 → u = u₀ := by
      intro u hu
      apply Units.ext
      exact (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hu.trans hu₀.symm)
    rcases hε with rfl | rfl <;> rcases h u₀ hu₀ with hv | hv
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
  · exact ⟨_, ⟨t.ne_zero, fun u hu => (hex ⟨u, hu⟩).elim⟩, Or.inl rfl⟩

theorem charLab_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hg k v i PP hdiv iso ε hε
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, -, hser, hchi⟩ := hg k
  refine ⟨L, hser, ?_⟩
  apply charLab_of_value L _ _ ε hε
  intro u hu
  have h1 : (((u : ZMod (D.host.g k)).val : ℕ) : ZMod (D.host.g k)) = u := ZMod.natCast_zmod_val _
  refine hchi v i PP hdiv (u : ZMod (D.host.g k)).val
    (Units.map (iso : ZMod (D.host.g k) →* kP PP) u) ?_ ?_
  · rw [← hu, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), h1]
  · rw [← map_natCast iso, h1]; rfl

end GlobalTheory.CharLabTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  first | exact @GlobalTheory.CharLabTransport.charLab_of_goodTypes | exact GlobalTheory.CharLabTransport.charLab_of_goodTypes | (intros; apply GlobalTheory.CharLabTransport.charLab_of_goodTypes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorConvMirabolicAvgEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodNoChiTr

open Polynomial

theorem not_root_of_good (N g : ℕ) [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) (h : Formalism.CyclotomicNorms.IsGood N g f χ) (v : PP) (j : J) :
    ¬ (f v).IsRoot (χ v j : ZMod g) := by
  intro hr
  have hne : f v ≠ 0 := (h.1 v).1.ne_zero
  have hmem : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g) ∈ Formalism.CyclotomicNorms.rootsBar (f v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne), Polynomial.IsRoot, Polynomial.eval_map,
      Polynomial.eval₂_hom, hr.eq_zero, map_zero]
  obtain ⟨ℓ, hℓ, hℓg⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ g := by
    by_cases h2 : g = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun e => h2 e.symm⟩
  exact h.2.2.2.1 ℓ hℓ hℓg v j _ hmem rfl

theorem conv_mirC_eC : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  intro hS D G _ _ Pl0 T A Ks _ _ _ R F hG i PP a ha b ε hε x
  obtain ⟨eR, plg, iso, hcoef, hdiv, hrec⟩ := hG.core.grp.record
  obtain ⟨kv0, rfl⟩ := plg.surjective PP
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have heC : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := by
    intro g
    rw [← hcoef g]
    unfold RealDat.eC sg0
    rw [sgAt_mk _ R.hv0]
  rw [Finset.sum_congr rfl (fun y _ => by rw [GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement D G Pl0 T A Ks R eR plg iso hrec i kv0 a b ε y, heC])]
  refine GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero D G eR kv0 _ ?_ x
  intro a' hgood
  obtain ⟨L, hL, c, hc, hcc⟩ := GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes D G Pl0 T A Ks R hG.types kv0.1 kv0.2 i (plg kv0).1 (hdiv kv0) (iso kv0) ε hε
  rw [← D.ntypes.eSer_central, hL]
  have h1 := not_root_of_good _ _ _ _ (hgood kv0.1).1 kv0.2 i
  have h2 := not_root_of_good _ _ _ _ (hgood kv0.1).2 kv0.2 i
  have ha' : (fun j => (iso kv0).symm (a j)) ≠ 0 := by
    intro h; apply ha; funext j
    have := congrArg (iso kv0) (congrFun h j)
    simpa using this
  refine hS _ L _ _ _ c hc ?_ ?_ _ b ha'
  · rcases hcc with rfl | rfl
    · exact h1
    · exact h2
  · rcases hcc with rfl | rfl
    · rw [← Units.val_inv_eq_inv_val]; exact h2
    · rw [Units.val_inv_eq_inv_val, inv_inv]; exact h1

end GlobalTheory.GoodNoChiTr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorConvMirabolicAvgEqZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  first | exact @GlobalTheory.GoodNoChiTr.conv_mirC_eC | exact GlobalTheory.GoodNoChiTr.conv_mirC_eC | (intros; apply GlobalTheory.GoodNoChiTr.conv_mirC_eC <;> assumption)
end

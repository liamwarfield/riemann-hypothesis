module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedFCrystalOfStratifiedPhiModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemiBCInjectiveOfInjective
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_injective_of_injective : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B),
    Function.Injective f → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N),
    SemiBC u → Function.Injective u := by
  intro A B _ _ f hf M _ _ _ _ N _ _ u h
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let v : M →ₛₗ[f] (Fin n → B) :=
    { toFun := fun x i => f (s x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  rw [← LinearMap.ker_eq_bot (τ₁₂ := f), LinearMap.ker_eq_bot']
  intro x hx
  have h1 : v x = 0 := by rw [← hS, hx, map_zero]
  have h2 : s x = 0 := by
    funext i
    apply hf
    rw [Pi.zero_apply, map_zero]
    exact congrFun h1 i
  have h3 : x = p (s x) := by
    rw [← LinearMap.comp_apply, hps, LinearMap.id_apply]
  rw [h3, h2, map_zero]

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationOfFramedMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeOfBasisMapsToBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeOfBasisMapsToBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  intro A B _ _ f M _ _ N _ _ u ι e b hb Q _ _ v
  refine ⟨b.constr B (fun i => v (e i)), ?_, ?_⟩
  · intro x
    have h : (b.constr B (fun i => v (e i))).comp u = v := by
      refine e.ext fun i => ?_
      simp [LinearMap.comp_apply, ← hb, Module.Basis.constr_basis]
    exact LinearMap.congr_fun h x
  · intro w hw
    refine b.ext fun i => ?_
    rw [Module.Basis.constr_basis, hb, hw]

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeOfBasisMapsToBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  first | exact @GlobalTheory.BSP.semiBC_of_basis | exact GlobalTheory.BSP.semiBC_of_basis | (intros; apply GlobalTheory.BSP.semiBC_of_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationOfFramedMatrices
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EtReal

open Matrix

variable {l : ℕ} [hl : Fact l.Prime]

theorem equivFun_frob {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      fun i => frobW l ((b.baseChange (WCb l)).equivFun y i) := by
  funext i
  simp only [Module.Basis.equivFun_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      map_smul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), Finsupp.add_apply, Finsupp.add_apply, map_add (f := _), hy, hz]

theorem equivFun_map {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (s : WCb l ≃ₐ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map s.toLinearMap r y) =
      (LinearMap.toMatrix b b r).map (algebraMap ℤ_[l] (WCb l)) *ᵥ
        fun k => s ((b.baseChange (WCb l)).equivFun y k) := by
  funext i
  simp only [Module.Basis.equivFun_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, AlgEquiv.toLinearMap_apply,
      ← LinearMap.toMatrix_mulVec_repr b b r t]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, map_smul, Algebra.smul_def,
      Finset.sum_mul, map_mul, mul_assoc, map_sum, AlgEquiv.commutes]
  | add y z hy hz =>
    simp only [map_add (f := _), Finsupp.add_apply, hy, hz, mul_add, Finset.sum_add_distrib]

theorem algEquiv_mulVec {R A : Type} [CommSemiring R] [CommRing A] [Algebra R A] {n : Type} [Fintype n]
    (s : A ≃ₐ[R] A) (U : Matrix n n A) (v : n → A) (i : n) :
    s ((U *ᵥ v) i) = (U.map s *ᵥ fun k => s (v k)) i :=
  RingHom.map_mulVec s.toRingEquiv.toRingHom U v i

theorem realises_of_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  intro l _ K bk d S M e hF T _ _ ρ b U hU
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  let σ : (ainfObj K).A →+* WCb l := (inclW l).comp (ainfId K).toRingHom
  let cv : (Fin d → (ainfObj K).A) →ₛₗ[σ] (Fin d → WCb l) :=
    { toFun := fun v k => σ (v k)
      map_add' := fun v w => funext fun k => map_add σ (v k) (w k)
      map_smul' := fun a v => funext fun k => map_mul σ a (v k) }
  let j : M.M (ainfObj K) →ₛₗ[σ] (WCb l ⊗[ℤ_[l]] T) :=
    ((b.baseChange (WCb l)).equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' U) ∘ₛₗ (cv ∘ₛₗ b₀.equivFun.toLinearMap)
  have hj : ∀ x, (b.baseChange (WCb l)).equivFun (j x) = U *ᵥ fun k => σ (b₀.equivFun x k) := fun x =>
    (b.baseChange (WCb l)).equivFun.apply_symm_apply _
  have hjs : ∀ c : Fin d → (ainfObj K).A, (b.baseChange (WCb l)).equivFun (j (b₀.equivFun.symm c)) = U *ᵥ fun k => σ (c k) := fun c => by
    rw [hj, LinearEquiv.apply_symm_apply]

  have hbc : SemiBC j := by
    letI := hU.unit.invertible
    let c := (Pi.basisFun (WCb l) (Fin d)).map ((Matrix.toLinearEquiv' U this).trans (b.baseChange (WCb l)).equivFun.symm)
    refine GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis _ _ _ _ _ j (Fin d) b₀ c fun i => ?_
    apply (b.baseChange (WCb l)).equivFun.injective
    rw [hj]
    simp only [c, Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [Module.Basis.equivFun_self]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ↥(ainfObj K).I, ((d₀ : (ainfObj K).A) : Ainf l) = bk.ev bk.E :=
    ⟨⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩, rfl⟩
  have hne : (d₀ : (ainfObj K).A) ≠ 0 := fun h => hu.ne_zero (by rw [← hd₀, h]; exact map_zero (inclW l))
  refine ⟨j, Realises.of_generator (isAinf_ainfObj K) hbc d₀ (by rw [hd₀]; exact bk.span_ev) ?_ ?_⟩
  · intro x m k hfr
    have hx : x = ∑ i, b₀.equivFun x i • M.tr bk.ι (e i) := by
      simp_rw [← hb₀]; exact (b₀.sum_equivFun x).symm
    rw [hx] at hfr
    obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι d₀ (b₀.equivFun x) m k hfr
    haveI : IsDomain (ainfObj K).A := (ainfId K).toMulEquiv.isDomain
    haveI := Module.Free.of_basis b₀
    have h1 := sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ hne))
    simp_rw [← hb₀] at h1
    rw [← b₀.equivFun_symm_apply] at h1
    have h2 : σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (d₀ : (ainfObj K).A) ^ k •
        j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i))) :=
      calc σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (BK.hf bk.ι bk.E ^ S.a) • j m := by rw [map_pow]
        _ = j (BK.hf bk.ι bk.E ^ S.a • m) := (j.map_smulₛₗ _ _).symm
        _ = j ((d₀ : (ainfObj K).A) ^ k • b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := congrArg j h1
        _ = σ ((d₀ : (ainfObj K).A) ^ k) • j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := j.map_smulₛₗ _ _
        _ = _ := congrArg (· • _) (map_pow σ _ _)
    suffices hs : σ (BK.hf bk.ι bk.E) ^ S.a • (σ (d₀ : (ainfObj K).A) ^ k •
        TensorProduct.map (frobW l).toLinearMap LinearMap.id (j x)) = σ (BK.hf bk.ι bk.E) ^ S.a • j m from
      (hu.pow S.a).smul_left_cancel.1 hs
    rw [h2]
    refine (smul_comm (σ (BK.hf bk.ι bk.E) ^ S.a) (σ (d₀ : (ainfObj K).A) ^ k) _).trans
      (congrArg (σ (d₀ : (ainfObj K).A) ^ k • ·) ?_)
    apply (b.baseChange (WCb l)).equivFun.injective
    have hz : (fun i => frobW l ((b.baseChange (WCb l)).equivFun (j x) i)) =
        U.map (frobW l) *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      rw [hj]
      funext i
      refine (RingHom.map_mulVec (frobW l).toRingHom U _ i).trans ?_
      exact congrArg (fun v => (U.map (frobW l) *ᵥ v) i) (funext fun k => frobW_inclW (b₀.equivFun x k))
    have hc : (fun k => σ (((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i)) k)) =
        S.A.map bk.evW *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      funext k
      have hA : (S.A.map (BK.hf bk.ι)).map σ = S.A.map bk.evW := Matrix.ext fun _ _ => rfl
      exact (RingHom.map_mulVec σ _ _ k).trans
        (congrArg (fun A => (A *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k))) k) hA)
    have hσE : σ (BK.hf bk.ι bk.E) = bk.evW bk.E := rfl
    refine ((b.baseChange (WCb l)).equivFun.map_smul _ _).trans ?_
    refine Eq.trans ?_ (hjs _).symm
    refine (congrArg (σ (BK.hf bk.ι bk.E) ^ S.a • ·) ((equivFun_frob b (j x)).trans hz)).trans ?_
    refine Eq.trans ?_ (congrArg (U *ᵥ ·) hc).symm
    exact (congrArg (fun t => t ^ S.a • (U.map (frobW l) *ᵥ _)) hσE).trans
      ((Matrix.smul_mulVec _ _ _).symm.trans
        ((congrArg (· *ᵥ _) hU.φ).trans (Matrix.mulVec_mulVec _ _ _).symm))
  · intro g x
    let h := (isAinf_ainfObj K).galHom g
    have hk : ∀ k, M.tr h (b₀ k) = ∑ i, S.ε bk.ι (h.comp bk.ι) i k • b₀ i := fun k =>
      (congrArg (M.tr h) (hb₀ k)).trans ((M.tr_comp h bk.ι (e k)).symm.trans
        ((hF.tr bk.ι (h.comp bk.ι) k).trans (Finset.sum_congr rfl fun i _ => congrArg _ (hb₀ i).symm)))
    have htr : M.tr h x = b₀.equivFun.symm ((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) :=
      calc M.tr h x = M.tr h (∑ k, b₀.equivFun x k • b₀ k) := congrArg (M.tr h) (b₀.sum_equivFun x).symm
        _ = ∑ k, h.f (b₀.equivFun x k) • M.tr h (b₀ k) :=
          (map_sum (M.tr h) _ _).trans (Finset.sum_congr rfl fun k _ => (M.tr h).map_smulₛₗ _ _)
        _ = ∑ k, ∑ i, (h.f (b₀.equivFun x k) * S.ε bk.ι (h.comp bk.ι) i k) • b₀ i :=
          Finset.sum_congr rfl fun k _ => (congrArg _ (hk k)).trans
            (Finset.smul_sum.trans (Finset.sum_congr rfl fun i _ => smul_smul _ _ _))
        _ = ∑ i, (∑ k, S.ε bk.ι (h.comp bk.ι) i k * h.f (b₀.equivFun x k)) • b₀ i :=
          Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
            (Finset.sum_congr rfl fun k _ => congrArg (· • b₀ i) (mul_comm _ _)).trans Finset.sum_smul.symm)
        _ = _ := (b₀.equivFun_symm_apply _).symm
    apply (b.baseChange (WCb l)).equivFun.injective
    have hσ : ∀ a : (ainfObj K).A, σ a = inclW l a := fun a => rfl
    have hh : ∀ a : (ainfObj K).A, h.f a = Per.σA (g : GQ l) a := fun a => rfl
    have hL : (fun k => σ (((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) k)) =
        (S.ε bk.ι (h.comp bk.ι)).map σ *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun k => RingHom.map_mulVec σ _ _ k
    have hR : (fun k => galW l (g : GQ l) ((b.baseChange (WCb l)).equivFun (j x) k)) =
        U.map (galW l (g : GQ l)) *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun i => by
        have h1 := congrArg (fun v : Fin d → WCb l => galW l (g : GQ l) (v i)) (hj x)
        have h2 := algEquiv_mulVec (galW l (g : GQ l)) U (fun k => σ (b₀.equivFun x k)) i
        have h3 : (fun k => galW l (g : GQ l) (σ (b₀.equivFun x k))) = fun k => σ (h.f (b₀.equivFun x k)) :=
          funext fun k => (congrArg (galW l (g : GQ l)) (hσ _)).trans ((galW_inclW (g : GQ l) (b₀.equivFun x k)).trans
            ((hσ _).symm.trans (congrArg σ (hh _).symm)))
        beta_reduce at h1 ⊢
        exact h1.trans (h2.trans (congrArg (fun v => (U.map (galW l (g : GQ l)) *ᵥ v) i) h3))
    have hg := hU.gal g
    refine ((congrArg (fun z => (b.baseChange (WCb l)).equivFun (j z)) htr).trans (hjs _)).trans ?_
    refine Eq.trans ?_ (equivFun_map b _ _ _).symm
    refine (congrArg (U *ᵥ ·) hL).trans (Eq.trans ?_ (congrArg (_ *ᵥ ·) hR).symm)
    exact (Matrix.mulVec_mulVec _ _ _).trans ((congrArg (· *ᵥ _) hg.symm).trans (Matrix.mulVec_mulVec _ _ _).symm)

end GlobalTheory.BSP.EtReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationOfFramedMatricesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRealisation_of_framedMatrices : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  first | exact @GlobalTheory.BSP.EtReal.realises_of_mreal | exact GlobalTheory.BSP.EtReal.realises_of_mreal | (intros; apply GlobalTheory.BSP.EtReal.realises_of_mreal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrism
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem galoisLatticeAction_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) (g h : ↥(GK K)) :
    actT L g ∘ₗ actT L h = actT L (g * h) := by
  ext x
  simp [actT, map_mul]
  rfl

theorem galoisLatticeAction_one {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) :
    actT L 1 = LinearMap.id := by
  ext x
  simp [actT, map_one]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem isUnit_toMatrix_actT {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥L.T) (g : ↥(GK K)) :
    IsUnit (LinearMap.toMatrix b b (actT L g)) := by
  have h1 : LinearMap.toMatrix b b (actT L g) * LinearMap.toMatrix b b (actT L g⁻¹) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, mul_inv_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  have h2 : LinearMap.toMatrix b b (actT L g⁻¹) * LinearMap.toMatrix b b (actT L g) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, inv_mul_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  exact ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem clause1_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  intro l _ K P AI hStd V _ _ _ _ _ _ _ ρ L hcont hcrys
  haveI : Module.Free ℤ_[l] ↥L.T := L.free
  haveI : Module.Finite ℤ_[l] ↥L.T := Module.Finite.iff_fg.mpr L.fg
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_breuilKisin_frobenius_period l K bk
  let b := Module.finBasis ℤ_[l] ↥L.T
  obtain ⟨s⟩ := GlobalTheory.T.exists_crystalline_lattice_periods_on_disc l K bk τ hτ P AI hStd V ρ L hcont hcrys _ b
  have hu : ∀ g, IsUnit (LinearMap.toMatrix b b (actT L g)) := fun g => isUnit_toMatrix_actT L b g
  obtain ⟨hs⟩ := GlobalTheory.T.nonempty_discPeriodAinfBasisData_of_isPer l K bk τ hτ _ _ hu s
  obtain ⟨S, T, hST⟩ := GlobalTheory.T.exists_stratified_phiModule_crystalline_lattice l K bk τ hτ _ _ hu s hs
  obtain ⟨M, e, hMe⟩ := GlobalTheory.T.exists_framed_fCrystal_of_stratifiedPhiModule l K bk _ S
  exact ⟨M, GlobalTheory.T.etaleRealisation_of_framedMatrices l K bk _ S M e hMe ↥L.T (fun g => actT L g) b T hST⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrismStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  first | exact @GlobalTheory.BSP.clause1_perfectPrism | exact GlobalTheory.BSP.clause1_perfectPrism | (intros; apply GlobalTheory.BSP.clause1_perfectPrism <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FCrystalHomEqOfEtaleRealisationPerfectPrism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrism
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem FHom.ext_u {M M' : FCrys l R} {u u' : FHom M M'} (h : ∀ P, u.u P = u'.u P) : u = u' := by
  cases u; cases u'
  congr
  funext P
  exact h P

theorem FHom.eq_of_tr {M M' : FCrys l R} (u u' : FHom M M') {P Q : Obj l R} (g : Hom P Q)
    (hP : u.u P = u'.u P) : u.u Q = u'.u Q := by
  let v : M.M P →ₛₗ[g.f] M'.M Q := (M'.tr g).comp (u.u P)
  obtain ⟨w, -, hw⟩ := M.tr_bc g (M'.M Q) v
  have h1 := hw (u.u Q) fun x => by simp [v, u.u_tr]
  have h2 := hw (u'.u Q) fun x => by simp [v, u'.u_tr, hP]
  rw [h1, h2]

theorem FHom.eq_of_inj {M M' : FCrys l R} (u u' : FHom M M') {B C : Obj l R} (h : Hom B C)
    (hinj : Function.Injective h.f) (hC : u.u C = u'.u C) : u.u B = u'.u B := by
  haveI := M'.fin B
  haveI := M'.proj B
  have hi : Function.Injective (M'.tr h) :=
    semiBC_injective_of_injective _ _ h.f hinj _ _ (M'.tr h) (M'.tr_bc h)
  ext x
  apply hi
  rw [← u.u_tr, ← u'.u_tr, hC]

theorem fhom_ext_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K))
    (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  intro l _ K bk M M' u u' hbk
  apply FHom.ext_u
  intro B
  obtain ⟨C, h, ⟨g⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hC := FHom.eq_of_tr u u' g hbk
  exact FHom.eq_of_inj u u' h (GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc).1 hC

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrismStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K)) (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  first | exact @GlobalTheory.BSP.fhom_ext_bk | exact GlobalTheory.BSP.fhom_ext_bk | (intros; apply GlobalTheory.BSP.fhom_ext_bk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDatumStructureMapInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDatumStructureMapInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bk_ev_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  intro a a' h
  have h1 : tb.c tb.i₀ 1 = 1 := by simpa [tb.b_i₀] using tb.c_self tb.i₀
  have key : ∀ x, tb.c tb.i₀ (bk.ev x) = x := fun x => by
    have := tb.c_mul tb.i₀ x (tb.b tb.i₀)
    rw [tb.b_i₀, mul_one, h1, mul_one] at this
    exact this
  rw [← key a, ← key a', h]

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDatumStructureMapInjectiveStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinDatum_structureMap_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  first | exact @GlobalTheory.BSP.bk_ev_injective | exact GlobalTheory.BSP.bk_ev_injective | (intros; apply GlobalTheory.BSP.bk_ev_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FCrystalHomEqOfEtaleRealisationPerfectPrism
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem fHom_eq_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T']
    (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K))
    (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')),
    Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M',
      (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  intro l _ K T' _ _ ρ' M M' j' H u u' h
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  apply GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism l K bk M M' u u'
  haveI := M'.fin (ainfObj K)
  haveI := M'.proj (ainfObj K)
  haveI := M'.fin bk.prism
  haveI := M'.proj bk.prism
  have hj : Function.Injective j' :=
    semiBC_injective_of_injective _ _ ((inclW l).comp (ainfId K).toRingHom)
      (GlobalTheory.Prism.inclW_injective.comp (ainfId K).injective) _ _ j' H.bc
  have ht : Function.Injective (M'.tr bk.ι) :=
    semiBC_injective_of_injective _ _ bk.ι.f (GlobalTheory.T.breuilKisinDatum_structureMap_injective l K bk) _ _ (M'.tr bk.ι) (M'.tr_bc bk.ι)
  refine LinearMap.ext fun x => ht (hj ?_)
  rw [← u.u_tr, ← u'.u_tr]
  exact h _

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FCrystalHomEqOfEtaleRealisationPerfectPrismStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fCrystalHom_eq_of_etale_realisation_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M', (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  first | exact @GlobalTheory.BSP.fHom_eq_of_realises | exact GlobalTheory.BSP.fHom_eq_of_realises | (intros; apply GlobalTheory.BSP.fHom_eq_of_realises <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationIndepAinfModel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationIndepAinfModel
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.ModelChange

def Via {B C : Type} [CommRing B] [CommRing C] (_g : B →+* C) (Q : Type) : Type := Q

instance instAddCommGroupVia {B C : Type} [CommRing B] [CommRing C] (g : B →+* C) (Q : Type)
    [AddCommGroup Q] : AddCommGroup (Via g Q) := ‹AddCommGroup Q›

instance instModuleVia {B C : Type} [CommRing B] [CommRing C] (g : B →+* C) (Q : Type) [AddCommGroup Q]
    [Module C Q] : Module B (Via g Q) := Module.compHom Q g

theorem semiBC_comp {A B C M N P : Type} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]
    {f : A →+* B} {g : B →+* C} {h : A →+* C} (hfg : ∀ a, g (f a) = h a)
    {u : M →ₛₗ[f] N} {v : N →ₛₗ[g] P} {w : M →ₛₗ[h] P} (hw : ∀ x, w x = v (u x))
    (hu : SemiBC u) (hv : SemiBC v) : SemiBC w := by
  intro Q _ _ q
  let q₁ : M →ₛₗ[f] Via g Q :=
    { toFun := fun x => (q x : Q)
      map_add' := fun x y => map_add q x y
      map_smul' := fun a x => by
        change q (a • x) = g (f a) • (q x : Q)
        rw [q.map_smulₛₗ, hfg] }
  obtain ⟨w₁, hw₁, hu₁⟩ := hu (Via g Q) q₁
  let w₂ : N →ₛₗ[g] Q :=
    { toFun := fun y => (w₁ y : Q)
      map_add' := fun y z => map_add w₁ y z
      map_smul' := fun b y => w₁.map_smul b y }
  obtain ⟨w₃, hw₃, hu₃⟩ := hv Q w₂
  refine ⟨w₃, fun x => ?_, fun w' hw' => ?_⟩
  · rw [hw, hw₃]; exact hw₁ x
  · let w'' : N →ₗ[B] Via g Q :=
      { toFun := fun y => (w' (v y) : Q)
        map_add' := fun y z => by
          change w' (v (y + z)) = w' (v y) + w' (v z)
          rw [map_add (f := _), map_add (f := _)]
        map_smul' := fun b y => by
          change w' (v (b • y)) = g b • w' (v y)
          rw [v.map_smulₛₗ, w'.map_smul] }
    have h1 : w'' = w₁ := hu₁ w'' fun x => by
      change w' (v (u x)) = q x
      rw [← hw x]; exact hw' x
    exact hu₃ w' fun y => by
      change w' (v y) = (w₁ y : Q)
      rw [← h1]; rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem torsionFree_of_equiv {P : Obj l ↥(OL K)} (e : P.A ≃+* Ainf l) (x : P.A) (h : (l : P.A) * x = 0) :
    x = 0 :=
  e.injective (by rw [map_zero]; apply ainf_torsionFree; rw [← map_natCast e, ← map_mul, h, map_zero])

def toAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) : Hom P (ainfObj K) where
  f := e.toRingHom
  f_δ := P.D.map_δ_of_map_φ (ainfObj K).D ainf_torsionFree _ fun a => H.e_φ a
  f_I a ha := ((isAinf_ainfObj K).e_I (e a)).2 ((H.e_I a).1 ha)
  f_str r a h := ((isAinf_ainfObj K).mk_eq_str_iff r (e a)).2 ((H.mk_eq_str_iff r a).1 h)

def ofAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) : Hom (ainfObj K) P where
  f := e.symm.toRingHom
  f_δ := (ainfObj K).D.map_δ_of_map_φ P.D (torsionFree_of_equiv e) _ fun a => e.injective
      ((e.apply_symm_apply _).trans ((congrArg WittVector.frobenius (e.apply_symm_apply (a : Ainf l))).symm.trans
        (H.e_φ _).symm))
  f_I a ha := (H.e_I _).2
      ((congrArg (Per.θ l) (e.apply_symm_apply (a : Ainf l))).trans (((isAinf_ainfObj K).e_I a).1 ha))
  f_str r a h := (H.mk_eq_str_iff r _).2
      ((congrArg (Per.θ l) (e.apply_symm_apply (a : Ainf l))).trans (((isAinf_ainfObj K).mk_eq_str_iff r a).1 h))

theorem ofAinf_comp_toAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) :
    (ofAinf H).comp (toAinf H) = Hom.id P :=
  Hom.ext' (RingHom.ext fun a => e.symm_apply_apply a)

theorem toAinf_comp_ofAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) :
    (toAinf H).comp (ofAinf H) = Hom.id (ainfObj K) :=
  Hom.ext' (RingHom.ext fun a => e.apply_symm_apply a)

variable {T : Type} [AddCommGroup T] [Module ℤ_[l] T]

def jOfModel {M : FCrys l ↥(OL K)} {P P' : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} {e' : P'.A ≃+* Ainf l}
    (c : Hom P P') (hc : ∀ a, e' (c.f a) = e a)
    (j' : M.M P' →ₛₗ[(inclW l).comp e'.toRingHom] (WCb l ⊗[ℤ_[l]] T)) :
    M.M P →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T) where
  toFun x := j' (M.tr c x)
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]
  map_smul' a x := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    change inclW l (e' (c.f a)) • _ = inclW l (e a) • _
    rw [hc]

theorem realises_of {M : FCrys l ↥(OL K)} {P P' : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l}
    {e' : P'.A ≃+* Ainf l} {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)} (H : IsAinf K P e) (c : Hom P P')
    (hc : ∀ a, e' (c.f a) = e a) {j' : M.M P' →ₛₗ[(inclW l).comp e'.toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (hj : Realises K M P' e' T ρ j') : Realises K M P e T ρ (jOfModel c hc j') := by
  have H' := hj.ainf
  obtain ⟨d₀, hd, hd0⟩ := H.exists_generator
  refine Realises.of_generator H ?_ d₀ hd ?_ ?_
  · exact semiBC_comp (f := c.f) (g := (inclW l).comp e'.toRingHom) (h := (inclW l).comp e.toRingHom)
      (u := M.tr c) (v := j') (w := jOfModel c hc j') (fun a => congrArg (inclW l) (hc a)) (fun _ => rfl)
      (M.tr_bc c) hj.bc
  · intro x m k h
    have : IsDomain P'.A := e'.toMulEquiv.isDomain
    have := M.proj P'
    let d' : ↥P'.I := ⟨c.f d₀, c.f_I _ d₀.2⟩
    have hd'e : e' (d' : P'.A) = e d₀ := hc _
    have hd'0 : (d' : P'.A) ≠ 0 := fun h0 => hd0 (e.injective (by rw [← hd'e, h0, map_zero, map_zero]))
    obtain ⟨n, i, hn⟩ := exists_isFrac (d' : P'.A) (M.Φ P' d' (M.tr c x))
    obtain ⟨r, hr⟩ := M.Φ_nat c d₀ d' x m k n i h hn
    have heq : (d' : P'.A) ^ i • M.tr c m = (d' : P'.A) ^ k • n :=
      sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero hd'0 hd'0)))
    have hu : IsUnit (((inclW l).comp e'.toRingHom) (d' : P'.A)) := by
      change IsUnit (inclW l (e' (d' : P'.A))); rw [hd'e]; exact H.isUnit_inclW hd
    have key := smul_eq_of_isUnit j' hu heq (hj.j_φ d' hd'0 (M.tr c x) n i hn)
    change inclW l (e d₀) ^ k • _ = j' (M.tr c m)
    rw [← hd'e]; exact key
  · intro g x
    have hcg : c.comp (H.galHom g) = (H'.galHom g).comp c := Hom.ext' (RingHom.ext fun a => e'.injective (by
      change e' (c.f ((H.galHom g).f a)) = e' ((H'.galHom g).f (c.f a))
      rw [hc, H.e_galHom, H'.e_galHom, hc]))
    have e0 : M.tr c (M.tr (H.galHom g) x) = M.tr (H'.galHom g) (M.tr c x) :=
      (M.tr_comp _ _ x).symm.trans ((congrArg (fun f => M.tr f x) hcg).trans (M.tr_comp _ _ x))
    exact (congrArg j' e0).trans (hj.j_act g (M.tr c x))

end GlobalTheory.Prism.ModelChange


open GlobalTheory.Prism.ModelChange in
theorem GlobalTheory.Prism.realisation_indep_model : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e₀ : P₀.A ≃+* Ainf l), IsAinf K P₀ e₀ → ∃ a : Hom P₀ (ainfObj K), ∀ (M : FCrys l ↥(OL K)), Function.Bijective (M.tr a) ∧ ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)), (∀ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ → ∃ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j) ∧ (∀ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j → ∃ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ ∧ ∀ x, j₀ (M.tr a x) = j x) := by
  intro l _ K P₀ e₀ H
  refine ⟨toAinf H, fun M => ⟨?_, fun T _ _ ρ => ⟨fun j₀ hj₀ => ⟨_, realises_of H (toAinf H) (fun _ => rfl) hj₀⟩,
    fun j hj => ⟨_, realises_of (isAinf_ainfObj K) (ofAinf H) (fun a => by exact e₀.apply_symm_apply a) hj,
      fun x => ?_⟩⟩⟩⟩
  · refine Function.bijective_iff_has_inverse.2 ⟨M.tr (ofAinf H), fun x => ?_, fun y => ?_⟩
    · rw [← M.tr_comp, ofAinf_comp_toAinf, M.tr_id]
    · rw [← M.tr_comp, toAinf_comp_ofAinf, M.tr_id]
  · change j (M.tr (ofAinf H) (M.tr (toAinf H) x)) = j x
    rw [← M.tr_comp, ofAinf_comp_toAinf, M.tr_id]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationIndepAinfModelStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRealisation_indep_ainfModel : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e₀ : P₀.A ≃+* Ainf l), IsAinf K P₀ e₀ → ∃ a : Hom P₀ (ainfObj K), ∀ (M : FCrys l ↥(OL K)), Function.Bijective (M.tr a) ∧ ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)), (∀ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ → ∃ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j) ∧ (∀ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j → ∃ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ ∧ ∀ x, j₀ (M.tr a x) = j x) := by
  first | exact @GlobalTheory.Prism.realisation_indep_model | exact GlobalTheory.Prism.realisation_indep_model | (intros; apply GlobalTheory.Prism.realisation_indep_model <;> assumption)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral := by
  intro l _ K P₀ e H
  obtain ⟨a, ha⟩ := GlobalTheory.T.etaleRealisation_indep_ainfModel l K P₀ e H
  refine ⟨?_, ?_⟩
  · intro P AI hstd V _ _ _ _ _ _ _ ρ L hc hcr
    obtain ⟨M, j₀, hj₀⟩ := GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism l K P AI hstd V ρ L hc hcr
    obtain ⟨j, hj⟩ := ((ha M).2 ↥L.T (fun g => actT L g)).1 j₀ hj₀
    exact ⟨M, j, hj⟩
  · intro T T' _ _ _ _ ρ ρ' E E' j j' hj hj' f hf
    obtain ⟨j₀, hj₀, e₀⟩ := ((ha E).2 T ρ).2 j hj
    obtain ⟨j₀', hj₀', e₀'⟩ := ((ha E').2 T' ρ').2 j' hj'
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_FCrystalHom_of_equivariantEtaleMap_ainf l K T ρ T' ρ' E E' j₀ j₀' hj₀ hj₀' f hf
    refine ⟨u, fun x => ?_, fun u' hu' => ?_⟩
    · exact (e₀' _).symm.trans ((congrArg j₀' (u.u_tr a x).symm).trans
        ((hu _).trans (congrArg (f.lTensor (WCb l)) (e₀ x))))
    · refine GlobalTheory.T.fCrystalHom_eq_of_etale_realisation_perfectPrism l K T' ρ' E E' j₀' hj₀' u' u fun y => ?_
      obtain ⟨x, rfl⟩ := (ha E).1.2 y
      exact (congrArg j₀' (u'.u_tr a x)).trans ((e₀' _).trans ((hu' x).trans
        ((congrArg (f.lTensor (WCb l)) (e₀ x).symm).trans (hu _).symm)))

end GlobalTheory.BSP

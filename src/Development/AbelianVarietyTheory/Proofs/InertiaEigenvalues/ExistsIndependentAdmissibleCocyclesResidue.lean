module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleCocyclesCardLeSumDimsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentAdmissibleCocyclesResidue
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1)

namespace GlobalTheory.ResidueBound

theorem exists_residue (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [FaithfulSMul ℤ_[l] O] (lam : O) (h : Irreducible lam) :
    Finite (O ⧸ Ideal.span {lam}) ∧ ∃ (k : Type) (_ : Field k) (_ : Algebra O k), CharP k l ∧
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {lam} := h.maximalIdeal_eq
  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    have h1 : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ Algebra.IsIntegral.isIntegral _
    have h2 := IsLocalRing.eq_maximalIdeal h1
    have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h2, Ideal.mem_comap, map_natCast] at h3
    exact h3
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hfin : Finite (IsLocalRing.ResidueField O) := by
    have : Finite (IsLocalRing.ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).toEquiv.symm
    exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[l])
  refine ⟨?_, IsLocalRing.ResidueField O, inferInstance, inferInstance, ?_, IsLocalRing.residue_surjective, fun x => ?_⟩
  · rw [← hm]; exact hfin
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff]
    exact hl
  · rw [← Ideal.mem_span_singleton, ← hm]
    exact IsLocalRing.residue_eq_zero_iff x

variable {O G k : Type} [CommRing O] [Group G] [Field k] [Algebra O k] {lam : O}

theorem exists_tensor_equiv {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (q : M →ₗ[O] N) (hq : Function.Surjective q) (hk : KerIs lam q) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] N, ∀ m y, φ (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := by
  have hN : ∀ x : N, lam • x = 0 := fun x => by
    obtain ⟨m, rfl⟩ := hq x
    rw [← map_smul]; exact (hk _).2 ⟨m, rfl⟩
  let f : (M ⊗[O] (O ⧸ Ideal.span {lam})) →ₗ[O] N := TensorProduct.lift ((cycMap hN).comp q)
  have hf : ∀ m y, f (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := fun _ _ => rfl
  have h1 : ∀ x : M ⊗[O] (O ⧸ Ideal.span {lam}), ∃ m : M, x = m ⊗ₜ Ideal.Quotient.mk _ 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m y =>
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨y • m, ?_⟩
      rw [TensorProduct.smul_tmul]
      congr 1
      change _ = Ideal.Quotient.mk _ (y * 1)
      rw [mul_one]
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩
  refine ⟨LinearEquiv.ofBijective f ⟨?_, fun x => ?_⟩, hf⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := h1 x
    rw [hf, one_smul] at hx
    obtain ⟨y, rfl⟩ := (hk m).1 hx
    rw [TensorProduct.smul_tmul]
    have : lam • Ideal.Quotient.mk (Ideal.span {lam}) 1 = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    rw [this, TensorProduct.tmul_zero]
  · obtain ⟨m, rfl⟩ := hq x
    exact ⟨m ⊗ₜ Ideal.Quotient.mk _ 1, by rw [hf, one_smul]⟩

theorem exists_ext (T : Ob k G) (z : G → Fin T.m → k) (hz : ∀ g h, z (g * h) = z g + T.ρ g (z h)) :
    ∃ (E : Ob k G) (e : ((Fin T.m → k) × k) ≃ₗ[k] (Fin E.m → k)), IsExt T E z ∧
      ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := by
  have hz1 : z 1 = 0 := by simpa using hz 1 1
  let π : Representation k G ((Fin T.m → k) × k) :=
    { toFun := fun g => ((T.ρ g).coprod (LinearMap.toSpanSingleton k _ (z g))).prod (LinearMap.snd k _ _)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp [hz1]
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp [hz g h]
        abel }
  obtain ⟨E, e, he⟩ := exists_ob π
  have he' : ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := fun g v y => (he g (v, y)).symm
  refine ⟨E, e, ⟨?_, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e (0, 1), fun g x => ?_, ?_, ?_, fun g => ?_⟩, he'⟩
  · have := e.finrank_eq
    simpa using this.symm
  · simp [he']
  · exact e.injective.comp LinearMap.inl_injective
  · rintro ⟨x, hx⟩
    have := congrArg Prod.snd (e.injective hx)
    simp at this
  · rw [he']
    change _ = e (0, 1) + e (z g, 0)
    rw [← map_add (f := _)]
    simp

variable [TopologicalSpace G]

theorem linearIndependent_of_indepMod (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) {N : Type} [AddCommGroup N] [Module O N]
    (π : Representation O G N) (T : Ob k G) (φ : N ≃ₗ[O] (Fin T.m → k)) (hφ : ∀ g x, φ (π g x) = T.ρ g (φ x))
    {s : ℕ} (z : Fin s → ↥(Z1 π ⊤)) (hz : IndepMod lam fun a => (Submodule.Quotient.mk (z a) : H1 π ⊤)) :
    LinearIndependent k fun a => (cob T).mkQ fun g => φ ((z a : G → N) g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  choose x hx using fun a => hs (c a)
  rw [← hx, hk]
  refine hz x ?_ a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_smul, ← map_sum] at hc
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  have h1 : ∑ a, x a • (Submodule.Quotient.mk (z a) : H1 π ⊤) = Submodule.Quotient.mk (∑ a, x a • z a) := by
    change ∑ a, x a • Submodule.mkQ _ (z a) = Submodule.mkQ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum]
  rw [h1, Submodule.Quotient.mk_eq_zero]
  refine ⟨φ.symm b, Submodule.mem_top, ?_⟩
  funext g
  apply φ.injective
  have h2 := congrFun hb g
  change φ (π g (φ.symm b) - φ.symm b) = _
  rw [map_sub, hφ, φ.apply_symm_apply]
  refine Eq.trans h2 ?_
  simp [← hx]

theorem exists_ext_Ea (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    {M X : Type} [AddCommGroup M] [Module O M] [AddCommGroup X] [Module O X] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (φ : (M ⊗[O] X) ≃ₗ[O] (Fin T.m → k))
    (hφ : ∀ g x, φ (twCoef W χ X g x) = T.ρ g (φ x)) (ha : ∀ x : X, lam ^ 1 • x = 0)
    (z : ↥(Z1 (twCoef W χ X) ⊤)) :
    ∃ (E : Ob k G) (e : ((M ⊗[O] X) × (O ⧸ Ideal.span {lam ^ 1})) ≃ₗ[O] (Fin E.m → k)),
      IsExt T E (fun g => φ ((z : G → M ⊗[O] X) g)) ∧
      ∀ g x, e (twistRep (Ea W χ ha z) χ⁻¹ g x) = E.ρ g (e x) := by
  obtain ⟨E, e, hE, he⟩ := exists_ext T (fun g => φ ((z : G → M ⊗[O] X) g)) (fun g h => by
    rw [cocycle_mul, map_add (f := _), hφ])
  have hker : Ideal.span {lam ^ 1} = LinearMap.ker (Algebra.linearMap O k) := by
    ext x
    rw [pow_one, Ideal.mem_span_singleton, ← hk]
    rfl
  let ψ : (O ⧸ Ideal.span {lam ^ 1}) ≃ₗ[O] k :=
    (Submodule.quotEquivOfEq _ _ hker).trans ((Algebra.linearMap O k).quotKerEquivOfSurjective hs)
  have hψ : ∀ y, ψ (Ideal.Quotient.mk _ y) = algebraMap O k y := fun _ => rfl
  refine ⟨E, (φ.prodCongr ψ).trans (e.restrictScalars O), hE, ?_⟩
  rintro g ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : twistRep (Ea W χ ha z) χ⁻¹ g (m, Ideal.Quotient.mk _ y) =
      (twCoef W χ X g m + y • (z : G → M ⊗[O] X) g, Ideal.Quotient.mk _ y) := by
    rw [twistRep_apply, Ea, twistRep_apply, smul_smul, extRep_apply]
    simp
  rw [h1]
  change e (φ _, ψ _) = E.ρ g (e (φ _, ψ _))
  rw [he, map_add (f := _), hφ, map_smul, hψ, algebraMap_smul]


omit [TopologicalSpace G] in
theorem exists_coef_equiv {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (q : M →ₗ[O] (Fin T.m → k)) (hq : Function.Surjective q) (hk : KerIs lam q)
    (he : ∀ σ x, q (twistRep W χ⁻¹ σ x) = T.ρ σ (q x)) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] (Fin T.m → k),
      ∀ g x, φ (twCoef W χ (O ⧸ Ideal.span {lam}) g x) = T.ρ g (φ x) := by
  obtain ⟨φ, hφ⟩ := exists_tensor_equiv q hq hk
  refine ⟨φ, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [coefRep_tmul, hφ, hφ, he, LinearMap.map_smul_of_tower]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem exists_independent_admissible_cocycles_residue {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    [Algebra O LL] [TopologicalSpace LL] {n r l : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (Γ : GalData G Qp LL O) (D : TopData n r) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {R : RingPG k l} (F : DFun R n G) (M : ModTh F D)
    (q : ↥Γ.T₀.L.T →ₗ[O] (Fin M.T.m → k)) (hq : Function.Surjective q) (hker : KerIs Γ.lam q)
    (hqe : ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x))
    (hmod : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
      (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
      (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    (h0 : ∀ (a : ℕ) (ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) =
        admAt PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) a ha)
    (s : ℕ) (c : Fin s → H1 (twCoef Γ.W₀ Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) ⊤)
    (hc : ∀ a, c a ∈ adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) (hi : IndepMod Γ.lam c) :
    ∃ z : Fin s → G → Fin M.T.m → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) ∧
      LinearIndependent k (fun a => (cob M.T).mkQ (z a)) := by
  obtain ⟨φ, hφ⟩ := exists_coef_equiv Γ.W₀ Γ.χ₁ M.T q hq hker hqe
  have ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ 1 • x = 0 := fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [h0 1 ha le_rfl] at hc
  choose z hz hadm using hc
  obtain rfl : c = fun a => Submodule.Quotient.mk (z a) := funext fun a => (hz a).symm
  refine ⟨_, fun a => ?_, linearIndependent_of_indepMod hs hk _ M.T φ hφ z hi⟩
  obtain ⟨E, e, hE, he⟩ := exists_ext_Ea hs hk Γ.W₀ Γ.χ₁ M.T φ hφ ha (z a)
  obtain ⟨L, hL⟩ := hmod E _ _ e (hadm a) he
  exact ⟨E, L, hE, hL⟩

theorem resBound_dsum : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P),
    S.Real → S.Lem0 S.Γ.W₀ → S.ResBound S.Γ.W₀ S.D.dsum := by
  intro hψ l _ P S hR h0 s c hc hi
  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hfinO : Module.Finite ℤ_[l] S.O :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥S.LL.1 ↥(integralClosure ℤ_[l] ↥S.LL.1)
  have hfa : FaithfulSMul ℤ_[l] S.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h1 : Function.Injective (algebraMap ℤ_[l] ↥S.LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥S.LL.1]
      exact (algebraMap ℚ_[l] ↥S.LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [IsScalarTower.algebraMap_eq ℤ_[l] S.O ↥S.LL.1, RingHom.coe_comp] at h1
    exact h1.of_comp
  obtain ⟨hst, -, hT1, hT2, hT3⟩ := S.hyp
  obtain ⟨hfin, k, _, _, hch, hs, hk⟩ := exists_residue l S.O S.Γ.lam hst.2.2.2.2.2
  obtain ⟨R, ι, hι, F, M, -, ⟨q, hq, hker, hqe⟩, hmod⟩ := hR k ⟨hs, hk⟩
  obtain ⟨z, hz, hli⟩ := exists_independent_admissible_cocycles_residue (P.PD S.K) S.emb S.Γ S.D hs hk F M q hq hker hqe hmod
    (@h0 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ) _ _ hfin).2.1 s c hc hi
  exact GlobalTheory.T.admissible_cocycles_card_le_sum_dims hψ F M ι hι hT1 hT2 hT3 s z hz hli

end GlobalTheory.ResidueBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAndKernelOfLetterImageTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAndKernelOfLetterImageTensor
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedDim

theorem count {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (g : M →ₗ[F] N) {r m s : ℕ} (v : Fin r → M) (V' : Submodule F M)
    (hle : V' ≤ Submodule.span F (Set.range v)) (hk : V' ≤ LinearMap.ker g) (hr : r ≤ m + s)
    (hm : m ≤ Module.finrank F ((Submodule.span F (Set.range v)).map g)) (hs : s ≤ Module.finrank F V') :
    Module.finrank F ((Submodule.span F (Set.range v)).map g) = m ∧
      Submodule.span F (Set.range v) ⊓ LinearMap.ker g = V' ∧ LinearIndependent F v := by
  set V := Submodule.span F (Set.range v) with hV
  haveI : FiniteDimensional F V := FiniteDimensional.span_of_finite F (Set.finite_range v)
  have h1 : Module.finrank F V ≤ r := (finrank_range_le_card (R := F) v).trans (Fintype.card_fin r).le
  have h2 := (g.domRestrict V).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h2
  haveI : FiniteDimensional F ↥(V ⊓ LinearMap.ker g) := Submodule.finiteDimensional_of_le inf_le_left
  have h3 : V' ≤ V ⊓ LinearMap.ker g := le_inf hle hk
  have h4 := Submodule.finrank_mono h3
  refine ⟨by omega, (Submodule.eq_of_le_of_finrank_le h3 (by omega)).symm, ?_⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin r) = Module.finrank F V
  rw [Fintype.card_fin]
  omega

section Abs

variable {F R EE : Type} [Field F] [CommRing R] [CommRing EE] (κ : F →+* R) (ρ : EE →+* R) (ε : R)

theorem mem_img (h1 : ∀ c, ∃ e, ε * κ c = ε * ρ e) {D N : Type} [AddCommGroup D] [Module EE D]
    [AddCommGroup N] [Module R N] [Module F N] (hκ : ∀ (c : F) (x : N), c • x = κ c • x)
    (J : D →+ N) (hJ : ∀ (e : EE) x, J (e • x) = ρ e • J x) {y : N}
    (hy : y ∈ Submodule.span F (Set.range fun x => ε • J x)) : ∃ x, y = ε • J x := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact ⟨x, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, rfl⟩ := hy; obtain ⟨x', rfl⟩ := hz
    exact ⟨x + x', by simp⟩
  | smul c y _ hy =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨e, he⟩ := h1 c
    exact ⟨e • x, by rw [hκ, hJ, smul_smul, smul_smul, mul_comm, he]⟩

theorem le_finrank {N : Type} [AddCommGroup N] [Module R N] [Module F N]
    (hκ : ∀ (c : F) (x : N), c • x = κ c • x) {D : Type} (w : D → N) (V : Submodule F N)
    [FiniteDimensional F V] (hw : ∀ x, w x ∈ V) {m : ℕ}
    (h : ∀ (t : ℕ) (u : Fin t → N), (∀ x, w x ∈ Submodule.span R (Set.range u)) → m ≤ t) :
    m ≤ Module.finrank F V := by
  let b := Module.finBasis F V
  refine h _ (fun j => (b j : N)) fun x => ?_
  have := congrArg Subtype.val (b.sum_repr ⟨w x, hw x⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  rw [← this]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hκ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem abs_main (h1 : ∀ c, ∃ e, ε * κ c = ε * ρ e) (h2 : ∀ e, ∃ c, ε * ρ e = ε * κ c)
    {D D' M N : Type} [AddCommGroup D] [Module EE D] [AddCommGroup D'] [Module EE D']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : D →+ M) (hJ : ∀ (e : EE) x, J (e • x) = ρ e • J x) (φ : D' →ₗ[EE] D) (g : M →ₗ[R] N)
    {r m s : ℕ} (b : Module.Basis (Fin r) EE D) (hg : ∀ y, g (J (φ y)) = 0) (hr : r ≤ m + s)
    (hm : ∀ (t : ℕ) (u : Fin t → N), (∀ x, ε • g (J x) ∈ Submodule.span R (Set.range u)) → m ≤ t)
    (hs : ∀ (t : ℕ) (u : Fin t → M), (∀ y, ε • J (φ y) ∈ Submodule.span R (Set.range u)) → s ≤ t) :
    (∃ u : Fin m → D, ∀ x, ∃ c : Fin m → F, ε • g (J x) = ∑ j, κ (c j) • ε • g (J (u j))) ∧
      ∀ x, ε • g (J x) = 0 → ∃ y, ∀ j, ε * ρ (b.repr (x - φ y) j) = 0 := by
  letI : Module F M := Module.compHom M κ
  letI : Module F N := Module.compHom N κ
  have hM : ∀ (c : F) (x : M), c • x = κ c • x := fun _ _ => rfl
  have hN : ∀ (c : F) (x : N), c • x = κ c • x := fun _ _ => rfl
  let gF : M →ₗ[F] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun c x => g.map_smul (κ c) x }
  have hgF : ∀ x, gF x = g x := fun _ => rfl
  let v : Fin r → M := fun j => ε • J (b j)
  choose cc hcc using h2
  have hexp : ∀ x, ε • J x = ∑ j, cc (b.repr x j) • v j := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr x, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ, hM, smul_smul, hcc, smul_smul, mul_comm]
  have hmem : ∀ x, ε • J x ∈ Submodule.span F (Set.range v) := fun x => by
    rw [hexp]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hback : ∀ y ∈ Submodule.span F (Set.range v), ∃ x, y = ε • J x := fun y hy =>
    mem_img κ ρ ε h1 hM J hJ (Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨b j, rfl⟩) hy)
  let J' : D' →+ M := J.comp φ.toAddMonoidHom
  let V' := Submodule.span F (Set.range fun y => ε • J' y)
  have hle : V' ≤ Submodule.span F (Set.range v) :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hmem _)
  have hk : V' ≤ LinearMap.ker gF := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    change g (ε • J (φ y)) = 0
    rw [map_smul, hg, smul_zero])
  haveI : FiniteDimensional F (Submodule.span F (Set.range v)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range v)
  haveI : FiniteDimensional F V' := Submodule.finiteDimensional_of_le hle
  have hmem' : ∀ x, ε • g (J x) ∈ (Submodule.span F (Set.range v)).map gF := fun x =>
    ⟨_, hmem x, by rw [hgF, map_smul]⟩
  obtain ⟨e1, e2, e3⟩ := count gF v V' hle hk hr
    (le_finrank κ hN (fun x => ε • g (J x)) _ hmem' hm)
    (le_finrank κ hM (fun y => ε • J (φ y)) V' (fun y => Submodule.subset_span (Set.mem_range_self y)) hs)
  constructor
  · let c := Module.finBasisOfFinrankEq F _ e1
    have hu : ∀ j, ∃ x, (c j : N) = ε • g (J x) := fun j => by
      obtain ⟨y, hy, e⟩ := (c j).2
      obtain ⟨x, rfl⟩ := hback y hy
      exact ⟨x, by rw [← e, hgF, map_smul]⟩
    choose u hu using hu
    refine ⟨u, fun x => ⟨fun j => c.repr ⟨_, hmem' x⟩ j, ?_⟩⟩
    have := congrArg Subtype.val (c.sum_repr ⟨_, hmem' x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hu, hN] at this
    exact this.symm
  · intro x hx
    have h3 : ε • J x ∈ V' := by
      rw [← e2]
      exact ⟨hmem x, by change g _ = 0; rw [map_smul, hx]⟩
    obtain ⟨y, hy⟩ := mem_img κ ρ ε h1 hM J' (fun e y => by
      change J (φ (e • y)) = _ • J (φ y); rw [map_smul, hJ]) h3
    refine ⟨y, fun j => ?_⟩
    have h4 : ε • J (x - φ y) = 0 := by rw [map_sub, smul_sub, hy]; exact sub_self _
    rw [hexp] at h4
    rw [hcc, Fintype.linearIndependent_iff.1 e3 _ h4 j, map_zero, mul_zero]

end Abs

section Comparison₂

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k]
    {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk)

theorem le_of_span (i : ZMod n) (h0 : eps E ρ i ≠ 0) (T : LocLat G Qp LL O) {m : ℕ}
    (q : ↥T.L.T →ₗ[O] (Fin m → k)) {s : ℕ} (b : Fin s → (Fin m → k)) (hb : LinearIndependent k b)
    (hq : ∀ j, ∃ x, q x = b j) (t : ℕ) (u : Fin t → Rk ⊗[k] (Fin m → k))
    (hu : ∀ x, eps E ρ i • J E ρ T q x ∈ Submodule.span Rk (Set.range u)) : s ≤ t := by
  refine card_le_of_span (eps_idem E ρ i) h0 u b hb fun j => ?_
  obtain ⟨x, hx⟩ := hq j
  have h1 : Submodule.span Rk (Set.range (J E ρ T q)) ≤
      (Submodule.span Rk (Set.range u)).comap (eps E ρ i • LinearMap.id) :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hu y)
  have h2 := h1 (J_span E ρ T q x)
  rw [hx] at h2
  simpa [TensorProduct.smul_tmul'] using h2

end Comparison₂

theorem dim_ker : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk), IsRed E ρ (k := k) lam κ → ∀ (T : LocLat G Qp LL O) (m : ℕ) (q : ↥T.L.T →ₗ[O] (Fin m → k)), Function.Surjective q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i, (∃ u : Fin m → W.DD T, ∀ x, ∃ c : Fin m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) ∧ ∀ h : LatHom T.L T'.L, (∀ x, f.f (h.f x) = algebraMap O LL lam • x) → ∀ x, eps E ρ i • J E ρ T q x = 0 → ∃ y, W.map f y = (letE i : LetA O n) • x := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W RA RW _ _ _ _
    inclR φR gR πA E k _ _ Rk _ _ _ _ ρ lam κ hR T m q hq T' f hf i
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI := (W.DD_free T).1
  haveI := GlobalTheory.EtaleExact.finite_DD E T
  haveI : Nontrivial W.EE := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply hR.eps_ne i
    rw [eps, Subsingleton.elim (algebraMap (LetA O n) W.EE (letE i)) 0, map_zero]
  set r := Module.finrank O ↥T.L.T with hr
  let t : Module.Basis (Fin r) O ↥T.L.T := Module.finBasis O _
  let b : Module.Basis (Fin r) W.EE (W.DD T) := Module.finBasisOfFinrankEq _ _ (W.DD_free T).2
  let qb : ↥T.L.T →ₗ[O] (Fin r → k) := t.constr O fun j => Pi.single j 1
  let g : (Fin r → k) →ₗ[k] (Fin m → k) := (Pi.basisFun k (Fin r)).constr k fun j => q (t j)
  have hgq : ∀ x, q x = g (qb x) := by
    have : q = (g.restrictScalars O) ∘ₗ qb := t.ext fun j => by
      have := (Pi.basisFun k (Fin r)).constr_basis k (fun j => q (t j)) j
      rw [Pi.basisFun_apply] at this
      simp only [LinearMap.comp_apply, qb, Module.Basis.constr_basis, LinearMap.restrictScalars_apply]
      exact this.symm
    intro x
    conv_lhs => rw [this]
    rfl
  have hqb : Function.Surjective qb := by
    intro y
    choose c hc using fun j => hR.res_surj (y j)
    refine ⟨∑ j, c j • t j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext a
    simp [qb, Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨_, (hgq x).symm⟩
  have hrk := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hg] at hrk
  simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
  let q' : ↥T'.L.T →ₗ[O] (Fin r → k) := qb ∘ₗ GlobalTheory.EtaleExact.latMap f
  have hJ' : ∀ y, J E ρ T qb (W.map f y) = J E ρ T' q' y := fun y => by
    rw [J_map E ρ f q' qb LinearMap.id (fun x x' e => congrArg qb (Subtype.ext e)), LinearMap.baseChange_id]
    rfl
  have hJ : ∀ x, g.baseChange Rk (J E ρ T qb x) = J E ρ T q x := fun x => (J_comp E ρ T qb q g hgq x).symm
  let cK := Module.finBasis k (LinearMap.ker g)
  obtain ⟨h1, h2⟩ := abs_main κ (rE E ρ) (eps E ρ i) (hR.κ_of i) (hR.of_κ i) (J E ρ T qb) (J_smul E ρ T qb)
    (W.map f) (g.baseChange Rk) (m := m) b (fun y => by
      rw [hJ, J_map E ρ f q' q 0 (fun x x' e => (hf x').2 ⟨x, x.2, e.symm⟩)]
      simp) hrk.ge
    (fun s u hu => le_of_span E ρ i (hR.eps_ne i) T q (Pi.basisFun k (Fin m))
      (Pi.basisFun k (Fin m)).linearIndependent (fun j => hq _) s u (fun x => hJ x ▸ hu x))
    (fun s u hu => le_of_span E ρ i (hR.eps_ne i) T' q' (fun j => (cK j : Fin r → k))
      (cK.linearIndependent.map' (LinearMap.ker g).subtype (Submodule.ker_subtype _)) (fun j => by
        obtain ⟨x, hx⟩ := hqb (cK j)
        obtain ⟨y, hy, e⟩ := (hf x).1 (by rw [hgq, hx]; exact (cK j).2)
        exact ⟨⟨y, hy⟩, hx ▸ congrArg qb (Subtype.ext e)⟩) s u (fun y => hJ' y ▸ hu y))
  simp only [hJ] at h1 h2
  refine ⟨h1, fun h hh x hx => ?_⟩
  obtain ⟨y, hy⟩ := h2 x hx
  choose e he using fun j => hR.ker i _ (hy j)
  have h3 : ∀ z, W.map f (W.map h z) = algebraMap O W.EE lam • z := fun z => by
    have : latComp f h = latSmul T lam := by
      have : f.f.comp h.f = algebraMap O LL lam • LinearMap.id := LinearMap.ext hh
      unfold latComp latSmul
      congr 1
    rw [← W.map_comp, this, W.map_latSmul, algebraMap_smul]
  have h4 : algebraMap (LetA O n) W.EE (letE i) • (x - W.map f y) =
      algebraMap O W.EE lam • ∑ j, e j • b j := by
    conv_lhs => rw [← b.sum_repr (x - W.map f y)]
    simp only [Finset.smul_sum, smul_smul, he]
  refine ⟨W.map h (∑ j, e j • b j) + algebraMap (LetA O n) W.EE (letE i) • y, ?_⟩
  rw [map_add (f := _), h3, ← h4, map_smul, ← smul_add, sub_add_cancel, algebraMap_smul]

end GlobalTheory.RedDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAndKernelOfLetterImageTensorStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_and_kernel_of_letter_image_tensor : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk), IsRed E ρ (k := k) lam κ → ∀ (T : LocLat G Qp LL O) (m : ℕ) (q : ↥T.L.T →ₗ[O] (Fin m → k)), Function.Surjective q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i, (∃ u : Fin m → W.DD T, ∀ x, ∃ c : Fin m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) ∧ ∀ h : LatHom T.L T'.L, (∀ x, f.f (h.f x) = algebraMap O LL lam • x) → ∀ x, eps E ρ i • J E ρ T q x = 0 → ∃ y, W.map f y = (letE i : LetA O n) • x := by
  first | exact @GlobalTheory.RedDim.dim_ker | exact GlobalTheory.RedDim.dim_ker | (intros; apply GlobalTheory.RedDim.dim_ker <;> assumption)
end
end

module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrysCopy
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleSequenceExact
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.HeckeCl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTowerHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AnnModel
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.PBTied
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AwayEq
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem cp_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[l] →+* ℂ_[l]) = galCp τ :=
  RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]) x

private theorem ainf_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (cp_eq σ τ h) _ _

private theorem away_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galAway σ = ACris.galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, ainf_eq σ τ h])

private theorem cris_eq {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galCris σ = ACris.galCris τ := by
  have e : ACris.galZero σ = ACris.galZero τ := RingHom.ext fun y => Subtype.ext (by
    rw [ACris.coe_galZero, ACris.coe_galZero, away_eq σ τ h])
  rw [ACris.galCris, ACris.galCris, e]

theorem actEq : ActEq := by
  intro l _
  refine ⟨fun K g x => ?_, fun z => ?_⟩
  · exact RingHom.congr_fun (cris_eq _ _ fun _ => rfl) x
  · have h : (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)).comp ((Formalism.Per6.ainfMap l).comp (Formalism.Per6.zA l)) = zA l :=
      ringHom_ext_padicInt _ _
    exact congrArg (Formalism.Per6.cB l) (RingHom.congr_fun h z)

end UpperTheory.Gal.crystallineComparison.Br
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.LocFacts
open Formalism.Per6 in
private theorem exists_finset_adjoin_laurent_preimage {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (x : Loc2 a t) : ∃ (k : ℕ) (y : A), Loc2.mk₀ a t t ^ k * x = Loc2.mk₀ a t y := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj
    (algebraMap A (Localization.Away a) t) (S := Localization.Away (algebraMap A (Localization.Away a) t)) x
  obtain ⟨m, y, hy⟩ := IsLocalization.Away.surj a (S := Localization.Away a) b
  have hb' : x * Loc2.mk₀ a t t ^ n = Loc2.mk₁ a t b := hb
  have hy' : Loc2.mk₁ a t b * Loc2.mk₀ a t a ^ m = Loc2.mk₀ a t y := by
    have := congrArg (Loc2.mk₁ a t) hy
    simpa [Loc2.mk₀] using this
  refine ⟨r * m + n, y * c ^ m, ?_⟩
  have hT : Loc2.mk₀ a t t ^ r = Loc2.mk₀ a t a * Loc2.mk₀ a t c := by
    rw [← map_pow, hc, map_mul]
  rw [map_mul, map_pow, ← hy', ← hb', pow_add, pow_mul, hT, mul_pow]
  ring

open Formalism.Per6 in
private theorem exists_pow_kill_of_localization_zero {A : Type} [CommRing A] (a t c : A) (r : ℕ) (hc : t ^ r = a * c)
    (y : A) (hy : Loc2.mk₀ a t y = 0) : ∃ k : ℕ, t ^ k * y = 0 := by
  have h1 : algebraMap (Localization.Away a) (Localization.Away (algebraMap A (Localization.Away a) t))
      (algebraMap A (Localization.Away a) y) = 0 := hy
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap A (Localization.Away a) t)) _ _).1 h1
  have h2 : algebraMap A (Localization.Away a) (t ^ k * y) = 0 := by
    simpa [map_mul, map_pow] using hk
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).1 h2
  refine ⟨r * m + k, ?_⟩
  have hm' : a ^ m * (t ^ k * y) = 0 := hm
  calc t ^ (r * m + k) * y = c ^ m * (a ^ m * (t ^ k * y)) := by
        rw [pow_add, pow_mul, hc, mul_pow]; ring
    _ = 0 := by rw [hm', mul_zero]

theorem UpperTheory.Gal.crystallineComparison.Br.locFacts :
    UpperTheory.Gal.crystallineComparison.Br.LocFacts := by
  intro A _ a t ⟨r, c, hc⟩
  exact ⟨exists_finset_adjoin_laurent_preimage a t c r hc, exists_pow_kill_of_localization_zero a t c r hc⟩
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison GroundTheory.PAdicHodge

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem l_dvd : ∃ r : ℕ, (l : Acris l) ∣ tA l ^ r := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1
    (ACris.periodT_pow_mem' (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l)))
  exact ⟨l - 1, u, by rw [tA, ← hu, mul_comm]⟩

private def cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : Acris l →+* P.R.B :=
  T.eB.symm.toRingHom.comp (Formalism.Per6.cB l)

private theorem eB_cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    T.eB (cT T a) = Formalism.Per6.cB l a :=
  T.eB.apply_symm_apply _

private theorem cT_unit {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : IsUnit (cT T (tA l)) :=
  (Formalism.Per6.Loc2.isUnit_right (l : Acris l) (tA l)).map T.eB.symm

private theorem cT_loc {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : P.R.B) :
    ∃ (r : ℕ) (a : Acris l), cT T (tA l) ^ r * x = cT T a := by
  obtain ⟨r, y, h⟩ := (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).1 (T.eB x)
  refine ⟨r, y, T.eB.injective ?_⟩
  rw [map_mul, map_pow, eB_cT, eB_cT]
  exact h

private theorem cT_ker {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l)
    (h : cT T a = 0) : ∃ r : ℕ, tA l ^ r * a = 0 := by
  refine (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).2 a ?_
  have h1 := eB_cT T a
  rw [h, map_zero] at h1
  exact h1.symm

private theorem cT_φ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    P.φB (cT T a) = cT T (phiA l a) := by
  refine T.eB.injective ?_
  rw [T.frob, eB_cT, eB_cT]
  exact PositivityTheory.LocInh.φB_cB a

private theorem cT_σ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (a : Acris l) :
    P.actQ g.1 (cT T a) = cT T (galA g a) := by
  refine T.eB.injective ?_
  rw [T.actB, eB_cT, eB_cT, ((actEq l).1 K g a)]
  exact PositivityTheory.LocInh.σB_cB _ a

private theorem algebraMap_padic_int_eq_period {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : ℤ_[l]) :
    algebraMap ℚ_[l] P.R.B (x : ℚ_[l]) = cT T (zA l x) := by
  refine T.eB.injective ?_
  rw [T.zB, eB_cT]
  exact (actEq l).2 x

private def pullbackToFiniteExtension {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) : PB l K.1 where
  C := P.R.B
  c := cT T
  φ := P.φB
  σ g := (P.actQ g.1).toAlgHom
  t_unit := cT_unit T
  loc := cT_loc T
  ker := cT_ker T
  φ_c := cT_φ T
  σ_c := cT_σ T K.1
  z_c := algebraMap_padic_int_eq_period T

theorem pBTied : PBTied := by
  intro l _ P AI hT K
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  exact ⟨pullbackToFiniteExtension T K, AlgEquiv.refl, fun _ _ => rfl, fun _ => rfl, PositivityTheory.LocInh.tiedA_φ_injective P⟩

end UpperTheory.Gal.crystallineComparison.Br
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AnnDrop
noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison.Br

theorem annDrop : AnnDrop := by
  intro F G B C _ _ _ _ _ _ σ φ s ψ e hσ hφ hψ V _ _ V₀ _ _ i act ρ hρ f q n N A T hT hrel x hx
  rw [mem_Dinv] at hx
  have hpow : ∀ (m : ℕ) (b : B), e ((φ.toLinearMap ^ m) b) = (ψ.toLinearMap ^ m) (e b) := by
    intro m
    induction m with
    | zero => intro b; simp
    | succ m ih =>
      intro b
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact hφ _
  let Φ : V₀ ⊗[F] B ≃ₗ[F] V ⊗[F] C := TensorProduct.congr i.symm e.toLinearEquiv
  have hcomm : ∀ (a : End F V₀) (a' : End F V) (b : End F B) (b' : End F C),
      (∀ v, i.symm (a v) = a' (i.symm v)) → (∀ y, e (b y) = b' (e y)) →
      ∀ z, Φ (AlgebraTensorModule.map a b z) = TensorProduct.map a' b' (Φ z) := by
    intro a a' b b' ha hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v y =>
      simp only [Φ, AlgebraTensorModule.map_tmul, TensorProduct.congr_tmul, TensorProduct.map_tmul]
      rw [ha v]
      congr 1
      exact hb y
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hinv : ∀ g, TensorProduct.map (act g) (s g).toLinearMap (Φ x) = Φ x := by
    intro g
    rw [← hcomm (ρ g) (act g) (σ g) (s g).toLinearMap ?_ (hσ g) x, hx g]
    intro v
    have h := hρ g (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  have hsum := hrel (Φ x) hinv
  have hinj : Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (ψ.toLinearMap ^ (f * N))) := by
    have h0 : Function.Injective (ψ.toLinearMap ^ (f * N)) := by
      rw [Module.End.coe_pow]
      exact Function.Injective.iterate hψ _
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h0
  have hz : ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) •
      TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j))) (Φ x) = 0 := by
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, ← Module.End.mul_eq_comp,
      ← pow_add]
    congr 3
    ring
  apply Φ.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum, Finset.sum_range, ← hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [hcomm (T j) (A j) ((φ.toLinearMap ^ f) ^ (n - (j : ℕ))) (ψ.toLinearMap ^ (f * (n - j))) ?_ ?_ x]
  · intro v
    have h := hT j (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  · intro y
    rw [← pow_mul]
    exact hpow _ y

end UpperTheory.Gal.crystallineComparison.Br
end
end

theorem UpperTheory.Gal.crystallineComparison.Br.annModel :
    UpperTheory.Gal.crystallineComparison.Br.AnnModel := by
  intro hF l _ P AI hT K _ _ f hf hc ϖ hϖ M hM n j T hr hP A hA V₀ _ _ i ρ hρ T₀ hT₀
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨B, e, heσ, heφ, hinj⟩ := UpperTheory.Gal.crystallineComparison.Br.pBTied l P AI hT K
  obtain ⟨N, hN⟩ := hF l K.1 f hf hc ϖ hϖ M hM n j T hr hP A hA B
  exact UpperTheory.Gal.crystallineComparison.Br.annDrop ℚ_[l] _ _ _ (UpperTheory.Gal.crystallineComparison.σCr P K) P.φB B.σ B.φ e heσ heφ hinj
    (M.V j) V₀ i (fun g => M.act j g) ρ hρ f (l ^ f) n N A T₀ hT₀ hN
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AdmissiblePi
noncomputable section

open TensorProduct Module Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Ru.crystallineComparison

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
  {I : Type} [Fintype I] {V : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]

private def prI (B : Type) [AddCommGroup B] [Module F B] (i : I) : (∀ i, V i) ⊗[F] B →ₗ[F] V i ⊗[F] B :=
  AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id

private theorem prI_map (i : I) (a : (∀ i, V i) →ₗ[F] (∀ i, V i)) (b : V i →ₗ[F] V i) (c : B →ₗ[F] B)
    (h : ∀ x, a x i = b (x i)) (x : (∀ i, V i) ⊗[F] B) :
    prI B i (AlgebraTensorModule.map a c x) = AlgebraTensorModule.map b c (prI B i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [prI, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]


open Classical in
private def inI (B : Type) [AddCommGroup B] [Module F B] (i : I) : V i ⊗[F] B →ₗ[F] (∀ i, V i) ⊗[F] B :=
  AlgebraTensorModule.map (LinearMap.single F V i) LinearMap.id

private theorem sum_inI_prI (x : (∀ i, V i) ⊗[F] B) : ∑ i, inI B i (prI B i x) = x := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
    simp only [prI, inI, AlgebraTensorModule.map_tmul, LinearMap.proj_apply, LinearMap.id_apply, LinearMap.coe_single]
    rw [← TensorProduct.sum_tmul, Finset.univ_sum_single]
  | add x y hx hy => simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]

private theorem prI_inI_same (i : I) (y : V i ⊗[F] B) : prI B i (inI B i y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [prI, inI]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem prI_inI_ne {i j : I} (h : j ≠ i) (y : V j ⊗[F] B) : prI B i (inI B j y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [prI, inI, Pi.single_eq_of_ne (Ne.symm h)]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

private theorem ext_prI {x y : (∀ i, V i) ⊗[F] B} (h : ∀ i, prI B i x = prI B i y) : x = y := by
  rw [← sum_inI_prI x, ← sum_inI_prI y]; simp only [h]

variable (σ : G → End F B) (ρ : ∀ i, Representation F G (V i)) (ρ' : Representation F G (∀ i, V i))

private theorem mem_Dinv_pi (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) (x : (∀ i, V i) ⊗[F] B) :
    x ∈ Dinv σ ρ' ↔ ∀ i, prI B i x ∈ Dinv σ (ρ i) := by
  simp only [mem_Dinv]
  constructor
  · intro h i g
    rw [← prI_map i (ρ' g) (ρ i g) (σ g) (fun x => hρ g x i), h]
  · intro h g
    refine ext_prI fun i => ?_
    rw [prI_map i (ρ' g) (ρ i g) (σ g) (fun x => hρ g x i), h]

private def dinvPi (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) : Dinv σ ρ' ≃ₗ[F] ∀ i, Dinv σ (ρ i) :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun i => ((prI B i).comp (Dinv σ ρ').subtype).codRestrict (Dinv σ (ρ i))
      fun x => (mem_Dinv_pi σ ρ ρ' hρ x).1 x.2 i)
    (by
      constructor
      · intro x y h
        exact Subtype.ext (ext_prI fun i => congrArg Subtype.val (congrFun h i))
      · intro y
        classical
        have hc : ∀ i, prI B i (∑ j, inI B j (y j : V j ⊗[F] B)) = y i := by
          intro i
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_eq_single i (fun j _ h => prI_inI_ne h _) (by simp), prI_inI_same]
        refine ⟨⟨∑ j, inI B j (y j : V j ⊗[F] B), (mem_Dinv_pi σ ρ ρ' hρ _).2 fun i => ?_⟩, ?_⟩
        · rw [hc]; exact (y i).2
        · funext i
          exact Subtype.ext (hc i))

private theorem adm_pi_rep_of_forall_adm_of_pos [∀ i, Module.Finite F (V i)] (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) {e : ℕ} (he : 0 < e)
    (h : ∀ i, admitted σ e (ρ i)) : admitted σ e ρ' := by
  have hfin : ∀ i, Module.Finite F (Dinv σ (ρ i)) := by
    intro i
    by_cases h0 : finrank F (V i) = 0
    · have : Subsingleton (V i) := Module.finrank_zero_iff.1 h0
      have : Subsingleton (V i ⊗[F] B) := by
        refine ⟨fun a b => ?_⟩
        have hz : ∀ c : V i ⊗[F] B, c = 0 := by
          intro c
          induction c using TensorProduct.induction_on with
          | zero => rfl
          | tmul v y => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add x y hx hy => rw [hx, hy, add_zero]
        rw [hz a, hz b]
      infer_instance
    · exact Module.finite_of_finrank_pos (by rw [h i]; exact Nat.mul_pos he (Nat.pos_of_ne_zero h0))
  unfold admitted at *
  rw [(dinvPi σ ρ ρ' hρ).finrank_eq, Module.finrank_pi_fintype, Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

private theorem annD_pi (ψ : End F B) (q n : ℕ) (T : ∀ i, ℕ → End F (V i)) (T' : ℕ → End F (∀ i, V i))
    (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) (hT : ∀ j x i, T' j x i = T i j (x i))
    (h : ∀ i, AnnD σ ψ q n (ρ i) (T i)) : AnnD σ ψ q n ρ' T' := by
  intro x hx
  refine ext_prI fun i => ?_
  have := h i _ ((mem_Dinv_pi σ ρ ρ' hρ x).1 hx i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, prI_map i (T' j) (T i j) (ψ ^ (n - j)) (fun x => hT j x i)]

end

end UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.annPi :
    UpperTheory.Ru.crystallineComparison.AnnPi := by
  intro l _ P K I _ V _ _ _ ρ f q n T ρ' T' hρ hT
  refine ⟨fun h => ?_, fun h => annD_pi _ ρ ρ' _ q n T T' hρ hT h⟩
  have he : 0 < finrank ℚ_[l] ↥(K0 K) := by
    have := (P.PD K).finK₀
    exact Module.finrank_pos
  exact adm_pi_rep_of_forall_adm_of_pos (fun g => (((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) ρ ρ' hρ he h
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ExistsGlRep
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison Module

namespace UpperTheory.Ru.crystallineComparison

private theorem exists_glRep {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] {a : ℕ}
    (b : Basis (Fin a) k V) (π : Representation k G V) :
    ∃ r : G →* GL (Fin a) k, ∀ g, (r g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix b b (π g) := by
  let f : G →* Matrix (Fin a) (Fin a) k :=
    { toFun := fun g => LinearMap.toMatrix b b (π g)
      map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.toMatrix_mul b _ _ }
  exact ⟨f.toHomUnits, fun g => MonoidHom.coe_toHomUnits f g⟩

private noncomputable def actRep {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ) :
    Representation ℚ_[l] K.fixingSubgroup (M.V n) :=
  (GlobalTheory.EtC.galHQ l (PadicAlgCl l) M.q n 0).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.crysCopy :
    UpperTheory.Ru.crystallineComparison.CrysCopy := by
  intro hC l _ P AI hT K M hM j a b
  haveI := K.2
  obtain ⟨FreeQuotientRank⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  obtain ⟨T⟩ := hT
  have hadm := UpperTheory.Gal.Seam.isAdmP_of_isAdm FreeQuotientRank (hC l K.1 M hM.1 hM.2 j a b)
  obtain ⟨r, hr⟩ : ∃ r : ↥(GK K) →* GL (Fin a) ℚ_[l], ∀ g : ↥(GK K),
      (r g : Matrix (Fin a) (Fin a) ℚ_[l]) = LinearMap.toMatrix b b (M.act j g) := exists_glRep b (actRep M j)
  have hadm' : UpperTheory.Gal.Seam.IsAdmP P (GK K) (fun σ => (r σ : Matrix (Fin a) (Fin a) ℚ_[l])) := by
    have h0 : (fun σ : ↥(GK K) => (r σ : Matrix (Fin a) (Fin a) ℚ_[l])) = (M.mat j b : ↥(GK K) → _) := funext hr
    rw [h0]
    exact hadm
  let r' : ↥(GK K) →* GL (Fin a) ↥K.1 :=
    (Units.map (RingHom.mapMatrix (algebraMap ℚ_[l] ↥K.1)).toMonoidHom).comp r
  have hr' : ∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥K.1 ((r σ).val i j) := fun σ i j => rfl
  have hc := UpperTheory.Gal.Seam.isCrys_of_isAdmP l P AI T K K a r r' hr' hadm'
  have hcρ : WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
      ((Units.coeHom _).comp r) : Representation ℚ_[l] ↥(GK K) (Fin a → ℚ_[l])) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD K) (fun g => ⟨(r g : Matrix (Fin a) (Fin a) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).1 hc
  refine ⟨_, fun g v => ?_, hcρ⟩
  show (r g : Matrix (Fin a) (Fin a) ℚ_[l]).mulVec (b.equivFun v) = b.equivFun (M.act j g v)
  rw [hr g]
  simpa using LinearMap.toMatrix_mulVec_repr b b (M.act j g) v
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison
open GlobalTheory.GalV (HTower Htot hop galV galTot pullTot)
open Module TensorProduct

section Alg

open TensorProduct

private theorem deg_bound {F L : Type*} [Field F] [Field L] [Algebra F L] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module F (A n)] (hneg : ∀ n : ℤ, n < 0 → Subsingleton (A n)) (y : L ⊗[F] DirectSum ℤ A) :
    ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      y ∈ Submodule.baseChange L (⨆ j : Fin N', LinearMap.range (DirectSum.lof F ℤ A ((j : ℕ) : ℤ))) := by
  have hx : ∀ x : DirectSum ℤ A, ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      x ∈ ⨆ j : Fin N', LinearMap.range (DirectSum.lof F ℤ A ((j : ℕ) : ℤ)) := fun x => by
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, fun _ _ => zero_mem _⟩
    | of i z =>
      rcases lt_or_ge i 0 with hi | hi
      · haveI := hneg i hi
        refine ⟨0, fun _ _ => ?_⟩
        rw [Subsingleton.elim z 0, map_zero]
        exact zero_mem _
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        refine ⟨k + 1, fun N' hN' => ?_⟩
        exact Submodule.mem_iSup_of_mem (⟨k, by omega⟩ : Fin N') ⟨z, rfl⟩
    | add a b ha hb =>
      obtain ⟨Na, ha⟩ := ha
      obtain ⟨Nb, hb⟩ := hb
      exact ⟨max Na Nb, fun N' h => add_mem (ha N' (le_trans (le_max_left _ _) h)) (hb N' (le_trans (le_max_right _ _) h))⟩
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, fun _ _ => zero_mem _⟩
  | tmul t x =>
    obtain ⟨N, hN⟩ := hx x
    exact ⟨N, fun N' h => Submodule.tmul_mem_baseChange_of_mem t (hN N' h)⟩
  | add a b ha hb =>
    obtain ⟨Na, ha⟩ := ha
    obtain ⟨Nb, hb⟩ := hb
    exact ⟨max Na Nb, fun N' h => add_mem (ha N' (le_trans (le_max_left _ _) h)) (hb N' (le_trans (le_max_right _ _) h))⟩

private theorem exists_lin {F L : Type*} [Field F] [Field L] [Algebra F L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (hy : ∀ i, y i ∈ LinearMap.range (Φ.baseChange L)) :
    ∃ b : (Fin a → L) →ₗ[L] L ⊗[F] V, ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i := by
  choose w hw using hy
  refine ⟨Fintype.linearCombination L w, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, hw]

private theorem lin_inj {F L : Type*} [Field F] [Field L] [Algebra F L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) {a : ℕ} (y : Fin a → L ⊗[F] W) (hl : LinearIndependent L y)
    (b : (Fin a → L) →ₗ[L] L ⊗[F] V) (hb : ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i) : Function.Injective b := by
  refine (injective_iff_map_eq_zero b).2 fun x hx => ?_
  have h0 : ∑ i, x i • y i = 0 := by rw [← hb, hx, map_zero]
  funext i
  exact Fintype.linearIndependent_iff.1 hl x h0 i

private theorem lin_equiv {F L : Type*} [Field F] [Field L] [Algebra F L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) (hΦ : Function.Injective (Φ.baseChange L)) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (b : (Fin a → L) →ₗ[L] L ⊗[F] V) (hb : ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i)
    (r : V →ₗ[F] V) (g : W →ₗ[F] W) (hc : g ∘ₗ Φ = Φ ∘ₗ r) (R : Matrix (Fin a) (Fin a) L)
    (hR : ∀ j, g.baseChange L (y j) = ∑ i, R i j • y i) (x : Fin a → L) :
    b (R.mulVec x) = r.baseChange L (b x) := by
  apply hΦ
  have h1 : Φ.baseChange L (r.baseChange L (b x)) = g.baseChange L (Φ.baseChange L (b x)) := by
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange L) hc) (b x)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, hb, hb, map_sum]
  simp only [map_smul, hR, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

private theorem lin_eig {F L : Type*} [Field F] [Field L] [Algebra F L] [CharZero L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) (hΦ : Function.Injective (Φ.baseChange L)) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (b : (Fin a → L) →ₗ[L] L ⊗[F] V) (hb : ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i)
    (t : V →ₗ[F] V) (h : W →ₗ[F] W) (m : ℕ) (hm : m ≠ 0) (hc : h ∘ₗ Φ = (m : F) • (Φ ∘ₗ t)) (θ ϑ : L) (hθ : θ = m * ϑ)
    (hy : ∀ i, h.baseChange L (y i) = θ • y i) (x : Fin a → L) :
    t.baseChange L (b x) = ϑ • b x := by
  apply hΦ
  have h1 : h.baseChange L (Φ.baseChange L (b x)) = (m : L) • Φ.baseChange L (t.baseChange L (b x)) := by
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange L) hc) (b x)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_smul, LinearMap.baseChange_comp] at this
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply] at this
    rw [this, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have h2 : h.baseChange L (Φ.baseChange L (b x)) = θ • Φ.baseChange L (b x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hb, map_sum]
    simp only [map_smul, hy, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [h2, hθ, mul_smul] at h1
  have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [map_smul]
  exact (smul_right_injective _ hm' h1).symm

private theorem sum_comp {F : Type*} [Field F] {I : Type*} [Fintype I] [DecidableEq I] {U : I → Type*} [∀ i, AddCommGroup (U i)]
    [∀ i, Module F (U i)] {W : Type*} [AddCommGroup W] [Module F W] (φ : ∀ i, U i →ₗ[F] W) (h : W →ₗ[F] W)
    (c : F) (t : ∀ i, U i →ₗ[F] U i) (t' : (∀ i, U i) →ₗ[F] ∀ i, U i) (ht : ∀ x i, t' x i = t i (x i))
    (hc : ∀ i, h ∘ₗ φ i = c • (φ i ∘ₗ t i)) :
    h ∘ₗ (∑ i, φ i ∘ₗ LinearMap.proj i) = c • ((∑ i, φ i ∘ₗ LinearMap.proj i) ∘ₗ t') := by
  refine LinearMap.ext fun x => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply, map_sum, ht, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    have := LinearMap.congr_fun (hc i) (x i)
    simpa using this

private def piRep {F G : Type*} [Field F] [Group G] {I : Type*} {U : I → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module F (U i)]
    (ρ : ∀ i, Representation F G (U i)) : Representation F G (∀ i, U i) where
  toFun g := LinearMap.pi fun i => ρ i g ∘ₗ LinearMap.proj i
  map_one' := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp

end Alg

section Alg2

open TensorProduct

private theorem e_facts {F : Type*} [Field F] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)] (N : ℕ)
    (d : Fin N → ℕ) (β : ∀ i : Fin N, Module.Basis (Fin (d i)) F (A ((i : ℕ) : ℤ)))
    (e : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] DirectSum ℤ A)
    (he : e = ∑ i : Fin N, (DirectSum.lof F ℤ A ((i : ℕ) : ℤ)) ∘ₗ (β i).equivFun.symm.toLinearMap ∘ₗ LinearMap.proj i) :
    Function.Injective e ∧ (⨆ j : Fin N, LinearMap.range (DirectSum.lof F ℤ A ((j : ℕ) : ℤ))) ≤ LinearMap.range e := by
  classical
  constructor
  · refine (injective_iff_map_eq_zero e).2 fun x hx => ?_
    funext i
    have h1 : DirectSum.component F ℤ A ((i : ℕ) : ℤ) (e x) = (β i).equivFun.symm (x i) := by
      rw [he]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
      rw [Finset.sum_eq_single i]
      · simp [DirectSum.component.lof_self]
      · intro k _ hk
        have hne : ((i : ℕ) : ℤ) ≠ ((k : ℕ) : ℤ) := fun h => hk (Fin.ext (by exact_mod_cast h.symm))
        simp [DirectSum.component.of, hne]
        intro h
        exact absurd (Fin.ext h) hk
      · simp
    rw [hx, map_zero] at h1
    have := (β i).equivFun.symm.injective (h1.symm.trans (map_zero _).symm)
    simpa using this
  · refine iSup_le fun j => ?_
    rintro _ ⟨v, rfl⟩
    refine ⟨Pi.single j ((β j).equivFun v), ?_⟩
    rw [he]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp

private theorem comp_facts {F L : Type*} [Field F] [Field L] [Algebra F L] {V D W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup D] [Module F D] [AddCommGroup W] [Module F W] (e : V →ₗ[F] D) (he : Function.Injective e)
    (p : D →ₗ[F] W) (hp : Function.Injective (p.baseChange L)) :
    Function.Injective ((p ∘ₗ e).baseChange L) ∧
      ∀ (P : Submodule F D), P ≤ LinearMap.range e → ∀ z ∈ P.baseChange L,
        p.baseChange L z ∈ LinearMap.range ((p ∘ₗ e).baseChange L) := by
  have hc : (p ∘ₗ e).baseChange L = p.baseChange L ∘ₗ e.baseChange L := LinearMap.baseChange_comp _ _
  refine ⟨?_, fun P hP z hz => ?_⟩
  · rw [hc]
    have h2 : Function.Injective (e.baseChange L) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap e he
    exact hp.comp h2
  · have h3 : z ∈ LinearMap.range (e.baseChange L) := by
      have h4 : P.baseChange L ≤ LinearMap.range (e.baseChange L) := by
        rw [Submodule.baseChange_eq_span, Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨v, rfl⟩ := hP hx
        exact ⟨(1 : L) ⊗ₜ[F] v, by simp⟩
      exact h4 hz
    obtain ⟨w, rfl⟩ := h3
    exact ⟨w, by rw [hc]; rfl⟩

end Alg2

section Core

open TensorProduct

private theorem core {F L : Type*} [Field F] [Field L] [Algebra F L] [CharZero L] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module F (A n)] (hneg : ∀ n : ℤ, n < 0 → Subsingleton (A n)) {W : Type*} [AddCommGroup W] [Module F W]
    (p : DirectSum ℤ A →ₗ[F] W) (hp : Function.Injective (p.baseChange L)) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (hl : LinearIndependent L y) (hy : ∀ i, y i ∈ LinearMap.range (p.baseChange L)) :
    ∃ N : ℕ, ∀ (d : Fin N → ℕ) (β : ∀ i : Fin N, Module.Basis (Fin (d i)) F (A ((i : ℕ) : ℤ))),
      ∃ b : (Fin a → L) →ₗ[L] L ⊗[F] (∀ i : Fin N, Fin (d i) → F), Function.Injective b ∧
        (∀ (r : ∀ i : Fin N, (Fin (d i) → F) →ₗ[F] (Fin (d i) → F))
          (r' : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] ∀ i : Fin N, Fin (d i) → F), (∀ x i, r' x i = r i (x i)) →
          ∀ g : W →ₗ[F] W, (∀ (i : Fin N) u, g (p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm u))) =
            p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm (r i u)))) →
          ∀ R : Matrix (Fin a) (Fin a) L, (∀ j, g.baseChange L (y j) = ∑ i, R i j • y i) →
          ∀ x, b (R.mulVec x) = r'.baseChange L (b x)) ∧
        (∀ (t : ∀ i : Fin N, (Fin (d i) → F) →ₗ[F] (Fin (d i) → F))
          (t' : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] ∀ i : Fin N, Fin (d i) → F), (∀ x i, t' x i = t i (x i)) →
          ∀ (h : W →ₗ[F] W) (m : ℕ), m ≠ 0 → (∀ (i : Fin N) u, h (p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm u))) =
            (m : F) • p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm (t i u)))) →
          ∀ θ ϑ : L, θ = m * ϑ → (∀ i, h.baseChange L (y i) = θ • y i) →
          ∀ x, t'.baseChange L (b x) = ϑ • b x) := by
  classical
  choose z hz using hy
  choose Nf hNf using fun i => deg_bound (F := F) (L := L) hneg (z i)
  refine ⟨Finset.univ.sup Nf, fun d β => ?_⟩
  have hle : ∀ i, Nf i ≤ Finset.univ.sup Nf := fun i => Finset.le_sup (f := Nf) (Finset.mem_univ i)
  generalize Finset.univ.sup Nf = N at d β hle
  let e : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] DirectSum ℤ A :=
    ∑ i : Fin N, (DirectSum.lof F ℤ A ((i : ℕ) : ℤ)) ∘ₗ (β i).equivFun.symm.toLinearMap ∘ₗ LinearMap.proj i
  obtain ⟨heI, heR⟩ := e_facts N d β e rfl
  obtain ⟨hΦ, hR⟩ := comp_facts (L := L) e heI p hp
  let φ : ∀ i : Fin N, (Fin (d i) → F) →ₗ[F] W := fun i =>
    p ∘ₗ (DirectSum.lof F ℤ A ((i : ℕ) : ℤ)) ∘ₗ (β i).equivFun.symm.toLinearMap
  have hφ : p ∘ₗ e = ∑ i : Fin N, φ i ∘ₗ LinearMap.proj i := by
    refine LinearMap.ext fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp [e, φ, map_sum]
  have hy' : ∀ i, y i ∈ LinearMap.range ((p ∘ₗ e).baseChange L) := fun i => by
    rw [← hz i]
    exact hR _ heR _ (hNf i N (hle i))
  obtain ⟨b, hb⟩ := exists_lin (L := L) (p ∘ₗ e) y hy'
  refine ⟨b, lin_inj (p ∘ₗ e) y hl b hb, fun r r' hr g hg R hRg x => ?_, fun t t' ht h m hm hh θ ϑ hθ hyh x => ?_⟩
  · have hc : g ∘ₗ (p ∘ₗ e) = (p ∘ₗ e) ∘ₗ r' := by
      have := sum_comp φ g (1 : F) r r' hr (fun i => LinearMap.ext fun u => by
        simpa [φ] using hg i u)
      rw [one_smul, ← hφ] at this
      exact this
    exact lin_equiv (p ∘ₗ e) hΦ y b hb r' g hc R hRg x
  · have hc : h ∘ₗ (p ∘ₗ e) = (m : F) • ((p ∘ₗ e) ∘ₗ t') := by
      have := sum_comp φ h (m : F) t t' ht (fun i => LinearMap.ext fun u => by
        simpa [φ] using hh i u)
      rw [← hφ] at this
      exact this
    exact lin_eig (p ∘ₗ e) hΦ y b hb t' h m hm hc θ ϑ hθ hyh x

end Core

private theorem basis_rel {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {d : ℕ} (β : Module.Basis (Fin d) F V)
    (r : (Fin d → F) →ₗ[F] (Fin d → F)) (s : V →ₗ[F] V) (h : ∀ v, r (β.equivFun v) = β.equivFun (s v)) (u : Fin d → F) :
    s (β.equivFun.symm u) = β.equivFun.symm (r u) := by
  have h1 := h (β.equivFun.symm u)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1, LinearEquiv.symm_apply_apply]

private theorem gal_inTot {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (j : ℕ)
    (g : K.fixingSubgroup) (v : M.V j) :
    galTot l (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K g) (Br.inTot M j v) = Br.inTot M j (M.act j g v) :=
  DirectSum.lmap_lof _ _ _

theorem UpperTheory.Ru.crystallineComparison.geoLoc :
    UpperTheory.Ru.crystallineComparison.GeoLoc := by
  intro hF hCr l _ P AI hT K _ _ f hf hc H θ hN C hOn n ϑ hCg a ρ₁ hMat
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨hinj, hle, heq⟩ := UpperTheory.Gal.Seam.pieceIn_holds l K.1 (Om l) H θ hN C hOn
  have hSm : (mod C).Sm := ⟨goodOf l K.1 (mod C) C.smooth C.proj, C.smooth⟩
  have hfin : ∀ j, FiniteDimensional ℚ_[l] ((mod C).V j) := fun j => (UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K.1).fin (mod C) hSm j
  obtain ⟨ϖ, Tc, γ, m, hϖ, hPt, hTc⟩ := hCg
  have hr : ∀ i, (Tc i).r ≫ (mod C).p = (Tc i).p ≫ (mod C).p := fun i => (hTc i).1
  have hA : ∀ i, ∃ A : ∀ j : ℕ, (mod C).V j →ₗ[ℚ_[l]] (mod C).V j, ∀ j, IsHk (mod C) (Tc i) (hr i) j (A j) ∧
      ∀ v, hop l H (PadicAlgCl l) (γ i) (pullTot l (sch.map (toMod C)) (Br.inTot (mod C) j v)) =
        (m i : ℚ_[l]) • pullTot l (sch.map (toMod C)) (Br.inTot (mod C) j (A j v)) := fun i => by
    obtain ⟨d, hd⟩ := hN.2.2 (γ i)
    exact Br.heckeCl l K.1 (Om l) H θ C (Tc i) (hr i) (γ i) (m i) d hd (hTc i).2.1
  choose A hAk using hA
  obtain ⟨b₀, hb₀⟩ := hMat
  obtain ⟨N, hcore⟩ := core (F := ℚ_[l]) (L := Om l) (A := fun n : ℤ => HQ l (mod C).spc n 0) (fun n hn => negVan l _ n hn)
    (pullTot l (sch.map (toMod C))) hinj (fun i => (b₀ i).1)
    (b₀.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)) (fun i => hle (b₀ i).2)
  obtain ⟨d, ⟨β⟩⟩ : ∃ d : Fin N → ℕ, Nonempty (∀ i : Fin N, Module.Basis (Fin (d i)) ℚ_[l] ((mod C).V i)) :=
    ⟨fun i => Module.finrank ℚ_[l] ((mod C).V i), ⟨fun i => haveI := hfin i; Module.finBasis ℚ_[l] ((mod C).V i)⟩⟩
  have hcr := fun i : Fin N => crysCopy hCr l P AI hT K (mod C) hSm i (d i) (β i)
  choose ρc hρ hcrys using hcr
  obtain ⟨Tk, hTk⟩ : ∃ Tk : ∀ i : Fin N, ℕ → End ℚ_[l] (Fin (d i) → ℚ_[l]), ∀ (i : Fin N) (k : Fin (n + 1)),
      Tk i k = (β i).equivFun.toLinearMap ∘ₗ A k i ∘ₗ (β i).equivFun.symm.toLinearMap :=
    ⟨fun i k => if h : k ≤ n then (β i).equivFun.toLinearMap ∘ₗ A ⟨k, Nat.lt_succ_of_le h⟩ i ∘ₗ (β i).equivFun.symm.toLinearMap else 0,
      fun i k => dif_pos (Nat.le_of_lt_succ k.2)⟩
  have hTv : ∀ (i : Fin N) (k : Fin (n + 1)) v, Tk i k ((β i).equivFun v) = (β i).equivFun (A k i v) := fun i k v => by
    rw [hTk]
    simp
  have hann : ∀ i : Fin N, AnnD (σCr P K) (ψCr P f) (l ^ f) n (ρc i) (Tk i) := fun i =>
    Br.annModel hF l P AI hT K f hf hc ϖ hϖ (mod C) hSm n i Tc hr hPt (fun k => A k i) (fun k => (hAk k i).1) _ (β i).equivFun (ρc i) (hρ i)
      (Tk i) (fun k v => hTv i k v)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Representation ℚ_[l] ↥(GK K) (∀ i : Fin N, Fin (d i) → ℚ_[l]), ∀ g x i, ρ' g x i = ρc i g (x i) :=
    ⟨piRep ρc, fun _ _ _ => rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : ℕ → End ℚ_[l] (∀ i : Fin N, Fin (d i) → ℚ_[l]), ∀ j x i, T' j x i = Tk i j (x i) :=
    ⟨fun k => LinearMap.pi fun i => Tk i k ∘ₗ LinearMap.proj i, fun _ _ _ => rfl⟩
  have hPi := annPi l P K (Fin N) (fun i => Fin (d i) → ℚ_[l]) ρc f (l ^ f) n Tk ρ' T' hρ' hT'
  obtain ⟨b, hbI, hbG, hbT⟩ := hcore d β
  refine ⟨∀ i : Fin N, Fin (d i) → ℚ_[l], inferInstance, inferInstance, inferInstance, ρ', T', b, hPi.1 hcrys, hPi.2 hann,
    hbI, fun g x => ?_, fun j hj x => ?_⟩
  · refine hbG (fun i => ρc i g) (ρ' g) (hρ' g) (galTot l (PadicAlgCl l) H.q (IntermediateField.fixingSubgroupEquiv K.1 g))
      (fun i u => ?_) _ (fun j => hb₀ _ j) x
    have h2 := basis_rel (β i) (ρc i g) ((mod C).act i g) (hρ i g) u
    have h3 := gal_inTot (mod C) i g ((β i).equivFun.symm u)
    rw [h2] at h3
    exact (LinearMap.congr_fun (heq (IntermediateField.fixingSubgroupEquiv K.1 g)) _).trans
      (congrArg (pullTot l (sch.map (toMod C))) h3)
  · have hk : j < n + 1 := Nat.lt_succ_of_le hj
    refine hbT (fun i => Tk i j) (T' j) (hT' j) (hop l H (PadicAlgCl l) (γ ⟨j, hk⟩)) (m ⟨j, hk⟩) (hTc ⟨j, hk⟩).2.1.1.ne'
      (fun i u => ?_) (θ (γ ⟨j, hk⟩)) (ϑ j) (hTc ⟨j, hk⟩).2.2 (fun i => ?_) x
    · have h2 := basis_rel (β i) (Tk i j) (A ⟨j, hk⟩ i) (hTv i ⟨j, hk⟩) u
      have h1 := (hAk ⟨j, hk⟩ i).2 ((β i).equivFun.symm u)
      rw [h2] at h1
      exact h1
    · exact Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 (b₀ i).2 (γ ⟨j, hk⟩))

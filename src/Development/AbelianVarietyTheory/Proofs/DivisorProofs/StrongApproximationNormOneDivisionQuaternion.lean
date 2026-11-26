module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FujisakiDivisionQuaternionAlgebraModCentre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupported
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalNormOneOfIdempotentConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtInvS
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

open scoped RestrictedProduct

namespace GlobalTheory.InvIdem

variable {F : Type} [Field F] [NumberField F]

def ci (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (fstA F).toRingHom

def cf (v : HeightOneSpectrum (𝓞 F)) : AF F →+* Fv F v :=
  (evalV F v).toRingHom.comp (sndA F).toRingHom

theorem continuous_ci (w : InfinitePlace F) : Continuous (ci (F := F) w) :=
  (continuous_apply w).comp continuous_fst

theorem continuous_cf (v : HeightOneSpectrum (𝓞 F)) : Continuous (cf (F := F) v) :=
  (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp
    continuous_snd

theorem ext_c {a b : AF F} (h1 : ∀ w, ci w a = ci w b) (h2 : ∀ v, cf v a = cf v b) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)


open Classical in
def sglI (w : InfinitePlace F) (c : w.Completion) : AF F :=
  ((Pi.single w c : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : AF F :=
  ((0 : InfiniteAdeleRing F), singleV F v c)

theorem ci_apply (w : InfinitePlace F) (a : AF F) : ci w a = a.1 w := rfl
theorem cf_apply (v : HeightOneSpectrum (𝓞 F)) (a : AF F) : cf v a = a.2 v := rfl

theorem ci_sglI_self (w : InfinitePlace F) (c : w.Completion) : ci w (sglI w c) = c := by
  classical
  rw [ci_apply]; simp [sglI]

theorem ci_sglI_ne {w u : InfinitePlace F} (h : u ≠ w) (c : w.Completion) : ci u (sglI w c) = 0 := by
  classical
  rw [ci_apply]; simp [sglI, Pi.single_apply, h]

theorem cf_sglI (w : InfinitePlace F) (c : w.Completion) (v : HeightOneSpectrum (𝓞 F)) :
    cf v (sglI w c) = 0 := by
  rw [cf_apply]; rfl

theorem ci_sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (w : InfinitePlace F) :
    ci w (sglF v c) = 0 := by
  rw [ci_apply]; rfl

theorem cf_sglF_self (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : cf v (sglF v c) = c := by
  classical
  show (singleV F v c) v = c
  unfold singleV
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v c

theorem cf_sglF_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (c : Fv F v) : cf u (sglF v c) = 0 := by
  classical
  show (singleV F v c) u = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) c h

open Classical in
theorem continuous_sglI (w : InfinitePlace F) : Continuous (sglI (F := F) w) := by
  unfold sglI
  exact (continuous_single w).prodMk continuous_const

open Classical in
theorem continuous_sglF (v : HeightOneSpectrum (𝓞 F)) : Continuous (sglF (F := F) v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf)

def invS (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (y : AF F) : AF F :=
  (∑ w ∈ S₁, sglI w (ci w y)⁻¹) + ∑ v ∈ S₂, sglF v (cf v y)⁻¹

variable {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))}

open Classical in
theorem ci_invS (y : AF F) (u : InfinitePlace F) :
    ci u (invS S₁ S₂ y) = if u ∈ S₁ then (ci u y)⁻¹ else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [invS, map_add (f := _), map_sum, map_sum]
  simp only [ci_sglF, Finset.sum_const_zero, add_zero]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => ci_sglI_ne (Ne.symm hw) _), ci_sglI_self]
  · exact Finset.sum_eq_zero fun w hw => ci_sglI_ne (fun h : u = w => hu (h ▸ hw)) _

open Classical in
theorem cf_invS (y : AF F) (u : HeightOneSpectrum (𝓞 F)) :
    cf u (invS S₁ S₂ y) = if u ∈ S₂ then (cf u y)⁻¹ else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [invS, map_add (f := _), map_sum, map_sum]
  simp only [cf_sglI, Finset.sum_const_zero, zero_add]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => cf_sglF_ne (Ne.symm hw) _), cf_sglF_self]
  · exact Finset.sum_eq_zero fun w hw => cf_sglF_ne (fun h : u = w => hu (h ▸ hw)) _

theorem invS_mul {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) {y z : AF F} (hyz : y * z = 1) :
    invS S₁ S₂ (ε * y) = ε * z := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  have hi : ∀ w, ci w y * ci w z = 1 := fun w => by rw [← map_mul (ci w), hyz, map_one]
  have hf : ∀ v, cf v y * cf v z = 1 := fun v => by rw [← map_mul (cf v), hyz, map_one]
  refine ext_c (fun w => ?_) (fun v => ?_)
  · rw [ci_invS, map_mul, map_mul]
    have e1 : ci w ε = fstA F ε w := rfl
    split_ifs with hw
    · rw [e1, h1 w hw, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hi w)
    · rw [e1, h2 w hw, zero_mul]
  · rw [cf_invS, map_mul, map_mul]
    have e1 : cf v ε = evalV F v (sndA F ε) := rfl
    split_ifs with hv
    · rw [e1, h3 v hv, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hf v)
    · rw [e1, h4 v hv, zero_mul]

theorem continuousAt_invS {y : AF F} (h1 : ∀ w ∈ S₁, ci w y ≠ 0) (h2 : ∀ v ∈ S₂, cf v y ≠ 0) :
    ContinuousAt (invS S₁ S₂) y := by
  unfold invS
  refine ContinuousAt.add ?_ ?_
  · exact tendsto_finsetSum S₁ fun w hw =>
      ((continuous_sglI w).continuousAt.comp ((continuousAt_inv₀ (h1 w hw)).comp (continuous_ci w).continuousAt))
  · exact tendsto_finsetSum S₂ fun v hv =>
      ((continuous_sglF v).continuousAt.comp ((continuousAt_inv₀ (h2 v hv)).comp (continuous_cf v).continuousAt))

end GlobalTheory.InvIdem

namespace GlobalTheory.InvIdem

theorem inv_cont : ∀ (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x : (AF F)ˣ, ∀ U : Set (AF F),
    U ∈ 𝓝 (ε * ((x⁻¹ : (AF F)ˣ) : AF F)) → ∃ V : Set (AF F), V ∈ 𝓝 (ε * (x : AF F)) ∧
      ∀ t : F, ε * algebraMap F (AF F) t ∈ V → (ε ≠ 0 → t ≠ 0) ∧ ε * algebraMap F (AF F) t⁻¹ ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  have hx : invS S₁ S₂ (ε * (x : AF F)) = ε * ((x⁻¹ : (AF F)ˣ) : AF F) := invS_mul hε x.mul_inv
  have hci : ∀ w ∈ S₁, ci w (ε * (x : AF F)) ≠ 0 := by
    intro w hw h
    rw [map_mul, show ci w ε = fstA F ε w from rfl, hε.1 w hw, one_mul] at h
    have e := congrArg (ci w) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hcf : ∀ v ∈ S₂, cf v (ε * (x : AF F)) ≠ 0 := by
    intro v hv h
    rw [map_mul, show cf v ε = evalV F v (sndA F ε) from rfl, hε.2.2.1 v hv, one_mul] at h
    have e := congrArg (cf v) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hV1 : invS S₁ S₂ ⁻¹' U ∈ 𝓝 (ε * (x : AF F)) :=
    (continuousAt_invS hci hcf).preimage_mem_nhds (by rw [hx]; exact hU)
  have hV2 : {y : AF F | (∀ w ∈ S₁, ci w y ≠ 0) ∧ ∀ v ∈ S₂, cf v y ≠ 0} ∈ 𝓝 (ε * (x : AF F)) :=
    ((Filter.eventually_all_finset S₁).2 fun w hw => (continuous_ci w).continuousAt.eventually_ne (hci w hw)).and
      ((Filter.eventually_all_finset S₂).2 fun v hv => (continuous_cf v).continuousAt.eventually_ne (hcf v hv))
  refine ⟨_, Filter.inter_mem hV1 hV2, fun t ht => ?_⟩
  have htne : ε ≠ 0 → t ≠ 0 := by
    intro hε0 ht0
    subst ht0
    apply hε0
    have hB := ht.2
    simp only [Set.mem_setOf_eq, map_zero, mul_zero] at hB
    refine ext_c (fun w => ?_) (fun v => ?_)
    · rw [map_zero]
      exact hε.2.1 w fun hw => hB.1 w hw rfl
    · rw [map_zero]
      exact hε.2.2.2 v fun hv => hB.2 v hv rfl
  refine ⟨htne, ?_⟩
  by_cases hε0 : ε = 0
  · subst hε0
    have e := mem_of_mem_nhds hU
    rw [zero_mul] at e
    rwa [zero_mul]
  · have ht0 := htne hε0
    have e := invS_mul (y := algebraMap F (AF F) t) (z := algebraMap F (AF F) t⁻¹) hε
      (by rw [← map_mul, mul_inv_cancel₀ ht0, map_one])
    rw [← e]
    exact ht.1

end GlobalTheory.InvIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalNormOneOfIdempotentConj
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.Unconj

section Top

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}

theorem continuous_re : Continuous (fun x : ℍ[R, a, b] => x.re) :=
  (continuous_apply 0).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) :=
  (continuous_apply 1).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) :=
  (continuous_apply 2).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) :=
  (continuous_apply 3).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_of_coords {X : Type*} [TopologicalSpace X] {f : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (f x).re) (h1 : Continuous fun x => (f x).imI)
    (h2 : Continuous fun x => (f x).imJ) (h3 : Continuous fun x => (f x).imK) : Continuous f := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

attribute [local fun_prop] continuous_re continuous_imI continuous_imJ continuous_imK

scoped instance : ContinuousMul ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_mul]; fun_prop) (by simp only [QuaternionAlgebra.imJ_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_mul]; fun_prop)⟩

scoped instance : ContinuousAdd ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_add]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_add]; fun_prop) (by simp only [QuaternionAlgebra.imJ_add]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_add]; fun_prop)⟩

scoped instance : ContinuousNeg ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_neg]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_neg]; fun_prop) (by simp only [QuaternionAlgebra.imJ_neg]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_neg]; fun_prop)⟩

scoped instance : IsTopologicalRing ℍ[R, a, b] := {}

scoped instance : ContinuousSMul R ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_smul, smul_eq_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_smul, smul_eq_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imJ_smul, smul_eq_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_smul, smul_eq_mul]; fun_prop)⟩

scoped instance : ContinuousStar ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_star]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_star]; fun_prop) (by simp only [QuaternionAlgebra.imJ_star]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_star]; fun_prop)⟩

theorem continuous_nrm : Continuous (fun x : ℍ[R, a, b] => nrm x) := by
  unfold nrm; fun_prop

end Top

end GlobalTheory.QSA.Unconj

noncomputable section

namespace GlobalTheory.QSA.Unconj

variable {F : Type} [Field F] [NumberField F]

theorem isPlacesIdem_mul_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {η : AF F}
    (hη : IsPlacesIdem S₁ S₂ η) : η * η = η := by
  have h1 : fstA F (η * η) = fstA F η := by
    rw [map_mul]
    funext w
    change fstA F η w * fstA F η w = fstA F η w
    by_cases hw : w ∈ S₁
    · rw [hη.1 w hw, one_mul]
    · rw [hη.2.1 w hw, zero_mul]
  have h2 : sndA F (η * η) = sndA F η := by
    refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV F u (sndA F (η * η)) = evalV F u (sndA F η)
    rw [map_mul, map_mul]
    by_cases hu : u ∈ S₂
    · rw [hη.2.2.1 u hu, one_mul]
    · rw [hη.2.2.2 u hu, zero_mul]
  exact Prod.ext h1 h2

theorem rat_mul {a b : F} (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat] <;> ring

theorem rat_one {a b : F} : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem rat_star {a b : F} (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem rat_smul {a b : F} (t : F) (x : ℍ[F, a, b]) : rat (t • x) = algebraMap F (AF F) t • rat x := by
  ext <;> simp [rat, Algebra.smul_def]

theorem nrm_smul {R : Type*} [CommRing R] {a b : R} (s : R) (x : ℍ[R, a, b]) : nrm (s • x) = s ^ 2 * nrm x := by
  simp only [nrm, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  ring

theorem star_smul' {R : Type*} [CommRing R] {a b : R} (s : R) (x : ℍ[R, a, b]) : star (s • x) = s • star x := by
  ext <;> simp <;> ring

end GlobalTheory.QSA.Unconj

namespace GlobalTheory.QSA.Unconj
theorem conj_core {R : Type*} [CommRing R] {a b : R} (η s : R) (hηη : η * η = η) (X c c' h : ℍ[R, a, b])
    (hh : η • h = h) :
    (η • X) * c * h * (c' * ((η * s) • star (η • X))) = X * (c * h * c') * (s • star X) := by
  conv_rhs => rw [← hh]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, star_smul', mul_assoc]
  rw [hηη, mul_left_comm, hηη]
end GlobalTheory.QSA.Unconj

namespace GlobalTheory.QSA.Unconj

theorem conj_mem_closure_normOne_of_idempotent : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η →
    ∀ ε : AF F, ε * ε = ε → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → ∀ c c' : DA F a b, c * c' = 1 →
    c' * c = 1 → c * g * c' ∈ closure (H0 (a := a) (b := b) ε) → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b _ _ T₁ T₂ η hη ε hε g _ hgη c c' hcc' hc'c hx
  have hηη := isPlacesIdem_mul_self hη
  obtain ⟨-, -, hconj, -⟩ := GlobalTheory.T.closure_normOneProducts_h0_properties F a b ε hε
  by_cases hη0 : η = 0
  · have hg1 : g = 1 := by
      rw [hη0, zero_smul] at hgη
      exact (sub_eq_zero.1 hgη.symm)
    rw [hg1]
    exact subset_closure (one_mem_H0_weight_zero ε)
  rw [← closure_closure (s := H0 (a := a) (b := b) ε), mem_closure_iff_nhds]
  intro W hW
  have hnn : nrm c' * nrm c = 1 := by
    rw [← nrm_mul, hc'c]
    simp [nrm]
  have hcstar : nrm c • star c' = c := by
    have h1 : star c' = nrm c' • c := by
      calc star c' = c * (c' * star c') := by rw [← mul_assoc, hcc', one_mul]
        _ = nrm c' • c := by rw [mul_star_eq, Algebra.algebraMap_eq_smul_one (nrm c'), mul_smul_comm, mul_one]
    rw [h1, smul_smul, mul_comm, hnn, one_smul]
  let u : (AF F)ˣ := ⟨nrm c', nrm c, hnn, by rw [mul_comm]; exact hnn⟩
  let Ξ : DA F a b × AF F → DA F a b := fun p => 1 + (p.1 * c) * (g - 1) * (c' * (p.2 • star p.1))
  have hΞc : Continuous Ξ :=
    continuous_const.add (((continuous_fst.mul continuous_const).mul continuous_const).mul
      (continuous_const.mul (continuous_snd.smul (continuous_star.comp continuous_fst))))
  have hΞ0 : Ξ (η • c', η * nrm c) = g := by
    have e1 : (η • c') * c = η • 1 := by rw [smul_mul_assoc, hc'c]
    have e2 : c' * ((η * nrm c) • star (η • c')) = η • 1 := by
      have hs : η * nrm c * η = η * nrm c := by linear_combination (nrm c) * hηη
      rw [star_smul', smul_smul, hs, ← smul_smul, hcstar, mul_smul_comm, hc'c]
    have e3 : (η • (1 : DA F a b)) * (g - 1) * (η • 1) = g - 1 := by
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hgη]
    show 1 + ((η • c') * c) * (g - 1) * (c' * ((η * nrm c) • star (η • c'))) = g
    rw [e1, e2, e3]
    abel
  have hW' : Ξ ⁻¹' W ∈ 𝓝 (η • c', η * nrm c) :=
    hΞc.continuousAt.preimage_mem_nhds (by rw [hΞ0]; exact hW)
  obtain ⟨N1, hN1, N2, hN2, hN12⟩ := mem_nhds_prod_iff.1 hW'
  obtain ⟨V, hV, hVt⟩ := GlobalTheory.InvIdem.inv_cont F T₁ T₂ η hη u N2 hN2
  have hN3 : (fun X : DA F a b => nrm X) ⁻¹' V ∈ 𝓝 (η • c') :=
    continuous_nrm.continuousAt.preimage_mem_nhds (by rw [nrm_smul, pow_two, hηη]; exact hV)
  let e : (Fin 4 → AF F) → DA F a b := fun v => η • c' - ⟨v 0, v 1, v 2, v 3⟩
  have hec : Continuous e := by
    refine continuous_const.sub (continuous_of_coords ?_ ?_ ?_ ?_) <;> exact continuous_apply _
  have hN : e ⁻¹' (N1 ∩ (fun X : DA F a b => nrm X) ⁻¹' V) ∈ 𝓝 (0 : Fin 4 → AF F) := by
    refine hec.continuousAt.preimage_mem_nhds ?_
    have : e 0 = η • c' := by
      show η • c' - ⟨0, 0, 0, 0⟩ = η • c'
      rw [show (⟨0, 0, 0, 0⟩ : DA F a b) = 0 from rfl, sub_zero]
    rw [this]
    exact Filter.inter_mem hN1 hN3
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hU : (⋂ i, t i) ∈ 𝓝 (0 : AF F) := Filter.iInter_mem.2 ht
  choose q hq using fun i : Fin 4 => GlobalTheory.PlaceApprox.weak_approx_idem F T₁ T₂ η hη (coords c' i) (⋂ i, t i) hU
  let δ : ℍ[F, a, b] := ⟨q 0, q 1, q 2, q 3⟩
  have hδe : η • rat δ = e (fun i => η * (coords c' i - algebraMap F (AF F) (q i))) := by
    ext <;> simp [e, δ, rat, coords] <;> ring
  have hδN : η • rat δ ∈ N1 ∩ (fun X : DA F a b => nrm X) ⁻¹' V := by
    rw [hδe]
    exact hIt (show (fun i => η * (coords c' i - algebraMap F (AF F) (q i))) ∈ (I.pi t) from
      fun i _ => Set.mem_iInter.1 (hq i) i)
  have hnδ : η * algebraMap F (AF F) (nrm δ) ∈ V := by
    have h := hδN.2
    simp only [Set.mem_preimage, nrm_smul, nrm_rat, pow_two, hηη] at h
    exact h
  obtain ⟨hn0, hn⟩ := hVt (nrm δ) hnδ
  have hn0 := hn0 hη0
  set δ' : ℍ[F, a, b] := (nrm δ)⁻¹ • star δ with hδ'
  have hδδ' : δ * δ' = 1 := by
    rw [hδ', mul_smul_comm, mul_star_eq, Algebra.algebraMap_eq_smul_one (nrm δ), smul_smul, inv_mul_cancel₀ hn0, one_smul]
  refine ⟨rat δ * (c * g * c') * rat δ', ?_, hconj δ δ' hδδ' _ hx⟩
  have hmem := hN12 (Set.mk_mem_prod hδN.1 hn)
  have hval : Ξ (η • rat δ, η * algebraMap F (AF F) (nrm δ)⁻¹) = rat δ * (c * g * c') * rat δ' := by
    have hcg : c * g * c' = 1 + c * (g - 1) * c' := by
      rw [mul_sub, sub_mul, mul_one, hcc']
      abel
    have hr : rat δ * (c * g * c') * rat δ' = 1 + rat δ * (c * (g - 1) * c') * rat δ' := by
      rw [hcg, mul_add, add_mul, mul_one, ← rat_mul, hδδ', rat_one]
    rw [hr]
    show 1 + ((η • rat δ) * c) * (g - 1) * (c' * ((η * algebraMap F (AF F) (nrm δ)⁻¹) • star (η • rat δ))) = _
    refine congrArg (fun z => 1 + z) ?_
    rw [hδ', rat_smul, rat_star]
    exact conj_core η _ hηη (rat δ) c c' (g - 1) hgη
  rw [← hval]
  exact hmem

end GlobalTheory.QSA.Unconj
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalNormOneOfIdempotentConjStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_rationalNormOne_of_idempotent_conj : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ ε : AF F, ε * ε = ε → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → ∀ c c' : DA F a b, c * c' = 1 → c' * c = 1 → c * g * c' ∈ closure (H0 (a := a) (b := b) ε) → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent | exact GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent | (intros; apply GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QuatTop

variable {R : Type} [CommRing R] [TopologicalSpace R] {a b : R}

theorem continuous_coord_re : Continuous (fun x : ℍ[R, a, b] => x.re) :=
  (continuous_apply (0 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) :=
  (continuous_apply (1 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) :=
  (continuous_apply (2 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) :=
  (continuous_apply (3 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_of_coords {X : Type*} [TopologicalSpace X] {g : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (g x).re) (h1 : Continuous fun x => (g x).imI)
    (h2 : Continuous fun x => (g x).imJ) (h3 : Continuous fun x => (g x).imK) : Continuous g := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem isTopologicalRing [IsTopologicalRing R] : IsTopologicalRing ℍ[R, a, b] := by
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  have p0 := c0.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p1 := c1.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p2 := c2.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p3 := c3.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q0 := c0.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q1 := c1.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q2 := c2.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q3 := c3.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have hadd : ContinuousAdd ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_add]; exact p0.add q0) (by simp only [QuaternionAlgebra.imI_add]; exact p1.add q1) (by simp only [QuaternionAlgebra.imJ_add]; exact p2.add q2) (by simp only [QuaternionAlgebra.imK_add]; exact p3.add q3)⟩
  have hmul : ContinuousMul ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imJ_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_mul]; fun_prop)⟩
  have hneg : ContinuousNeg ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_neg]; exact c0.neg) (by simp only [QuaternionAlgebra.imI_neg]; exact c1.neg) (by simp only [QuaternionAlgebra.imJ_neg]; exact c2.neg) (by simp only [QuaternionAlgebra.imK_neg]; exact c3.neg)⟩
  exact {}

end GlobalTheory.QuatTop

open GlobalTheory.QuatTop in
theorem GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  intro R _ _ _ a b
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  refine ⟨isTopologicalRing, ?_, c0, fun _ => ?_⟩
  · unfold nrm; fun_prop
  · have hinj : Function.Injective (coords : ℍ[R, a, b] → Fin 4 → R) := by
      intro x y h
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      have e2 := congrFun h 2
      have e3 := congrFun h 3
      simp [coords] at e0 e1 e2 e3
      ext <;> assumption
    exact (Topology.IsEmbedding.mk ⟨rfl⟩ hinj).t2Space
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRingStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_algebra_topological_ring : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  first | exact @GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | exact GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | (intros; apply GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseConjMemClosureOfIsCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseConjMemClosureOfIsCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem exists_inverse_conj_mem_closure_of_isCompact :
    ∀ (X : Type) [Monoid X] [TopologicalSpace X] [ContinuousMul X] [T2Space X] (H C : Set X),
      IsCompact C → ∀ g : X, (∀ W ∈ 𝓝 g, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧
        ∃ w ∈ W, c * w * c' ∈ H) →
      ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ c * g * c' ∈ closure H := by
  intro X _ _ _ _ H C hC g hW
  let K : Set (X × X) := (C ×ˢ C) ∩ {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}
  have hK : IsCompact K := by
    refine (hC.prod hC).inter_right ?_
    exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  by_contra hne
  push_neg at hne
  have hcont : Continuous fun z : X × (X × X) => z.2.1 * z.1 * z.2.2 :=
    ((continuous_snd.fst).mul continuous_fst).mul continuous_snd.snd
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (X × X) in 𝓝 (g, y), z.2.1 * z.1 * z.2.2 ∈ (closure H)ᶜ := by
    intro y hy
    apply hcont.continuousAt.preimage_mem_nhds
    apply isClosed_closure.isOpen_compl.mem_nhds
    exact hne y.1 hy.1.1 y.2 hy.1.2 hy.2.1 hy.2.2
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := g)
    (P := fun w (y : X × X) => y.1 * w * y.2 ∈ (closure H)ᶜ) hP
  obtain ⟨c, hc, c', hc', h1, h2, w, hw, hH⟩ := hW _ hev
  exact hw (c, c') ⟨⟨hc, hc'⟩, h1, h2⟩ (subset_closure hH)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseConjMemClosureOfIsCompactStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_mem_closure_of_isCompact : ∀ (X : Type) [Monoid X] [TopologicalSpace X] [ContinuousMul X] [T2Space X] (H C : Set X), IsCompact C → ∀ g : X, (∀ W ∈ 𝓝 g, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ ∃ w ∈ W, c * w * c' ∈ H) → ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ c * g * c' ∈ closure H := by
  first | exact @GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact | exact GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact | (intros; apply GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdeles
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section
namespace GlobalTheory

open Filter

theorem placesIdem_mem_nhds_one (F : Type) [Field F] [NumberField F] (U : Set (AF F)) (hU : U ∈ 𝓝 (1 : AF F)) :
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  classical
  let x : Finset (HeightOneSpectrum (𝓞 F)) → Π v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun T v => if v ∈ T then ⟨1, (v.adicCompletionIntegers F).one_mem⟩ else ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  let one' : Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨1, (v.adicCompletionIntegers F).one_mem⟩
  let sm := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AF F := fun T => ((1 : Ainf F), (sm (x T) : Af F))
  have hx : Tendsto x atTop (𝓝 one') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_atTop_of_eventually_const (i₀ := {v})
    intro T hT
    simp [x, one', hT (Finset.mem_singleton_self v)]
  have h1 : (sm one' : Af F) = 1 := by
    ext v; rfl
  have he : Tendsto e atTop (𝓝 (1 : AF F)) := by
    have hc : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
    have h2 : Tendsto (fun T => (sm (x T) : Af F)) atTop (𝓝 (1 : Af F)) := by
      have h3 := (hc.tendsto one').comp hx
      rw [h1] at h3
      exact h3
    exact Tendsto.prodMk_nhds tendsto_const_nhds h2
  obtain ⟨T, hT⟩ := (he.eventually hU).exists
  refine ⟨Finset.univ, T, e T, ⟨?_, ?_, ?_, ?_⟩, hT⟩
  · intro w _; rfl
  · intro w hw; exact absurd (Finset.mem_univ w) hw
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 1
    simp [x, hv]
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 0
    simp [x, hv]

theorem placesIdem_tendsto_one : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) →
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U :=
  fun F _ _ U hU => placesIdem_mem_nhds_one F U hU

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdelesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placesIdempotent_near_one_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) → ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  first | exact @GlobalTheory.placesIdem_tendsto_one | exact GlobalTheory.placesIdem_tendsto_one | (intros; apply GlobalTheory.placesIdem_tendsto_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneDivisionQuaternion
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.DivAssembly

section Ring

variable {R : Type*} [CommRing R] {a b : R}

theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

theorem nrm_star' (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by simp [nrm]

theorem star_mul_eq' (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  have h := mul_star_eq (star x)
  rwa [star_star, nrm_star'] at h

theorem nrm_trunc (e : R) (he : e * e = e) (g : ℍ[R, a, b]) :
    nrm (e • (g - 1) + 1) = e * nrm g + (1 - e) := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub, QuaternionAlgebra.imJ_sub,
    QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
    QuaternionAlgebra.imK_one, smul_eq_mul]
  linear_combination ((g.re - 1) ^ 2 - a * g.imI ^ 2 - b * g.imJ ^ 2 + a * b * g.imK ^ 2) * he

end Ring

section Alg

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem prod_decomp (e : R) (he : e * e = e) (g : A) :
    ((1 - e) • (g - 1) + 1) * (e • (g - 1) + 1) = g := by
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, h0, zero_smul, zero_add]
  rw [← add_assoc, ← add_smul, show e + (1 - e) = 1 by ring, one_smul, sub_add_cancel]

end Alg

variable {F : Type} [Field F] [NumberField F]

theorem isPlacesIdem_idem {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h.1 w hw, one_mul]
    · rw [h.2.1 w hw, zero_mul]
  · refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV F u (sndA F (ε * ε)) = evalV F u (sndA F ε)
    rw [map_mul, map_mul]
    by_cases hu : u ∈ S₂
    · rw [h.2.2.1 u hu, one_mul]
    · rw [h.2.2.2 u hu, zero_mul]

theorem rat_mul' {a b : F} (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_one' {a b : F} : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem continuous_smul_const {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}
    (x : ℍ[R, a, b]) : Continuous fun t : R => t • x := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

end GlobalTheory.QSA.DivAssembly

namespace GlobalTheory.QSA.DivAssembly

variable {F : Type} [Field F] [NumberField F]

theorem conj_mem_normOneIdempotentSubgroup_of_rational_relation {a b : F} (ε : AF F) (w c c' : DA F a b) (l : AF F) (hl : IsUnit l) (δ γ : ℍ[F, a, b])
    (hδ : nrm δ ≠ 0) (hγ : nrm γ = 1) (h : DA F a b) (hh : nrm h = 1) (hhε : ε • (h - 1) = h - 1)
    (hcc' : c * c' = 1)
    (hyw : l • (rat δ * c) * w = rat γ * l • (rat δ * c) * h) : c * w * c' ∈ H0 ε := by
  set δ' : ℍ[F, a, b] := (nrm δ)⁻¹ • star δ with hδ'
  have hδδ : δ' * δ = 1 := by
    rw [hδ', smul_mul_assoc, star_mul_eq', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hδ, map_one]
  have E1 : rat δ * c * w = rat γ * rat δ * c * h := by
    have h2 : l • (rat δ * c * w) = l • (rat γ * rat δ * c * h) := by
      rw [← smul_mul_assoc, hyw, mul_smul_comm, smul_mul_assoc, mul_assoc (rat γ), mul_assoc (rat γ)]
      simp only [mul_assoc]
    exact hl.smul_left_cancel.1 h2
  refine ⟨δ' * γ * δ, ?_, c * h * c', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hγ, mul_one, ← nrm_mul, hδδ, nrm_one']
  · rw [nrm_mul, nrm_mul, hh, mul_one, ← nrm_mul, hcc', nrm_one']
  · have e1 : c * h * c' - 1 = c * (h - 1) * c' := by
      rw [mul_sub, sub_mul, mul_one, hcc']
    rw [e1, ← smul_mul_assoc, ← mul_smul_comm, hhε]
  · calc c * w * c' = (rat δ' * rat δ) * c * w * c' := by rw [← rat_mul', hδδ, rat_one', one_mul]
      _ = rat δ' * (rat δ * c * w) * c' := by simp only [mul_assoc]
      _ = rat δ' * (rat γ * rat δ * c * h) * c' := by rw [E1]
      _ = rat (δ' * γ * δ) * (c * h * c') := by simp only [rat_mul', mul_assoc]

theorem strongApproximation_normOne_divisionQuaternion : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hdiv S₁ S₂ ε hε hS hsurj g hg
  have hee : ε * ε = ε := isPlacesIdem_idem hε
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.closure_normOneProducts_h0_properties F a b ε hee
  obtain ⟨htr, -, -, hT2⟩ := GlobalTheory.T.quaternion_algebra_topological_ring (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b)
  haveI : IsTopologicalRing (DA F a b) := htr
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  haveI : T2Space (DA F a b) := hT2 inferInstance
  obtain ⟨C, hC, hfuj⟩ := GlobalTheory.T.fujisaki_divisionQuaternionAlgebra_mod_centre F a b ha hb hdiv

  have key : ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F),
      IsPlacesIdem T₁ T₂ η → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
    intro T₁ T₂ η hη g hg hgη
    have hee' : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
    set gS : DA F a b := ε • (g - 1) + 1 with hgSdef
    set gN : DA F a b := (1 - ε) • (g - 1) + 1 with hgNdef
    have hprod : gN * gS = g := prod_decomp ε hee g
    have hgS : gS ∈ H0 (a := a) (b := b) ε := by
      refine ⟨1, nrm_one', gS, ?_, ?_, by rw [rat_one', one_mul]⟩
      · rw [hgSdef, nrm_trunc ε hee, hg]; ring
      · rw [hgSdef, add_sub_cancel_right, smul_smul, hee]
    have hgN1 : nrm gN = 1 := by rw [hgNdef, nrm_trunc (1 - ε) hee', hg]; ring
    have hgNε : ε • (gN - 1) = 0 := by
      rw [hgNdef, add_sub_cancel_right, smul_smul, show ε * (1 - ε) = 0 by linear_combination -hee, zero_smul]
    have hgNη : η • (gN - 1) = gN - 1 := by
      rw [hgNdef, add_sub_cancel_right, smul_comm, hgη]
    have hW : ∀ W ∈ 𝓝 gN, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ ∃ w ∈ W, c * w * c' ∈ H0 (a := a) (b := b) ε := by
      intro W hW
      obtain ⟨w, hwW, y, hy, γ, hγ, h, hh, hhε, hyw⟩ :=
        GlobalTheory.T.normOneQuaternion_near_conj_rational_times_supported F a b ha hb S₁ S₂ ε hε hS hsurj gN hgN1 hgNε W hW
      obtain ⟨δ, l, c, c', hδ, hl, hc, hc', hcc', hc'c, rfl⟩ := hfuj y hy
      exact ⟨c, hc, c', hc', hcc', hc'c, w, hwW, conj_mem_normOneIdempotentSubgroup_of_rational_relation ε w c c' l hl δ γ hδ hγ h hh hhε hcc' hyw⟩
    obtain ⟨c, -, c', -, hcc', hc'c, hmem⟩ := GlobalTheory.T.exists_conj_mem_closure_of_isCompact (DA F a b) (H0 (a := a) (b := b) ε) C hC gN hW
    have hgN := GlobalTheory.T.mem_closure_rationalNormOne_of_idempotent_conj F a b ha hb T₁ T₂ η hη ε hee gN hgN1 hgNη c c' hcc' hc'c hmem
    rw [← hprod]
    exact hmul _ hgN _ (subset_closure hgS)

  suffices g ∈ closure (closure (H0 (a := a) (b := b) ε)) by rwa [closure_closure] at this
  have hφ : Continuous fun η : AF F => η • (g - 1) + 1 := (continuous_smul_const (g - 1)).add continuous_const
  rw [mem_closure_iff_nhds]
  intro V hV
  have hpre : (fun η : AF F => η • (g - 1) + 1) ⁻¹' V ∈ 𝓝 (1 : AF F) :=
    hφ.continuousAt.preimage_mem_nhds (by rwa [one_smul, sub_add_cancel])
  obtain ⟨T₁, T₂, η, hη, hηV⟩ := GlobalTheory.T.exists_placesIdempotent_near_one_adeles F _ hpre
  have hηη : η * η = η := isPlacesIdem_idem hη
  refine ⟨η • (g - 1) + 1, hηV, key T₁ T₂ η hη _ ?_ ?_⟩
  · rw [nrm_trunc η hηη, hg]; ring
  · rw [add_sub_cancel_right, smul_smul, hηη]

end GlobalTheory.QSA.DivAssembly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneDivisionQuaternionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_normOne_of_strongApproximation : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | exact GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | (intros; apply GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion <;> assumption)
end

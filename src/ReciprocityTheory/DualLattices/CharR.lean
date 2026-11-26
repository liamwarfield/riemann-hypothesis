module

public import ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement
public import ReciprocityTheory.DualLattices.HeightFunctionalStatementOfPairingProperties

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.ExistsLimTensor
section -- merged from ReciprocityTheory.DualLattices.NsmulKerZero
section -- merged from ReciprocityTheory.DualLattices.IsHeightUnique
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

lemma lhom_ext {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)

lemma isHeight_map (hB1 : PairingPropertiesStatement B) {R S : LAlg R₀} (Dp : DualPair R) (Dq : DualPair S)
    (g : LHom R S) (f : LHom Dp.D Dq.D) (hfπ : ∀ x, Dq.π.1 (f.1 x) = g.1 (Dp.π.1 x))
    (hfσ : ∀ x, f.1 (Dp.σ.1 x) = Dq.σ.1 (g.1 x)) (hfη : f.1 Dp.η = Dq.η) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (H : B.IsHeight Dp N y h) :
    B.IsHeight Dq N (B.map g y) (g.1.toLinearMap ∘ₗ h) := by
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨Units.map (f.1 : (Dp.D : Type u) →* Dq.D) z, ?_, ?_⟩
  · have h1 := hnat _ _ f N _ _ z hz
    have hf : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dq.π.ker := by
      intro a ha
      rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
      change Dq.π.1 (f.1 a) = 0
      rw [hfπ, ha, map_zero]
    have e1 : B.map f (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = B.tg Dq.π Dq.sqZero (v ⊗ₜ Dq.ηk) := by
      rw [← B.tg_nat Dp.π Dq.π Dp.sqZero Dq.sqZero f hf, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext hfη
    have e2 : B.map f (B.map Dp.σ y) = B.map Dq.σ (B.map g y) := by
      have hc : f.comp Dp.σ = Dq.σ.comp g := lhom_ext fun x => hfσ x
      rw [← B.map_comp, ← B.map_comp, hc]
    rw [e1, e2] at h1
    exact h1
  · simp only [Units.coe_map, MonoidHom.coe_coe, hze, map_add (f := _), map_one, map_mul, hfσ, hfη]
    rfl

lemma nsmul_tg_eta {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0) (v : B.gg) :
    N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by
  rw [← map_nsmul, ← tmul_smul]
  have : N • Dp.ηk = 0 := by
    apply Subtype.ext
    change N • Dp.η = 0
    rw [nsmul_eq_mul, ← map_natCast Dp.σ.1, hN, map_zero, zero_mul]
  rw [this, tmul_zero, map_zero]

lemma isHeight_mul_p (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N p : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : (N * p) • y = 0) (h : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp (N * p) y h) : B.IsHeight Dp N (p • y) h := by
  obtain ⟨-, -, -, -, -, -, -, hNp⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨z, ?_, hze⟩
  have h1 := hNp _ N p _ _ z (B.nsmul_tg_eta Dp N hN v) (by rw [← map_nsmul, hy, map_zero]) hz
  rwa [← map_nsmul] at h1

lemma isHeight_unique (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (h h' : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y h') : h = h' :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).unique H H'

lemma isHeight_exists (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) :
    ∃ h, B.IsHeight Dp N y h :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).exists

lemma isHeight_add (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y y' : B.G R} {h h' : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') :=
  (heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.2 y y' h h' H H'

lemma isHeight_zero (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) : B.IsHeight Dp N 0 0 := by
  obtain ⟨h, hh⟩ := B.isHeight_exists hB1 Dp N hN 0 (smul_zero N)
  have h2 := B.isHeight_add hB1 Dp N hN hh hh
  rw [add_zero] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ hh h2
  have h4 : h = 0 := by
    have := congrArg (fun k => k - h) h3
    simpa using this.symm
  rwa [h4] at hh

lemma isHeight_neg (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) : B.IsHeight Dp N (-y) (-h) := by
  obtain ⟨h', hh'⟩ := B.isHeight_exists hB1 Dp N hN (-y) (by rw [smul_neg, hy, neg_zero])
  have h2 := B.isHeight_add hB1 Dp N hN H hh'
  rw [add_neg_cancel] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ h2 (B.isHeight_zero hB1 Dp N hN)
  have h4 : h' = -h := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
  rwa [h4] at hh'

lemma isHeight_zsmul (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (k : ℤ) : B.IsHeight Dp N (k • y) (k • h) := by
  have hnat : ∀ m : ℕ, B.IsHeight Dp N (m • y) (m • h) := by
    intro m
    induction m with
    | zero => simpa using B.isHeight_zero hB1 Dp N hN
    | succ m ih => rw [succ_nsmul, succ_nsmul]; exact B.isHeight_add hB1 Dp N hN ih H
  rcases k with m | m
  · simpa using hnat m
  · have hm : N • ((m + 1) • y) = 0 := by rw [smul_comm, hy, smul_zero]
    have := B.isHeight_neg hB1 Dp N hN hm (hnat (m + 1))
    simpa [negSucc_zsmul] using this

lemma isHeight_sum (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {ι : Type} (s : Finset ι) (y : ι → B.G R) (hy : ∀ i, N • y i = 0)
    (h : ι → B.gg →ₗ[R₀] (R : Type u)) (H : ∀ i, B.IsHeight Dp N (y i) (h i)) :
    B.IsHeight Dp N (∑ i ∈ s, y i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using B.isHeight_zero hB1 Dp N hN
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact B.isHeight_add hB1 Dp N hN (H a) ih

end BX

end ReciprocityTheory.PGsh
end
end

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace ATower

variable {p : ℕ} (Tw : ATower R₀ p)

lemma ξmul_surj (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by
  rintro ⟨k, hk⟩
  have hk' : k ∈ Ideal.span {Tw.ξ n} := by
    rw [← Tw.ker_eq n]
    simpa using hk
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hk'
  refine ⟨a, Subtype.ext ?_⟩
  show Tw.ξ n * a = k
  rw [← ha, mul_comm]

lemma exists_factor (n : ℕ) : ∃ g' : (Tw.π n).ker →ₗ[R₀] (Tw.R n : Type u),
    g' ∘ₗ ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) = (Tw.π n).1.toLinearMap := by
  have hle : LinearMap.ker (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) ≤
      LinearMap.ker (Tw.π n).1.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : Tw.ξ n * a = 0 := congrArg Subtype.val ha
    have hm : a ∈ Ideal.span {Tw.ξ n} := Tw.ann n a (by rw [mul_comm]; exact h0)
    rw [← Tw.ker_eq n, RingHom.mem_ker] at hm
    exact hm
  have hs := Tw.ξmul_surj n
  refine ⟨(LinearMap.ker _).liftQ _ hle ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hs).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun a => ?_
  have h1 : (LinearMap.quotKerEquivOfSurjective _ hs).symm (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) a) =
      Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]

end ATower

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma nsmul_ker_zero (Tw : ATower R₀ p) (n : ℕ) (V : B.gg ⊗[R₀] (Tw.π n).ker) :
    (p ^ (n + 1)) • V = 0 := by
  have hc : ((p : (Tw.R' n : Type u))) ^ (n + 1) = 0 := by exact_mod_cast Tw.char n
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul g k =>
    have hk : (p ^ (n + 1)) • k = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul, hc]
    rw [← TensorProduct.tmul_smul, hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

lemma exists_lift (Tw : ATower R₀ p) (n : ℕ) (y : B.G (Tw.R n)) (hy : (p ^ (n + 1)) • y = 0) :
    ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.map (Tw.π n) th = y ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) := by
  obtain ⟨th, hth⟩ := B.surj (Tw.π n) (Tw.sqZero n) y
  have h0 : B.map (Tw.π n) ((p ^ (n + 1)) • th) = 0 := by rw [map_nsmul, hth, hy]
  obtain ⟨v, hv⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 h0
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective B.gg (Tw.ξmul_surj n) v
  exact ⟨th, w, hth, by rw [← hv, ← hw]; rfl⟩

lemma lift_indep (Tw : ATower R₀ p) (n : ℕ) (th th' : B.G (Tw.R' n)) (w w' : B.gg ⊗[R₀] (Tw.R' n : Type u))
    (he : B.map (Tw.π n) th = B.map (Tw.π n) th')
    (hw : (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w))
    (hw' : (p ^ (n + 1)) • th' = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w')) :
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w = LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w' := by
  have hd : B.map (Tw.π n) (th - th') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨v0, hv0⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 hd
  have hp : (p ^ (n + 1)) • th = (p ^ (n + 1)) • th' := by
    have h : (p ^ (n + 1)) • (th - th') = 0 := by
      rw [← hv0, ← map_nsmul, B.nsmul_ker_zero Tw n v0, map_zero]
    rwa [smul_sub, sub_eq_zero] at h
  rw [hw, hw'] at hp
  have hx := B.tg_inj (Tw.π n) (Tw.sqZero n) hp
  obtain ⟨g', hg'⟩ := Tw.exists_factor n
  rw [← hg', LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (LinearMap.lTensor B.gg g') hx

end BX

end ReciprocityTheory.PGsh
end
end

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma tw_πr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.π n).comp (Tw.r' n) = (Tw.r n).comp (Tw.π (n + 1)) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact (Tw.r_π n x).symm

lemma tw_qr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.r n).comp (Tw.q (n + 1)) = Tw.q n := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact Tw.r_q n x

lemma lift_down (Tw : ATowerL R₀ p) (n : ℕ) (τ1 : B.G Tw.O) (th1 : B.G (Tw.R' (n + 1)))
    (w1 : B.gg ⊗[R₀] (Tw.R' (n + 1) : Type u)) (h1 : B.map (Tw.π (n + 1)) th1 = B.map (Tw.q (n + 1)) τ1)
    (h2 : (p ^ (n + 1 + 1)) • th1 = B.tg (Tw.π (n + 1)) (Tw.sqZero (n + 1))
      (TensorProduct.map LinearMap.id (ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1))) w1)) :
    B.map (Tw.π n) (p • B.map (Tw.r' n) th1) = B.map (Tw.q n) (p • τ1) ∧
    (p ^ (n + 1)) • (p • B.map (Tw.r' n) th1) = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n))
        (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1)) ∧
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1) =
      LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
        (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap w1) := by
  have e1 : B.map (Tw.π n) (B.map (Tw.r' n) th1) = B.map (Tw.q n) τ1 := by
    rw [← B.map_comp, tw_πr Tw n, B.map_comp, h1, ← B.map_comp, tw_qr Tw n]
  have hf : ∀ a ∈ (Tw.π (n + 1)).ker, (Tw.r' n).1.toLinearMap a ∈ (Tw.π n).ker := by
    intro a ha
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
    rw [AlgHom.toLinearMap_apply, ← Tw.r_π n a, ha, map_zero]
  have hcomm : ((Tw.r' n).1.toLinearMap.restrict hf) ∘ₗ
      ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1)) =
      ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) ∘ₗ (Tw.r' n).1.toLinearMap := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    show (Tw.r' n).1 (Tw.ξ (n + 1) * a) = Tw.ξ n * (Tw.r' n).1 a
    rw [map_mul, Tw.r'_ξ n]
  have h3 : (Tw.π n).1.toLinearMap ∘ₗ (Tw.r' n).1.toLinearMap =
      (Tw.r n).1.toLinearMap ∘ₗ (Tw.π (n + 1)).1.toLinearMap :=
    LinearMap.ext fun a => (Tw.r_π n a).symm
  refine ⟨by rw [map_nsmul, map_nsmul, e1], ?_, ?_⟩
  · rw [smul_smul, ← pow_succ, ← map_nsmul, h2,
      ← B.tg_nat (Tw.π (n + 1)) (Tw.π n) (Tw.sqZero (n + 1)) (Tw.sqZero n) (Tw.r' n) hf]
    have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) hcomm
    simp only [LinearMap.lTensor_comp, LinearMap.comp_apply] at h
    exact congrArg (B.tg (Tw.π n) (Tw.sqZero n)) h
  · have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) h3
    simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply] using h

def coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (k : Module.Free.ChooseBasisIndex R₀ B.gg) :
    B.gg ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M ((Module.Free.chooseBasis R₀ B.gg).coord k)

lemma coordK_lTensor {M M' : Type u} [AddCommGroup M] [Module R₀ M] [AddCommGroup M'] [Module R₀ M']
    (f : M →ₗ[R₀] M') (k : Module.Free.ChooseBasisIndex R₀ B.gg) (x : B.gg ⊗[R₀] M) :
    B.coordK M' k (LinearMap.lTensor B.gg f x) = f (B.coordK M k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m => simp [coordK]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma sum_coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (x : B.gg ⊗[R₀] M) :
    ∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] B.coordK M k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m =>
    simp only [coordK, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, Module.Basis.coord_apply]
    simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

lemma exists_lim_tensor (Tw : ATowerL R₀ p) (wb : ∀ n, B.gg ⊗[R₀] (Tw.R n : Type u))
    (hwb : ∀ n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap (wb (n + 1)) = wb n) :
    ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n, LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt = wb n := by
  choose a ha using fun k => Tw.complete (fun n => B.coordK (Tw.R n) k (wb n)) (fun n => by
    rw [← hwb n, B.coordK_lTensor]
    rfl)
  refine ⟨∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] a k, fun n => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [LinearMap.lTensor_tmul]
  conv_rhs => rw [← B.sum_coordK _ (wb n)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← ha k n]
  rfl

end BX

end ReciprocityTheory.PGsh
end
end

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma ATower.char_R {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := by
  have h := congrArg (Tw.π n).1 (Tw.char n)
  rwa [map_natCast, map_zero] at h

theorem lim (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) :
    LimStatement B Tw Dt := by
  intro ι τ hτ hc
  have hN : ∀ n, ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := fun n => Tw.toATower.char_R n
  have hy : ∀ i n, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i n => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hex : ∀ i n, ∃ h, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n)) h :=
    fun i n => BX.isHeight_exists (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n)
  choose h hh using hex
  have hcomp : ∀ i n, (Tw.r n).1.toLinearMap ∘ₗ h i (n + 1) = h i n := by
    intro i n
    have H1 := BX.isHeight_map (B := B) hB1 (Dt.Dp (n + 1)) (Dt.Dp n) (Tw.r n) (Dt.d n) (Dt.d_π n)
      (Dt.d_σ n) (Dt.d_η n) _ _ _ (hh i (n + 1))
    rw [← B.map_comp, BX.tw_qr Tw n, pow_succ] at H1
    have hy1 : (p ^ (n + 1) * p) • B.map (Tw.q n) (τ i (n + 1)) = 0 := by
      rw [← pow_succ, ← map_nsmul, hτ i (n + 1), map_zero]
    have H2 := BX.isHeight_mul_p (B := B) hB1 (Dt.Dp n) (p ^ (n + 1)) p (hN n) _ hy1 _ H1
    rw [← map_nsmul, ← hc i n] at H2
    exact BX.isHeight_unique (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n) _ _ H2 (hh i n)
  have hlimv : ∀ i (v : B.gg), ∃ a : (Tw.O : Type u), ∀ n, (Tw.q n).1 a = h i n v := fun i v =>
    Tw.complete (fun n => h i n v) (fun n => by
      have := LinearMap.congr_fun (hcomp i n) v
      simpa using this)
  choose hta hta_spec using hlimv
  have hsep : ∀ a b : (Tw.O : Type u), (∀ n, (Tw.q n).1 a = (Tw.q n).1 b) → a = b := fun a b hab =>
    sub_eq_zero.mp (Tw.sep _ (fun n => by rw [map_sub, hab n, sub_self]))
  let ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u) := fun i =>
    { toFun := hta i
      map_add' := fun v w => hsep _ _ (fun n => by simp only [map_add (f := _), hta_spec])
      map_smul' := fun c v => hsep _ _ (fun n => by simp only [map_smul, hta_spec, RingHom.id_apply]) }
  have hlift : ∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) :=
    fun i n => BX.exists_lift (B := B) Tw.toATower n _ (hy i n)
  choose th w hthw using hlift
  have hwb : ∀ i n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
      (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap (w i (n + 1))) =
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := by
    intro i n
    obtain ⟨d1, d2, d3⟩ := BX.lift_down (B := B) Tw n (τ i (n + 1)) (th i (n + 1)) (w i (n + 1))
      (hthw i (n + 1)).1 (hthw i (n + 1)).2
    rw [← d3]
    apply BX.lift_indep (B := B) Tw.toATower n _ _ _ _ ?_ d2 (hthw i n).2
    rw [d1, ← hc i n, (hthw i n).1]
  have hbt : ∀ i, ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n,
      LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt =
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := fun i =>
    BX.exists_lim_tensor (B := B) Tw (fun n => LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n))
      (hwb i)
  choose bt hbt using hbt
  refine ⟨ht, bt, fun i n => ?_, fun i n => ⟨th i n, w i n, (hthw i n).1, (hthw i n).2, (hbt i n).symm⟩⟩
  have hq : (Tw.q n).1.toLinearMap ∘ₗ ht i = h i n := by
    ext v
    simp [ht, hta_spec]
  rw [hq]
  exact hh i n

theorem htLin (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) :
    HtLinStatement B Tw Dp := by
  intro ι _ τ ht a α hτ hH hα n
  have hN := Tw.char_R n
  have hy : ∀ i, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hlin : (Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i =
      ∑ i, a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i) := by
    ext v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [LinearMap.sum_apply, map_sum, map_mul, hα, zsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hlin]
  simp only [map_zsmul]
  exact BX.isHeight_sum (B := B) hB1 (Dp n) (p ^ (n + 1)) hN Finset.univ
    (fun i => a i n • B.map (Tw.q n) (τ i n)) (fun i => by rw [smul_comm, hy i, smul_zero])
    (fun i => a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i))
    (fun i => BX.isHeight_zsmul (B := B) hB1 (Dp n) (p ^ (n + 1)) hN (hy i) (hH i n) (a i n))

end ReciprocityTheory.PGsh

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LocGradedTop

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsCocycle
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section Co

variable {A k ι : Type} [CommRing A] [CommRing k] [Fintype ι] [DecidableEq ι] {K : Ideal A} {σ co : A → k}

private theorem co_zero (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) : co 0 = 0 := by
  have := h1 0 K.zero_mem 0 K.zero_mem
  rw [add_zero] at this
  exact left_eq_add.1 this

private theorem co_sum (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (S : Finset ι) (f : ι → A)
    (hf : ∀ c, f c ∈ K) : co (∑ c ∈ S, f c) = ∑ c ∈ S, co (f c) := by
  induction S using Finset.induction_on with
  | empty => simpa using co_zero h1
  | insert c S hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, h1 _ (hf c) _ (K.sum_mem fun c _ => hf c), ih]

omit [DecidableEq ι] in
private theorem mem_left (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) (a b : ι) : (M * Z) a b ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun c _ => K.mul_mem_left _ (hZ _ _)

omit [DecidableEq ι] in
private theorem mem_right (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) (a b : ι) :
    (Z * M) a b ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun c _ => K.mul_mem_right _ (hZ _ _)

private theorem co_left (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (h2 : ∀ a, ∀ x ∈ K, co (a * x) = σ a * co x)
    (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) : (M * Z).map co = M.map σ * Z.map co := by
  ext a b
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [co_sum h1 _ _ fun c => K.mul_mem_left _ (hZ _ _)]
  exact Finset.sum_congr rfl fun c _ => h2 _ _ (hZ _ _)

private theorem co_right (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (h2 : ∀ a, ∀ x ∈ K, co (a * x) = σ a * co x)
    (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) : (Z * M).map co = Z.map co * M.map σ := by
  ext a b
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [co_sum h1 _ _ fun c => K.mul_mem_right _ (hZ _ _)]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm, h2 _ _ (hZ _ _), mul_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem co_add (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y)
    {Z Z' : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) (hZ' : ∀ a b, Z' a b ∈ K) :
    (Z + Z').map co = Z.map co + Z'.map co := by
  ext a b
  exact h1 _ (hZ _ _) _ (hZ' _ _)

end Co

section LC

variable {T A ι : Type} [TopologicalSpace T] [CommRing A] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem lc_matrix {B : Type} {f : T → Matrix ι ι B} (h : ∀ a b, IsLocallyConstant fun s => f s a b) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in nhds x, ∀ a b, f y a b = f x a b :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (h a b).eventually_eq x
  exact this.mono fun y hy => Matrix.ext hy

omit [DecidableEq ι] in
private theorem lc_ac {I : Ideal A} {f : T → Matrix ι ι A} (h : ∀ a b, AdicCont I fun s => f s a b) (N : ℕ) :
    IsLocallyConstant fun s => (f s).map (Ideal.Quotient.mk (I ^ N)) :=
  lc_matrix fun a b => h a b N

omit [Fintype ι] [DecidableEq ι] in
private theorem lc_ker [IsNoetherianRing A] {I K : Ideal A} (hs : I * K = ⊥) {f : T → Matrix ι ι A}
    (hf : ∀ s a b, f s a b ∈ K) (h : ∀ N, IsLocallyConstant fun s => (f s).map (Ideal.Quotient.mk (I ^ N))) :
    IsLocallyConstant f := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_inf_eq_pow_smul I (K : Submodule A A)
  have e := hn (n + 1) (Nat.le_succ n)
  have e2 : ∀ x ∈ K, x ∈ I ^ (n + 1) → x = 0 := fun x hx hx' => by
    have m : x ∈ (I ^ (n + 1) • (⊤ : Submodule A A)) ⊓ K := ⟨by simpa using hx', hx⟩
    rw [e, Nat.add_sub_cancel_left, pow_one] at m
    have : x ∈ I * K := Submodule.smul_mono le_rfl inf_le_right m
    rwa [hs, Ideal.mem_bot] at this
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  refine ((h (n + 1)).eventually_eq x).mono fun y hy => ?_
  ext a b
  have := congrFun (congrFun hy a) b
  exact sub_eq_zero.1 (e2 _ (K.sub_mem (hf _ _ _) (hf _ _ _)) (Ideal.Quotient.eq.1 this))

end LC

section G

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  {A : Type} [CommRing A] [Algebra O A]

omit [IsLocalRing O] [DecidableEq ι] in
private theorem part_mul (W : WPres O X A) {M M' : Matrix ι ι A} (h : ∀ a b, M a b ∈ W.part (w a - w b))
    (h' : ∀ a b, M' a b ∈ W.part (w a - w b)) (a b : ι) : (M * M') a b ∈ W.part (w a - w b) := by
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have := SetLike.GradedMul.mul_mem (h a c) (h' c b)
  rwa [sub_add_sub_cancel] at this

omit [IsLocalRing O] [DecidableEq ι] [Fintype ι] in
private theorem part_alg (W : WPres O X A) {M : Matrix ι ι O} (h : ∀ a b, w a ≠ w b → M a b = 0) (a b : ι) :
    (M.map (algebraMap O A)) a b ∈ W.part (w a - w b) := by
  rw [Matrix.map_apply]
  by_cases e : w a = w b
  · rw [e, sub_self, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  · rw [h a b e, map_zero]
    exact Submodule.zero_mem _

private theorem co_gw [IsCO O A] (Φ : FormData O w) (W : WPres O X A) {K : Ideal A} {j : X} {co : A → ResidueField O}
    (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (h2 : ∀ a, ∀ x ∈ K, co (a * x) = res O A a * co x)
    (h3 : ∀ j', j' ≠ j → ∀ x ∈ K, x ∈ W.part j' → co x = 0) {Y : Matrix ι ι A} (hK : ∀ a b, Y a b ∈ K)
    (hW : ∀ a b, Y a b ∈ W.part (w a - w b)) (hY : Y ∈ Φ.g A) : Y.map co ∈ Φ.gw (ResidueField O) j := by
  obtain ⟨y1, y2⟩ := hY
  have hJ : (Φ.JR A).map (res O A) = Φ.JR (ResidueField O) := by
    ext a b
    simp [FormData.JR]
  have hK' : ∀ a b, Y.transpose a b ∈ K := fun a b => hK b a
  refine ⟨⟨?_, fun a b e => ?_⟩, fun a b e => h3 _ e _ (hK a b) (hW a b)⟩
  · have := congrArg (fun M : Matrix ι ι A => M.map co) y1
    rw [co_add h1 (mem_right _ hK') (mem_left _ hK), co_left h1 h2 _ hK, co_right h1 h2 _ hK', hJ,
      Matrix.transpose_map] at this
    rw [this]
    ext a b
    exact co_zero h1
  · rw [Matrix.map_apply, y2 a b e, co_zero h1]

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

end G

theorem UpperTheory.V.Alg.obs_cocycle :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (W : WPres O X A) (j : X) (co : A → ResidueField O),
          (∀ x ∈ RingHom.ker p, ∀ y ∈ RingHom.ker p, co (x + y) = co x + co y) → (∀ (a : A), ∀ x ∈ RingHom.ker p, co (a * x) = res O A a * co x) → (∀ j', j' ≠ j → ∀ x ∈ RingHom.ker p, x ∈ W.part j' → co x = 0) →
          ∀ (rt : Γ → Matrix ι ι A), (∀ s, Φ.HH (rt s * (r0.hom s⁻¹).map (algebraMap O A))) → (∀ a b, AdicCont (maximalIdeal A) fun s => rt s a b) → (∀ s a b, rt s a b ∈ W.part (w a - w b)) → (∀ s t, (rt s * rt t).map p = (rt (s * t)).map p) →
          ∀ (α : F.T → Matrix ι ι A) (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) A), (∀ v, Φ.HH (α v)) → (∀ v a b, α v a b ∈ W.part (w a - w b)) → (∀ v, Φ.InH (r0.hom.comp (F.φ v)) A (ρ v)) → (∀ v s a b, (ρ v).hom s a b ∈ W.part (w a - w b)) → (∀ v s, (rt (F.φ v s) * α v).map p = (α v * (ρ v).hom s).map p) →
          ∀ (rq : ∀ q, Lift O (rbar.comp (F.ψ q)) A), (∀ q, Φ.InH (r0.hom.comp (F.ψ q)) A (rq q)) → (∀ q s a b, (rq q).hom s a b ∈ W.part (w a - w b)) → (∀ q s, (rt (F.ψ q s)).map p = ((rq q).hom s).map p) →
          ∃ z ∈ F.framedTwoCocycles (FormData.adRep hbar j), (∀ s t, (z.1 (s, t)).1 * rbar (s * t) = (rt s * rt t - rt (s * t)).map co) ∧ (∀ v s, (z.2.1 v s).1 * rbar (F.φ v s) = (rt (F.φ v s) * α v - α v * (ρ v).hom s).map co) ∧ ∀ q s, (z.2.2 q s).1 * rbar (F.ψ q s) = (rt (F.ψ q s) - (rq q).hom s).map co := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F A _ _ _ R _ _ _ p hp hs W j co c1 c2 c3 rt t1 t2 t3 t4
    α ρ a1 a2 a3 a4 a5 rq q1 q2 q3
  obtain ⟨g1, g2, -, -, g5, -⟩ := hh_group O ι X w Φ A
  have g6 := g5 Γ r0.hom h0
  obtain ⟨-, s2, -⟩ := hh_small O ι X w Φ h2 A R p hp hs
  have r0res : ∀ s, ((r0.hom s).map (algebraMap O A)).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, AlgHom.commutes, ← r0.red, ← (res O O).commutes]
    rfl
  have r0inv : ∀ s, (r0.hom s⁻¹).map (algebraMap O A) * (r0.hom s).map (algebraMap O A) = 1 := fun s => by
    rw [← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one]; simp
  have rinv : ∀ s, rbar s⁻¹ * rbar s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  have rtres : ∀ s, (rt s).map (res O A) = rbar s := fun s => by
    have := (t1 s).2.2
    rw [map_mul_alg, r0res] at this
    calc (rt s).map (res O A) = (rt s).map (res O A) * rbar s⁻¹ * rbar s := by rw [mul_assoc, rinv, mul_one]
      _ = rbar s := by rw [this, one_mul]
  have hker : ∀ {Z Z' : Matrix ι ι A}, Z.map p = Z'.map p → ∀ a b, (Z - Z') a b ∈ RingHom.ker p := by
    intro Z Z' e a b
    have := congrFun (congrFun e a) b
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
    exact sub_eq_zero.2 this
  have key : ∀ (s : Γ) (Z Z' : Matrix ι ι A), Φ.HH (Z * (r0.hom s⁻¹).map (algebraMap O A)) →
      Φ.HH (Z' * (r0.hom s⁻¹).map (algebraMap O A)) → Z.map p = Z'.map p →
      (∀ a b, Z a b ∈ W.part (w a - w b)) → (∀ a b, Z' a b ∈ W.part (w a - w b)) →
      (Z - Z').map co * rbar s⁻¹ ∈ Φ.gw (ResidueField O) j := by
    intro s Z Z' k1 k2 e w1 w2
    rw [← r0res, ← co_right c1 c2 _ (hker e)]
    refine co_gw Φ W c1 c2 c3 (mem_right _ (hker e))
      (part_mul W (fun a b => Submodule.sub_mem _ (w1 a b) (w2 a b)) (part_alg W (h0.2.2 _))) ?_
    rw [sub_mul]
    exact s2 _ _ k2 k1 (by rw [map_mul_alg, map_mul_alg, e])
  have lcbar : IsLocallyConstant rbar := by
    refine lc_matrix fun a b => ?_
    have := (r0.cont a b 1).comp (Ideal.Quotient.lift (maximalIdeal O ^ 1) (res O O : O →+* ResidueField O)
      fun x hx => (res_eq_zero_iff O O x).2 (by rwa [pow_one] at hx))
    convert this using 1
    funext s
    exact (r0.red s a b).symm
  have lcinv : IsLocallyConstant fun s : Γ => rbar s⁻¹ := lcbar.comp_continuous continuous_inv
  have lct := lc_ac t2
  have mD : ∀ x : Γ × Γ, (rt x.1 * rt x.2 - rt (x.1 * x.2)).map co * rbar (x.1 * x.2)⁻¹ ∈
      Φ.gw (ResidueField O) j := by
    rintro ⟨s, t⟩
    refine key _ _ _ ?_ (t1 _) (t4 s t) (part_mul W (t3 s) (t3 t)) (t3 _)
    convert g2 _ _ (t1 s) (g6 s _ (t1 t)) using 1
    simp only [mul_inv_rev, map_mul, Matrix.map_mul, mul_assoc]
    rw [← mul_assoc _ ((r0.hom s).map _), r0inv, one_mul]
  have lD : IsLocallyConstant fun x : Γ × Γ => (⟨_, mD x⟩ : Φ.gw (ResidueField O) j) := by
    refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
    have l1 : IsLocallyConstant fun x : Γ × Γ => rt x.1 * rt x.2 - rt (x.1 * x.2) := by
      refine lc_ker hs (fun x => hker (t4 x.1 x.2)) fun N => ?_
      simp only [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk _)), Matrix.map_mul]
      exact (((lct N).comp_continuous continuous_fst).mul ((lct N).comp_continuous continuous_snd)).sub
        ((lct N).comp_continuous continuous_mul)
    exact (l1.comp (fun M => M.map co)).mul (lcinv.comp_continuous continuous_mul)
  have loc : ∀ (G : Type) [Group G] [TopologicalSpace G] (φ : G →* Γ), Continuous φ → ∀ (β : Matrix ι ι A)
      (τ : Lift O (rbar.comp φ) A), Φ.HH β → (∀ a b, β a b ∈ W.part (w a - w b)) → Φ.InH (r0.hom.comp φ) A τ →
      (∀ s a b, τ.hom s a b ∈ W.part (w a - w b)) → (∀ s, (rt (φ s) * β).map p = (β * τ.hom s).map p) →
      ∃ y : G → Φ.gw (ResidueField O) j, IsLocallyConstant y ∧
        (∀ s t, (⟨_, mD (φ s, φ t)⟩ : Φ.gw (ResidueField O) j) =
          dOne ((FormData.adRep hbar j).comp φ) y (s, t)) ∧
        ∀ s, (y s).1 * rbar (φ s) = (rt (φ s) * β - β * τ.hom s).map co := by
    intro G _ _ φ hφ β τ b1 b2 b3 b4 b5
    have mE : ∀ s, (rt (φ s) * β - β * τ.hom s).map co * rbar (φ s)⁻¹ ∈ Φ.gw (ResidueField O) j := by
      intro s
      refine key _ _ _ ?_ ?_ (b5 s) (part_mul W (t3 _) b2) (part_mul W b2 (b4 s))
      · convert g2 _ _ (t1 (φ s)) (g6 (φ s) _ b1) using 1
        simp only [mul_assoc]
        rw [← mul_assoc _ ((r0.hom (φ s)).map _), r0inv, one_mul]
      · have := g2 _ _ b1 (b3 s)
        rwa [MonoidHom.comp_apply, map_inv, ← mul_assoc] at this
    refine ⟨fun s => ⟨_, mE s⟩, ?_, fun s t => Subtype.ext ?_, fun s => ?_⟩
    · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      have l1 : IsLocallyConstant fun s => rt (φ s) * β - β * τ.hom s := by
        refine lc_ker hs (fun s => hker (b5 s)) fun N => ?_
        simp only [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk _)), Matrix.map_mul]
        exact (((lct N).comp_continuous hφ).mul (IsLocallyConstant.const _)).sub
          ((IsLocallyConstant.const _).mul (lc_ac τ.cont N))
      exact (l1.comp (fun M => M.map co)).mul (lcinv.comp_continuous hφ)
    · have e : (rt (φ s) * β - β * τ.hom s) * τ.hom t + rt (φ s) * (rt (φ t) * β - β * τ.hom t) =
          (rt (φ s) * rt (φ t) - rt (φ s * φ t)) * β + (rt (φ (s * t)) * β - β * τ.hom (s * t)) := by
        simp only [map_mul]
        noncomm_ring
      have e' := congrArg (fun M : Matrix ι ι A => M.map co) e
      have τres : (τ.hom t).map (res O A) = rbar (φ t) := Matrix.ext fun a b => τ.red t a b
      rw [co_add c1 (mem_right _ (hker (b5 s))) (mem_left _ (hker (b5 t))),
        co_add c1 (mem_right _ (hker (t4 _ _))) (hker (b5 _)), co_right c1 c2 _ (hker (b5 s)),
        co_left c1 c2 _ (hker (b5 t)), co_right c1 c2 _ (hker (t4 _ _)), b1.2.2, τres, rtres, mul_one] at e'
      show (rt (φ s) * rt (φ t) - rt (φ s * φ t)).map co * rbar (φ s * φ t)⁻¹ =
        (rt (φ s) * β - β * τ.hom s).map co * rbar (φ s)⁻¹ +
        rbar (φ s) * ((rt (φ t) * β - β * τ.hom t).map co * rbar (φ t)⁻¹) * rbar (φ s)⁻¹ -
        (rt (φ (s * t)) * β - β * τ.hom (s * t)).map co * rbar (φ (s * t))⁻¹
      rw [eq_sub_iff_add_eq, map_mul φ s t]
      rw [map_mul φ s t] at e'
      rw [← add_mul, ← e', mul_inv_rev, map_mul, add_mul]
      simp only [mul_assoc]
      rw [← mul_assoc (rbar (φ t)), ← map_mul rbar (φ t), mul_inv_cancel, map_one, one_mul]
    · show _ * rbar (φ s)⁻¹ * _ = _
      rw [mul_assoc, rinv, mul_one]
  have one_part : ∀ a b, (1 : Matrix ι ι A) a b ∈ W.part (w a - w b) := fun a b => by
    have := part_alg W (w := w) (M := 1) (fun a b e => Matrix.one_apply_ne fun h => e (by rw [h])) a b
    rwa [Matrix.map_one _ (map_zero _) (map_one _)] at this
  choose y y1 y2 y3 using fun v => loc _ (F.φ v) (F.hφ v) (α v) (ρ v) (a1 v) (a2 v) (a3 v) (a4 v) (a5 v)
  choose x x1 x2 x3 using fun q => loc _ (F.ψ q) (F.hψ q) 1 (rq q) g1 one_part (q1 q) (q2 q)
    (fun s => by rw [mul_one, one_mul, q3])
  refine ⟨(fun x => ⟨_, mD x⟩, y, x), ⟨lD, y1, x1, fun s t u => Subtype.ext ?_, y2, x2⟩, fun s t => ?_, y3,
    fun q s => ?_⟩
  · have e : rt s * (rt t * rt u - rt (t * u)) + (rt s * rt (t * u) - rt (s * (t * u))) =
        (rt (s * t) * rt u - rt (s * t * u)) + (rt s * rt t - rt (s * t)) * rt u := by
      rw [mul_assoc s t u]
      noncomm_ring
    have e' := congrArg (fun M : Matrix ι ι A => M.map co) e
    rw [co_add c1 (mem_left _ (hker (t4 _ _))) (hker (t4 _ _)), co_add c1 (hker (t4 _ _)) (mem_right _ (hker (t4 _ _))),
      co_left c1 c2 _ (hker (t4 _ _)), co_right c1 c2 _ (hker (t4 _ _)), rtres, rtres] at e'
    show rbar s * ((rt t * rt u - rt (t * u)).map co * rbar (t * u)⁻¹) * rbar s⁻¹ +
      (rt s * rt (t * u) - rt (s * (t * u))).map co * rbar (s * (t * u))⁻¹ =
      (rt (s * t) * rt u - rt (s * t * u)).map co * rbar (s * t * u)⁻¹ +
      (rt s * rt t - rt (s * t)).map co * rbar (s * t)⁻¹
    have e2 := congrArg (fun M => M * rbar (s * t * u)⁻¹) e'
    simp only [add_mul, mul_assoc, ← map_mul] at e2 ⊢
    have n1 : (t * u)⁻¹ * s⁻¹ = (s * (t * u))⁻¹ := by group
    have n2 : u * (s * (t * u))⁻¹ = (s * t)⁻¹ := by group
    rw [n2] at e2
    rw [n1]
    exact e2
  · show _ * rbar (s * t)⁻¹ * _ = _
    rw [mul_assoc, rinv, mul_one]
  · have := x3 q s
    rwa [mul_one, one_mul] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsCorrect
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CocycleNormalForm
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.cocycle_normal_form :
    ∀ (k Γ M : Type) [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] (F : Frame Γ) (ρ : Representation k Γ M), (∀ m : M, IsLocallyConstant fun s => ρ s m) → (∀ q, ∀ n ∈ F.N q, ∀ m, ρ (F.ψ q n) m = m) →
          ∀ x ∈ F.framedTwoCoboundaries ρ, ∃ (h : Γ → M) (y : F.T → M), IsLocallyConstant h ∧ y F.v0 = 0 ∧ x.1 = dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧ ∀ q, ∀ n ∈ F.N q, x.2.2 q n = h (F.ψ q n) := by
  intro k Γ M _ _ _ _ _ F ρ hρ hN x hx
  unfold Frame.framedTwoCoboundaries at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, y, e, h1, h2, h3, h4, h5⟩ := hx
    refine ⟨fun s => h s - (ρ s (y F.v0) - y F.v0), fun v => y v - y F.v0,
      h1.sub ((hρ _).sub (IsLocallyConstant.const _)), sub_self _, ?_, fun v s => ?_, fun q n hn => ?_⟩
    · rw [h3]
      funext p
      simp only [dOne, map_sub, map_mul, Module.End.mul_apply]
      abel
    · rw [h4]
      simp only [map_sub]
      abel
    · rw [h5, (h2 q).2.2 n hn]
      simp only [hN q n hn, sub_self]
  | zero =>
    refine ⟨0, 0, IsLocallyConstant.const 0, rfl, ?_, by simp, by simp⟩
    funext p
    simp [dOne]
  | add x x' _ _ ih ih' =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    obtain ⟨h', y', b1, b2, b3, b4, b5⟩ := ih'
    refine ⟨h + h', y + y', a1.add b1, by simp [a2, b2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp only [Prod.fst_add, Pi.add_apply, a3, b3, dOne, map_add (f := _)]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add (f := _)]
      abel
    · simp only [Prod.snd_add, Pi.add_apply, a5 q n hn, b5 q n hn]
  | smul c x _ ih =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    refine ⟨c • h, c • y, a1.comp (c • ·), by simp [a2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp [a3, dOne, smul_sub]
    · simp [a4, smul_sub]
    · simp [a5 q n hn]
end

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_strictHenselian_absolutely_closed_local_ring {k A ι : Type} [CommRing k] [CommRing A] [Fintype ι] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : Matrix ι ι k →+ Matrix ι ι A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : Matrix ι ι A) Y, M * T Y = T (M.map π * Y)) ∧
      ∀ (M : Matrix ι ι A) Y, T Y * M = T (Y * M.map π) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_⟩
  · ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]

private theorem rbar_lc {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] (r : Lift O rbar R) : IsLocallyConstant fun s => rbar s := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rbar t a b = rbar s a b := fun a b => by
    filter_upwards [(r.cont a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff O, map_sub, r.red, r.red, sub_eq_zero] at ht
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

theorem UpperTheory.V.Alg.obs_correct :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) →
          ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ →
          ∀ (μ : ResidueField O → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res O A a * c) = a * μ c) → (∀ c, p (μ c) = 0) →
          ∀ (i : B →ₐ[O] A) (r : Lift O rbar R) (rt : Γ → Matrix ι ι A), (∀ s, Φ.HH (rt s * (r0.hom s⁻¹).map (algebraMap O A))) → (∀ a b, AdicCont (maximalIdeal A) fun s => rt s a b) → (∀ s, (rt s).map p = r.hom s) →
          ∀ (α : F.T → Matrix ι ι A), (∀ v, Φ.HH (α v)) → α F.v0 = 1 →
          ∀ (rq : ∀ q, Lift O (rbar.comp (F.ψ q)) A), (∀ q, Φ.InH (r0.hom.comp (F.ψ q)) A (rq q)) → (∀ q, L q A (rq q)) → (∀ q, (rq q).map p = r.comap (F.ψ q) (F.hψ q)) →
          ∀ (j : X), ∀ x ∈ F.framedTwoCoboundaries (FormData.adRep hbar j), (∀ s t, rt s * rt t - rt (s * t) = ((x.1 (s, t)).1 * rbar (s * t)).map μ) → (∀ v s, rt (F.φ v s) * α v - α v * ((ρ v).hom s).map i = ((x.2.1 v s).1 * rbar (F.φ v s)).map μ) → (∀ q s, rt (F.ψ q s) - (rq q).hom s = ((x.2.2 q s).1 * rbar (F.ψ q s)).map μ) →
          ∃ (r' : Lift O rbar A) (α' : F.T → Matrix ι ι A), IsFramed Φ r0.hom F L ρ i r' α' ∧ r'.map p = r ∧ ∀ v, (α' v).map p = (α v).map p := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F L hN hL B _ _ _ ρ A _ _ _ R _ _ _ p hp hs μ m1 m2 m3
    i r rt t1 t2 t3 α a1 a2 rq q1 q2 q3 j x hx x1 x2 x3
  obtain ⟨T, T0, Tl, Tr⟩ := exists_strictHenselian_absolutely_closed_local_ring (ι := ι) (res O A) μ m1 m2
  simp only [T0] at x1 x2 x3
  have lc := rbar_lc r0
  have ad : ∀ s (Y : Φ.gw (ResidueField O) j), (FormData.adRep hbar j s Y).1 = rbar s * Y.1 * rbar s⁻¹ :=
    fun _ _ => rfl
  obtain ⟨h, y, b1, b2, b3, b4, b5⟩ := cocycle_normal_form _ _ _ F (FormData.adRep hbar j) (fun m => by
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      exact (lc.comp (· * m.1)).mul (lc.comp_continuous continuous_inv))
    (fun q n hn m => Subtype.ext (by
      rw [ad, ← map_inv, hN q n hn, hN q _ (inv_mem hn), one_mul, mul_one])) x hx
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res O A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res O A (μ _) = 0
    rw [← res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (rt s).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← r.red, ← t3, Matrix.map_apply]
  have r0res : ∀ s, ((r0.hom s).map (algebraMap O A)).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, ← r0.red]
    exact res_map (Algebra.ofId O A) _
  have ρres : ∀ v s, (((ρ v).hom s).map i).map (res O A) = rbar (F.φ v s) := fun v s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, res_map, (ρ v).red]
    rfl
  have Jres : (Φ.JR A).map (res O A) = Φ.JR (ResidueField O) := by
    ext a b
    simp [FormData.JR]
  have Tg : ∀ Y : Φ.gw (ResidueField O) j, T Y.1 ∈ Φ.g A := fun Y => by
    obtain ⟨⟨y1, y2⟩, -⟩ := Y.2
    refine ⟨?_, fun a b e => ?_⟩
    · have : (T Y.1).transpose = T Y.1.transpose := by rw [← T0, ← T0, Matrix.transpose_map]
      rw [this, Tl, Tr, Jres, ← map_add (f := _), y1, map_zero]
    · have : T 0 a b = 0 := by rw [map_zero]; rfl
      rw [← T0, Matrix.map_apply, y2 a b e, ← this, ← T0]
      rfl
  obtain ⟨-, -, s3⟩ := hh_small O ι X w Φ h2 A R p hp hs
  obtain ⟨-, -, g3, -⟩ := hh_group O ι X w Φ A
  have inv1 : ∀ s, rbar s * rbar s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rbar s⁻¹ * rbar s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → Matrix ι ι A := fun s => rt s - T ((h s).1 * rbar s) with hf
  have fH : ∀ s, Φ.HH (f s * (r0.hom s⁻¹).map (algebraMap O A)) := fun s => by
    have := s3 _ _ (t1 s) (Tg (-h s)) (Tp _)
    rw [hf]
    simp only
    rw [sub_mul, Tr, r0res, mul_assoc, inv1, mul_one, sub_eq_add_neg, ← map_neg]
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (FormData.adRep hbar j) h (s, t)).1 : Matrix ι ι _) * rbar (s * t) =
        (h s).1 * rbar s * rbar t + rbar s * ((h t).1 * rbar t) - (h (s * t)).1 * rbar (s * t) := by
      show ((h s).1 + rbar s * (h t).1 * rbar s⁻¹ - (h (s * t)).1) * rbar (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rbar s * (h t).1), ← mul_assoc (rbar s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add (f := _)]
    abel
  have fone : f 1 = 1 := by
    obtain ⟨u, -, hu, -⟩ := g3 _ (fH 1)
    rw [inv_one, map_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at hu
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = f 1 * (f 1 * u) := by rw [hu, mul_one]
      _ = 1 := by rw [← mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r.hom s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, t3, sub_zero]
  let r' : Lift O rbar A :=
    { hom := { toFun := f, map_one' := fone, map_mul' := fmul }
      cont := fun a b N => by
        have c1 := t2 a b N
        have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rbar s) a b) :=
          ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
        have c3 := c1.sub c2
        convert c3 using 2 with s
        exact map_sub _ _ _
      red := fun s a b => by
        have := congrFun (congrFun (fp s) a) b
        rw [← r.red, ← this, Matrix.map_apply, res_map]
        rfl }
  have r'p : r'.map p = r := by
    ext s a b
    exact congrFun (congrFun (fp s) a) b
  refine ⟨r', fun v => α v + T (y v).1, ⟨fH, fun q => ?_, fun v => s3 _ _ (a1 v) (Tg _) (Tp _), ?_, fun v s => ?_⟩,
    r'p, fun v => ?_⟩
  · refine ((hL q).tangent A R p hp hs (rq q) (r'.comap (F.ψ q) (F.hψ q)) (q1 q) (fun s => ?_) ?_ (q2 q)).2
      fun n hn => ?_
    · have := fH (F.ψ q s)
      rw [← map_inv] at this
      exact this
    · rw [q3, ← r'p]
      rfl
    · have e := x3 q n
      rw [b5 q n hn] at e
      show rt (F.ψ q n) - T _ = _
      rw [← e, sub_sub_cancel]
  · simp only [a2, b2]
    simp
  · have e := x2 v s
    rw [b4, sub_eq_iff_eq_add] at e
    have e' : ((h (F.φ v s) - (FormData.adRep hbar j (F.φ v s) (y v) - y v)).1 : Matrix ι ι _) * rbar (F.φ v s) =
        (h (F.φ v s)).1 * rbar (F.φ v s) - (rbar (F.φ v s) * (y v).1 - (y v).1 * rbar (F.φ v s)) := by
      show ((h (F.φ v s)).1 - (rbar (F.φ v s) * (y v).1 * rbar (F.φ v s)⁻¹ - (y v).1)) * rbar (F.φ v s) = _
      rw [sub_mul, sub_mul, mul_assoc, inv2, mul_one]
    show (rt (F.φ v s) - T _) * (α v + T _) = (α v + T _) * _
    rw [sub_mul, mul_add, mul_add, add_mul, TT, Tl, Tr, Tr, rtres, ρres, (a1 v).2.2, mul_one, e, e', map_sub, map_sub]
    abel
  · show (α v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerCoef
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Classical in
private theorem wcomp_of_mem_ite {O : Type} [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X) {i j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt i) : wcomp O wt j f = if i = j then f else 0 := by
  ext n
  rw [coeff_wcomp]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    split_ifs with hn
    · rfl
    · exact (hf n hn).symm
  · rw [if_neg h, map_zero]
    split_ifs with hn
    · exact hf n (fun hi => h (hi.symm.trans hn))
    · rfl

theorem UpperTheory.V.Alg.ker_coef :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (W : WPres O X A) (κ : Type) [Fintype κ] (ε : κ → A) (wf : κ → X), (∀ u, ε u ∈ W.part (wf u)) → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) →
          ∃ co : κ → A → ResidueField O, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res O A a * co u x) ∧
            (∀ u j, j ≠ wf u → ∀ x ∈ K, x ∈ W.part j → co u x = 0) ∧ ∀ x ∈ K, ∃ a : κ → O, (∀ u, residue O (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro O _ _ X _ A _ _ _ K hK W κ _ ε wf hε hspan hrel
  classical
  have hεK : ∀ v, ε v ∈ K := fun v => by
    rw [hspan]
    exact Ideal.subset_span ⟨v, rfl⟩
  have hkill : ∀ (r : A) (y : A), r ∈ maximalIdeal A → y ∈ K → r * y = 0 := by
    intro r y hr hy
    have h1 := Ideal.mul_mem_mul hr hy
    rw [hK] at h1
    exact (Ideal.mem_bot).1 h1
  have hrep : ∀ x ∈ K, ∃ a : κ → O, x = ∑ v, a v • ε v := by
    intro x hx
    rw [hspan] at hx
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hx
    choose a ha using fun v => IsCO.res_surj (O := O) (r v)
    refine ⟨a, ?_⟩
    rw [← hr]
    apply Finset.sum_congr rfl
    intro v _
    have h0 := hkill _ _ (ha v) (hεK v)
    rw [smul_eq_mul, Algebra.smul_def]
    linear_combination h0
  let co : κ → A → ResidueField O := fun u x =>
    if h : ∃ a : κ → O, x = ∑ v, a v • ε v then residue O (h.choose u) else 0
  have hco : ∀ x (a : κ → O), x = ∑ v, a v • ε v → ∀ u, co u x = residue O (a u) := by
    intro x a hx u
    have h : ∃ a : κ → O, x = ∑ v, a v • ε v := ⟨a, hx⟩
    simp only [co]
    rw [dite_eq_left h]
    have hd : ∑ v, (h.choose v - a v) • ε v = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h.choose_spec, ← hx, sub_self]
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hrel _ hd u)
  refine ⟨co, ?_, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hrep x hx
    obtain ⟨b, hb⟩ := hrep y hy
    have hxy : x + y = ∑ v, (a + b) v • ε v := by
      rw [ha, hb, ← Finset.sum_add_distrib]
      simp only [Pi.add_apply, add_smul]
    rw [hco _ _ hxy u, hco _ _ ha u, hco _ _ hb u, Pi.add_apply, map_add (f := _)]
  · intro u a x hx
    obtain ⟨b, hb⟩ := hrep x hx
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have hax : a * x = ∑ v, (c * b v) • ε v := by
      have h0 := hkill _ _ hc hx
      have h1 : a * x = algebraMap O A c * x := by linear_combination h0
      rw [h1, hb, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_smul, ← Algebra.smul_def]
    have hr : res O A a = residue O c := by
      have h1 := (res_eq_zero_iff O A _).2 hc
      rw [map_sub, sub_eq_zero, AlgHom.commutes] at h1
      rw [h1]
      rfl
    rw [hco _ _ hax u, hco _ _ hb u, map_mul, hr]
  · intro u j hj x hxK hxP
    obtain ⟨a, ha⟩ := hrep x hxK
    rw [hco x a ha u]
    apply (IsLocalRing.residue_eq_zero_iff _).2
    have hε' : ∀ v, ε v ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt (wf v)) := hε
    choose f hf hfε using fun v => Submodule.mem_map.1 (hε' v)
    have hxP' : x ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j) := hxP
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.1 hxP'
    simp only [AlgHom.toLinearMap_apply] at hfε hgx
    have hk : g - ∑ v, a v • f v ∈ RingHom.ker W.π := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, map_sub, map_sum]
      simp only [map_smul, hfε]
      rw [hgx, ← ha, sub_self]
    have hh := W.homog _ hk (wf u)
    have hfw : ∀ v, wcomp O W.wt (wf u) (f v) = if wf v = wf u then f v else 0 :=
      fun v => wcomp_of_mem_ite W.wt (hf v)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, wcomp_of_mem_ite W.wt hg, if_neg hj] at hh
    simp only [map_smul, hfw] at hh
    have hrel0 : ∑ v, (if wf v = wf u then a v else 0) • ε v = 0 := by
      have h2 := RingHom.mem_ker.1 hh
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_zero, map_sum, zero_sub, neg_eq_zero] at h2
      rw [← h2]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with hv
      · rw [map_smul, hfε]
      · rw [smul_zero, map_zero, zero_smul]
    have h5 := hrel _ hrel0 u
    simpa using h5
  · intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    exact ⟨a, fun u => (hco x a ha u).symm, ha⟩
end

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem ac_mul {S A ι : Type} [TopologicalSpace S] [CommRing A] [Fintype ι] (I : Ideal A)
    {M N : S → Matrix ι ι A} (hM : ∀ a b, AdicCont I fun s => M s a b) (hN : ∀ a b, AdicCont I fun s => N s a b) :
    ∀ a b, AdicCont I fun s => (M s * N s) a b := by
  intro a b n
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const _
  | insert c t hc ih =>
    simp only [Finset.sum_insert hc]
    exact ((hM a c n).mul (hN c b n)).add ih

private theorem ac_map {O S R R' : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace S] [CommRing R] [Algebra O R]
    [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : S → R}
    (hx : AdicCont (maximalIdeal R) x) : AdicCont (maximalIdeal R') fun s => f (x s) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hx N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem hmul {O ι X R : Type} [CommRing O] [Fintype ι] [AddCommGroup X] [CommRing R] [Algebra O R]
    (P : X → Submodule O R) (hP : ∀ i j x y, x ∈ P i → y ∈ P j → x * y ∈ P (i + j)) (w : ι → X)
    {A B : Matrix ι ι R} (hA : ∀ a b, A a b ∈ P (w a - w b))
    (hB : ∀ a b, B a b ∈ P (w a - w b)) : ∀ a b, (A * B) a b ∈ P (w a - w b) := by
  intro a b
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have := hP _ _ _ _ (hA a c) (hB c b)
  rwa [sub_add_sub_cancel] at this

private theorem hconst {O ι X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (P : X → Submodule O R) (hP : (1 : R) ∈ P 0) (w : ι → X) {M : Matrix ι ι O}
    (hM : ∀ a b, w a ≠ w b → M a b = 0) : ∀ a b, (M.map (algebraMap O R)) a b ∈ P (w a - w b) := by
  intro a b
  rw [Matrix.map_apply]
  by_cases h : w a = w b
  · rw [h, sub_self, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ hP
  · rw [hM a b h, map_zero]
    exact zero_mem _

private theorem norm_comp {O : Type} [CommRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X]
    {w : ι → X} {Φ : FormData O w} {R : Type} [CommRing R] [Algebra O R] {Γ H : Type} [Group Γ] [Group H]
    {ρ : Γ →* Matrix ι ι R} (h : Φ.Normalises ρ) (φ : H →* Γ) : Φ.Normalises (ρ.comp φ) := by
  obtain ⟨h1, ⟨π, h2⟩, h3⟩ := h
  exact ⟨fun g => h1 (φ g), ⟨π.comp φ, fun g => h2 (φ g)⟩, fun g => h3 (φ g)⟩

private theorem ex_mu {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsCO O A] (η : A)
    (hη : ∀ x ∈ maximalIdeal A, x * η = 0) :
    ∃ μ : ResidueField O →+ A, (∀ a : O, μ (residue O a) = a • η) ∧ ∀ (a : A) c, μ (res O A a * c) = a * μ c := by
  have k : ∀ a b : O, residue O a = residue O b → a • η = b • η := fun a b h => by
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    refine hη _ ?_
    rw [← res_eq_zero_iff O, AlgHom.commutes, ResidueField.algebraMap_eq, map_sub, h, sub_self]
  choose s hs using residue_surjective (R := O)
  have k2 : ∀ a : O, s (residue O a) • η = a • η := fun a => k _ _ (hs _)
  refine ⟨AddMonoidHom.mk' (fun c => s c • η) fun c d => ?_, k2, fun a c => ?_⟩
  · rw [← add_smul]
    exact k _ _ (by rw [map_add (f := _), hs, hs, hs])
  · obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
    have e : res O A a = residue O b := by
      have := (res_eq_zero_iff O A _).2 hb
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
    have e2 : a * η = b • η := by
      have := hη _ hb
      rwa [sub_mul, sub_eq_zero, ← Algebra.smul_def] at this
    show s _ • η = a * (s c • η)
    rw [mul_smul_comm, e2, smul_smul]
    exact k _ _ (by rw [map_mul, hs, hs, e, mul_comm])

private theorem mmap {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

private theorem cmap {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A : Matrix ι ι O) : (A.map (algebraMap O R)).map f = A.map (algebraMap O S) := by
  ext a b
  simp

theorem UpperTheory.V.Alg.obs_class :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (W : WPres O X A), (∀ s, W.z s ∈ maximalIdeal A) →
      ∀ (κ : Type) [Fintype κ] (ε : κ → A) (wf : κ → X), (∀ u, ε u ∈ W.part (wf u)) → RingHom.ker p = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) →
      ∀ (i : B →ₐ[O] A) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsFramed Φ r0.hom F L ρ (p.comp i) r α →
      (∀ v s a b, i ((ρ v).hom s a b) ∈ W.part (w a - w b)) → (∀ s a b, r.hom s a b ∈ (W.part (w a - w b)).map p.toLinearMap) → (∀ v a b, α v a b ∈ (W.part (w a - w b)).map p.toLinearMap) →
      ∃ o : ∀ j, {u // wf u = j} → F.Ob (FormData.adRep hbar j), ∀ (j : X) [Fintype {u // wf u = j}] (c : {u // wf u = j} → O), ∑ u, residue O (c u) • o j u = 0 →
        ∀ (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A'] (p' : A →ₐ[O] A') (p'' : A' →ₐ[O] R) (η : A'), Function.Surjective p' → p''.comp p' = p → (∀ x ∈ maximalIdeal A', x * η = 0) → p'' η = 0 →
          (∀ u : {u // wf u = j}, p' (ε u) = c u • η) → (∀ u, wf u ≠ j → p' (ε u) = 0) →
          ∃ (r' : Lift O rbar A') (α' : F.T → Matrix ι ι A'), IsFramed Φ r0.hom F L ρ (p'.comp i) r' α' ∧ r'.map p'' = r ∧ ∀ v, (α' v).map p'' = α v := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F L hN hL hL0 B _ _ _ ρ hρ A _ _ _ R _ _ _ p hp hs W hz
    κ _ ε wf hε hK hind i r α hfr hw1 hw2 hw3
  classical
  obtain ⟨hr, hrL, hα, hα0, hE⟩ := hfr
  have P1 : ∀ i j x y, x ∈ W.part i → y ∈ W.part j → x * y ∈ W.part (i + j) := fun _ _ _ _ hx hy =>
    SetLike.GradedMul.mul_mem hx hy
  have P0 : (1 : A) ∈ W.part 0 := SetLike.GradedOne.one_mem
  have Q1 : ∀ i j x y, x ∈ (W.part i).map p.toLinearMap → y ∈ (W.part j).map p.toLinearMap →
      x * y ∈ (W.part (i + j)).map p.toLinearMap := by
    rintro _ _ _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, P1 _ _ _ _ hx hy, map_mul p x y⟩
  have Q0 : (1 : R) ∈ (W.part 0).map p.toLinearMap := ⟨1, P0, map_one p⟩
  have c0 : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S] (a b : ι),
      AdicCont (maximalIdeal S) fun s => ((r0.hom s).map (algebraMap O S)) a b := fun S _ _ _ a b =>
    ac_map (Algebra.ofId O S) (r0.cont a b)
  have inv0 : ∀ (S : Type) [CommRing S] [Algebra O S] (s t : Γ), s * t = 1 →
      (r0.hom s).map (algebraMap O S) * (r0.hom t).map (algebraMap O S) = 1 := fun S _ _ s t h => by
    rw [← Matrix.map_mul, ← map_mul, h, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨ht, ht1, ht2, ht3, ht4⟩ := hh_section O ι X w Φ h2 A R p hp hs W hz Γ
    (fun s => r.hom s * (r0.hom s⁻¹).map (algebraMap O R)) hr
    (ac_mul _ r.cont fun a b n => (c0 R a b n).comp_continuous continuous_inv)
    (fun s => hmul _ Q1 w (hw2 s) (hconst (fun i => (W.part i).map p.toLinearMap) Q0 w (h0.2.2 _)))
  obtain ⟨rt, r1, r2, r3, r4⟩ : ∃ rt : Γ → Matrix ι ι A, (∀ s, Φ.HH (rt s * (r0.hom s⁻¹).map (algebraMap O A))) ∧
      (∀ a b, AdicCont (maximalIdeal A) fun s => rt s a b) ∧ (∀ s a b, rt s a b ∈ W.part (w a - w b)) ∧
      ∀ s, (rt s).map p = r.hom s := by
    refine ⟨fun s => ht s * (r0.hom s).map (algebraMap O A), fun s => ?_, ac_mul _ ht2 (c0 A),
      fun s => hmul _ P1 w (ht3 s) (hconst _ P0 w (h0.2.2 _)), fun s => ?_⟩
    · rw [mul_assoc, inv0 A _ _ (mul_inv_cancel s), mul_one]
      exact ht1 s
    · rw [mmap, ht4, cmap, mul_assoc, inv0 R _ _ (inv_mul_cancel s), mul_one]
  obtain ⟨αt, a1, a2, a3, a4⟩ : ∃ αt : F.T → Matrix ι ι A, (∀ v, Φ.HH (αt v)) ∧
      (∀ v a b, αt v a b ∈ W.part (w a - w b)) ∧ (∀ v, (αt v).map p = α v) ∧ αt F.v0 = 1 := by
    letI : TopologicalSpace F.T := ⊥
    haveI : DiscreteTopology F.T := ⟨rfl⟩
    obtain ⟨β, b1, -, b3, b4⟩ := hh_section O ι X w Φ h2 A R p hp hs W hz F.T α hα
      (fun a b n => IsLocallyConstant.of_discrete _) hw3
    refine ⟨fun v => if v = F.v0 then 1 else β v, fun v => ?_, fun v => ?_, fun v => ?_, if_pos rfl⟩
    · beta_reduce
      split_ifs
      · exact (hh_group O ι X w Φ A).1
      · exact b1 v
    · beta_reduce
      split_ifs
      · have := hconst (R := A) _ P0 w (M := 1) fun a b h => Matrix.one_apply_ne fun e => h (by rw [e])
        rwa [Matrix.map_one _ (map_zero _) (map_one _)] at this
      · exact b3 v
    · beta_reduce
      split_ifs with h
      · rw [h, hα0, Matrix.map_one _ (map_zero _) (map_one _)]
      · exact b4 v
  have hhom : IsHomog O W.wt (RingHom.ker (p.comp W.π)) := by
    have := (homog_span O A X W κ (fun u => ⟨ε u, W.part_le_A (hε u)⟩) wf hε).1
    rw [← hK] at this
    exact this
  choose rq q1 q2 q3 q4 using fun q => loc_graded_top O ι X w Φ h2 (F.Gq q) (rbar.comp (F.ψ q))
    (r0.comap (F.ψ q) (F.hψ q)) (norm_comp hbar _) (norm_comp h0 _) (F.N q) (L q) (hL q) A R p hp hs W hz hhom
    (r.comap (F.ψ q) (F.hψ q)) (fun s => by simpa [Lift.comap] using hr (F.ψ q s)) (hrL q) (fun s => hw2 _)
  obtain ⟨co, k1, k2, k3, k4⟩ := ker_coef O X A (RingHom.ker p) hs W κ ε wf hε hK hind
  have inH : ∀ (S S' : Type) [CommRing S] [Algebra O S] [IsCO O S] [CommRing S'] [Algebra O S'] [IsCO O S']
      (f : S →ₐ[O] S') (M : Matrix ι ι S) (N : Matrix ι ι O), Φ.HH (M * N.map (algebraMap O S)) →
      Φ.HH (M.map f * N.map (algebraMap O S')) := fun S S' _ _ _ _ _ _ f M N h => by
    have := (hh_group O ι X w Φ S).2.2.2.1 S' f _ h
    rwa [mmap, cmap] at this
  have d1 : ∀ s t, (rt s * rt t).map p = (rt (s * t)).map p := fun s t => by
    rw [mmap, r4, r4, r4, map_mul]
  have d2 : ∀ v s, (rt (F.φ v s) * αt v).map p = (αt v * ((ρ v).map i).hom s).map p := fun v s => by
    rw [mmap, mmap, r4, a3, hE]
    rfl
  have d3 : ∀ q s, (rt (F.ψ q s)).map p = ((rq q).hom s).map p := fun q s => by
    rw [r4]
    exact (congrArg (fun x : Lift O _ R => x.hom s) (q3 q)).symm
  choose z z0 z1 z2 z3 using fun u : κ => obs_cocycle O ι X w Φ h2 Γ rbar r0 hbar h0 F A R p hp hs W (wf u) (co u)
    (k1 u) (k2 u) (k3 u) rt r1 r2 r3 d1 αt (fun v => (ρ v).map i) a1 a2 (fun v s => inH _ _ i _ _ (hρ v s)) hw1 d2
    rq q1 q4 d3
  have ex : ∀ j (u : {u // wf u = j}), ∃ z ∈ F.framedTwoCocycles (FormData.adRep hbar j),
      (∀ s t, (z.1 (s, t)).1 * rbar (s * t) = (rt s * rt t - rt (s * t)).map (co u)) ∧
      (∀ v s, (z.2.1 v s).1 * rbar (F.φ v s) = (rt (F.φ v s) * αt v - αt v * ((ρ v).map i).hom s).map (co u)) ∧
      ∀ q s, (z.2.2 q s).1 * rbar (F.ψ q s) = (rt (F.ψ q s) - (rq q).hom s).map (co u) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨z u, z0 u, z1 u, z2 u, z3 u⟩
  clear z0 z1 z2 z3 z
  choose z z0 z1 z2 z3 using ex
  refine ⟨fun j u => Submodule.Quotient.mk ⟨z j u, z0 j u⟩, ?_⟩
  intro j _ c hc A' _ _ _ p' p'' η hp' hpp hη hη0 e1 e2
  have hx : ∑ u, residue O (c u) • z j u ∈ F.framedTwoCoboundaries (FormData.adRep hbar j) := by
    have h1 : (Submodule.Quotient.mk (∑ u, residue O (c u) • (⟨z j u, z0 j u⟩ : F.framedTwoCocycles (FormData.adRep hbar j))) :
        F.Ob (FormData.adRep hbar j)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, ← Submodule.mkQ_apply, map_sum]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_sum] at h1
    exact h1
  obtain ⟨μ, m1, m2⟩ := ex_mu (O := O) η hη
  have pp : ∀ x, p'' (p' x) = p x := fun x => DFunLike.congr_fun hpp x
  have key : ∀ x, p x = 0 → p' x = μ (∑ u : {u // wf u = j}, residue O (c u) * co u x) := fun x hx => by
    obtain ⟨a, ha, hxa⟩ := k4 x hx
    have : ∑ u : {u // wf u = j}, residue O (c u) * co u x = residue O (∑ u : {u // wf u = j}, a u * c u) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_mul, ha, mul_comm]
    rw [this, m1, Finset.sum_smul]
    conv_lhs => rw [hxa]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Fintype.sum_subtype_add_sum_subtype (fun u => wf u = j),
      Finset.sum_eq_zero (s := (Finset.univ : Finset {u // ¬ wf u = j})) fun u _ => by
        rw [map_smul, e2 u u.2, smul_zero], add_zero]
    convert Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, e1, mul_smul]
  have keyM : ∀ (M N : Matrix ι ι A) (Y : {u // wf u = j} → Φ.gw (ResidueField O) j) (g : Matrix ι ι (ResidueField O)),
      M.map p = N.map p → (∀ u, (Y u).1 * g = (M - N).map (co u)) →
      M.map p' - N.map p' = ((∑ u, residue O (c u) • Y u).1 * g).map μ := fun M N Y g h1 h3 => by
    ext a b
    have h4 : p ((M - N) a b) = 0 := by
      rw [Matrix.sub_apply, map_sub, sub_eq_zero]
      exact congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, key _ h4,
      Matrix.map_apply, Submodule.coe_sum, Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Submodule.coe_smul, smul_mul_assoc, h3]
    rfl
  have m3 : ∀ d, p'' (μ d) = 0 := fun d => by
    obtain ⟨a, rfl⟩ := residue_surjective d
    rw [m1, map_smul, hη0, smul_zero]
  have hp'' : Function.Surjective p'' := fun y => by
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨p' x, pp x⟩
  have hs' : maximalIdeal A' * RingHom.ker p'' = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨y, rfl⟩ := hp' y
    rw [RingHom.mem_ker, pp] at hy
    rw [Ideal.mem_bot, key y hy, ← m2, (res_eq_zero_iff O A' x).2 hx, zero_mul, map_zero]
  have mm : ∀ M : Matrix ι ι A, (M.map p').map p'' = M.map p := fun M => by
    ext a b
    exact pp _
  refine (obs_correct O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL B ρ A' R p'' hp'' hs' μ
    μ.map_add m2 m3 (p'.comp i) r (fun s => (rt s).map p') (fun s => inH _ _ p' _ _ (r1 s))
    (fun a b => ac_map p' (r2 a b)) (fun s => by rw [mm, r4]) (fun v => (αt v).map p')
    (fun v => (hh_group O ι X w Φ A).2.2.2.1 A' p' _ (a1 v))
    (by rw [a4, Matrix.map_one _ (map_zero _) (map_one _)]) (fun q => (rq q).map p')
    (fun q s => inH _ _ p' _ _ (q1 q s)) (fun q => ?_) (fun q => ?_) j _ hx (fun s t => ?_) (fun v s => ?_)
    (fun q s => ?_)).elim fun r' h => h.elim fun α' f => ⟨r', α', f.1, f.2.1, fun v => by rw [f.2.2, mm, a3]⟩
  · obtain ⟨I, hI⟩ := (hL q).closed A (rq q) (q1 q)
    refine (hI A' p').2 fun x hx => ?_
    have : x = 0 := (hI A (AlgHom.id O A)).1 (q2 q) x hx
    rw [this, map_zero]
  · rw [← q3 q]
    ext s a b
    exact pp _
  · have := keyM _ _ (fun u => (z j u).1 (s, t)) _ (d1 s t) fun u => z1 j u s t
    rw [mmap] at this
    rw [this, Prod.fst_sum, Finset.sum_apply]
    rfl
  · have := keyM _ _ (fun u => (z j u).2.1 v s) _ (d2 v s) fun u => z2 j u v s
    rw [mmap, mmap] at this
    rw [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Finset.sum_apply]
    exact this
  · have := keyM _ _ (fun u => (z j u).2.2 q s) _ (d3 q s) fun u => z3 j u q s
    rw [Prod.snd_sum, Prod.snd_sum, Finset.sum_apply, Finset.sum_apply]
    exact this

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MapThetaLie
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrpOfMemSucc
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prp_of_mem {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K j) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = X := by
  ext a b
  show (if pw a b = j then X a b else 0) = X a b
  split_ifs with h
  · rfl
  · exact (hX a b h).symm

private theorem prp_of_mem_succ {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K (j + 1)) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext a b
  show (if pw a b = j then X a b else 0) = 0
  split_ifs with h
  · have hne : ∀ p q : ZMod 2, p = q → p ≠ q + 1 := by decide
    exact hX a b (hne _ _ h)
  · rfl

private theorem prp_add {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K) :
    X = ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) + (prp K (j + 1) X : adp K (j + 1)) := by
  ext a b
  show X a b = (if pw a b = j then X a b else 0) + (if pw a b = j + 1 then X a b else 0)
  have hc : ∀ p q : ZMod 2, (p = q ∧ p ≠ q + 1) ∨ (p ≠ q ∧ p = q + 1) := by decide
  rcases hc (pw a b) j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_pos h2, zero_add]

theorem UpperTheory.V.Fr.ep_prp :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), (∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X)) ∧ ∀ (j : ZMod 2) (χ : F.Γ → K), (∀ f : Matrix (Fin 3) (Fin 3) K →ₗ[K] K, (∀ g X, f (B.ad g X) = χ g * f X) → f = 0) → ∀ f : adp K j →ₗ[K] K, (∀ g X, f (h.ad j g X) = χ g * f X) → f = 0 := by
  intro l _ k _ F K _ h2 B π h
  have P1 : ∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X) := by
    intro j s X
    apply Subtype.ext
    rw [Box.Ev.ad_apply]
    conv_lhs => rw [prp_add j X]
    rw [map_add (f := _), map_add (f := _), Submodule.coe_add,
      prp_of_mem j _ (h.stab j s (prp K j X).2),
      prp_of_mem_succ j _ (h.stab (j + 1) s (prp K (j + 1) X).2), add_zero]
  refine ⟨P1, ?_⟩
  intro j χ hχ f hf
  have hF := hχ (f.comp (prp K j)) (fun g X => by simp only [LinearMap.comp_apply, P1, hf])
  ext v
  have := LinearMap.congr_fun hF (v : Matrix (Fin 3) (Fin 3) K)
  have hv : prp K j (v : Matrix (Fin 3) (Fin 3) K) = v := Subtype.ext (prp_of_mem j _ v.2)
  simpa [hv] using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.BorelProjectionIsTwoCocycle
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem grp_id {H : Type*} [Group H] (a b c ab bc abc : H) :
    (a * b * ab⁻¹) * (ab * c * abc⁻¹) = (a * (b * c * bc⁻¹) * a⁻¹) * (a * bc * abc⁻¹) := by
  group

theorem UpperTheory.V.Fr.borelProjection_isTwoCocycle :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ s t r, (B.bar O).ad s ((D.co u).1 (t, r)) + (D.co u).1 (s, t * r) = (D.co u).1 (s * t, r) + (D.co u).1 (s, t) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK s t r
  have hKm : RingHom.ker p ≤ maximalIdeal C' := by
    intro y hy
    rw [← res_eq_zero_iff O C', ← res_map p y, RingHom.mem_ker.mp hy, map_zero]
  obtain ⟨hom, -, -, -⟩ := pr_omk hF O C' C p B D hK
  obtain ⟨x, hx⟩ : ∃ x : F.Γ → GG (m := n) (R := C'), ∀ a, x a = ⟨D.r a, F.del a⟩ := ⟨_, fun _ => rfl⟩
  have hW : ∀ a b, x a * x b * (x (a * b))⁻¹ =
      GG.ofGL (D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹) := by
    intro a b
    rw [hx, hx, hx]
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
        SemidirectProduct.inv_right, SemidirectProduct.left_inl, GG.ofGL]
      rw [← MulAut.mul_apply, ← map_mul, map_mul F.del a b, mul_inv_cancel, map_one, MulAut.one_apply]
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.right_inl,
        GG.ofGL, map_mul, mul_inv_cancel, mul_one]
  have hz : ∀ a b, ((D.r a * sgnAct n C' (F.del a) (D.r b) * (D.r (a * b))⁻¹ : GL (Fin n) C') :
      Matrix (Fin n) (Fin n) C') = 1 + D.om (a, b) := by
    intro a b
    simp [SetLift.om]
  have hbar : (B.bar O).r s = GG.map (res O C' : C' →+* ResidueField O) (x s) := by
    rw [hx]
    apply SemidirectProduct.ext
    · ext i j
      simp [Box.map, GG.map, ← D.r_map s, res_map]
    · simp [Box.map, GG.map, B.nu]
  have key : ∀ a b : GG (m := n) (R := C'), a.right = 1 → (a * b).mat = a.mat * b.mat := by
    intro a b ha
    simp only [GG.mat, SemidirectProduct.mul_left, ha, map_one, MulAut.one_apply, Units.val_mul]
  have hofr : ∀ w : GL (Fin n) C', (GG.ofGL w).right = 1 := fun w => rfl
  have hmat : ∀ w : GL (Fin n) C', (GG.ofGL w).mat = (w : Matrix (Fin n) (Fin n) C') := fun w => rfl
  have hW' : x s * x (t * r) * (x (s * t * r))⁻¹ =
      GG.ofGL (D.r s * sgnAct n C' (F.del s) (D.r (t * r)) * (D.r (s * (t * r)))⁻¹) := by
    rw [mul_assoc s t r]
    exact hW s (t * r)
  have h := grp_id (x s) (x t) (x r) (x (s * t)) (x (t * r)) (x (s * t * r))
  rw [hW s t, hW (s * t) r, hW t r, hW'] at h
  have hyr : (x s * GG.ofGL (D.r t * sgnAct n C' (F.del t) (D.r r) * (D.r (t * r))⁻¹) * (x s)⁻¹).right
      = 1 := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, GG.ofGL,
      SemidirectProduct.right_inl, mul_one, mul_inv_cancel]
  have hM := congrArg GG.mat h
  rw [key _ _ (hofr _), key _ _ hyr, hmat, hmat, hmat] at hM
  obtain ⟨-, -, hE3⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (t, r)) (hom (t, r))
  obtain ⟨hAK, hAmap, hconj⟩ := hE3 (x s)
  rw [hconj _ (hz t r), hz s t, hz (s * t) r, hz s (t * r)] at hM
  obtain ⟨h1, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm (D.om (s, t)) (hom (s, t))
  obtain ⟨h12, h12add, -⟩ := h1 (D.om (s * t, r)) (hom _)
  obtain ⟨hA, -, -⟩ := pr_evk O C' n (RingHom.ker p) u hK hKm ((x s).adFun (D.om (t, r))) hAK
  obtain ⟨hA4, hA4add, -⟩ := hA (D.om (s, t * r)) (hom _)
  have hsum : D.om (s, t) + D.om (s * t, r) = (x s).adFun (D.om (t, r)) + D.om (s, t * r) := by
    have e1 : (1 + D.om (s, t)) * (1 + D.om (s * t, r)) = 1 + (D.om (s, t) + D.om (s * t, r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, h12]
      abel
    have e2 : (1 + (x s).adFun (D.om (t, r))) * (1 + D.om (s, t * r)) =
        1 + ((x s).adFun (D.om (t, r)) + D.om (s, t * r)) := by
      rw [add_mul, one_mul, mul_add, mul_one, hA4]
      abel
    rw [e1, e2] at hM
    exact add_left_cancel hM
  change ((B.bar O).r s).adFun ((D.om (t, r)).map (evK (RingHom.ker p) u)) +
      (D.om (s, t * r)).map (evK (RingHom.ker p) u) =
      (D.om (s * t, r)).map (evK (RingHom.ker p) u) + (D.om (s, t)).map (evK (RingHom.ker p) u)
  rw [hbar, ← hAmap, ← hA4add, add_comm ((D.om (s * t, r)).map _), ← h12add, hsum]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothVectorFixedByOpenSubgroup
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.smooth_vector_fixed_by_open_subgroup :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ χ : F.Γ →* kˣ, χ F.c = -1 → (∀ v, ∃ s, χ (F.loc v s) ≠ 1) → Nontrivial (H1C F.loc (chRep χ) fun _ => ⊥) → ∃ x : F.Γ → k, IsLocallyConstant x ∧ (∀ g h, x (g * h) = x g + χ g * x h) ∧ x F.c = 0 ∧ (∀ v, ∃ Y : k, ∀ s, x (F.loc v s) = χ (F.loc v s) * Y - Y) ∧ ∃ g : F.G0, x g ≠ 0 := by
  intro l _ k _ _ F C₀ hok χ hc hloc hnt
  obtain ⟨q, hq⟩ := exists_ne (0 : H1C F.loc (chRep χ) fun _ => ⊥)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq
  obtain ⟨⟨x, y⟩, hz⟩ := z
  obtain ⟨hlc, hcoc, hlocz⟩ := hz
  simp only [chRep_apply] at hcoc
  simp only [chRep_apply, Submodule.mem_bot] at hlocz
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h')
  have hx1 : x 1 = 0 := by
    have e := hcoc 1 1
    rw [mul_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  have hχ : ∀ s, (χ s : k) * x F.c = x (s * F.c) - x s := by
    intro s
    rw [hcoc]
    ring
  set X : k := -(x F.c) / 2 with hX
  set x' : F.Γ → k := fun s => x s - ((χ s : k) * X - X) with hx'
  have hform : x' = fun s => (x s + x (s * F.c) - x F.c) / 2 := by
    funext s
    simp only [hx', hX]
    rw [show x (s * F.c) = (χ s : k) * x F.c + x s by rw [hχ]; ring]
    field_simp
    ring
  have hcoc' : ∀ g h, x' (g * h) = x' g + (χ g : k) * x' h := by
    intro g h
    simp only [hx']
    rw [hcoc, map_mul, Units.val_mul]
    ring
  have hc' : x' F.c = 0 := by
    rw [hform]
    simp only
    rw [hok.c_sq, hx1]
    ring
  have hloc' : ∀ v s, x' (F.loc v s) = (χ (F.loc v s) : k) * (y v - X) - (y v - X) := by
    intro v s
    simp only [hx']
    have e := hlocz v s
    linear_combination e
  refine ⟨x', ?_, hcoc', hc', fun v => ⟨y v - X, hloc' v⟩, ?_⟩
  · rw [hform]
    exact IsLocallyConstant.comp₂ hlc (hlc.comp_continuous (continuous_mul_const F.c))
      (fun a b => (a + b - x F.c) / 2)
  · by_contra hall
    push_neg at hall
    have hzero : ∀ γ, x' γ = 0 := by
      intro γ
      rcases Int.units_eq_one_or (F.del γ) with hd | hd
      · exact hall ⟨γ, hd⟩
      · have hm : γ * F.c ∈ F.del.ker := by
          rw [MonoidHom.mem_ker, map_mul, hd, hok.del_c]
          rfl
        have e : γ = (γ * F.c) * F.c := by
          rw [mul_assoc, hok.c_sq, mul_one]
        rw [e, hcoc', hc', mul_zero, add_zero]
        exact hall ⟨_, hm⟩
    have hy : ∀ v, y v - X = 0 := by
      intro v
      obtain ⟨s, hs⟩ := hloc v
      have e := hloc' v s
      rw [hzero] at e
      have e' : ((χ (F.loc v s) : k) - 1) * (y v - X) = 0 := by
        linear_combination -e
      rcases mul_eq_zero.1 e' with h | h
      · exact absurd (by
          have : (χ (F.loc v s) : k) = 1 := sub_eq_zero.1 h
          exact Units.val_eq_one.1 this) hs
      · exact h
    apply hq
    refine ⟨X, fun s => ?_, fun v => ?_⟩
    · have e := hzero s
      simp only [hx'] at e
      show x s = (chRep χ s) X - X
      rw [chRep_apply]
      linear_combination e
    · show y v - X ∈ (⊥ : Submodule k k)
      rw [Submodule.mem_bot]
      exact hy v
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCocv
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_gl {C : Type} [CommRing C] {n : ℕ} (a b c : GL (Fin n) C)
    (ha : UpT (a : Matrix (Fin n) (Fin n) C)) (hb : UpT (b : Matrix (Fin n) (Fin n) C))
    (hc : UpT (c : Matrix (Fin n) (Fin n) C)) :
    UpT (((a * b * c⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) - 1) := by
  have ha' : (a : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => ha i j h
  have hb' : (b : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hb i j h
  have hc' : (c : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hc i j h
  letI : Invertible (c : Matrix (Fin n) (Fin n) C) := c.invertible
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hc'
  rw [← Matrix.coe_units_inv] at hi
  intro i j h
  have h1 := ((ha'.mul hb').mul hi) (show id j < id i from h)
  rw [Matrix.sub_apply, Units.val_mul, Units.val_mul, h1, Matrix.one_apply_ne (ne_of_gt h), sub_zero]

private theorem ring_id {R : Type} [Ring R] (o c x a w : R) (h : (1 + o) * (1 + c) = (1 + x) * (1 + a) * (1 + w))
    (h1 : o * c = 0) (h2 : x * a = 0) (h3 : x * w = 0) (h4 : a * w = 0) : o - (x - c + a) = w := by
  have e1 : (1 + o) * (1 + c) = 1 + o + c + o * c := by noncomm_ring
  have e2 : (1 + x) * (1 + a) * (1 + w) = 1 + x + a + w + x * a + x * w + a * w + x * a * w := by noncomm_ring
  rw [e1, e2, h1, h2, h3, h4] at h
  simp only [add_zero, zero_mul] at h
  have : o = 1 + x + a + w - c - 1 := by rw [← h]; abel
  rw [this]; abel

theorem UpperTheory.V.Fr.pr_cocv :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ v s t, (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) ∈ (B.bar O).b v := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK v s t
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' C p B D hK
  have hle : RingHom.ker p ≤ maximalIdeal C' := fun x hx => by
    rw [← res_eq_zero_iff O, ← res_map p, (RingHom.mem_ker).1 hx, map_zero]
  have ev := pr_evk O C' n (RingHom.ker p) u hK hle
  have hdel : ∀ s, F.del (F.loc v s) = 1 := fun s => (F.loc0 v s).2
  have hright : ∀ s, (B.r (F.loc v s)).right = 1 := fun s => (B.nu _).trans (hdel s)
  have hres : ∀ x : GL (Fin n) C', GeneralLinearGroup.map (res O C : C →+* ResidueField O)
      (GeneralLinearGroup.map (p : C' →+* C) x) = GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x := by
    intro x
    ext i j
    exact res_map p _
  have hval : ∀ x : GL (Fin n) C', (x : Matrix (Fin n) (Fin n) C').map (res O C') =
      ((GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x : GL (Fin n) (ResidueField O)) :
        Matrix (Fin n) (Fin n) (ResidueField O)) := fun x => rfl

  set T : Matrix (Fin n) (Fin n) C' :=
    ((D.t v s * D.t v t * (D.t v (s * t))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1 with hT
  have hTup : UpT T := upT_gl _ _ _ (D.t_tri v s) (D.t_tri v t) (D.t_tri v _)
  have hTK : ∀ i j, T i j ∈ RingHom.ker p := by
    have e : GeneralLinearGroup.map (p : C' →+* C) (D.t v s * D.t v t * (D.t v (s * t))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, D.t_map, D.t_map, D.t_map, map_mul, map_mul, SemidirectProduct.mul_left,
        hright, sgnAct_one]
      group
    intro i j
    have e2 := congrArg (fun x : GL (Fin n) C => (x : Matrix (Fin n) (Fin n) C) i j) e
    rw [RingHom.mem_ker, hT, Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 (Eq.trans e2 ?_)
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  set gi : Matrix (Fin n) (Fin n) C' := (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hgi
  set g : Matrix (Fin n) (Fin n) C' := ((D.g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hg
  set ri : Matrix (Fin n) (Fin n) C' := (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hri
  set r : Matrix (Fin n) (Fin n) C' := ((D.r (F.loc v s) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hr
  have hW1 : ∀ i j, (gi * T) i j ∈ RingHom.ker p := fun i j => (((ev T hTK).2.1 gi).1 i j).1
  have hW : ∀ i j, (gi * T * g) i j ∈ RingHom.ker p := fun i j => (((ev _ hW1).2.1 g).1 i j).2
  have hX1 : ∀ i j, (r * D.a v t) i j ∈ RingHom.ker p := fun i j => (((ev _ (ha v t)).2.1 r).1 i j).1
  have hX : ∀ i j, (r * D.a v t * ri) i j ∈ RingHom.ker p := fun i j => (((ev _ hX1).2.1 ri).1 i j).2
  have key : D.om (F.loc v s, F.loc v t) - (r * D.a v t * ri - D.a v (s * t) + D.a v s) = gi * T * g := by
    refine ring_id _ _ _ _ _ ?_ ((ev _ (hom _)).1 _ (ha v _)).1 ((ev _ hX).1 _ (ha v _)).1
      ((ev _ hX).1 _ hW).1 ((ev _ (ha v _)).1 _ hW).1
    have e1 : 1 + r * D.a v t * ri = ((D.r (F.loc v s) * (D.r (F.loc v t) * ((D.g v)⁻¹ * D.t v t * D.g v)⁻¹) *
        (D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') := by
      rw [SetLift.a, mul_sub, sub_mul, mul_one, hr, hri, Units.mul_inv, add_sub_cancel]
      rfl
    have e2 : 1 + gi * T * g = (((D.g v)⁻¹ * (D.t v s * D.t v t * (D.t v (s * t))⁻¹) * D.g v : GL (Fin n) C') :
        Matrix (Fin n) (Fin n) C') := by
      rw [hT, mul_sub, sub_mul, mul_one, hg, hgi, Units.inv_mul, add_sub_cancel]
      rfl
    rw [e1, e2]
    simp only [SetLift.om, SetLift.a, add_sub_cancel, hdel, sgnAct_one, ← Units.val_mul, map_mul]
    congr 1
    group
  have hXc : ∀ i j, (r * D.a v t * ri - D.a v (s * t)) i j ∈ RingHom.ker p := fun i j =>
    sub_mem (hX i j) (ha v _ i j)
  have hXca : ∀ i j, (r * D.a v t * ri - D.a v (s * t) + D.a v s) i j ∈ RingHom.ker p := fun i j =>
    add_mem (hXc i j) (ha v _ i j)
  have k2 := congrArg (fun M : Matrix (Fin n) (Fin n) C' => M.map (evK (RingHom.ker p) u)) key
  rw [((ev _ (hom _)).1 _ hXca).2.2, ((ev _ hXc).1 _ (ha v _)).2.1, ((ev _ hX).1 _ (ha v _)).2.2,
    ((ev _ hX1).2.1 ri).2.2, ((ev _ (ha v t)).2.1 r).2.1, ((ev _ hW1).2.1 g).2.2, ((ev _ hTK).2.1 gi).2.1,
    hr, hri, hg, hgi, hval, hval, hval, hval, map_inv, map_inv, ← hres, ← hres (D.g v), D.r_map, D.g_map] at k2
  have k3 : (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) =
      ((((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) *
        T.map (evK (RingHom.ker p) u) * ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) := by
    refine Eq.trans ?_ k2
    have e : ((B.bar O).ad.comp (F.loc v)) s ((D.co u).2 v t) =
        ((B.bar O).r (F.loc v s)).adFun ((D.a v t).map (evK (RingHom.ker p) u)) := rfl
    have e' : ((B.bar O).r (F.loc v s)).right = 1 := hright s
    simp only [dOne]
    rw [e, GG.adFun, if_pos e', add_sub_assoc, add_comm]
    rfl
  rw [k3]
  intro i j h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one, Matrix.map_apply, hTup i j h, evK_of_mem u (zero_mem _)]
  exact map_zero u
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GgMapOfGL
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O (DualNumber (ResidueField O)) x = x.fst := by
  obtain ⟨a, ha⟩ := residue_surjective x.fst
  have h1 : x - algebraMap O _ a ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not,
      TrivSqZeroExt.fst_sub, ← ha]
    exact sub_self _
  have h2 := (res_eq_zero_iff O _ _).2 h1
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h2
  rw [h2, ← ha]
  rfl

private theorem of_unique {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C : Type}
    [CommRing C] {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  refine NRep.ext e (funext fun v => funext fun i => MonoidHom.ext fun s => Units.ext ?_)
  rw [← h.psi, ← h'.psi, e]

private theorem conj_mat {m : ℕ} {C : Type} [CommRing C] (h : GL (Fin m) C)
    (x : GG (m := m) (R := C)) (hx : x.right = 1) :
    (GG.ofGL h * x * (GG.ofGL h)⁻¹).left = h * x.left * h⁻¹ := by
  rw [← map_inv]
  simp [hx]

private theorem gg_map_ofGL {m : ℕ} {C C' : Type} [CommRing C] [CommRing C'] (f : C →+* C') (h : GL (Fin m) C) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := rfl

private theorem dual_mul {K : Type} [Field K] (a : DualNumber K) (c : K) :
    (TrivSqZeroExt.inr (a.fst * c) : DualNumber K) = a * TrivSqZeroExt.inr c := by
  ext <;> simp [mul_comm]

private theorem dual_fst {K : Type} [Field K] {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (i j : Fin m) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) i j).fst = (1 : Matrix (Fin m) (Fin m) K) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

private theorem dual_snd {K : Type} [Field K] {m : ℕ} (X A : Matrix (Fin m) (Fin m) K) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) * A.map (TrivSqZeroExt.inl : K → DualNumber K)).map
      TrivSqZeroExt.snd = X * A := by
  ext i j
  rw [Matrix.add_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum]

theorem UpperTheory.V.Fr.pr_tor :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → thetaLie (lieT (ResidueField O) n) = lieT (ResidueField O) n → ∃ D ∈ Tan O R, ∀ s, B.tanCo O D s = (B.bar O).ad s (lieT _ n) - lieT _ n := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hB hC _ hT
  haveI := (co_res O).2
  let K := ResidueField O
  let C := DualNumber K
  let μ : K →+ C := (TrivSqZeroExt.inrHom K K).toAddMonoidHom
  let ι : K →+* C := (TrivSqZeroExt.inlHom K K)
  have hμ : IsSq O μ := by
    refine ⟨fun a c => ?_, fun c => ?_⟩
    · rw [res_dual]
      exact dual_mul a c
    · rw [← res_eq_zero_iff O, res_dual]
      rfl
  have hres : (res O C : C →+* K).comp ι = RingHom.id K := RingHom.ext fun a => res_dual O _
  obtain ⟨e, e1, e2, e3, -, e5⟩ := pr_sqz O C n μ hμ
  set T := lieT K n with hTdef
  let B₀ : Box F n C := (B.bar O).map ι
  have hB₀ : B₀.bar O = B.bar O := by
    show ((B.bar O).map ι).map _ = _
    rw [Box.map_map, hres]
    rfl
  have hr₀ : ∀ s, GG.map (res O C : C →+* K) (B₀.r s) = (B.bar O).r s := fun s => by
    rw [← hB₀]; rfl
  let h := e (-T)
  have hinv : h⁻¹ = e T := by rw [e3, neg_neg]
  have hloc : ∀ s : F.G0, (B₀.r s).right = 1 := fun s => (B₀.nu s).trans s.2
  let B' : Box F n C :=
    { r := conjBy h B₀.r
      nu := fun s => by
        show (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹).right = _
        rw [← map_inv]
        simp [B₀.nu]
      g := fun v => B₀.g v * h⁻¹
      tri := fun v s => by
        have : (conjBy h B₀.r (F.loc v s)).left = h * (B₀.r (F.loc v s)).left * h⁻¹ :=
          conj_mat h _ (hloc (F.loc0 v s))
        have h2 := B₀.tri v s
        unfold GG.mat at h2 ⊢
        rw [this, ← Units.val_mul, ← Units.val_mul]
        rw [← Units.val_mul, ← Units.val_mul] at h2
        convert h2 using 2
        group }
  have hform : ∀ s, B'.r s = GG.ofGL (e ((B.bar O).ad s T - T)) * B₀.r s := fun s => by
    show GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹ = _
    rw [← map_inv, hinv, mul_assoc, e5, hr₀, ← mul_assoc, ← map_mul, ← e2, neg_add_eq_sub]
    rfl
  have hmat : ∀ s, (B'.r s).mat = (1 + ((B.bar O).ad s T - T).map μ) * ((B.bar O).r s).mat.map ι := fun s => by
    rw [hform, ← e1]
    simp [GG.mat]
    rfl
  have hbar : B.bar O |>.Of (ρ.bar O) := hB.map _
  have hc : (B'.r F.c).mat = 1 := by
    have h1 : (B.bar O).ad F.c T = T := by
      have hl : ((B.bar O).r F.c).left = 1 := Units.ext hbar.atc
      have hd : ((B.bar O).r F.c).right ≠ 1 := by
        rw [(B.bar O).nu, hF.del_c]; decide
      show ((B.bar O).r F.c).adFun T = T
      unfold GG.adFun GG.mat
      rw [hl, if_neg hd, hT]
      simp
    rw [hmat, h1, hbar.atc, sub_self, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.map_zero _ (map_zero μ)]
    simp
  have hdiagE : ∀ a : K, ((e (a • T) : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      Matrix.diagonal fun i => 1 + μ (a * (w n i : K)) := fun a => by
    rw [e1]
    ext1 i j
    by_cases hij : i = j
    · subst hij; simp [hTdef, lieT]
    · simp [hTdef, lieT, hij]
  have hd : ∀ i j, i ≠ j → ((B'.r F.g0).mat - (B'.r (F.star F.g0)).mat) i j = 0 := fun i j hij => by
    have h1 : ∀ s : F.G0, (B'.r s).mat = (h : Matrix (Fin n) (Fin n) C) * ((ρ.bar O).r s).map ι *
        ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := fun s => by
      rw [← hbar.res]
      exact congrArg Units.val (conj_mat h _ (hloc s))
    have h2 := (ρ.bar O).diag i j hij
    rw [h1, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, hinv, ← one_smul K T, hdiagE, Matrix.mul_diagonal]
    have h3 : h = e ((-1 : K) • T) := by rw [neg_one_smul]
    rw [h3, hdiagE, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub,
      ← Matrix.sub_apply, h2]
    simp
  have hcont : B'.Cont (maximalIdeal C) := fun i j N => by
    have h1 := lc_of_ker _ (pr_open hF O R B hC).1
    exact h1.comp fun x => Ideal.Quotient.mk _ ((GG.ofGL h * GG.map ι x * (GG.ofGL h)⁻¹).mat i j)
  obtain ⟨ρ', hρ', hc'⟩ := pr_ofbox hF C _ B' hc hd hcont
  have hh : GeneralLinearGroup.map (res O C : C →+* K) h = 1 := by
    apply Units.ext
    ext i j
    show res O C ((e (-T) : Matrix (Fin n) (Fin n) C) i j) = _
    rw [e1, res_dual]
    exact dual_fst _ i j
  have hB' : B'.bar O = B.bar O := by
    rw [← hB₀]
    refine Box.ext (MonoidHom.ext fun s => ?_) (funext fun v => ?_)
    · show GG.map _ (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹) = GG.map _ (B₀.r s)
      rw [map_mul, map_mul, map_inv, gg_map_ofGL, hh]
      simp
    · show GeneralLinearGroup.map _ (B₀.g v * h⁻¹) = GeneralLinearGroup.map _ (B₀.g v)
      rw [map_mul, map_inv, hh]
      simp
  have hρb : ρ'.bar O = ρ.bar O := of_unique (hB' ▸ hρ'.map _) hbar
  obtain ⟨D, hD, hD'⟩ := pr_dof hF O R ρ B hU hB ρ' B'.r hc' hρb B'.nu hc hρ'.res
  refine ⟨D, hD, fun s => ?_⟩
  have h1 : (B'.r s).mat.map TrivSqZeroExt.snd = ((B.bar O).ad s T - T) * ((B.bar O).r s).mat := by
    rw [hmat]
    exact dual_snd _ _
  have h2 := (hD' s).symm.trans h1
  exact (Units.mul_left_inj ((B.bar O).r s).left).1 h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCorrect
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C} (hM : UpT M) (hN : UpT N) :
    UpT (M * N) := fun i j h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hM i c hc, zero_mul]
  · rw [hN c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

theorem UpperTheory.V.Fr.pr_correct :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (μ : ResidueField O →+ C'), IsSq O μ → (∀ c, p (μ c) = 0) → ∀ (β : F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) (Y : F.V → Matrix (Fin n) (Fin n) (ResidueField O)) (a : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)), IsLocallyConstant β → (∀ x, D.om x = (dOne (B.bar O).ad β x).map μ) → (∀ v s, D.a v s = (a v s).map μ) → (∀ v s, a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v)) ∈ (B.bar O).b v) → ∃ B' : Box F n C', B'.Cont (maximalIdeal C') ∧ B'.map (p : C' →+* C) = B ∧ ∀ s, (B'.r s).mat = (1 - (β s).map μ) * (D.r s : Matrix (Fin n) (Fin n) C') := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D μ hμ hpμ β Y a hβ hom ha hb
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := pr_sqz O C' n μ hμ
  have hres : ∀ z : C', res O C (p z) = res O C' z := fun z => res_map p z
  let x : F.Γ → GG (m := n) (R := C') := fun s => SemidirectProduct.mk (D.r s) (F.del s)
  have hK1 : ∀ s, GG.map (res O C' : C' →+* ResidueField O) (x s) = (B.bar O).r s := by
    intro s
    apply SemidirectProduct.ext
    · ext i j
      simp [x, GG.map, Box.map, hres, ← D.r_map s]
    · simp [x, GG.map, Box.map, B.nu]
  have hdl : ∀ v (s : F.Gv v), F.del (F.loc v s) = 1 := fun v s => MonoidHom.mem_ker.1 (F.loc0 v s).2
  have hAd : ∀ v (s : F.Gv v) M, (B.bar O).ad (F.loc v s) M =
      (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C') * M *
        (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v s M
    show GG.adFun ((B.bar O).r (F.loc v s)) M = _
    rw [← hK1]
    clear hom ha hb he5 he4 he3 he2 he1 hβ hpμ hμ
    simp [GG.adFun, GG.mat, GG.map, x, hdl]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.coe_units_inv]
    calc (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') *
          (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C')
        = ((((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
            (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C')).map (res O C') :=
          (Matrix.map_mul (f := (res O C').toRingHom)).symm
      _ = 1 := by
          rw [Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxmul : ∀ s t, x s * x t = GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
    intro s t
    have hu : D.r s * sgnAct (m := n) (R := C') (F.del s) (D.r t) * (D.r (s * t))⁻¹ = e (dOne (B.bar O).ad β (s, t)) := by
      apply Units.ext
      rw [he1, ← hom (s, t)]
      simp [SetLift.om]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, ← hu]
      simp [x]
    · simp [x]
  have hcomm : ∀ s X, x s * GG.ofGL (e X) = GG.ofGL (e ((B.bar O).ad s X)) * x s := by
    intro s X
    rw [he5 (x s) X, hK1 s]
    rfl
  let R' : F.Γ → GG (m := n) (R := C') := fun s => GG.ofGL (e (-β s)) * x s
  have hmul : ∀ s t, R' (s * t) = R' s * R' t := by
    intro s t
    symm
    calc R' s * R' t = GG.ofGL (e (-β s)) * (x s * GG.ofGL (e (-β t))) * x t := by
          simp only [R', mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) * (x s * x t) := by
          rw [hcomm]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) *
            GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [hxmul]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s + (B.bar O).ad s (-β t) + dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [he2, he2, map_mul, map_mul]
      _ = R' (s * t) := by
          simp only [R']
          congr 3
          simp only [dOne, map_neg]
          abel
  let rr : F.Γ →* GG (m := n) (R := C') := MonoidHom.mk' R' hmul
  have hneg : ∀ Z : Matrix (Fin n) (Fin n) (ResidueField O), (-Z).map μ = -(Z.map μ) := by
    intro Z
    ext i j
    simp
  have hpe : ∀ X, GeneralLinearGroup.map (p : C' →+* C) (e X) = 1 := by
    intro X
    ext i j
    simp only [GeneralLinearGroup.map_apply, he1, Matrix.add_apply, Matrix.map_apply, Units.val_one, map_add (f := _)]
    have h0 : (p : C' →+* C) (μ (X i j)) = 0 := hpμ _
    rw [h0, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hconj : ∀ (A : GL (Fin n) C') X, A * e X * A⁻¹ =
      e ((A : Matrix (Fin n) (Fin n) C').map (res O C') * X * ((A⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
    intro A X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he1, mul_add, mul_one, add_mul, Units.mul_inv, (he4 _ X).1, (he4 _ _).2]
  have hGbar : ∀ v, ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) =
        (D.g v : Matrix (Fin n) (Fin n) C').map (res O C') ∧
      (((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) =
        (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v
    constructor
    · ext i j
      simp [Box.map, ← D.g_map v, hres]
    · ext i j
      simp [Box.map, ← D.g_map v, hres, ← map_inv]
  refine ⟨{ r := rr, nu := ?_, g := fun v => D.g v * e (-(Y v)), tri := ?_ }, ?_, ?_, ?_⟩
  · intro s
    show (GG.ofGL (e (-β s)) * x s).right = F.del s
    simp [x]
  · intro v s
    show UpT ((↑(D.g v * e (-(Y v))) : Matrix (Fin n) (Fin n) C') * (R' (F.loc v s)).mat *
      (((D.g v * e (-(Y v)))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C'))
    have hr : D.r (F.loc v s) = e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v) := by
      rw [← mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [he1, ← ha v s]
      simp [SetLift.a]
    have hmat : (R' (F.loc v s)).mat = ↑(e (-β (F.loc v s)) * D.r (F.loc v s)) := by
      simp [R', GG.mat, x]
    have h1 : D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹ = e ((B.bar O).ad (F.loc v s) (Y v)) := by
      rw [hconj, hAd]
    have hX : e (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) =
        e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s) := by
      rw [← he2, ← he2, ← he2]
      congr 1
      abel
    have key : D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹ =
        e ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) * D.t v s := by
      rw [← hconj, hX]
      calc D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹
          = D.g v * e (-(Y v)) * e (-β (F.loc v s)) *
              (D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹) * D.r (F.loc v s) * (D.g v)⁻¹ := by
            rw [_root_.mul_inv_rev, he3, neg_neg]
            group
        _ = D.g v * e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) *
              (e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v)) * (D.g v)⁻¹ := by
            rw [h1, ← hr]
        _ = D.g v * (e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s)) *
              (D.g v)⁻¹ * D.t v s := by
            group
    have hW : UpT ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
      rw [← (hGbar v).1, ← (hGbar v).2]
      exact hb v s
    rw [hmat, ← Units.val_mul, ← Units.val_mul, key, Units.val_mul, he1]
    apply upT_mul _ (D.t_tri v s)
    intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.map_apply, hW i j hij, map_zero, add_zero]
  · intro i j N
    have hB : IsLocallyConstant fun s =>
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro s0
      have hall : ∀ᶠ s in nhds s0, ∀ a b,
          Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s : Matrix (Fin n) (Fin n) C') a b) =
            Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s0 : Matrix (Fin n) (Fin n) C') a b) :=
        Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
          (IsLocallyConstant.iff_eventually_eq _).1 (D.r_cont a b N) s0
      filter_upwards [hall] with s hs
      ext a b
      exact hs a b
    have hA := hβ.comp (fun Z =>
      ((1 : Matrix (Fin n) (Fin n) C') + (-Z).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N)))
    have hM := (IsLocallyConstant.comp₂ hA hB (· * ·)).comp (fun M => M i j)
    convert hM using 1
    funext s
    change Ideal.Quotient.mk (maximalIdeal C' ^ N) ((R' s).mat i j) =
      (((1 + (-β s).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N))) *
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N))) i j
    rw [← Matrix.map_mul, Matrix.map_apply]
    congr 1
    show (R' s).mat i j = _
    simp [R', GG.mat, x, he1]
  · apply Box.ext
    · apply MonoidHom.ext
      intro s
      apply SemidirectProduct.ext
      · show GeneralLinearGroup.map (p : C' →+* C) (R' s).left = (B.r s).left
        simp [R', x, hpe, D.r_map]
      · show (R' s).right = (B.r s).right
        simp [R', x, B.nu]
    · funext v
      show GeneralLinearGroup.map (p : C' →+* C) (D.g v * e (-(Y v))) = B.g v
      rw [map_mul, hpe, mul_one, D.g_map]
  · intro s
    show (R' s).mat = _
    simp [R', GG.mat, x, he1, hneg, sub_eq_add_neg]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpDimb
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem db_inv {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (a b : Fin 3) (e : π a ≠ pq b) :
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b a = 0 := by
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h1 : u * g = 1 := g.inv_mul
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  let P : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if π i = π a then 1 else 0
  let Q : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if pq i = π a then 1 else 0
  have hc : P * g = g * Q := by
    ext i j
    simp only [P, Q, diagonal_mul, mul_diagonal]
    by_cases c : π i = pq j
    · rw [c, mul_comm]
    · rw [h i j c, mul_zero, zero_mul]
  have hd : u * P = Q * u := by
    calc u * P = u * (P * g) * u := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Q * u := by rw [hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have := congrFun (congrFun hd b) a
  simpa [P, Q, diagonal_mul, mul_diagonal, e.symm] using this

private theorem db_ex {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (b : Fin 3) : ∃ a, π a = pq b := by
  by_contra c
  push Not at c
  have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := g.inv_mul
  have := congrFun (congrFun h1 b) b
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => by rw [h a b (c a), mul_zero]] at this
  simp at this

private theorem db_card {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (j : ZMod 2) :
    Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} ≤
      Module.finrank K ((bor g).comap (adp K j).subtype) := by
  have h' := db_inv g π h
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  have hc : ∀ X : Matrix (Fin 3) (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) * (u * X * g) * u = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let f : {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} → (bor g).comap (adp K j).subtype := fun p =>
    ⟨⟨u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K), fun a b e => by
      have : (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) a b =
          u a p.1.1 * (g : Matrix (Fin 3) (Fin 3) K) p.1.2 b := by
        rw [Matrix.mul_apply, Finset.sum_eq_single p.1.2]
        · simp
        · intro c _ hc
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
        · simp
      rw [this]
      by_cases c : π p.1.1 = pq a
      · rw [h p.1.2 b fun c' => e (by rw [pw_eq, ← c, ← c', p.2.2]), mul_zero]
      · rw [h' _ _ c, zero_mul]⟩, by
      show UpT ((g : Matrix (Fin 3) (Fin 3) K) * (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) * u)
      rw [hc]
      intro a b e
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact absurd p.2.1 (not_le.2 e)⟩
  refine LinearIndependent.fintype_card_le_finrank (b := f) ?_
  let L : (bor g).comap (adp K j).subtype →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
    (LinearMap.mulRight K u) ∘ₗ (LinearMap.mulLeft K (g : Matrix (Fin 3) (Fin 3) K)) ∘ₗ (adp K j).subtype ∘ₗ
      Submodule.subtype _
  refine LinearIndependent.of_comp L ?_
  have : L ∘ f = (Matrix.stdBasis K (Fin 3) (Fin 3)) ∘ Subtype.val := by
    funext p
    have := Matrix.stdBasis_eq_single (R := K) p.1.1 p.1.2
    exact (hc _).trans this.symm
  rw [this]
  exact (Matrix.stdBasis K (Fin 3) (Fin 3)).linearIndependent.comp _ Subtype.val_injective

private theorem db_counts : ∀ π : Fin 3 → ZMod 2, (∃ a, π a = 0) → (∃ a, π a = 1) →
    4 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 0} ∧
    2 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 1} := by
  decide +kernel

theorem UpperTheory.V.Fr.ep_dimb :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ v, 4 ≤ Module.finrank K (B.bp 0 v) ∧ 2 ≤ Module.finrank K (B.bp 1 v) := by
  intro l _ k _ F K _ _ B π h v
  have h0 : pq 1 = 0 := by decide
  have h1 : pq 0 = 1 := by decide
  obtain ⟨c0, c1⟩ := db_counts (π v) (h0 ▸ db_ex (B.g v) (π v) (h.g v) 1) (h1 ▸ db_ex (B.g v) (π v) (h.g v) 0)
  exact ⟨c0.trans (db_card (B.g v) (π v) (h.g v) 0), c1.trans (db_card (B.g v) (π v) (h.g v) 1)⟩
end

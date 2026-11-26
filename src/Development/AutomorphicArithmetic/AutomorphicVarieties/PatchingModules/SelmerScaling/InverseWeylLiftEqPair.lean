module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InverseWeylLiftEqPair
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section P

variable {A : Type} (R : Type) [CommRing A] [CommRing R] [Algebra A R] {e n : ℕ}

private def PP (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) (DD R e) :=
  Matrix.of fun a b => ⟨algebraMap A R (M a b), fun j => algebraMap A R (Z j a b), 0, 0⟩

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD R e) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD R e) (j) : (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD R e) (j) : (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD R e) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem congruenceCondition_mul (M M' : Matrix (Fin n) (Fin n) A) (Z Z' : Fin e → Matrix (Fin n) (Fin n) A) :
    PP R M Z * PP R M' Z' = PP R (M * M') (fun j => M * Z' j + Z j * M') := by
  ext a b j <;> simp [PP, Matrix.mul_apply, sum_a, sum_ep, sum_ep', sum_eta, Finset.sum_add_distrib]

private theorem pair_matrix_transpose (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (PP R M Z)ᵀ = PP R Mᵀ (fun j => (Z j)ᵀ) := rfl

private theorem PP_map (M : Matrix (Fin n) (Fin n) A) :
    M.map (algebraMap A (DD R e)) = PP R M (fun _ => 0) := by
  ext a b j
  · rfl
  · simp only [PP, Matrix.of_apply, Matrix.zero_apply, map_zero]; rfl
  · rfl
  · rfl

private theorem PP_one : PP R (1 : Matrix (Fin n) (Fin n) A) (fun _ : Fin e => 0) = 1 := by
  rw [← PP_map]; exact Matrix.map_one _ (map_zero _) (map_one _)

private theorem PP_add (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (1 + DD.epM fun j => (Z j).map (algebraMap A R)) = PP R 1 Z := by
  rw [← PP_one (A := A) R]
  ext a b j <;> simp [PP, DD.epM]

private theorem PP_sub (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (1 - DD.epM fun j => (Z j).map (algebraMap A R)) = PP R 1 (fun j => -Z j) := by
  rw [← PP_one (A := A) R, sub_eq_add_neg]
  ext a b j <;> simp [PP, DD.epM]

private theorem PP_apply (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) (a b : Fin n)
    (h : ∀ j, Z j a b = 0) : PP R M Z a b = algebraMap A (DD R e) (M a b) := by
  have := congrFun (congrFun (PP_map R (e := e) M) a) b
  rw [Matrix.map_apply] at this
  rw [this]
  simp [PP, h]

private theorem od_ev {a : ℕ} {Z M : Matrix (Fin n) (Fin n) A} (hZ : Z ∈ Od A A n a) (hM : M ∈ Ev A A n a) :
    Z * M ∈ Od A A n a := by
  intro i j
  refine ⟨fun h => ?_, fun _ => trivial⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [(Submodule.mem_bot A).1 ((hZ i k).1 hk), zero_mul]
  · rw [(Submodule.mem_bot A).1 ((hM k j).2 (by tauto)), mul_zero]

private theorem ev_od {a : ℕ} {Z M : Matrix (Fin n) (Fin n) A} (hZ : Z ∈ Od A A n a) (hM : M ∈ Ev A A n a) :
    M * Z ∈ Od A A n a := by
  intro i j
  refine ⟨fun h => ?_, fun _ => trivial⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [(Submodule.mem_bot A).1 ((hZ k j).1 (by tauto)), mul_zero]
  · rw [(Submodule.mem_bot A).1 ((hM i k).2 hk), zero_mul]

private theorem tri_mul {M N : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    ∀ i j, j < i → (M * N) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hM i k hk, zero_mul]
  · rw [hN k j (lt_of_lt_of_le hij (not_lt.1 hk)), mul_zero]

end P

section K

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (R : Type) [CommRing R] [Algebra x.A R]

private theorem ρ1_eq (g : F.G₀) : k.ρ1 R g = PP R (x.ρX x.A g) (fun j => k.κ j g * x.ρX x.A g) := by
  have : x.ρX (DD R k.g) g = PP R (x.ρX x.A g) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.ρ1, PP_add, this, congruenceCondition_mul]; simp

private theorem weyl_lift_eq_pair (v) : k.w1 R v = PP R (x.wX x.A v) (fun j => -(k.Y j v * x.wX x.A v)) := by
  have : x.wX (DD R k.g) v = PP R (x.wX x.A v) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.w1, PP_sub, this, congruenceCondition_mul]; simp

private theorem inverse_weyl_lift_eq_pair (v) : k.wi1 R v = PP R (x.wiX x.A v) (fun j => x.wiX x.A v * k.Y j v) := by
  have : x.wiX (DD R k.g) v = PP R (x.wiX x.A v) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.wi1, PP_add, this, congruenceCondition_mul]; simp

end K

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.rho1Tri :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ (R : Type) [CommRing R] [Algebra x.A R], (∀ g g', k.ρ1 R (g * g') = k.ρ1 R g * k.ρ1 R g') ∧ k.ρ1 R 1 = 1 ∧ (∀ g, (k.ρ1 R g)ᵀ * k.ρ1 R (G0.frame.conj g) = algebraMap x.A (DD R k.g) ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD R k.g))) ∧ (∀ w, ∀ g ∈ G0.frame.Iu w, k.ρ1 R g = 1) ∧ (∀ g, k.ρ1 R g ∈ W1 n x.A R k.g x.a) ∧ ∀ v, k.w1 R v * k.wi1 R v = 1 ∧ k.wi1 R v * k.w1 R v = 1 ∧ ∀ g, (∀ i j, j < i → (k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v) i j = 0) ∧ ∀ i, (k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v) i i = algebraMap x.A (DD R k.g) (x.ψ v i g) := by
  intro l _ L G G0 h n x k R _ _
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := fun g => rfl
  have hmul : ∀ g g', x.ρX x.A (g * g') = x.ρX x.A g * x.ρX x.A g' := by
    intro g g'; simp [hρ, mat]
  have hone : x.ρX x.A 1 = 1 := by simp [hρ, mat]
  have hinv : ∀ g, x.ρX x.A g⁻¹ * x.ρX x.A g = 1 := by
    intro g; rw [← hmul, inv_mul_cancel, hone]
  have hev : ∀ g, x.ρX x.A g ∈ Ev x.A x.A n x.a := x.blk
  have hform : ∀ g, (x.ρX x.A g)ᵀ * x.ρX x.A (G0.frame.conj g) =
      ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) x.A) := by
    intro g
    have := x.form g
    rw [Units.val_one, Matrix.mul_one] at this
    exact this
  refine ⟨fun g g' => ?_, ?_, fun g => ?_, fun w g hg => ?_, fun g => ?_, fun v => ?_⟩
  · rw [ρ1_eq, ρ1_eq, ρ1_eq, congruenceCondition_mul, hmul]
    congr 1
    funext j
    rw [(k.mem j).2.2.1 g g', add_mul, add_comm, Matrix.mul_assoc (_ * _), ← Matrix.mul_assoc (x.ρX x.A g⁻¹), hinv]
    simp only [Matrix.mul_assoc, Matrix.one_mul]
  · rw [ρ1_eq, hone, ← PP_one (A := x.A) R]
    congr 1
    funext j
    have := (k.mem j).2.2.1 1 1
    simp only [mul_one, inv_one, hone, one_mul] at this
    rw [mul_one]
    exact left_eq_add.1 this
  · rw [ρ1_eq, ρ1_eq, pair_matrix_transpose, congruenceCondition_mul, hform]
    have : (fun j => (x.ρX x.A g)ᵀ * (k.κ j (G0.frame.conj g) * x.ρX x.A (G0.frame.conj g)) +
        (k.κ j g * x.ρX x.A g)ᵀ * x.ρX x.A (G0.frame.conj g)) = fun _ => 0 := by
      funext j
      rw [(k.mem j).2.2.2.1 g]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, ← PP_map]
    ext1 a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · rw [ρ1_eq, ← PP_one (A := x.A) R]
    have : x.ρX x.A g = 1 := by simp [hρ, mat, x.ine w g hg]
    rw [this]
    congr 1
    funext j
    rw [(k.mem j).2.2.2.2.1 w g hg, zero_mul]
  · rw [ρ1_eq]
    intro a b
    refine ⟨fun hab => ⟨by simp, fun _ => ?_, fun _ => rfl, fun _ => rfl⟩,
      fun hab => ⟨fun _ => ?_, by simp, fun _ => rfl, fun _ => rfl⟩⟩
    · funext j
      have := (Submodule.mem_bot _).1 ((od_ev ((k.mem j).1 g) (hev g) a b).1 hab)
      simp [PP, this]
    · have := (Submodule.mem_bot _).1 ((hev g a b).2 hab)
      simp [PP, this]
  · obtain ⟨h1, h2, h3, h4, -⟩ := oddDiag l L G G0 h n x x.A v
    refine ⟨?_, ?_, fun g => ?_⟩
    · rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, congruenceCondition_mul, h1, ← PP_one (A := x.A) R]
      congr 1
      funext j
      rw [← Matrix.mul_assoc, h1, neg_mul, Matrix.mul_assoc, h1]; simp
    · rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, congruenceCondition_mul, h2, ← PP_one (A := x.A) R]
      congr 1
      funext j
      simp [Matrix.mul_assoc]
    · set r := x.ρX x.A (G0.φ v g) with hr
      have key : k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v = PP R (x.wiX x.A v * r * x.wX x.A v)
          (fun j => x.wiX x.A v * (k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v) * x.wX x.A v) := by
        rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, ρ1_eq, congruenceCondition_mul, congruenceCondition_mul]
        congr 1
        funext j
        rw [← hr]
        noncomm_ring
      rw [key]
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · rw [PP_apply, (h4 g).1 a b hab, map_zero]
        intro j
        have e : x.wiX x.A v * (k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v) * x.wX x.A v =
            (x.wiX x.A v * (k.κ j (G0.φ v g) - dY G0.frame (x.ρX x.A) (k.Y j v) (G0.φ v g)) * x.wX x.A v) *
              (x.wiX x.A v * r * x.wX x.A v) := by
          have e1 : (k.κ j (G0.φ v g) - dY G0.frame (x.ρX x.A) (k.Y j v) (G0.φ v g)) * r =
              k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v := by
            rw [dY, sub_mul, sub_mul, Matrix.mul_assoc _ _ r, hr, hinv, mul_one]; abel
          rw [← e1]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (x.wX x.A v), h1, one_mul]
        rw [e]
        exact tri_mul (k.loc j v g).1 (h4 g).1 a b hab
      · rw [PP_apply, (h4 g).2 a]
        · rfl
        intro j
        refine h3 _ ?_ a
        exact Submodule.sub_mem _ (Submodule.add_mem _ (od_ev ((k.mem j).1 _) (hev _)) (od_ev (k.Y_mem j v) (hev _)))
          (ev_od (k.Y_mem j v) (hev _))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TestVal
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem padicInt_ringHom_finite_field_eq {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (φ ψ : ℤ_[p] →+* K) (z : ℤ_[p]) : φ z = ψ z := by
  have key : ∀ χ : ℤ_[p] →+* K, IsLocalRing.maximalIdeal ℤ_[p] ≤ RingHom.ker χ := by
    intro χ
    have hne : RingHom.ker χ ≠ ⊥ := by
      intro h
      have hinj : Function.Injective χ := (RingHom.injective_iff_ker_eq_bot χ).mpr h
      haveI : Finite ℤ_[p] := Finite.of_injective χ hinj
      haveI : Infinite ℤ_[p] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[p]) Nat.cast_injective
      exact not_finite ℤ_[p]
    have hmax : (RingHom.ker χ).IsMaximal := (RingHom.ker_isPrime χ).isMaximal hne
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  have h1 := key φ (PadicInt.sub_zmodRepr_mem z)
  have h2 := key ψ (PadicInt.sub_zmodRepr_mem z)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, map_natCast, map_natCast]

theorem UpperTheory.V.Pa.testVal :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → (∀ c : S.O, θ (algebraMap S.B S.U.AA (algebraMap S.O S.B c)) = algebraMap S.F R (algebraMap S.x.A S.F (algebraMap S.O S.x.A c))) ∧ (∀ (g : S.G.G₀) (m : ℤ), θ (algebraMap S.B S.U.AA ((S.G.frame.eps S.O S.B g ^ m : S.Bˣ) : S.B)) = algebraMap S.F R (algebraMap S.x.A S.F ((S.G.frame.eps ℤ_[l] S.x.A g ^ m : S.x.Aˣ) : S.x.A))) ∧ θ (algebraMap S.B S.U.AA S.P.s) = algebraMap S.F R (algebraMap S.x.A S.F S.x.t) ∧ (∀ v i g, e (θ (algebraMap S.B S.U.AA (S.u.ψ v i g))) = algebraMap S.x.A S.F (S.x.ψ v i g)) ∧ ∀ v i, ∀ g ∈ S.G.frame.mu v, θ (algebraMap S.B S.U.AA (S.u.ψ v i g)) = 1 := by
  intro l _ S R _ _ e θ hT
  have hB : ∀ b : S.B, algebraMap S.B S.U.AA b = algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b) :=
    fun b => IsScalarTower.algebraMap_apply S.B S.Bh S.U.AA b
  have hO : ∀ c : S.O, θ (algebraMap S.B S.U.AA (algebraMap S.O S.B c)) =
      algebraMap S.F R (algebraMap S.x.A S.F (algebraMap S.O S.x.A c)) := by
    intro c
    obtain ⟨o, ho⟩ := S.oo_O c
    rw [hB, ← ho, hT.oo o, ho, S.rF_f, S.P.f.commutes]
  have hpr : ∀ b : S.Bh, S.pr0 (algebraMap S.Bh S.U.AA b) = b := by
    intro b
    have h1 := (Ctx.exists_pr S (algebraMap S.Bh S.U.AA b)).choose_spec
    have h2 : algebraMap S.Bh S.U.AA b - algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b))
        ∈ (1 : Submodule S.Bh S.U.AA) := by
      rw [← map_sub]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩
    have h4 := (Submodule.disjoint_def.mp S.U.compl.disjoint) _ h2 h1
    rw [← map_sub] at h4
    have h5 := S.U.inj (h4.trans (map_zero _).symm)
    exact (sub_eq_zero.mp h5).symm
  refine ⟨hO, ?_, ?_, ?_, ?_⟩
  · intro g m
    rw [← map_zpow, ← map_zpow]
    show θ (algebraMap S.B S.U.AA (algebraMap S.O S.B (algebraMap ℤ_[l] S.O _))) = _
    rw [hO]
    congr 2
    change algebraMap S.O S.x.A (algebraMap ℤ_[l] S.O _) = algebraMap ℤ_[l] S.x.A (algebraMap ℤ_[l] ℤ_[l] _)
    rw [Algebra.algebraMap_self, RingHom.id_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] S.x.K (PowerSeries S.x.K),
      IsScalarTower.algebraMap_apply S.O S.x.K (PowerSeries S.x.K)]
    congr 1
    exact padicInt_ringHom_finite_field_eq ((algebraMap S.O S.x.K).comp (algebraMap ℤ_[l] S.O)) (algebraMap ℤ_[l] S.x.K) _
  · obtain ⟨o, ho⟩ := S.ordinaryPointSection
    rw [hB, ← ho, hT.oo o, ho, S.rF_f, S.P.f_s]
  · intro v i g
    rw [hT.res, hB, hpr, S.rF_f]
    have h := congrArg (fun χ => ((χ g : S.x.Aˣ) : S.x.A)) (S.P.maps.2 v i)
    exact congrArg _ h
  · intro v i g hg
    have hψ : ((S.u.ψ v i g : S.Bˣ) : S.B) = algebraMap S.O S.B ((S.r.th v i ⟨g, hg⟩ : S.Oˣ) : S.O) :=
      (S.u.psi v i).mu ⟨g, hg⟩
    have h := congrArg (fun χ => ((χ g : S.x.Aˣ) : S.x.A)) (S.P.maps.2 v i)
    have h' : S.P.f ((S.u.ψ v i g : S.Bˣ) : S.B) = ((S.x.ψ v i g : S.x.Aˣ) : S.x.A) := h
    rw [hψ, hO, ← S.P.f.commutes, ← hψ, h', S.x.ψ_mu v i g hg]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem selLift {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R R' : Type} [CommRing A] [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] (t : A) (f : R →+* R') (hf : Function.Injective f)
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' : F.G₀ → Matrix (Fin n) (Fin n) R') (w' wi' : F.Vl → Matrix (Fin n) (Fin n) R')
    (hρ : ∀ g, (ρ g).map f = ρ' g) (hw : ∀ g, (w g).map f = w' g) (hwi : ∀ g, (wi g).map f = wi' g)
    (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R'))
    (c : R') (hV : ∀ Z : Matrix (Fin n) (Fin n) R, ∀ Z' ∈ V', Z.map f = c • Z' → Z ∈ V)
    (z' : F.G₀ → Matrix (Fin n) (Fin n) R') (hz' : z' ∈ SelZ F t ρ' w' wi' V')
    (Y' : F.Vl → Matrix (Fin n) (Fin n) R') (hY' : ∀ v, Y' v ∈ V' ∧ LocAt F ρ' w' wi' z' v (Y' v))
    (z : F.G₀ → Matrix (Fin n) (Fin n) R) (hc : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => z g i j)
    (hz : ∀ g, (z g).map f = c • z' g) (Y : F.Vl → Matrix (Fin n) (Fin n) R) (hY : ∀ v, (Y v).map f = c • Y' v) :
    z ∈ SelZ F t ρ w wi V := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hz'
  have inj : Function.Injective fun Z : Matrix (Fin n) (Fin n) R => Z.map f := Matrix.map_injective hf
  refine ⟨fun g => hV _ _ (h1 g) (hz g), hc, fun g g' => inj ?_, fun g => inj ?_, fun u g hg => inj ?_,
    fun v => ⟨Y v, hV _ _ (hY' v).1 (hY v), fun g => ?_⟩⟩
  · simp only [Matrix.map_add f (map_add f), Matrix.map_mul, hz, hρ, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  · simp only [Matrix.map_neg f (map_neg f), Matrix.transpose_map, hz, h4, smul_neg, Matrix.transpose_smul]
  · simp only [hz, h5 u g hg, smul_zero, Matrix.map_zero f (map_zero f)]
  · have key : (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v).map f =
        c • (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) := by
      simp only [dY, Matrix.map_sub f (map_sub f), Matrix.map_mul, hz, hρ, hw, hwi, hY, ← smul_sub, Matrix.mul_smul,
        Matrix.smul_mul]
    have k2 : ∀ i j, (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) i j = 0 →
        (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v) i j = 0 := by
      intro i j h0
      apply hf
      have := congrFun (congrFun key i) j
      rw [Matrix.map_apply, Matrix.smul_apply, h0, smul_zero] at this
      rw [this, map_zero]
    exact ⟨fun i j hij => k2 i j (((hY' v).2 g).1 i j hij), fun hg i => k2 i i (((hY' v).2 g).2 hg i)⟩

private theorem liftF {K Γ : Type} [Field K] [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] {n : ℕ}
    (z : Γ → Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K))) (hz : BndM (PowerSeries.X : PowerSeries K) z) :
    ∀ᶠ s : ℕ in Filter.atTop, ∃ z' : Γ → Matrix (Fin n) (Fin n) (PowerSeries K),
      (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) (PowerSeries K) PowerSeries.X}) fun g => z' g i j) ∧
      ∀ g, (z' g).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) =
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s) • z g := by
  have B := fun φ hφ => Filter.eventually_atTop.2 ((bndOps K Γ).2.2.2.2 φ hφ)
  have e1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j)
  filter_upwards [e1] with s a1
  choose b1 c1 a1 using a1
  refine ⟨fun g => Matrix.of fun i j => b1 i j g, fun i j => c1 i j, fun g => ?_⟩
  ext i j
  exact a1 i j g

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selScale :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ b : Bool, ∀ z ∈ SelZ G.frame x.t (fun g => x.ρX x.Fr (h.p₀ g)) (x.wX x.Fr) (x.wiX x.Fr) (if b then Ev x.A x.Fr n x.a else Od x.A x.Fr n x.a), BndM x.t z → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ z' ∈ SelZ G.frame x.t (fun g => x.ρX x.A (h.p₀ g)) (x.wX x.A) (x.wiX x.A) (if b then Ev x.A x.A n x.a else Od x.A x.A n x.a), ∀ g, (z' g).map (algebraMap x.A x.Fr) = algebraMap x.A x.Fr x.t ^ s • z g := by
  intro l _ L G G0 h n x b z hz hb
  choose Y hY using hz.2.2.2.2.2
  have c0 := (bndOps x.K G.G₀).1
  have e1 := liftF z hb
  have e2 := Filter.eventually_all.2 fun v => liftF (K := x.K) (fun _ : G.G₀ => Y v) fun i j => c0 _
  apply Filter.eventually_atTop.1
  filter_upwards [e1, e2] with s a1 a2
  obtain ⟨z', hc, hz'⟩ := a1
  choose Y' _ hY' using a2
  have hf : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective _ _
  refine ⟨z', selLift G.frame x.t (algebraMap x.A x.Fr) hf _ _ _ _ _ _ (fun g => rfl) (fun v => rfl) (fun v => rfl)
    _ _ (algebraMap x.A x.Fr x.t ^ s) (fun Z Z' hZ' hZ => ?_) z hz Y hY z' hc hz' (fun v => Y' v 1) (fun v => hY' v 1), hz'⟩
  have key : ∀ i j, Z' i j = 0 → Z i j = 0 := fun i j e => hf (by
    have := congrFun (congrFun hZ i) j
    rw [Matrix.map_apply, Matrix.smul_apply, e, smul_zero] at this
    rw [this, map_zero])
  cases b
  · exact fun i j => ⟨fun e => key i j ((hZ' i j).1 e), fun _ => trivial⟩
  · exact fun i j => ⟨fun _ => trivial, fun e => key i j ((hZ' i j).2 e)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TestEx
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dd_fin (X : Type) [CommRing X] (g : ℕ) : Module.Finite X (DD X g) := by
  let f : (X × (Fin g → X) × (Fin g → X) × X) →ₗ[X] DD X g :=
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      map_add' := fun p q => DD.ext (by simp) (by ext j; simp) (by ext j; simp) (by simp)
      map_smul' := fun c p => by
        have hC : (DD.C c : DD X g) = ⟨c, 0, 0, 0⟩ := rfl
        simp only [RingHom.id_apply]
        change _ = DD.C c * _
        rw [hC]
        apply DD.ext <;> (try funext j) <;> simp }
  refine Module.Finite.of_surjective f ?_
  intro y
  exact ⟨(y.a, y.ep, y.ep', y.eta), rfl⟩

private theorem dd_nil (X : Type) [CommRing X] (g : ℕ) : RingHom.ker (DD.aug X g) ^ 3 = ⊥ := by
  set I := RingHom.ker (DD.aug X g) with hIdef
  have hI : ∀ y ∈ I, y.a = 0 := fun y hy => RingHom.mem_ker.mp hy
  have h2 : ∀ w ∈ I ^ 2, w.a = 0 ∧ w.ep = 0 ∧ w.ep' = 0 := by
    intro w hw
    rw [sq] at hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro m hm n hn
      have e1 := hI m hm
      have e2 := hI n hn
      refine ⟨by simp [e1, e2], by ext j; simp [e1, e2], by ext j; simp [e1, e2]⟩
    · rintro x y ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
      refine ⟨by simp [h1, h4], by ext j; simp [h2, h5], by ext j; simp [h3, h6]⟩
  rw [eq_bot_iff, pow_succ, Ideal.mul_le]
  intro r hr s hs
  obtain ⟨a1, a2, a3⟩ := h2 r hr
  have e := hI s hs
  rw [Ideal.mem_bot]
  apply DD.ext
  · simp [a1]
  · ext j
    simp [a1, a2, e]
  · ext j
    simp [a1, a3, e]
  · simp [a1, a2, a3, e]

theorem UpperTheory.V.Pa.testEx :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F) (Φ : S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) → (∀ k, μ k ∈ S.La) → (∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y) → ∃ θ : S.U.AA →+* DD S.F e, S.Test (DD S.F e) (DD.aug S.F e) θ ∧ ∀ a, θ a = ⟨S.rF (S.pr0 a), fun k => μ k (S.pr1 a), fun k => α k (S.pr0 a), Φ (S.pr1 a)⟩ := by
  intro l _ S e α μ Φ hα hμ hΦ
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := prAdd l S
  have hα' : ∀ k, (∀ b b', α k (b * b') = S.rF b * α k b' + S.rF b' * α k b) ∧
      (∀ o, α k (algebraMap S.OO S.Bh o) = 0) ∧ ∀ b ∈ ired S.U.N, α k b = 0 := fun k => hα k
  have hμ' : ∀ k (b : S.Bh) y, μ k (b • y) = S.rF b * μ k y := fun k => hμ k
  have q0 : ∀ b : S.Bh, S.pr0 (algebraMap S.Bh S.U.AA b) = b := fun b => by simpa using (p2 b 0).1
  have q1 : ∀ b : S.Bh, S.pr1 (algebraMap S.Bh S.U.AA b) = 0 := fun b => by simpa using (p2 b 0).2
  have o0 : S.pr0 1 = 1 := by simpa using q0 1
  have o1 : S.pr1 1 = 0 := by simpa using q1 1
  have z0 : S.pr0 0 = 0 := by simpa using q0 0
  have z1 : S.pr1 0 = 0 := by simpa using q1 0
  have hα1 : ∀ k, α k 1 = 0 := fun k => by simpa using (hα' k).2.1 1
  let T : S.U.AA → DD S.F e := fun a =>
    ⟨S.rF (S.pr0 a), fun k => μ k (S.pr1 a), fun k => α k (S.pr0 a), Φ (S.pr1 a)⟩
  have hmul : ∀ a a', T (a * a') = T a * T a' := by
    intro a a'
    have hd : S.rF (S.pr0 (a * a')) = S.rF (S.pr0 a) * S.rF (S.pr0 a') := by
      have h0 : S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ RingHom.ker S.rF := by
        rw [S.rF_ker]
        exact p6 (p5 a a').1
      rw [RingHom.mem_ker, map_sub, map_mul, sub_eq_zero] at h0
      exact h0
    have hda : ∀ k, α k (S.pr0 (a * a')) =
        S.rF (S.pr0 a) * α k (S.pr0 a') + S.rF (S.pr0 a') * α k (S.pr0 a) := by
      intro k
      have h0 := (hα' k).2.2 _ (p5 a a').1
      rw [map_sub, sub_eq_zero] at h0
      rw [h0, (hα' k).1]
    have hp1 := (p5 a a').2
    apply DD.ext
    · simp only [T, DD.mul_a]
      exact hd
    · funext k
      simp only [T, DD.mul_ep]
      rw [hp1, map_add (f := _), hμ', hμ']
      ring
    · funext k
      simp only [T, DD.mul_ep']
      rw [hda k]
      ring
    · simp only [T, DD.mul_eta]
      rw [hp1, map_add (f := _), hΦ, hΦ, Finset.sum_add_distrib]
      have s1 : ∑ j, μ j (S.pr1 a) * α j (S.pr0 a') = ∑ j, α j (S.pr0 a') * μ j (S.pr1 a) :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [s1]
      ring
  let θ : S.U.AA →+* DD S.F e :=
    { toFun := T
      map_one' := DD.ext (by simp [T, o0]) (by funext k; simp [T, o1]) (by funext k; simp [T, o0, hα1])
        (by simp [T, o1])
      map_mul' := hmul
      map_zero' := DD.ext (by simp [T, z0]) (by funext k; simp [T, z1]) (by funext k; simp [T, z0])
        (by simp [T, z1])
      map_add' := fun a a' => DD.ext (by simp [T, (p3 a a').1]) (by funext k; simp [T, (p3 a a').2])
        (by funext k; simp [T, (p3 a a').1]) (by simp [T, (p3 a a').2]) }
  have hAlg : ∀ c : S.F, algebraMap S.F (DD S.F e) c = ⟨c, 0, 0, 0⟩ := fun c => rfl
  refine ⟨θ, ⟨dd_fin _ _, ⟨3, dd_nil _ _⟩, fun a => rfl, fun o => ?_⟩, fun a => rfl⟩
  rw [hAlg]
  apply DD.ext
  · simp [θ, T, q0]
  · funext k
    simp [θ, T, q1]
  · funext k
    simp [θ, T, q0, (hα' k).2.1]
  · simp [θ, T, q1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TpDual
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dual_of_univ {R F W : Type} [AddCommGroup R] [Field F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (π : R →+ W) (T : Submodule F (R →+ F))
    (h1 : ∀ φ : Module.Dual F W, φ.toAddMonoidHom.comp π ∈ T)
    (h2 : ∀ α ∈ T, ∃ φ : Module.Dual F W, φ.toAddMonoidHom.comp π = α) :
    Module.Finite F T ∧ (∀ b, (∀ α ∈ T, α b = 0) → π b = 0) ∧
      ∀ ξ : Module.Dual F T, ∃ w : W, ∀ b, π b = w → ∀ α : T, (α : R →+ F) b = ξ α := by
  let Φ : Module.Dual F W →ₗ[F] T :=
    { toFun := fun φ => ⟨φ.toAddMonoidHom.comp π, h1 φ⟩
      map_add' := fun _ _ => Subtype.ext (by ext; simp)
      map_smul' := fun _ _ => Subtype.ext (by ext; simp) }
  have hΦ : Function.Surjective Φ := fun α => by
    obtain ⟨φ, e⟩ := h2 α.1 α.2
    exact ⟨φ, Subtype.ext e⟩
  refine ⟨Module.Finite.of_surjective Φ hΦ, fun b hb => ?_, fun ξ => ?_⟩
  · exact (Module.forall_dual_apply_eq_zero_iff F (π b)).1 fun φ => hb _ (h1 φ)
  · obtain ⟨w, hw⟩ := (Module.evalEquiv F W).surjective (ξ.comp Φ)
    refine ⟨w, fun b hb α => ?_⟩
    obtain ⟨φ, rfl⟩ := hΦ α
    have := LinearMap.congr_fun hw φ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply] at this
    rw [← this, ← hb]
    rfl

private theorem tp_abs {O R F : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field F] [Algebra O R] [IsLocalHom (algebraMap O R)] (r : R →+* F) (hk : RingHom.ker r = maximalIdeal R)
    (hs : Function.Surjective (r.comp (algebraMap O R))) (I J : Ideal R)
    (hJ : J = (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ⊔ I) (hI : I ≤ maximalIdeal R)
    (hJm : J ≤ maximalIdeal R) (T : Submodule F (R →+ F))
    (hT : ∀ α, α ∈ T ↔ (∀ b b', α (b * b') = r b * α b' + r b' * α b) ∧ (∀ o, α (algebraMap O R o) = 0) ∧
      ∀ b ∈ I, α b = 0) :
    Module.Finite F T ∧ (∀ b ∈ maximalIdeal R, (∀ α ∈ T, α b = 0) → b ∈ J) ∧
      ∀ ξ : Module.Dual F T, ∃ b ∈ maximalIdeal R, ∀ α : T, (α : R →+ F) b = ξ α := by
  have hm : ∀ b, b ∈ maximalIdeal R ↔ r b = 0 := fun b => by rw [← hk, RingHom.mem_ker]
  have hO : ∀ o : O, algebraMap O R o ∈ maximalIdeal R → algebraMap O R o ∈ J := fun o ho => by
    rw [hJ]
    refine Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ?_))
    exact fun hu => ho (hu.map _)
  have hsq : ∀ x ∈ maximalIdeal R, ∀ y ∈ maximalIdeal R, x * y ∈ J := fun x hx y hy => by
    rw [hJ, pow_two]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mul_mem_mul hx hy))
  have hdec : ∀ b : R, ∃ o : O, ∃ x ∈ maximalIdeal R, b = algebraMap O R o + x := fun b => by
    obtain ⟨o, ho⟩ := hs (r b)
    refine ⟨o, b - algebraMap O R o, (hm _).2 ?_, by ring⟩
    rw [map_sub, ← ho]; simp
  let N : Submodule O R := J.restrictScalars O ⊔ 1
  have hNJ : ∀ b ∈ J, N.mkQ b = 0 := fun b hb =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_left hb)
  have hNO : ∀ o : O, N.mkQ (algebraMap O R o) = 0 := fun o =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_right (Submodule.mem_one.2 ⟨o, rfl⟩))
  have hkill : ∀ o : O, r (algebraMap O R o) = 0 → ∀ w : R ⧸ N, o • w = 0 := fun o ho w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [← map_smul, Algebra.smul_def]
    exact hNJ _ (J.mul_mem_right _ (hO o ((hm _).2 ho)))
  letI : SMul F (R ⧸ N) := ⟨fun c w => Function.surjInv hs c • w⟩
  have hsm : ∀ (o : O) (w : R ⧸ N), (r.comp (algebraMap O R)) o • w = o • w := fun o w => by
    show Function.surjInv hs _ • w = o • w
    rw [← sub_eq_zero, ← sub_smul]
    refine hkill _ ?_ w
    have := Function.surjInv_eq hs ((r.comp (algebraMap O R)) o)
    rw [map_sub, map_sub, sub_eq_zero]
    exact this
  letI : Module F (R ⧸ N) := Function.Surjective.moduleLeft (r.comp (algebraMap O R)) hs hsm
  have hder : ∀ b b' : R, N.mkQ (b * b') = r b • N.mkQ b' + r b' • N.mkQ b := fun b b' => by
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    obtain ⟨o', x', hx', rfl⟩ := hdec b'
    have e : (algebraMap O R o + x) * (algebraMap O R o' + x') =
        algebraMap O R (o * o') + (o • x' + o' • x) + x * x' := by
      simp only [Algebra.smul_def, map_mul]; ring
    have e1 : r (algebraMap O R o + x) = (r.comp (algebraMap O R)) o := by
      rw [map_add (f := _), (hm x).1 hx, add_zero]; rfl
    have e2 : r (algebraMap O R o' + x') = (r.comp (algebraMap O R)) o' := by
      rw [map_add (f := _), (hm x').1 hx', add_zero]; rfl
    rw [e, e1, e2, hsm, hsm]
    simp only [map_add (f := _), hNO, hNJ _ (hsq x hx x' hx'), map_smul, zero_add, add_zero]
  have hsurj : ∀ w : R ⧸ N, ∃ b ∈ maximalIdeal R, N.mkQ b = w := fun w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    exact ⟨x, hx, by rw [map_add (f := _), hNO, zero_add]⟩
  haveI : Module.Finite F (R ⧸ N) := by
    obtain ⟨s, hs'⟩ := IsNoetherian.noetherian (maximalIdeal R)
    refine ⟨Submodule.fg_def.2 ⟨N.mkQ '' s, s.finite_toSet.image _, eq_top_iff.2 fun w _ => ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := hsurj w
    rw [← hs'] at hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | smul c x hx ih =>
      rw [hs'] at hx
      rw [smul_eq_mul, hder, (hm x).1 hx, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (ih trivial)
  obtain ⟨f1, f2, f3⟩ := dual_of_univ (F := F) N.mkQ.toAddMonoidHom T (fun φ => (hT _).2 ⟨fun b b' => by
      show φ (N.mkQ (b * b')) = r b * φ (N.mkQ b') + r b' * φ (N.mkQ b)
      rw [hder, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul], fun o => by
      show φ (N.mkQ _) = 0
      rw [hNO, map_zero], fun b hb => by
      show φ (N.mkQ _) = 0
      rw [hNJ b (by rw [hJ]; exact Ideal.mem_sup_right hb), map_zero]⟩) (fun α hα => by
    obtain ⟨a1, a2, a3⟩ := (hT α).1 hα
    let K : Ideal R :=
      { carrier := {b | r b = 0 ∧ α b = 0}
        add_mem' := fun {x y} hx hy => ⟨by rw [map_add (f := _), hx.1, hy.1, add_zero], by rw [map_add (f := _), hx.2, hy.2, add_zero]⟩
        zero_mem' := ⟨map_zero _, map_zero _⟩
        smul_mem' := fun c x hx => ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero],
          by rw [smul_eq_mul, a1, hx.1, hx.2]; ring⟩ }
    have hK : J ≤ K := by
      rw [hJ]
      refine sup_le (sup_le (Ideal.map_le_iff_le_comap.2 fun o ho => ⟨(hm _).1 (hJm ?_), a2 o⟩) ?_)
        fun b hb => ⟨(hm _).1 (hI hb), a3 b hb⟩
      · rw [hJ]; exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))
      · rw [pow_two]
        refine Ideal.mul_le.2 fun x hx y hy => ⟨?_, ?_⟩
        · rw [map_mul, (hm x).1 hx, zero_mul]
        · rw [a1, (hm x).1 hx, (hm y).1 hy]; ring
    have hN : ∀ b ∈ N.toAddSubgroup, α b = 0 := fun b hb => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from hb)
      obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
      rw [map_add (f := _), a2, (hK hy).2, add_zero]
    let ψ : (R ⧸ N) →+ F := QuotientAddGroup.lift N.toAddSubgroup α hN
    have hψ : ∀ b, ψ (N.mkQ b) = α b := fun _ => rfl
    refine ⟨{ toFun := ψ, map_add' := ψ.map_add, map_smul' := fun c w => ?_ }, AddMonoidHom.ext hψ⟩
    obtain ⟨o, rfl⟩ := hs c
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [hsm, ← map_smul, hψ, hψ, Algebra.smul_def, a1, a2]
    simp)
  refine ⟨f1, fun b hb h => ?_, fun ξ => ?_⟩
  · have h0 : b ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (f2 b h)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from h0)
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
    refine J.add_mem hy (hO o ?_)
    have := (maximalIdeal R).sub_mem hb (hJm hy)
    rwa [add_sub_cancel_left] at this
  · obtain ⟨w, hw⟩ := f3 ξ
    obtain ⟨b, hb, e⟩ := hsurj w
    exact ⟨b, hb, hw b e⟩

theorem UpperTheory.V.Pa.tpDual :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), Module.Finite S.F S.Tp ∧ (∀ b ∈ maximalIdeal S.Bh, (∀ α ∈ S.Tp, α b = 0) → b ∈ S.J2) ∧ ∀ ξ : Module.Dual S.F S.Tp, ∃ b ∈ maximalIdeal S.Bh, ∀ α : S.Tp, (α : S.Bh →+ S.F) b = ξ α := by
  intro l _ S
  haveI : IsNoetherianRing S.Bh := { noetherian := S.d6.noetherian }
  have hI : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]
    exact hc
  have hJ : S.J2 ≤ maximalIdeal S.Bh := by
    refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hI
    exact ((IsLocalRing.local_hom_tfae (algebraMap S.OO S.Bh)).out 1 3).1
      (IsCO.isLocalHom (O := S.OO) (R := S.Bh))
  exact tp_abs S.rF S.rF_ker S.oo_surj (ired S.U.N) S.J2 rfl hI hJ S.Tp fun _ => Iff.rfl
end

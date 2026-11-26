module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

end

theorem UpperTheory.V.Th.Coc.starFacts :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R : Type} [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] {n : ℕ}, (∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a) ∧ (∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b) ∧ (∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a) ∧ (∀ a, F.star O R n (F.star O R n a) = a) ∧ (∀ g, F.star O R n (MonoidAlgebra.single g 1) = MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O))) ∧ ∀ (x : R →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O), F.IsForm O n ρ P → ∀ a, repR x (mat ρ) (F.star O R n a) = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (repR x (mat ρ) a)ᵀ * (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R _ _ _ _ n
  have hmul : ∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a := by
    intro a b
    simp [GFrame.star, map_mul]
  have hadd : ∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro a b
    simp [GFrame.star, map_add (f := _)]
  have hsmul : ∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a := by
    intro r a
    simp [GFrame.star, map_smul]
  have hzero : F.star O R n 0 = 0 := by
    simp [GFrame.star]
  have hsingle : ∀ g (r : R), F.star O R n (MonoidAlgebra.single g r)
      = MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
    intro g r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hepsR : ∀ g (k : ℤ), ((F.eps O R g ^ k : Rˣ) : R)
      = algebraMap O R ((F.eps O O g ^ k : Oˣ) : O) := by
    intro g k
    have h : F.eps O R g = Units.map (algebraMap O R).toMonoidHom (F.eps O O g) := by
      ext
      simp [GFrame.eps, pushCh]
    rw [h, ← map_zpow]
    rfl
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hcc : ∀ g, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
    rw [hci, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]
  have hepsc : ∀ g, F.eps O R (F.conj g) = F.eps O R g := by
    intro g
    have h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
      show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = _
      rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]
    simp [GFrame.eps, pushCh, h]
  refine ⟨hmul, hadd, hsmul, ?_, ?_, ?_⟩
  · intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [hzero, hzero]
    | add f g hf hg => rw [hadd, hadd, hf, hg]
    | single g r =>
      rw [hsingle, hsingle]
      simp only [map_inv, hcc, inv_inv, hepsc]
      congr 1
      rw [mul_assoc, ← Units.val_mul, _root_.inv_zpow', ← _root_.zpow_add, add_neg_cancel, _root_.zpow_zero,
        Units.val_one, mul_one]
  · intro g
    rw [hsingle, one_mul, hepsR]
  · intro x ρ P hP a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [hzero]
    | add f g hf hg =>
      rw [hadd, map_add (f := _), hf, hg, map_add (f := _), transpose_add, Matrix.mul_add, Matrix.add_mul]
    | single g r =>
      have key : ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
          = ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) • mat ρ (F.conj g)⁻¹ := by
        have h := hP g
        have hm : mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        calc ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
            = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
              * (mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹) := by rw [hm, mul_one]
          _ = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
              * ((mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O) * mat ρ (F.conj g)) * mat ρ (F.conj g)⁻¹ := by
            simp only [mul_assoc]
          _ = _ := by
            rw [h, Matrix.mul_smul, Units.inv_mul, Matrix.smul_mul, one_mul]
      rw [hsingle, repR_single, repR_single, map_mul, hepsR, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        transpose_smul, Matrix.mul_smul, Matrix.smul_mul, key, mul_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrRep
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.trRep :
    ∀ {O R G : Type} [CommRing O] [CommRing R] [Algebra O R] [Group G] {n : ℕ} (D : GDet n R G) (x : R →ₐ[O] O) (ρ : G →* Matrix (Fin n) (Fin n) O), 1 ≤ n → D.map x.toRingHom = GDet.ofRep ρ → (∀ y, (repR x ρ y).trace = x (D.tr y)) ∧ (∀ (r : R) y, repR x ρ (r • y) = x r • repR x ρ y) ∧ ∃ t : MonoidAlgebra R G →ₗ[R] R, ∀ y, t y = D.tr y := by
  intro O R G _ _ _ _ n D x ρ hn h
  refine ⟨fun y => ?_, fun r y => ?_, ?_⟩
  · have h1 := (((CA.d_gmap D).2.2.1 x.toRingHom y).2 1)
    rw [h] at h1
    have h2 := (CA.d_toDet (GDet.ofRep ρ) (MonoidAlgebra.mapRingHom G x.toRingHom y)).2.2.1
    rw [CA.d_toDet_ofRep.1 ρ, (CA.d_ofRep _ _ _).2.2.1 hn] at h2
    exact h2.trans h1
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | single g a =>
      rw [MonoidAlgebra.smul_single, repR_single, repR_single, smul_eq_mul, map_mul, mul_smul]
  · obtain ⟨t, ht⟩ := (CA.d_tr D.toDet).1 hn
    exact ⟨t, fun y => (ht y).trans (CA.d_toDet D y).2.2.1⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftConj
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftConj :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ ρ' : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (c : O) (Q : GL (Fin n) O) (d : E →+ Matrix (Fin n) (Fin n) X), (∀ a, ρ a = (Q : Matrix (Fin n) (Fin n) O) * ρ' a * ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) → IsLift x δ ρ' τ c d → ∃ d' : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ c d' ∧ ∀ a, d' a = bar X (Q : Matrix (Fin n) (Fin n) O) * d a * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ ρ' τ c Q d hρ hL
  have hbm : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := by
    intro A B
    simp [bar, Matrix.map_mul]
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hl : bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * bar X (Q : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hbm, Units.inv_mul, hbar1]
  have hbρ : ∀ a, bar X (ρ a) = bar X (Q : Matrix (Fin n) (Fin n) O) * bar X (ρ' a) * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    intro a
    rw [hρ, hbm, hbm]
  set P := bar X (Q : Matrix (Fin n) (Fin n) O) with hPdef
  set Pi := bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hPidef
  refine ⟨AddMonoidHom.mk' (fun a => P * d a * Pi) (fun a b => by rw [map_add (f := _), mul_add, add_mul]), ?_, fun a => rfl⟩
  constructor
  · intro a b
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.mul, hbρ, hbρ]
    have e1 : P * d a * Pi * (P * bar X (ρ' b) * Pi) = P * (d a * bar X (ρ' b)) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    have e2 : P * bar X (ρ' a) * Pi * (P * d b * Pi) = P * (bar X (ρ' a) * d b) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    rw [e1, e2, mul_add, add_mul]
  · intro r a
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.smul, hbρ, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  · intro a
    simp only [AddMonoidHom.mk'_apply]
    rw [Matrix.trace_mul_cycle, hl, Matrix.one_mul, hL.tr]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Kill0
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem k0 {O G : Type} [CommRing O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O)
    (hs : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) (X : Type) [CommRing X] [Algebra O X]
    (W : Matrix (Fin n) (Fin n) X) (h : ∀ g, (bar X (ρ g) * W).trace = 0) : c₀ • W = 0 := by
  have key : ∀ M ∈ Submodule.span O (Set.range ρ), (bar X M * W).trace = 0 := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h g
    | zero => simp [bar]
    | add x y _ _ hx hy =>
      have e : bar X (x + y) = bar X x + bar X y := by
        ext i j
        simp [bar]
      rw [e, add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx =>
      have e : bar X (a • x) = a • bar X x := by
        ext i j
        simp only [bar]
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul,
          Algebra.smul_def]
      rw [e, Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  have t := key _ (hs (Matrix.single j i 1))
  have e : bar X (c₀ • Matrix.single j i (1 : O)) = Matrix.single j i (algebraMap O X c₀) := by
    ext a b
    simp [bar, Matrix.single_apply]
    split_ifs <;> simp
  rw [e] at t
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Algebra.smul_def] using t

theorem UpperTheory.V.Th.Coc.kill0 :
    ∀ {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ W : Matrix (Fin n) (Fin n) O, (∀ g, (ρ g * W).trace = 0) → W = 0) ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (W : Matrix (Fin n) (Fin n) X), (∀ g, (bar X (ρ g) * W).trace = 0) → c₀ • W = 0 := by
  intro O G _ _ _ n ρ c₀ hc hs
  refine ⟨fun W hW => ?_, fun X _ _ W hW => k0 ρ c₀ hs X W hW⟩
  have hb : ∀ g, (bar O (ρ g) * W).trace = 0 := by
    intro g
    have e : bar O (ρ g) = ρ g := by
      ext i j
      simp [bar]
    rw [e]
    exact hW g
  have := k0 ρ c₀ hs O W hb
  ext i j
  have := congrFun (congrFun this i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DerPow
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem x_loc {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    (x : R →ₐ[O] O) (y : R) (hy : y ∈ maximalIdeal R) : x y ∈ maximalIdeal O := by
  intro hu
  have h2 : IsUnit (y - algebraMap O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem der_pow {O R X : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [AddCommGroup X] [Module O X] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (h : IsDer x δ) (k : ℕ) :
    ∀ a ∈ maximalIdeal R ^ (k + 1), x a ∈ maximalIdeal O ^ (k + 1) ∧
      δ a ∈ (maximalIdeal O ^ k • ⊤ : Submodule O X) := by
  induction k with
  | zero =>
    intro a ha
    rw [zero_add, pow_one] at ha
    refine ⟨by simpa using x_loc x a ha, by simp⟩
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun b c hb hc => ?_)
    · obtain ⟨h1, h2⟩ := ih b hb
      have h3 := x_loc x c hc
      refine ⟨?_, ?_⟩
      · rw [map_mul, pow_succ _ (k + 1)]
        exact Ideal.mul_mem_mul h1 h3
      · rw [h b c]
        refine Submodule.add_mem _ (Submodule.smul_mem_smul h1 Submodule.mem_top) ?_
        rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul h3 h2
    · rw [map_add (f := _), map_add (f := _)]
      exact ⟨Ideal.add_mem _ hb.1 hc.1, Submodule.add_mem _ hb.2 hc.2⟩

theorem UpperTheory.V.Th.Coc.lcDer :
    ∀ {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [TopologicalSpace Γ] (m : ℕ), (∀ f : Γ → O, AdicCont (maximalIdeal O) f → IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ m) (f g)) ∧ ∀ (x : R →ₐ[O] O) (δ : R →ₗ[O] Om O m), IsDer x δ → ∀ f : Γ → R, AdicCont (maximalIdeal R) f → IsLocallyConstant fun g => δ (f g) := by
  intro O R Γ _ _ _ _ _ _ m
  refine ⟨fun f hf => hf m, fun x δ h f hf => ?_⟩
  have hk : ∀ a ∈ maximalIdeal R ^ (m + 1), δ a = 0 := fun a ha => by
    refine Submodule.smul_induction_on (p := fun z => z = 0) (der_pow x δ h m a ha).2 (fun r hr z _ => ?_)
      (fun u v hu hv => by rw [hu, hv, add_zero])
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  have h1 := hf (m + 1)
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  intro g
  filter_upwards [h1 g] with g' hg
  rw [← sub_eq_zero, ← map_sub]
  exact hk _ (Ideal.Quotient.eq.1 hg)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LcMat
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lc_mat {Γ K : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) K)
    (h : ∀ a b, IsLocallyConstant fun g => f g a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ a b, ∀ᶠ y in nhds x, f y a b = f x a b := fun a b =>
    (IsLocallyConstant.iff_eventually_eq _).mp (h a b) x
  filter_upwards [Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (hx a)] with y hy
  ext a b
  exact hy a b

theorem UpperTheory.V.Th.Coc.lc :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsLift x δ (repR x ρ) τ c d → (IsLocallyConstant fun g => bar X (ρ g)) → (IsLocallyConstant fun g => δ (τ (MonoidAlgebra.single g 1))) → IsLocallyConstant fun g => c₀ • d (MonoidAlgebra.single g 1) := by
  intro O R X _ _ _ _ _ n G _ _ _ x δ ρ τ c c₀ d hspan hL hρ hτ
  have hsingle : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have hmulD : ∀ g h : G, d (MonoidAlgebra.single (g * h) 1) =
      d (MonoidAlgebra.single g 1) * bar X (ρ h) + bar X (ρ g) * d (MonoidAlgebra.single h 1) := by
    intro g h
    have e := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single h 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, hsingle, hsingle] at e
    exact e
  have hgen : ∀ h : G, IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace := by
    intro h
    have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace) =
        fun g => c • δ (τ (MonoidAlgebra.single (g * h) 1)) -
          (bar X (ρ g) * d (MonoidAlgebra.single h 1)).trace := by
      funext g
      rw [← hL.tr, hmulD, Matrix.trace_add, add_sub_cancel_right]
    rw [e]
    refine IsLocallyConstant.sub ?_ ?_
    · exact (hτ.comp_continuous (continuous_mul_const h)).comp (fun y => c • y)
    · exact hρ.comp fun M => (M * d (MonoidAlgebra.single h 1)).trace
  have hspanLC : ∀ Z ∈ Submodule.span O (Set.range ρ),
      IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨h, rfl⟩ := hZ
      exact hgen h
    | zero =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (0 : Matrix (Fin n) (Fin n) O)).trace) =
          fun _ => 0 := by
        funext g
        have hb : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_zero, Matrix.trace_zero]
      rw [e]
      exact IsLocallyConstant.const 0
    | add Z W _ _ hZ hW =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (Z + W)).trace) =
          fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace +
            (d (MonoidAlgebra.single g 1) * bar X W).trace := by
        funext g
        have hb : bar X (Z + W) = bar X Z + bar X W := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_add, Matrix.trace_add]
      rw [e]
      exact hZ.add hW
    | smul k Z _ hZ =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (k • Z)).trace) =
          fun g => algebraMap O X k * (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
        funext g
        have hb : bar X (k • Z) = algebraMap O X k • bar X Z := by
          ext i j
          simp [bar, Matrix.smul_apply, smul_eq_mul]
        rw [hb, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [e]
      exact hZ.comp fun y => algebraMap O X k * y
  apply lc_mat
  intro a b
  have key : ∀ M : Matrix (Fin n) (Fin n) X,
      (M * bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace = (c₀ • M) a b := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, bar, Matrix.map_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_ite, smul_zero, smul_eq_mul, mul_one, ite_and]
    simp only [apply_ite (algebraMap O X), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Algebra.smul_def, mul_one]
    rw [mul_comm]
  have e : (fun g => (c₀ • d (MonoidAlgebra.single g 1)) a b) =
      fun g => (d (MonoidAlgebra.single g 1) *
        bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace := by
    funext g
    rw [key]
  rw [e]
  exact hspanLC _ (hspan _)
end

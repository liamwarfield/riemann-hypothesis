module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.SignLemma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualInclUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.psiInj :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
        ∀ {n : ℕ} (κ : Fin n → Dec (F := L) A →* (PadicAlgCl l)ˣ) (m : Fin n → ℤ) (k : ℕ), Function.Injective m → 0 < k → (∀ i (g : Dec (F := L) A), (g : G L Ω) ∈ Ine (F := L) A → (κ i g * cycBar L Ω l g ^ (-m i)) ^ k = 1) → Function.Injective κ := by
  intro l _ L Ω _ _ _ _ _ A w hA hw n κ m k hm hk h i i' e
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hA hw
  obtain ⟨-, φ, b1, -, -, b4, b5, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, _, ⟨⟨g, rfl⟩, hg⟩, h2⟩ := (Loc.cycInertia l).2 φ.range b1.isOpen_range
  rw [b5] at h2
  have h3 : ¬ IsOfFinOrder (cycBar L Ω l (g : G L Ω)) := fun hf => by
    obtain ⟨N, hN, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    refine h2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, Units.ext (Subtype.ext
      ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))⟩)
    have h4 := congrArg Units.val h1
    simp [cycBar] at h4 ⊢
    exact h4
  have a1 := h i g ((b4 g).1 hg)
  have a2 := h i' g ((b4 g).1 hg)
  rw [← e] at a2
  have a3 := a1.trans a2.symm
  rw [mul_pow, mul_pow, mul_right_inj, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul] at a3
  have a4 := (injective_zpow_iff_not_isOfFinOrder.2 h3) a3
  have a5 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  exact hm (neg_injective (mul_right_cancel₀ a5 a4))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.BkAbEmb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

open scoped Pointwise in
private theorem bkAb_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω) (hA : ∀ w, IsPlaceOver (A w) w)
    (τ : F →+* Formalism.BasicNotions.Loc.Om l) :
    ∃ (j : Ω →+* Formalism.BasicNotions.Loc.Om l) (w : HeightOneSpectrum (𝓞 F)), j.comp (algebraMap F Ω) = τ ∧
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ Loc.placeJ j = A w := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨j₀, hj₀⟩ : ∃ j : Ω →+* Formalism.BasicNotions.Loc.Om l, j.comp (algebraMap F Ω) = τ := by
    letI : Algebra F (Formalism.BasicNotions.Loc.Om l) := τ.toAlgebra
    exact ⟨(IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).toRingHom,
      (IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).comp_algebraMap⟩
  obtain ⟨w, hw, hl⟩ := ((Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j₀).1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA w) hw
  refine ⟨j₀.comp (g : Ω →+* Ω), w, hj₀ ▸ RingHom.ext fun x => congrArg j₀ (g.commutes x), hl, ?_⟩
  ext x
  change g • x ∈ Loc.placeJ j₀ ↔ _
  rw [← hg]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

theorem UpperTheory.V.Ws.Eb.bkAb :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {n : ℕ} (R : Representation (PadicAlgCl l) V.frame.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))), ∀ z ∈ Z1 R,
        (∀ (v : V.frame.Vl) (φ : V.frame.Gv v →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ → (∀ g, φ g ∈ Loc.Iq l ↔ g ∈ V.frame.Iv v) → (∀ g, Loc.cycA l l (PadicAlgCl l) (φ g) = cycBar L Ω l (Subtype.val g)) →
          (fun g : V.frame.Gv v => z (V.frame.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (V.frame.η.ker.subtype.comp (V.frame.φ v)) : Representation (PadicAlgCl l) (V.frame.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l)))) →
        (∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal → ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w), z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X) →
        Af.IsBK l (R.comp (toGS Ω V.S') : Representation (PadicAlgCl l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) (fun g => z (toGS Ω V.S' g)) := by
  intro l _ L Ω _ _ _ _ _ _ s V n R z hz h1 h2
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  refine ⟨fun w hw => ⟨s.A w, s.hA w, h2 w hw⟩, fun τ => ?_⟩
  obtain ⟨j, w, hj, hl, hA⟩ := bkAb_emb s.A s.hA τ
  refine ⟨j, hj, ?_⟩
  have key : ∃ φ : ↥(Dec (F := L) (s.A w)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
      (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A w)) ∧
      (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
    rw [← hA]
    obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
    exact ⟨φ, a, b, c, d l⟩
  obtain ⟨φ, a, b, c, d⟩ := key
  have h3 := h1 ⟨w, hl⟩ φ a c fun g => congrArg (Units.map _) (d g)
  exact (Loc.bkAbove (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A w)).subtype) a b
    (R.comp (toGS Ω V.S')) (fun g => z (toGS Ω V.S' g))
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩).1 h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocRel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cr_fst_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst :=
  Matrix.map_mul (f := dF K)

private theorem cr_snd_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul, mul_comm]

private theorem cr_alg {K : Type} [CommRing K] {n : ℕ} (A B P Q y y' Ai Bi Pi : Matrix (Fin n) (Fin n) K) (e : K)
    (hA : Ai * A = 1) (hB : B * Bi = 1) (hP : Pi * P = 1) (hP' : P * Pi = 1)
    (h1 : Aᵀ * P * B = e • P)
    (h2 : Aᵀ * P * (y' * B) + (Aᵀ * Q + (y * A)ᵀ * P) * B = e • Q) :
    y' = -(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q) := by
  have hBi : Bi * B = 1 := mul_eq_one_comm.mp hB
  have hAi : A * Ai = 1 := mul_eq_one_comm.mp hA
  have canc : ∀ X : Matrix (Fin n) (Fin n) K, Pi * Aiᵀ * (Aᵀ * P * X * B) * Bi = X := by
    intro X
    simp only [Matrix.mul_assoc]
    rw [hB, Matrix.mul_one, ← Matrix.mul_assoc Aiᵀ Aᵀ, ← Matrix.transpose_mul, hAi, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mul_assoc Pi P, hP, Matrix.one_mul]
  have lhs : Aᵀ * P * y' * B = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    rw [Matrix.transpose_mul] at h2
    rw [← h2]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
    abel
  have rhs : Aᵀ * P * (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)) * B
      = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    have t1 : Aᵀ * P * (Pi * yᵀ * P) * B = Aᵀ * (yᵀ * (P * B)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    have t2 : Aᵀ * P * (B * (Pi * Q) * Bi) * B = e • Q := by
      calc Aᵀ * P * (B * (Pi * Q) * Bi) * B = (Aᵀ * P * B) * (Pi * Q) * (Bi * B) := by
            simp only [Matrix.mul_assoc]
        _ = e • Q := by
            rw [h1, hBi, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_assoc, hP', Matrix.one_mul]
    have t3 : Aᵀ * P * (Pi * Q) * B = Aᵀ * (Q * B) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul, t1, t2, t3]
    abel
  rw [← canc y', ← canc (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)), lhs, rhs]

theorem UpperTheory.V.Ws.Eb.cocRel :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (y : F.G₀ → Matrix (Fin n) (Fin n) K) (ρ' : F.G₀ →* GL (Fin n) (DualNumber K)) (P' : GL (Fin n) (DualNumber K)), IsTan ρ y ρ' → F.IsForm O n ρ' P' →
        F.IsForm O n ρ (Matrix.GeneralLinearGroup.map (dF K) P') ∧ ∀ R, IsAdExt F ρ (Matrix.GeneralLinearGroup.map (dF K) P') R → ∃ Z, ∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z) := by
  intro l _ F O _ _ K _ _ n ρ y ρ' P' hT hF
  have hfst : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.fst = W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hsnd : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.snd = y g * W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hP : (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.fst
      = (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hc : ∀ g, ((F.eps O (DualNumber K) g ^ (1 - (n : ℤ)) : (DualNumber K)ˣ) : DualNumber K)
      = (TrivSqZeroExt.inl ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) : DualNumber K) := by
    intro g
    have : F.eps O (DualNumber K) g = Units.map (TrivSqZeroExt.inlHom K K : K →* DualNumber K) (F.eps O K g) :=
      Units.ext rfl
    rw [this, ← map_zpow]; rfl
  have hs1 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.fst = e • M.map TrivSqZeroExt.fst := by
    intro e M; ext i j; simp
  have hs2 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.snd = e • M.map TrivSqZeroExt.snd := by
    intro e M; ext i j; simp
  have part1 : ∀ g, (W.mat ρ g)ᵀ * (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K)
      * W.mat ρ (F.conj g)
      = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) •
        (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    intro g
    have h := congrArg (fun M => M.map TrivSqZeroExt.fst) (hF g)
    rw [cr_fst_mul, cr_fst_mul] at h
    simp only [Matrix.transpose_map, hfst, hP, hc, hs1] at h
    exact h
  refine ⟨fun g => part1 g, fun R hR => ?_⟩
  refine ⟨(↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹ : Matrix (Fin n) (Fin n) K) *
    (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.snd, fun g => ?_⟩
  have h := congrArg (fun M => M.map TrivSqZeroExt.snd) (hF g)
  rw [cr_snd_mul, cr_fst_mul, cr_snd_mul] at h
  simp only [Matrix.transpose_map, hfst, hsnd, hP, hc, hs2] at h
  rw [hR.c, hR.ad]
  exact cr_alg (A := W.mat ρ g) (B := W.mat ρ (F.conj g)) (Ai := ↑(ρ g)⁻¹) (Bi := ↑(ρ (F.conj g))⁻¹)
    (Pi := ↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹) (hA := Units.inv_mul _) (hB := Units.mul_inv _)
    (hP := Units.inv_mul _) (hP' := Units.mul_inv _) (h1 := part1 g) (h2 := h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocExt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cocExt_mem {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {x : F.Γ} (hx : x ∉ F.η.ker) : x * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η x) with h | h
  · exact absurd h hx
  · rw [h]
    rfl

private theorem cocycle_extends_to_conj_group {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K M : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (R : Representation K F.Γ M) (y : F.G₀ → M) (w : M)
    (hy : Continuous y) (hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h))
    (hw : Continuous fun g : F.G₀ => R g w) (hcw : R F.c w = -w)
    (hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w)) :
    ∃ z : F.Γ → M, Continuous z ∧ (∀ g h, z (g * h) = z g + R g (z h)) ∧ ∀ g : F.G₀, z g = y g := by
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hc2 : ∀ x : F.Γ, x * F.c * F.c = x := fun x => by rw [mul_assoc, hcc, mul_one]
  have I1 : ∀ g h : F.Γ, g * F.c * (F.c * h * F.c) = g * h * F.c := fun g h => by
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hcc, one_mul]
  have I2 : ∀ g h : F.Γ, g * F.c * (F.c * (h * F.c) * F.c) = g * h := fun g h => by
    simp only [mul_assoc]
    rw [hcc, mul_one, ← mul_assoc F.c F.c, hcc, one_mul]
  have hker : IsOpen (F.η.ker : Set F.Γ) := F.η_open
  have hkerc : IsOpen (F.η.ker : Set F.Γ)ᶜ := (Subgroup.isClosed_of_isOpen _ hker).isOpen_compl
  have Rm : ∀ (a b : F.Γ) (v : M), R (a * b) v = R a (R b v) := fun a b v => by rw [map_mul]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have hneg : ∀ x : F.Γ, x ∉ F.η.ker → F.η x = -1 := fun x hx => by
    rcases Int.units_eq_one_or (F.η x) with h | h
    · exact absurd (MonoidHom.mem_ker.mpr h) hx
    · exact h
  let z : F.Γ → M := fun x =>
    if hx : x ∈ F.η.ker then y ⟨x, hx⟩ else y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w
  have zin : ∀ x (hx : x ∈ F.η.ker), z x = y ⟨x, hx⟩ := fun x hx => dif_pos hx
  have zout : ∀ x (hx : x ∉ F.η.ker), z x = y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w :=
    fun x hx => dif_neg hx
  refine ⟨z, ?_, ?_, fun g => zin g g.2⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ F.η.ker
    · apply ContinuousOn.continuousAt _ (hker.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : (F.η.ker : Set F.Γ) => (⟨p.1, p.2⟩ : F.G₀) :=
        continuous_subtype_val.subtype_mk fun p => p.2
      refine (hy.comp hm).congr fun p => ?_
      exact (zin p.1 p.2).symm
    · apply ContinuousOn.continuousAt _ (hkerc.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : ((F.η.ker : Set F.Γ)ᶜ : Set F.Γ) => (⟨p.1 * F.c, cocExt_mem F p.2⟩ : F.G₀) :=
        (continuous_subtype_val.mul continuous_const).subtype_mk _
      refine ((hy.comp hm).add (hw.comp hm)).congr fun p => ?_
      exact (zout p.1 p.2).symm
  · intro g h
    by_cases hg : g ∈ F.η.ker <;> by_cases hh : h ∈ F.η.ker
    · rw [zin _ (mul_mem hg hh), zin _ hg, zin _ hh]
      exact hyc ⟨g, hg⟩ ⟨h, hh⟩
    · have hgh : g * h ∉ F.η.ker := fun H => hh (by simpa using mul_mem (inv_mem hg) H)
      rw [zout _ hgh, zin _ hg, zout _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g, hg⟩ * ⟨h * F.c, cocExt_mem F hh⟩ :=
        Subtype.ext (mul_assoc _ _ _)
      rw [e, hyc, map_add (f := _), ← Rm, ← mul_assoc]
      exact add_assoc _ _ _
    · have hgh : g * h ∉ F.η.ker := fun H => hg (by simpa using mul_mem H (inv_mem hh))
      rw [zout _ hgh, zout _ hg, zin _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h, hh⟩ := by
        apply Subtype.ext
        show g * h * F.c = g * F.c * ((F.conj ⟨h, hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I1 g h).symm
      rw [e, hyc, hrel, map_add (f := _), map_sub]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h, hh⟩)) = R g (y ⟨h, hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h, hh⟩)) w) = R (g * h * F.c) w := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * h * F.c)) w = _
        rw [I1]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - R (g * h * F.c) w)) + R (g * h * F.c) w = y _ + R (g * F.c) w + R g _
      abel
    · have hgh : g * h ∈ F.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, hneg g hg, hneg h hh]
        decide
      rw [zin _ hgh, zout _ hg, zout _ hh]
      have e : (⟨g * h, hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h * F.c, cocExt_mem F hh⟩ := by
        apply Subtype.ext
        show g * h = g * F.c * ((F.conj ⟨h * F.c, cocExt_mem F hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I2 g h).symm
      rw [e, hyc, hrel, map_add (f := _), map_sub, map_add (f := _)]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h * F.c, cocExt_mem F hh⟩)) =
          R g (y ⟨h * F.c, cocExt_mem F hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h * F.c, cocExt_mem F hh⟩)) w) =
          -R g (R (h * F.c) w) := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * (h * F.c) * F.c)) w = _
        rw [I2, ← Rm, ← mul_assoc, Rm (g * h) F.c, hcw, map_neg, neg_neg]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - -R g (R (h * F.c) w))) = y _ + R (g * F.c) w + (R g _ + R g (R (h * F.c) w))
      abel

theorem UpperTheory.V.Ws.Eb.cocExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)), Full ρ → Continuous ρ → IsAdExt F ρ P R →
        ∀ y ∈ Z1 (Loc.adGL ρ), ∀ Z, (∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z)) → ∃ z ∈ Z1 R, ∀ g : F.G₀, z g = y g := by
  intro l _ F K _ _ _ _ n ρ P R hF hρ hA y hy Z hZ
  obtain ⟨hy0, hycoc⟩ := hy
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have Rm : ∀ (a b : F.Γ) (v : Matrix (Fin n) (Fin n) K), R (a * b) v = R a (R b v) :=
    fun a b v => by rw [map_mul]; rfl
  have Rcc : ∀ v, R F.c (R F.c v) = v := fun v => by rw [← Rm, hcc, map_one]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have cc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    rw [hconj, hconj]
    simp only [← mul_assoc, hcc, one_mul]
    rw [mul_assoc, hcc, mul_one]
  have hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h) := fun g h => by
    rw [hycoc g h, hA.ad]
  have hinv : ∀ g : F.G₀, R g (Z + R F.c Z) = Z + R F.c Z := by
    intro g
    have e2 := hZ (F.conj g)
    rw [cc, hZ g, map_add (f := _), Rcc, map_sub, ← Rm, hconj] at e2
    have ec : F.c * (F.c * (g : F.Γ) * F.c) = g * F.c := by
      rw [← mul_assoc, ← mul_assoc, hcc, one_mul]
    rw [ec, Rm] at e2
    rw [map_add (f := _), ← sub_eq_zero, ← neg_eq_zero]
    rw [← sub_eq_zero] at e2
    rw [← e2]
    abel
  set w : Matrix (Fin n) (Fin n) K := (2 : K)⁻¹ • (R F.c Z - Z) with hwdef
  have hcw : R F.c w = -w := by
    rw [hwdef, map_smul, map_sub, Rcc, ← smul_neg, neg_sub]
  have hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w) := by
    intro g
    rw [hZ g]
    congr 1
    have hi := hinv (F.conj g)
    rw [map_add (f := _)] at hi
    rw [hwdef, map_smul, map_sub, ← smul_sub]
    have hb : R (F.conj g) (R F.c Z) = Z + R F.c Z - R (F.conj g) Z := by
      rw [← hi]
      abel
    rw [hb]
    have e : R F.c Z - Z - (Z + R F.c Z - R (↑(F.conj g)) Z - R (↑(F.conj g)) Z) =
        (2 : K) • (R (↑(F.conj g)) Z - Z) := by
      rw [two_smul]
      abel
    rw [e, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hw : Continuous fun g : F.G₀ => R g w := by
    have e : (fun g : F.G₀ => R g w) =
        fun g => (↑(ρ g) : Matrix (Fin n) (Fin n) K) * w * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
      funext fun g => by rw [hA.ad]; rfl
    rw [e]
    exact ((Units.continuous_val.comp hρ).matrix_mul continuous_const).matrix_mul (Units.continuous_coe_inv.comp hρ)
  obtain ⟨z, hz, hzc, hzy⟩ := cocycle_extends_to_conj_group F R y w hy0 hyc hw hcw hrel
  exact ⟨z, ⟨hz, hzc⟩, hzy⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AeComm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_rep_conj_chi_smul_and_q_twisted {K : Type} [Field K] {n : ℕ} (u v r ri r' ri' : Matrix (Fin n) (Fin n) K) (e : K)
    (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1) (hr' : r' * ri' = 1)
    (hA : rᵀ * u * r' = e • u) (X : Matrix (Fin n) (Fin n) K) :
    -(v * (r * X * ri)ᵀ * u) = r' * -(v * Xᵀ * u) * ri' := by
  have hrT : riᵀ * rᵀ = 1 := by rw [← Matrix.transpose_mul, hr, Matrix.transpose_one]
  have h1 : u * r' = e • (riᵀ * u) := by
    calc u * r' = riᵀ * (rᵀ * u * r') := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrT, Matrix.one_mul]
      _ = e • (riᵀ * u) := by rw [hA, Matrix.mul_smul]
  have h2 : ∀ Z, r' * (v * Z) = e • (v * (riᵀ * Z)) := by
    intro Z
    calc r' * (v * Z) = v * (u * r') * (v * Z) := by
          rw [← Matrix.mul_assoc v u r', hvu, Matrix.one_mul]
      _ = e • (v * (riᵀ * Z)) := by
          rw [h1]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc u v Z, huv, Matrix.one_mul]
  have hA' : rᵀ * (u * r') = e • u := by rw [← Matrix.mul_assoc]; exact hA
  have h3 : -(v * (r * X * ri)ᵀ * u) * r' = r' * -(v * Xᵀ * u) := by
    simp only [Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hA', h2,
      Matrix.mul_smul]
  calc -(v * (r * X * ri)ᵀ * u) = -(v * (r * X * ri)ᵀ * u) * (r' * ri') := by
        rw [hr', Matrix.mul_one]
    _ = r' * -(v * Xᵀ * u) * ri' := by rw [← Matrix.mul_assoc, h3]

private theorem u_mul_ri_mul_v_eq_transpose_of_eigen {K : Type} [Field K] {n : ℕ} (u v A r ri : Matrix (Fin n) (Fin n) K) (e : K)
    (he : e ≠ 0) (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1)
    (h1 : A * u * r = e • u) (h2 : A * uᵀ * r = e • uᵀ) : u * ri * v = uᵀ * ri * vᵀ := by
  have huvT : uᵀ * vᵀ = 1 := by rw [← Matrix.transpose_mul, hvu, Matrix.transpose_one]
  have hA1 : A = e • (u * ri * v) := by
    calc A = A * u * r * ri * v := by
          rw [Matrix.mul_assoc (A * u) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A u v, huv,
            Matrix.mul_one]
      _ = e • (u * ri * v) := by rw [h1, Matrix.smul_mul, Matrix.smul_mul]
  have hA2 : A = e • (uᵀ * ri * vᵀ) := by
    calc A = A * uᵀ * r * ri * vᵀ := by
          rw [Matrix.mul_assoc (A * uᵀ) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A uᵀ vᵀ, huvT,
            Matrix.mul_one]
      _ = e • (uᵀ * ri * vᵀ) := by rw [h2, Matrix.smul_mul, Matrix.smul_mul]
  exact smul_right_injective _ he (hA1.symm.trans hA2)

private theorem neg_conj_neg_transpose_eq_self_of_symm {K : Type} [Field K] {n : ℕ} (u v X : Matrix (Fin n) (Fin n) K)
    (hvu : v * u = 1) (hS : u * X * v = uᵀ * X * vᵀ) : -(v * (-(v * Xᵀ * u))ᵀ * u) = X := by
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc uᵀ X vᵀ, ← hS, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  simp only [Matrix.mul_assoc]
  rw [hvu, Matrix.mul_one, ← Matrix.mul_assoc, hvu, Matrix.one_mul]

theorem UpperTheory.V.Ws.Eb.adExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K), Full ρ → F.IsForm O n ρ P →
        ∃ R : Representation K F.Γ (Matrix (Fin n) (Fin n) K), IsAdExt F ρ P R := by
  intro l _ F O _ _ K _ _ n ρ P hFull hForm
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hcc' : ∀ x : F.Γ, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hconjv : ∀ g : F.G₀, ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c := by
    intro g
    show F.c * ↑g * F.c⁻¹ = _
    rw [hci]
  have hconj2 : ∀ g : F.G₀, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    rw [hconjv, hconjv]
    simp only [mul_assoc, hcc, mul_one, hcc']
  have heps : ∀ g : F.G₀, F.eps O K (F.conj g) = F.eps O K g := by
    intro g
    simp [W.GFrame.eps, W.GFrame.conj, W.pushCh]
  have hF : ∀ g : F.G₀, (↑(ρ g) : Matrix (Fin n) (Fin n) K)ᵀ * (↑P : Matrix (Fin n) (Fin n) K) *
      (↑(ρ (F.conj g)) : Matrix (Fin n) (Fin n) K) =
      ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (↑P : Matrix (Fin n) (Fin n) K) := hForm
  have huv : (↑P : Matrix (Fin n) (Fin n) K) * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv P
  have hvu : (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * (↑P : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul P
  have hS : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑P : Matrix (Fin n) (Fin n) K) * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) =
      (↑P : Matrix (Fin n) (Fin n) K)ᵀ * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ := by
    intro X
    have hX : X ∈ Submodule.span K (Set.range (W.mat ρ)) := by
      have h : Submodule.span K (Set.range (W.mat ρ)) = ⊤ := hFull
      rw [h]
      exact Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have e1 := hF (F.conj h⁻¹)
      rw [hconj2] at e1
      have e2 := congrArg Matrix.transpose (hF h⁻¹)
      rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, ← Matrix.mul_assoc, ← heps h⁻¹] at e2
      refine u_mul_ri_mul_v_eq_transpose_of_eigen _ _ ((↑(ρ (F.conj h⁻¹)) : Matrix (Fin n) (Fin n) K)ᵀ) (↑(ρ h⁻¹)) _ _
        (Units.ne_zero _) huv hvu ?_ e1 e2
      show (↑(ρ h⁻¹) : Matrix (Fin n) (Fin n) K) * (↑(ρ h) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul a x _ hx => simp only [Matrix.mul_smul, Matrix.smul_mul, hx]
  let θ : Module.End K (Matrix (Fin n) (Fin n) K) :=
    { toFun := fun X => -((↑P⁻¹ : Matrix (Fin n) (Fin n) K) * Xᵀ * (↑P : Matrix (Fin n) (Fin n) K))
      map_add' := fun X Y => by
        simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
      map_smul' := fun a X => by
        simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
          RingHom.id_apply] }
  have hkey : ∀ g : F.G₀, θ * Loc.adGL ρ g = Loc.adGL ρ (F.conj g) * θ := by
    intro g
    apply LinearMap.ext
    intro X
    exact exists_rep_conj_chi_smul_and_q_twisted _ _ _ _ _ _ _ huv hvu (Units.mul_inv _) (Units.mul_inv _) (hF g) X
  have hθθ : θ * θ = 1 := by
    apply LinearMap.ext
    intro X
    exact neg_conj_neg_transpose_eq_self_of_symm _ _ X hvu (hS X)
  have hker : ∀ γ : F.Γ, F.η γ ≠ 1 → γ * F.c ∈ F.η.ker := by
    intro γ h
    rw [MonoidHom.mem_ker, map_mul, F.η_c]
    rcases Int.units_eq_one_or (F.η γ) with h' | h'
    · exact absurd h' h
    · rw [h']
      exact Int.units_mul_self _
  have hAd : ∀ x y : F.G₀, (x : F.Γ) = y → Loc.adGL ρ x = Loc.adGL ρ y := by
    intro x y hxy
    rw [Subtype.ext hxy]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  let f : F.Γ → Module.End K (Matrix (Fin n) (Fin n) K) := fun γ =>
    if h : F.η γ = 1 then Loc.adGL ρ ⟨γ, h⟩ else Loc.adGL ρ ⟨γ * F.c, hker γ h⟩ * θ
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ⟨?_, ?_⟩⟩
  · show f 1 = 1
    simp only [f, dif_pos (map_one F.η)]
    exact map_one (Loc.adGL ρ)
  · intro a b
    show f (a * b) = f a * f b
    have hab : F.η (a * b) = F.η a * F.η b := map_mul _ _ _
    rcases Int.units_eq_one_or (F.η a) with ha | ha <;>
      rcases Int.units_eq_one_or (F.η b) with hb | hb
    · have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb, one_mul]
      simp only [f, dif_pos ha, dif_pos hb, dif_pos h1]
      rw [← map_mul (Loc.adGL ρ)]
      exact hAd _ _ rfl
    · have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, one_mul]; exact hne
      simp only [f, dif_pos ha, dif_neg hb', dif_neg h1]
      rw [← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [mul_assoc])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, mul_one]; exact hne
      simp only [f, dif_neg ha', dif_pos hb, dif_neg h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, hkey, ← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc'])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb]; exact Int.units_mul_self _
      simp only [f, dif_neg ha', dif_neg hb', dif_pos h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, ← mul_assoc θ, hkey, mul_assoc (Loc.adGL ρ _) θ θ, hθθ,
        mul_one, ← map_mul (Loc.adGL ρ)]
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc, hcc'])
  · intro g X
    show f ↑g X = _
    simp only [f, dif_pos (MonoidHom.mem_ker.mp g.2)]
  · intro X
    show f F.c X = _
    have hn : ¬ F.η F.c = 1 := by rw [F.η_c]; exact hne
    simp only [f, dif_neg hn]
    rw [Module.End.mul_apply]
    have h1 : ∀ p, (⟨F.c * F.c, p⟩ : F.G₀) = 1 := fun p => Subtype.ext hcc
    rw [h1, map_one]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LamIso
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem pushCh_comp_alg {H O A B C : Type} [Group H] [CommRing O] [CommRing A] [CommRing B] [CommRing C]
    [Algebra O A] [Algebra O B] [Algebra O C] (f : A →ₐ[O] B) (g : B →ₐ[O] C) (χ : H →* Aˣ) :
    W.pushCh ((g.comp f : A →ₐ[O] C) : A →+* C) χ = W.pushCh (g : B →+* C) (W.pushCh (f : A →+* B) χ) := by
  ext s
  rfl

private theorem pushCh_id_alg {H O A : Type} [Group H] [CommRing O] [CommRing A] [Algebra O A] (χ : H →* Aˣ) :
    W.pushCh ((AlgHom.id O A : A →ₐ[O] A) : A →+* A) χ = χ := by
  ext s
  rfl

theorem UpperTheory.V.Ws.Eb.lamIso :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ Λ' : W.LamObj r), Nonempty (Λ.Λ ≃ₐ[O] Λ'.Λ) := by
  intro l _ F O _ _ _ n r Λ Λ'
  obtain ⟨f, hf, -⟩ := Λ.univ Λ'.Λ Λ'.κ Λ'.inert
  obtain ⟨g, hg, -⟩ := Λ'.univ Λ.Λ Λ.κ Λ.inert
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_⟩
  · exact (Λ'.univ Λ'.Λ Λ'.κ Λ'.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hg, hf]) (fun v i => pushCh_id_alg _)
  · exact (Λ.univ Λ.Λ Λ.κ Λ.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hf, hg]) (fun v i => pushCh_id_alg _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.ConjOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dmk {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (DualNumber K) := Matrix.of fun i j => (⟨A i j, B i j⟩ : DualNumber K)

private theorem dmk_mul {K : Type} [CommRing K] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) K) :
    dmk A B * dmk C D = dmk (A * C) (A * D + B * C) := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.mul_apply, TrivSqZeroExt.fst_sum, Matrix.mul_apply]
    simp only [TrivSqZeroExt.fst_mul, hf]
  · rw [hs, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [TrivSqZeroExt.snd_mul, hf, hs, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

private theorem dmk_one {K : Type} [CommRing K] {n : ℕ} :
    dmk (1 : Matrix (Fin n) (Fin n) K) 0 = 1 := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [hs, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.conjOf :
    ∀ {K H : Type} [CommRing K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) (X : Matrix (Fin n) (Fin n) K), IsTan ρ y ρ' → (∀ g, y g = Loc.adGL ρ g X - X) →
        ∃ Q : GL (Fin n) (DualNumber K), ∀ g, ρ' g = Q * W.pushRep (algebraMap K (DualNumber K)) ρ g * Q⁻¹ := by
  intro K H _ _ n ρ y ρ' X hT hy
  unfold IsTan at hT
  have hinv : dmk (1 : Matrix (Fin n) (Fin n) K) (-X) * dmk 1 X = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  have hinv' : dmk (1 : Matrix (Fin n) (Fin n) K) X * dmk 1 (-X) = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  refine ⟨⟨dmk 1 (-X), dmk 1 X, hinv, hinv'⟩, fun g => ?_⟩
  have hp : ((W.pushRep (algebraMap K (DualNumber K)) ρ g : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)) = dmk (ρ g : Matrix (Fin n) (Fin n) K) 0 := by
    ext i j
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
  have hyg : y g * (ρ g : Matrix (Fin n) (Fin n) K) = 1 * (ρ g : Matrix (Fin n) (Fin n) K) * X + (1 * 0 + -X * (ρ g : Matrix (Fin n) (Fin n) K)) * 1 := by
    rw [hy g]
    simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sub_mul, mul_assoc, ← Matrix.coe_units_inv, Units.inv_mul, mul_one, one_mul, mul_zero, zero_add, neg_mul, sub_eq_add_neg]
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, neg_mul]
  ext i j : 2
  rw [Units.val_mul, Units.val_mul, hp, Units.inv_mk]
  rw [dmk_mul, dmk_mul, hT g i j, ← hyg]
  simp only [one_mul, mul_one]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LocLOpen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.locL_cyc (l : ℕ) [Fact l.Prime] :
    Continuous (Loc.cycA l l (PadicAlgCl l)) := by
  have hc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (PadicAlgCl l)
  have ha : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map (algebraMap ℤ_[l] (PadicAlgCl l) : ℤ_[l] →* PadicAlgCl l) ha).comp hc

private theorem UpperTheory.V.Ws.Eb.locL_open {H K ι : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H] [Field K] [TopologicalSpace K] [T1Space K] [Finite ι]
    (f : ι → H → K) (hf : ∀ i, Continuous (f i)) (h1 : ∀ i, f i 1 = 1) {k : ℕ} (hk : 0 < k) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ i, ∀ g ∈ U, f i g ^ k = 1 → f i g = 1 := by
  have hfin : ({z : K | z ^ k = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (nthRoots k (1 : K))) fun z hz => ?_
    exact (mem_nthRoots hk).2 hz.1
  have ho : IsOpen (⋂ i, f i ⁻¹' ({z : K | z ^ k = 1} \ {1})ᶜ) :=
    isOpen_iInter_of_finite fun i => hfin.isClosed.isOpen_compl.preimage (hf i)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (Set.mem_iInter.2 fun i h => h.2 (h1 i))
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun i g hg e => ?_⟩
  by_contra hne
  exact Set.mem_iInter.1 (hU hg) i ⟨e, hne⟩

theorem UpperTheory.V.Ws.Eb.locL :
    Loc.LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ →
        ∀ {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ), ∀ ρ' : H →* GL (Fin n) (DualNumber (PadicAlgCl l)), IsTan ρ y ρ' → ∀ (κ : Fin n → H →* (DualNumber (PadicAlgCl l))ˣ) (m : Fin n → ℤ) (k : ℕ), W.HasFlag ρ' κ → (∀ i j, i < j → m j + 2 ≤ m i) → 0 < k →
        (∀ i g, φ g ∈ Loc.Iq l → (κ i g : DualNumber (PadicAlgCl l)).snd = 0 ∧ (W.pushCh (dF _) (κ i) g * Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i)) ^ k = 1) → y ∈ Loc.finiteCocycles φ (Loc.adGL ρ) := by
  intro P l _ H _ _ _ _ _ φ hφ n ρ hρ y hy ρ' ht κ m k hF hm hk hκ
  have hpush : ∀ g, GeneralLinearGroup.map (dF (PadicAlgCl l)) (ρ' g) = ρ g := fun g =>
    Units.ext (Matrix.ext fun a b => congrArg TrivSqZeroExt.fst (ht g a b))
  have hκc : ∀ i, Continuous fun g => (κ i g : DualNumber (PadicAlgCl l)).fst := by
    obtain ⟨h, hh⟩ := hF
    intro i
    have e : (fun g => (κ i g : DualNumber (PadicAlgCl l)).fst) = fun g =>
        ((GeneralLinearGroup.map (dF (PadicAlgCl l)) h * ρ g * (GeneralLinearGroup.map (dF (PadicAlgCl l)) h)⁻¹ :
          GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i i := by
      funext g
      rw [← hpush, ← map_inv, ← map_mul, ← map_mul, ← (hh g).2 i]
      rfl
    rw [e]
    exact (Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i i
  obtain ⟨U, hUo, hU⟩ := locL_open
    (fun i g => ((W.pushCh (dF _) (κ i) g * Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i) : (PadicAlgCl l)ˣ) : PadicAlgCl l))
    (fun i => (hκc i).mul (Units.continuous_val.comp (((locL_cyc l).comp hφ.continuous).zpow (-m i))))
    (fun i => by simp only [map_one, _root_.one_zpow, mul_one, Units.val_one]) hk
  refine Loc.pr6Bar P φ hφ ρ hρ y hy ρ' ht κ m hF (fun i j hij => by have := hm i j hij; omega) U hUo
    (fun i g hg hI => ?_) (fun i j hij => Or.inl (hm i j hij))
  obtain ⟨h0, h1⟩ := hκ i g hI
  have h2 := hU i g hg (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  rw [Units.val_eq_one, _root_.zpow_neg, mul_inv_eq_one] at h2
  rw [← h2]
  exact TrivSqZeroExt.ext rfl h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.FlagDual
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.residue_dual {K : Type} [Field K] (x : DualNumber K) :
    residue (DualNumber K) x = ((residue (DualNumber K)).comp (algebraMap K (DualNumber K))) (dF K x) := by
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have e : x - algebraMap K (DualNumber K) (dF K x) = TrivSqZeroExt.inr x.snd := by
    ext <;> simp [dF, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simp

private theorem UpperTheory.V.Ws.Eb.charpoly_lift {A K H : Type} [CommRing A] [CommRing K] [Group H] {n : ℕ} (f : A →+* K)
    (r : H →* GL (Fin n) A) (κ : Fin n → H →* Aˣ) (h : W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i))
    (z : MonoidAlgebra A H) :
    (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) z).charpoly.map f =
      ∏ i, (X - C (f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) z))) := by
  unfold W.HasFlag W.pushRep W.pushCh at h
  obtain ⟨g, hg⟩ := h
  have key : ∀ y : MonoidAlgebra A H,
      (∀ i j : Fin n, j < i → ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
      ∀ i, ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, add_mul, Matrix.add_apply]
      exact ⟨fun i j hij => by rw [hx.1 i j hij, hy.1 i j hij, add_zero], fun i => by rw [hx.2, hy.2]⟩
    | single s a =>
      have e : (g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) (MonoidAlgebra.single s a)) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = f a • ((g * ((GeneralLinearGroup.map f).comp r) s * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [MonoidAlgebra.lift_single]
        have e' : f.mapMatrix (a • ((r s : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) = f a • ((GeneralLinearGroup.map f (r s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          ext i j
          simp [GeneralLinearGroup.map]
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, e', Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
      · rw [Matrix.smul_apply, (hg s).2 i]
        simp [MonoidAlgebra.lift_single]
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv]
  simp only [← RingHom.mapMatrix_apply]
  rw [Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (key z).1 i j hij)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(key z).2 i]

theorem UpperTheory.V.Ws.Eb.flagDual :
    ∀ {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ' : H →* GL (Fin n) (DualNumber K)) (κ : Fin n → H →* (DualNumber K)ˣ), (Function.Injective fun i => W.pushCh (dF K) (κ i)) →
        W.HasFlag (W.pushRep (dF K) ρ') (fun i => W.pushCh (dF K) (κ i)) → (∀ g : Fin n → H, (List.ofFn fun i => W.mat ρ' (g i) - algebraMap (DualNumber K) _ (κ i (g i) : DualNumber K)).prod = 0) → W.HasFlag ρ' κ := by
  intro K H _ _ _ n ρ' κ hinj hflag hprod
  set φ : K →+* ResidueField (DualNumber K) := (residue (DualNumber K)).comp (algebraMap K (DualNumber K)) with hφ
  have hres : residue (DualNumber K) = φ.comp (dF K) := RingHom.ext fun x => UpperTheory.V.Ws.Eb.residue_dual x
  have hcard : (n : Cardinal) ≤ Cardinal.mk (ResidueField (DualNumber K)) := by
    haveI : Infinite (ResidueField (DualNumber K)) := Infinite.of_injective φ φ.injective
    exact (Cardinal.natCast_lt_aleph0 (n := n)).le.trans (Cardinal.infinite_iff.mp inferInstance)
  have hinj' : Function.Injective fun i => ((residue (DualNumber K) : DualNumber K →* ResidueField (DualNumber K))).comp ((Units.coeHom (DualNumber K)).comp (κ i)) := by
    intro i j hij
    apply hinj
    ext s
    have hs := DFunLike.congr_fun hij s
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.coe_ofClass] at hs
    rw [hres, RingHom.comp_apply, RingHom.comp_apply] at hs
    have := φ.injective hs
    simpa [W.pushCh] using this
  have hchar : ∀ z : MonoidAlgebra (DualNumber K) H,
      Polynomial.map (residue (DualNumber K))
          ((MonoidAlgebra.lift (DualNumber K) (Matrix (Fin n) (Fin n) (DualNumber K)) H ((Units.coeHom _).comp ρ')) z).charpoly =
        ∏ i, (X - C ((residue (DualNumber K)) ((MonoidAlgebra.lift (DualNumber K) (DualNumber K) H ((Units.coeHom _).comp (κ i))) z))) := by
    intro z
    rw [hres, ← Polynomial.map_map, UpperTheory.V.Ws.Eb.charpoly_lift (dF K) ρ' κ hflag z, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply]
    rfl
  obtain ⟨z, g, -, -, hg⟩ := AlgebraTools.lemma_L ρ' κ hcard hprod hinj' hchar
  unfold W.HasFlag
  exact ⟨g, hg⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelForm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws.Eb

section
variable {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

private theorem rf_star_single (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (a : R) :
    F.star O R n (MonoidAlgebra.single g a) =
      MonoidAlgebra.single (F.conj g)⁻¹ (a * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp only [W.GFrame.star, W.GFrame.starOp]
  rw [MonoidAlgebra.lift_single]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, MonoidAlgebra.smul_single',
    smul_eq_mul]

private noncomputable def rf_dual (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) :
    F.G₀ →* Matrix (Fin n) (Fin n) K where
  toFun g := ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, map_mul, transpose_mul, mul_zpow, Units.val_mul, smul_mul_smul_comm]

private theorem rf_dual_apply (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) (g : F.G₀) :
    rf_dual F O K n r g = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ := rfl

end

private theorem rf_rep_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (g : G) (b : R) : W.GDet.repAlg ρ R (MonoidAlgebra.single g b) = b • ρ g := by
  simp only [W.GDet.repAlg]
  rw [MonoidAlgebra.lift_single]
  simp

end UpperTheory.V.Ws.Eb

theorem UpperTheory.V.Ws.Eb.relForm :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) {A : Type} [CommRing A] [IsLocalRing A] [Algebra c.O A] (f : B.B →ₐ[c.O] A) (ρ : F.G₀ →* GL (Fin n) A), Full ρ → B.u.D.map (f : B.B →+* A) = W.GDet.ofRep (W.mat ρ) →
        ∃ P : GL (Fin n) A, F.IsForm c.O n ρ P := by
  intro l _ F c n r B A _ _ _ f ρ hF hD
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  have hF' : Submodule.span A (Set.range (W.mat ρ)) = ⊤ := hF
  have key : ∀ g : F.G₀, (W.GDet.ofRep (W.mat ρ)).lam 1 (F.star c.O A n (MonoidAlgebra.single g 1)) =
      (W.GDet.ofRep (W.mat ρ)).lam 1 (MonoidAlgebra.single g 1) := by
    intro g
    have h1 := congrArg (f : B.B →+* A) (B.u.P 1 g)
    have hm := (AlgebraTools.Det.mapApi B.u.D (f : B.B →+* A)).2.1 1
    rw [← hm, ← hm] at h1
    have hs := (AlgebraTools.Det.starApi F c.O B.B n).2.2.2.2.2 A f (MonoidAlgebra.single g 1)
    rw [← hs, hD] at h1
    simpa using h1
  have trs : ∀ y, (W.GDet.ofRep (W.mat ρ)).lam 1 y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
    intro y
    have h := (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn y
    simpa only [W.GDet.tr] using h
  have hsingle : ∀ g, (W.mat ρ g).trace = (rf_dual F c.O A n ρ g).trace := by
    intro g
    have h := key g
    rw [trs, trs, rf_star_single, rf_rep_single, rf_rep_single] at h
    rw [rf_dual_apply, trace_smul, trace_transpose]
    simpa [trace_smul] using h.symm
  have htr : ∀ x, (W.GDet.repAlg (W.mat ρ) A x).trace = (W.GDet.repAlg (rf_dual F c.O A n ρ) A x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      simp only [MonoidAlgebra.of_apply, rf_rep_single, one_smul]
      exact hsingle g
    | add x y hx hy => simp only [map_add (f := _), trace_add, hx, hy]
    | smul a x hx => simp only [map_smul, trace_smul, hx]
  have hsurj : Function.Surjective (W.GDet.repAlg (W.mat ρ) A) := by
    intro M
    have hM : M ∈ Submodule.span A (Set.range (W.mat ρ)) := by
      rw [hF']
      trivial
    have hle : Submodule.span A (Set.range (W.mat ρ)) ≤ LinearMap.range (W.GDet.repAlg (W.mat ρ) A).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [rf_rep_single]⟩
    obtain ⟨x, hx⟩ := hle hM
    exact ⟨x, by simpa using hx⟩
  obtain ⟨U, hU⟩ := GlobalTheory.TraceConjugacy.exists_conj_of_surjective (W.GDet.repAlg (W.mat ρ) A)
    (W.GDet.repAlg (rf_dual F c.O A n ρ) A) hsurj htr
  refine ⟨⟨(↑U : Matrix (Fin n) (Fin n) A)ᵀ, (↑U⁻¹ : Matrix (Fin n) (Fin n) A)ᵀ, ?_, ?_⟩, fun g => ?_⟩
  · rw [← transpose_mul, Units.inv_mul, transpose_one]
  · rw [← transpose_mul, Units.mul_inv, transpose_one]
  · show (W.mat ρ g)ᵀ * (↑U : Matrix (Fin n) (Fin n) A)ᵀ * W.mat ρ (F.conj g) = _
    have h := congrArg transpose (hU (MonoidAlgebra.single g 1))
    rw [rf_rep_single, rf_rep_single, one_smul, one_smul, rf_dual_apply, transpose_mul, transpose_mul,
      transpose_smul, transpose_transpose] at h
    rw [← h, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]
end

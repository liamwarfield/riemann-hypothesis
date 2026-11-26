module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.phiSub :
    ∀ (l : ℕ) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G),
      IsOpen (H : Set G) → PhiCond (Γ := G) l → PhiCond (Γ := H) l := by
  intro l G _ _ _ H hH hG
  unfold PhiCond at *
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hG (K.map H.subtype) hK'
  let e := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
  have he : ∀ y : K.map H.subtype, (((e.symm y : K) : H) : G) = (y : G) := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  have hc : Continuous fun y : K.map H.subtype => (e.symm y : K) := by
    apply continuous_induced_rng.2
    apply continuous_induced_rng.2
    exact continuous_subtype_val.congr fun y => (he y).symm
  refine Finite.of_injective
    (β := {ψ : K.map H.subtype →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, by
      show IsOpen ((fun y => (e.symm y : K)) ⁻¹' (φ.1.ker : Set K))
      exact φ.2.preimage hc⟩) ?_
  intro φ ψ h
  apply Subtype.ext
  ext k
  have h' := congrArg (fun χ : {ψ : K.map H.subtype →* Multiplicative (ZMod l) //
    IsOpen (ψ.ker : Set (K.map H.subtype))} => χ.1 (e k)) h
  simpa using h'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM
noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.Det

section Ep

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

private theorem epM_mul_epM (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z' = 0 := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta]

private theorem epM_add (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (fun j => Z j + Z' j) = DD.epM Z + DD.epM Z' := by
  ext a b <;> simp [DD.epM]

private theorem epM_zero : DD.epM (fun _ : Fin g => (0 : Matrix (Fin n) (Fin n) X)) = 0 := by
  ext a b <;> simp [DD.epM]

private theorem mul_epM (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    M.map (algebraMap A (DD X g)) * DD.epM Z = DD.epM fun j => M.map (algebraMap A X) * Z j := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private theorem epM_mul (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * M.map (algebraMap A (DD X g)) = DD.epM fun j => Z j * M.map (algebraMap A X) := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private theorem add_mul_sub_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 + DD.epM Z) * (1 - DD.epM Z) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, epM_mul_epM]; abel

private theorem sub_mul_add_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 - DD.epM Z) * (1 + DD.epM Z) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, epM_mul_epM]; abel

end Ep

section Rho

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X] [Algebra x.A X]

private theorem ρX_one : x.ρX X 1 = 1 := by
  simp [NP.ρX, mat]

private theorem ρX_mul (g h : F.G₀) : x.ρX X (g * h) = x.ρX X g * x.ρX X h := by
  simp [NP.ρX, mat, Matrix.map_mul]

private theorem w_wi (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

private theorem wi_w (v : F.Vl) : x.wiX X v * x.wX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

variable {x} (k : Kap x)

private theorem coc (j) (g h : F.G₀) : k.κ j (g * h) = k.κ j g + mat x.ρ g * k.κ j h * mat x.ρ g⁻¹ := by
  have := (k.mem j).2.2.1 g h
  simpa [NP.ρX] using this

private theorem κ_one (j) : k.κ j 1 = 0 := by
  have := coc k j 1 1
  simpa [mat] using this

private theorem ρ1_one : k.ρ1 X 1 = 1 := by
  simp [Kap.ρ1, κ_one, ρX_one, epM_zero]

private theorem ρ1_mul (g h : F.G₀) : k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h := by
  have e : (DD.epM fun j => (k.κ j (g * h)).map (algebraMap x.A X)) =
      (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) +
        x.ρX (DD X k.g) g * (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) * x.ρX (DD X k.g) g⁻¹ := by
    rw [NP.ρX, NP.ρX, mul_epM, epM_mul, ← epM_add]
    congr 1
    funext j
    rw [coc, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]
  have i : x.ρX (DD X k.g) g⁻¹ * x.ρX (DD X k.g) g = 1 := by rw [← ρX_mul, inv_mul_cancel, ρX_one]
  have z : (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * x.ρX (DD X k.g) g *
      (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = 0 := by
    rw [NP.ρX, epM_mul, epM_mul_epM]
  simp only [Kap.ρ1]
  rw [e, ρX_mul]
  generalize (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) = P at *
  generalize (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = Q at *
  generalize x.ρX (DD X k.g) g⁻¹ = s at *
  generalize x.ρX (DD X k.g) g = r at *
  generalize x.ρX (DD X k.g) h = r' at *
  calc (1 + (P + r * Q * s)) * (r * r') = r * r' + P * r * r' + r * Q * (s * r) * r' := by noncomm_ring
    _ = r * r' + P * r * r' + r * Q * r' + P * r * Q * r' := by rw [i, z]; noncomm_ring
    _ = _ := by noncomm_ring

end Rho

end UpperTheory.V.Pa.Det

open IsLocalRing UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.rho1Hom :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ (∀ g, k.ρ1 X g⁻¹ = x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X))) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ k.wi1 X v * k.w1 X v = 1 := by
  intro l _ F n x k X _ _
  refine ⟨ρ1_one X k, ρ1_mul X k, fun g => ?_, fun v => ⟨?_, ?_⟩⟩
  · have h1 : k.ρ1 X g * k.ρ1 X g⁻¹ = 1 := by rw [← ρ1_mul, mul_inv_cancel, ρ1_one]
    have h2 : x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * k.ρ1 X g = 1 := by
      rw [Kap.ρ1, mul_assoc, ← mul_assoc (1 - _), sub_mul_add_epM, one_mul, ← ρX_mul, inv_mul_cancel, ρX_one]
    exact (left_inv_eq_right_inv h2 h1).symm
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (x.wX _ v), w_wi, one_mul, sub_mul_add_epM]
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (1 + _), add_mul_sub_epM, one_mul, wi_w]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtFree
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.extFree :
    ∀ {K K' : Type} [Field K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), Function.Injective j → IsLocalHom j → j.Finite → ∃ (m : ℕ) (b : Fin m → PowerSeries K') (p : Fin m → PowerSeries K' →+ PowerSeries K), 0 < m ∧ (∀ y, y = ∑ i, j (p i y) * b i) ∧ (∀ i a y, p i (j a * y) = a * p i y) ∧ (∀ i i', p i (b i') = if i = i' then (1 : PowerSeries K) else 0) ∧ (∀ N : ℕ, ∃ N' : ℕ, ∀ y ∈ Ideal.span {(PowerSeries.X : PowerSeries K')} ^ N', ∀ i, p i y ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N) ∧ ∃ (e : ℕ) (u : (PowerSeries K')ˣ), 0 < e ∧ j PowerSeries.X = (u : PowerSeries K') * (PowerSeries.X : PowerSeries K') ^ e := by
  intro K K' _ _ j hi hl hf
  letI : Algebra (PowerSeries K) (PowerSeries K') := j.toAlgebra
  haveI : Module.Finite (PowerSeries K) (PowerSeries K') := hf
  haveI : FaithfulSMul (PowerSeries K) (PowerSeries K') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  haveI : Module.Free (PowerSeries K) (PowerSeries K') := Module.free_of_finite_type_torsion_free'
  let B := Module.finBasis (PowerSeries K) (PowerSeries K')
  have hsm : ∀ (a : PowerSeries K) (y : PowerSeries K'), j a * y = a • y := fun a y => rfl
  have hX : ∃ (e : ℕ) (u : (PowerSeries K')ˣ), 0 < e ∧
      j PowerSeries.X = (u : PowerSeries K') * (PowerSeries.X : PowerSeries K') ^ e := by
    have h0 : j PowerSeries.X ≠ 0 := by
      intro h
      exact PowerSeries.X_ne_zero (hi (h.trans (map_zero j).symm))
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := K'))
    refine ⟨e, v⁻¹, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos e with h | h
      · exfalso
        rw [h, pow_zero] at hv
        have hu : IsUnit (j PowerSeries.X) := IsUnit.of_mul_eq_one _ hv
        exact (PowerSeries.X_irreducible (R := K)).not_isUnit (isUnit_of_map_unit j _ hu)
      · exact h
    · rw [← hv, mul_left_comm, Units.inv_mul, mul_one]
  obtain ⟨e, u, he, hu⟩ := hX
  refine ⟨Module.finrank (PowerSeries K) (PowerSeries K'), fun i => B i, fun i => (B.coord i).toAddMonoidHom,
    Module.finrank_pos, ?_, ?_, ?_, ?_, e, u, he, hu⟩
  · intro y
    conv_lhs => rw [← B.sum_repr y]
    rfl
  · intro i a y
    show B.coord i (j a * y) = a * B.coord i y
    rw [hsm, LinearMap.map_smul, smul_eq_mul]
  · intro i i'
    show B.repr (B i') i = _
    rw [B.repr_self_apply]
    by_cases h : i = i'
    · subst h
      simp
    · simp [h, Ne.symm h]
  · intro N
    refine ⟨e * N, fun y hy i => ?_⟩
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy ⊢
    obtain ⟨z, rfl⟩ := hy
    have hu1 : (u : PowerSeries K') ^ N * ((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    have hz : (PowerSeries.X : PowerSeries K') ^ (e * N) * z =
        j (PowerSeries.X ^ N) * (((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N * z) := by
      rw [map_pow, hu, pow_mul]
      linear_combination (-(((PowerSeries.X : PowerSeries K') ^ e) ^ N * z)) * hu1
    refine ⟨B.coord i (((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N * z), ?_⟩
    show B.coord i _ = _
    rw [hz, hsm, LinearMap.map_smul, smul_eq_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LatInt
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_stable_lattice {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A)
    (hd : d ≠ 0) (h : ∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) :
    ∃ L : Submodule A (Fin m → F), Submodule.IsFullLattice F L ∧
      ∀ g, ∀ x ∈ L, (r g : Matrix (Fin m) (Fin m) F) *ᵥ x ∈ L := by
  classical
  let S : Set (Fin m → F) :=
    Set.range fun p : G × Fin m => (r p.1 : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single p.2 1)
  have hd' : algebraMap A F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
  refine ⟨Submodule.span A S,
    { toIsLattice := Submodule.IsLattice.of_fg F ?_, span_eq_top := ?_ }, ?_⟩
  · let N : Submodule A (Fin m → F) :=
      Submodule.span A (Set.range fun i : Fin m => (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F))
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine hN.of_le ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, j⟩, rfl⟩
    choose a ha using h g
    have e : (r g : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single j 1) =
        ∑ i, a i j • (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F) := by
      funext k
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Algebra.smul_def, ← ha]
      field_simp
    simp only [SetLike.mem_coe]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff, ← (Pi.basisFun F (Fin m)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by
      simp only [map_one, Units.val_one, Matrix.one_mulVec, Pi.basisFun_apply]⟩
  · intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g', i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * g', i), by
        simp only [map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

theorem UpperTheory.V.Pa.Det.latInt :
    ∀ {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A), d ≠ 0 → (∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) → ∃ (Q : GL (Fin m) F) (r₀ : G →* GL (Fin m) A), ∀ g, r g * Q = Q * pushRep (algebraMap A F) r₀ g := by
  intro A F G _ _ _ _ _ _ _ m r d hd h
  classical
  obtain ⟨L, hL, hst⟩ := exists_stable_lattice r d hd h
  have hr : Module.finrank A L = m := by
    simpa using ((Submodule.IsFullLattice.finrank_eq F L).trans (Module.finrank_fintype_fun_eq_card F))
  have := Submodule.IsLattice.free F L
  have := Submodule.IsLattice.finite F L
  let bL : Module.Basis (Fin m) A L := Module.finBasisOfFinrankEq A L hr
  let b : Module.Basis (Fin m) F (Fin m → F) := bL.extendOfIsFullLattice F
  let Q₀ : Matrix (Fin m) (Fin m) F := (Pi.basisFun F (Fin m)).toMatrix b
  have hQ : IsUnit Q₀ := by
    letI := (Pi.basisFun F (Fin m)).invertibleToMatrix b
    exact isUnit_of_invertible _
  have hQa : ∀ i j, Q₀ i j = (bL j : Fin m → F) i := fun i j => by
    simp [Q₀, b, Module.Basis.toMatrix_apply]
  let M : G → Matrix (Fin m) (Fin m) A := fun g k j => bL.repr ⟨_, hst g _ (bL j).2⟩ k
  have hM : ∀ g, (r g : Matrix (Fin m) (Fin m) F) * Q₀ = Q₀ * (M g).map (algebraMap A F) := by
    intro g
    ext i j
    have e := congrArg (fun x : L => (x : Fin m → F) i) (bL.sum_repr ⟨_, hst g _ (bL j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Algebra.smul_def] at e
    simp only [Matrix.mul_apply, hQa, Matrix.map_apply]
    refine Eq.trans e.symm ?_
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have inj : ∀ X Y : Matrix (Fin m) (Fin m) A,
      Q₀ * X.map (algebraMap A F) = Q₀ * Y.map (algebraMap A F) → X = Y := fun X Y hXY =>
    Matrix.map_injective (IsFractionRing.injective A F) (hQ.mul_left_cancel hXY)
  let M' : G →* Matrix (Fin m) (Fin m) A :=
    { toFun := M
      map_one' := inj _ _ (by rw [← hM]; simp)
      map_mul' := fun g g' => inj _ _ (by
        rw [← hM, Matrix.map_mul, ← mul_assoc, ← hM, mul_assoc, ← hM, map_mul, Units.val_mul,
          mul_assoc]) }
  refine ⟨hQ.unit, M'.toHomUnits, fun g => Units.ext ?_⟩
  exact hM g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Central
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.central :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (Z : Matrix (Fin n) (Fin n) F), (∀ g ∈ D.G', D.r g * Z = Z * D.r g) → (Z ∈ Od F F n D.a → Z = 0) ∧ (Z ∈ Ev F F n D.a → ∀ g, D.r g * Z = Z * D.r g) := by
  intro F G _ _ n D Z hZ
  have key : ∀ X ∈ Ev F F n D.a, X * Z = Z * X := by
    intro X hX
    rw [← D.span] at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact hZ g hg
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  refine ⟨fun hO => ?_, fun _ g => key _ (D.ev g)⟩
  ext i j
  by_cases hij : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a)
  · simpa using (hO i j).1 hij
  · have hne : i ≠ j := fun h => hij (by rw [h])
    have hE : Matrix.diagonal (Pi.single i (1 : F)) ∈ Ev F F n D.a := by
      intro p q
      refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
      have hpq : p ≠ q := fun e => h (by rw [e])
      simp [Matrix.diagonal_apply_ne _ hpq]
    have h := congrFun (congrFun (key _ hE) i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    simpa [Pi.single_eq_of_ne hne.symm] using h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DSigma
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.dSigma :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G), (∀ g, χ (D.σ g) = χ g) → dTw χ D.r Y (D.σ g) = (dTw χ D.r Yᵀ g)ᵀ := by
  intro F G _ _ n D χ Y g hχ
  have e1 : D.r (D.σ g) = (D.μ g : F) • (D.r g⁻¹)ᵀ := by
    have h : (D.r g⁻¹)ᵀ * (D.r g)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.transpose_one]
    calc D.r (D.σ g) = (D.r g⁻¹)ᵀ * ((D.r g)ᵀ * D.r (D.σ g)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e2 : D.r (D.σ g)⁻¹ = (D.μ g⁻¹ : F) • (D.r g)ᵀ := by
    have h : (D.r g)ᵀ * (D.r g⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]
    rw [← map_inv]
    calc D.r (D.σ g⁻¹) = (D.r g)ᵀ * ((D.r g⁻¹)ᵀ * D.r (D.σ g⁻¹)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e3 : ((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F) = 1 := by
    have h : D.r (D.σ g) * D.r (D.σ g)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.transpose_mul, ← map_mul, mul_inv_cancel,
      map_one, Matrix.transpose_one, smul_smul] at h
    exact h
  have key : D.r (D.σ g) * Y * D.r (D.σ g)⁻¹ = (D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ := by
    rw [e1, e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show ((D.μ g : F) * D.μ g⁻¹) • ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ)
        = (((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F)) * ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ) by
      rw [Matrix.smul_mul, Matrix.one_mul], e3, Matrix.one_mul]
  simp only [dTw, hχ, key, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ZlUniq
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem zlUniq_val (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hl : (l : R) = 0) (a : ℤ_[l]) : f a = ((PadicInt.toZMod a).val : R) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (PadicInt.maximalIdeal_eq_span_p (p := l) ▸ PadicInt.sub_zmodRepr_mem a)
  rw [PadicInt.val_toZMod_eq_zmodRepr]
  have h := congrArg f hc
  rw [map_mul, map_natCast, hl, mul_zero, map_sub, map_natCast, eq_comm, sub_eq_zero] at h
  exact h

theorem UpperTheory.V.Pa.Det.zlUniq :
    ∀ (l : ℕ) [Fact l.Prime], (∀ {K : Type} [Field K] [Finite K] (_ : ℤ_[l] →+* K), CharP K l) ∧ ∀ {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R), (l : R) = 0 → f = f' ∧ ∀ a, f a = ((PadicInt.toZMod a).val : R) := by
  intro l _
  refine ⟨fun {K} _ _ f => ?_, fun {R} _ f f' hl => ⟨?_, zlUniq_val l f hl⟩⟩
  · obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : p.Prime := CharP.char_is_prime K p
    have hpl : p = l := by
      by_contra hne
      have hunit : IsUnit (p : ℤ_[l]) := by
        by_contra hnu
        have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
          rw [Int.cast_natCast]
          exact PadicInt.mem_nonunits.mp hnu
        rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
        exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
      have h := hunit.map f
      rw [map_natCast, CharP.cast_eq_zero] at h
      exact not_isUnit_zero h
    subst hpl
    exact hchar
  · ext a
    rw [zlUniq_val l f hl, zlUniq_val l f' hl]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LocallyConstantCocyclesFiniteOfPhi
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] [Module (ZMod l) M] (v : M)
    (hv : ∀ f : M →+ ZMod l, f v = 0) : v = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
  intro f
  exact hv (LinearMap.toAddMonoidHom f)

theorem UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi :
    ∀ (l : ℕ) [Fact l.Prime] {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [AddCommGroup M] [Finite M] (ρ : G →* AddMonoid.End M), PhiCond G l → (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) → {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)}.Finite := by
  intro l _ G M _ _ _ _ _ _ _ ρ hΦ hl hc
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set S := {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)} with hS
  have hker : IsOpen (ρ.ker : Set G) := by
    have he : (ρ.ker : Set G) = ⋂ m, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        ext m
        exact h m
    rw [he]
    exact isOpen_iInter_of_finite fun m => (hc m).isOpen_fiber m
  haveI : Finite (G ⧸ ρ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  haveI := hΦ ρ.ker hker
  haveI : Finite (M →+ ZMod l) :=
    Finite.of_injective (fun f : M →+ ZMod l => (⇑f : M → ZMod l))
      (fun a b hab => AddMonoidHom.ext (congrFun hab))
  have h1 : ∀ z ∈ S, z 1 = 0 := by
    intro z hz
    have h11 : z 1 = z 1 + z 1 := by
      have := hz.2 1 1
      rw [one_mul, map_one] at this
      exact this
    exact add_left_cancel (h11.symm.trans (add_zero _).symm)
  have hH : ∀ z ∈ S, ∀ a b : G, a ∈ ρ.ker → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [hz.2, MonoidHom.mem_ker.mp ha]
    rfl
  let φ : ∀ z ∈ S, (M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)} := fun z hz f =>
    ⟨{ toFun := fun h => Multiplicative.ofAdd (f (z h))
       map_one' := by simp [h1 z hz]
       map_mul' := fun a b => by simp [hH z hz a b a.2, ofAdd_add] },
     by
       have hlc : IsLocallyConstant (fun h : ρ.ker => Multiplicative.ofAdd (f (z h))) :=
         (hz.1.comp_continuous continuous_subtype_val).comp _
       exact hlc.isOpen_fiber 1⟩
  let F : S → ((G ⧸ ρ.ker) → M) × ((M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)}) :=
    fun z => (fun q => z.1 (Quotient.out q), φ z.1 z.2)
  have hinj : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have hq : (fun q : G ⧸ ρ.ker => z (Quotient.out q)) = fun q => z' (Quotient.out q) := congrArg Prod.fst hzz
    have hf : φ z hz = φ z' hz' := congrArg Prod.snd hzz
    have hHeq : ∀ h ∈ ρ.ker, z h = z' h := by
      intro h hh
      rw [← sub_eq_zero]
      apply @eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod l _ M _ (AddCommGroup.zmodModule hl)
      intro f
      have hx := congrArg (fun p => (p.1 ⟨h, hh⟩ : Multiplicative (ZMod l))) (congrFun hf f)
      change Multiplicative.ofAdd (f (z h)) = Multiplicative.ofAdd (f (z' h)) at hx
      rw [map_sub, sub_eq_zero]
      exact Multiplicative.ofAdd.injective hx
    apply Subtype.ext
    funext g
    show z g = z' g
    obtain ⟨h0, hh0⟩ := QuotientGroup.mk_out_eq_mul ρ.ker g
    have hg : g = Quotient.out (g : G ⧸ ρ.ker) * (h0 : G)⁻¹ := by
      rw [hh0, mul_inv_cancel_right]
    have hr := congrFun hq (g : G ⧸ ρ.ker)
    rw [hg, hz.2, hz'.2, hr, hHeq _ (inv_mem h0.2)]
  exact Set.finite_coe_iff.mp (Finite.of_injective F hinj)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanDesc
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem sd_map_ev {F F' : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) F} (hZ : Z ∈ Ev F F n a) : Z.map f ∈ Ev F' F' n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  have h0 : Z i j = 0 := (hZ i j).2 e
  rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]

private theorem sd_up {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F)
    (hY : Y ∈ Submodule.span F (Set.range r)) :
    Y.map f ∈ Submodule.span F' (Set.range fun i => (r i).map f) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin n) (Fin n) F).map f = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (y + z).map f = y.map f + z.map f := by ext i j; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map f = f c • y.map f := by ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hy

private theorem sd_down {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (p : F' →+ F) (hp : ∀ (c : F') (x : F), p (c * f x) = p c * x)
    (Y : Matrix (Fin n) (Fin n) F')
    (hY : Y ∈ Submodule.span F' (Set.range fun i => (r i).map f)) :
    ∀ c : F', (c • Y).map p ∈ Submodule.span F (Set.range r) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro c
    have : (c • (r i).map f).map p = p c • r i := by
      ext s t; simp [hp]
    show (c • (r i).map f).map p ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero =>
    intro c
    have : (c • (0 : Matrix (Fin n) (Fin n) F')).map p = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    intro c
    have : (c • (y + z)).map p = (c • y).map p + (c • z).map p := by ext i j; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ (hy c) (hz c)
  | smul d y _ hy =>
    intro c
    rw [smul_smul]; exact hy _

theorem UpperTheory.V.Pa.Det.spanDesc :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) F), (∀ i, r i ∈ Ev F F n a) → (Submodule.span F (Set.range r) = Ev F F n a ↔ Submodule.span F' (Set.range fun i => (r i).map f) = Ev F' F' n a) := by
  intro F F' ι _ _ f n a r hr
  constructor
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact sd_map_ev f (hr i)
    · intro Z hZ
      have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
      rw [hZ']
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
      · have h1 : (single i j 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a :=
          fun p q => ⟨fun _ => trivial, fun e' => by
            rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
            rintro ⟨rfl, rfl⟩
            exact e' e⟩
        rw [← h] at h1
        have h2 := Submodule.smul_mem _ (Z i j) (sd_up f r _ h1)
        convert h2 using 1
        ext p q
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs <;> simp
      · have : Z i j = 0 := (hZ i j).2 e
        simp [this]
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hr i
    · intro Z hZ
      letI : Algebra F F' := f.toAlgebra
      obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F F')
        (LinearMap.ker_eq_bot.2 f.injective)
      have hp1 : ∀ x : F, p (f x) = x := fun x => LinearMap.congr_fun hp x
      have hp2 : ∀ (c : F') (x : F), p.toAddMonoidHom (c * f x) = p.toAddMonoidHom c * x := by
        intro c x
        have h3 : c * f x = x • c := by rw [mul_comm]; rfl
        show p (c * f x) = p c * x
        rw [h3, map_smul, smul_eq_mul, mul_comm]
      have h1 := sd_map_ev f hZ
      rw [← h] at h1
      have h2 := sd_down f r p.toAddMonoidHom hp2 _ h1 1
      convert h2 using 1
      ext s t
      simp [hp1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]

private theorem dY_add (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (Y + Y') g = dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul]
  abel

private theorem dY_zero (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (g : F.G₀) : dY F ρ 0 g = 0 := by
  simp [dY]

private theorem dY_smul (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (c : A) (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y) g = c • dY F ρ Y g := by
  simp only [dY, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private theorem ac_add {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f f' : Γ → R} (h : AdicCont I f)
    (h' : AdicCont I f') : AdicCont I fun g => f g + f' g := by
  intro N
  have key := (h N).add (h' N)
  convert key using 1
  funext g
  simp [map_add (f := _)]

private theorem ac_smul {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f : Γ → R} (c : A) (h : AdicCont I f) :
    AdicCont I fun g => c • f g := by
  intro N
  have key := (h N).comp (fun x => Ideal.Quotient.mk (I ^ N) (algebraMap A R c) * x)
  convert key using 1
  funext g
  simp [Function.comp, Algebra.smul_def, map_mul]

end

theorem UpperTheory.V.Pa.Det.selSub :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  intro l _ F n A R _ _ _ t ρ w wi V
  refine ⟨⟨⟨⟨⟨SelZ F t ρ w wi V, ?_⟩, ?_⟩, ?_⟩, rfl⟩, ⟨⟨⟨⟨Bd F ρ V, ?_⟩, ?_⟩, ?_⟩, rfl⟩⟩
  · intro z z' hz hz'
    simp only [SelZ, Set.mem_setOf_eq] at hz hz' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
    obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hz'
    refine ⟨fun g => V.add_mem (h1 g) (h1' g), fun i j => ?_, fun g k => ?_, fun g => ?_,
      fun u g hg => ?_, fun v => ?_⟩
    · have e := ac_add (h2 i j) (h2' i j)
      simpa only [Pi.add_apply, Matrix.add_apply] using e
    · rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, h3, h3', Matrix.mul_add, Matrix.add_mul]
      abel
    · rw [Pi.add_apply, Pi.add_apply, h4, h4', Matrix.transpose_add, neg_add]
    · rw [Pi.add_apply, h5 u g hg, h5' u g hg, add_zero]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      obtain ⟨Y', hY', hl'⟩ := h6' v
      refine ⟨Y + Y', V.add_mem hY hY', ?_⟩
      intro g
      obtain ⟨a, b⟩ := hl g
      obtain ⟨a', b'⟩ := hl' g
      have e : ∀ x, (z + z') x - dY F ρ (Y + Y') x = (z x - dY F ρ Y x) + (z' x - dY F ρ Y' x) := by
        intro x
        rw [Pi.add_apply, dY_add]
        abel
      refine ⟨fun i j hij => ?_, fun hm i => ?_⟩
      · rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, a i j hij, a' i j hij, add_zero]
      · rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, b hm i, b' hm i, add_zero]
  · simp only [SelZ, Set.mem_setOf_eq]
    refine ⟨fun g => V.zero_mem, fun i j => ?_, fun g k => ?_, fun g => ?_, fun u g hg => rfl, fun v => ?_⟩
    · intro N
      simp only [Pi.zero_apply, Matrix.zero_apply, map_zero]
      exact IsLocallyConstant.const 0
    · simp
    · simp
    · refine ⟨0, V.zero_mem, ?_⟩
      intro g
      simp [dY_zero]
  · intro c z hz
    simp only [SelZ, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
    refine ⟨fun g => V.smul_mem c (h1 g), fun i j => ?_, fun g k => ?_, fun g => ?_,
      fun u g hg => ?_, fun v => ?_⟩
    · have e := ac_smul c (h2 i j)
      simpa only [Pi.smul_apply, Matrix.smul_apply] using e
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
    · rw [Pi.smul_apply, Pi.smul_apply, h4, Matrix.transpose_smul, smul_neg]
    · rw [Pi.smul_apply, h5 u g hg, smul_zero]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      refine ⟨c • Y, V.smul_mem c hY, ?_⟩
      intro g
      obtain ⟨a, b⟩ := hl g
      have e : ∀ x, (c • z) x - dY F ρ (c • Y) x = c • (z x - dY F ρ Y x) := by
        intro x
        rw [Pi.smul_apply, dY_smul, smul_sub]
      refine ⟨fun i j hij => ?_, fun hm i => ?_⟩
      · rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, a i j hij, smul_zero]
      · rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, b hm i, smul_zero]
  · rintro z z' ⟨Y, hY, hT, rfl⟩ ⟨Y', hY', hT', rfl⟩
    refine ⟨Y + Y', V.add_mem hY hY', by rw [Matrix.transpose_add, hT, hT', neg_add], ?_⟩
    funext g
    rw [Pi.add_apply, dY_add]
  · exact ⟨0, V.zero_mem, by simp, by funext g; rw [dY_zero]; rfl⟩
  · rintro c z ⟨Y, hY, hT, rfl⟩
    refine ⟨c • Y, V.smul_mem c hY, by rw [Matrix.transpose_smul, hT, smul_neg], ?_⟩
    funext g
    rw [Pi.smul_apply, dY_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SolBase
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.solBase :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ} (e : ι → F) (r : ι → Matrix (Fin n) (Fin n) F), (∀ X : Matrix (Fin n) (Fin n) F, (∀ i, e i • (r i * X) = X * r i) → X = 0) → ∀ X : Matrix (Fin n) (Fin n) F', (∀ i, f (e i) • ((r i).map f * X) = X * (r i).map f) → X = 0 := by
  intro F F' ι _ _ f n e r h X hX
  letI : Algebra F F' := f.toAlgebra
  have hs : ∀ (x : F) (y : F'), f x * y = x • y := fun x y => (Algebra.smul_def x y).symm
  let b := Module.Basis.ofVectorSpace F F'
  have key : ∀ k, (Matrix.of fun a c => b.repr (X a c) k) = 0 := by
    intro k
    apply h
    intro i
    ext a c
    have hac := congrArg (fun M => b.repr (M a c) k) (hX i)
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Matrix.of_apply] at hac ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hs, mul_comm (X _ _) (f _), ← Finset.smul_sum, map_sum, map_smul, Finsupp.smul_apply,
      smul_eq_mul] at hac
    change e i * (Finsupp.applyAddHom k : (_ →₀ F) →+ F) (∑ x, r i a x • b.repr (X x c)) =
      (Finsupp.applyAddHom k : (_ →₀ F) →+ F) (∑ x, r i x c • b.repr (X a x)) at hac
    simp only [map_sum, Finsupp.applyAddHom_apply, Finsupp.smul_apply, smul_eq_mul] at hac
    simpa only [mul_comm] using hac
  ext a c
  have hk : b.repr (X a c) = 0 := by
    ext k
    exact congrFun (congrFun (key k) a) c
  simpa using hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FiniteOfGeneratedByOneElement
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.sqExt :
    ∀ {K : Type} [Field K], ∃ j : PowerSeries K →+* PowerSeries K, Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ j PowerSeries.X = PowerSeries.X ^ 2 := by
  intro K _
  refine ⟨(PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom, ?_, ?_, ?_, by simp⟩
  · intro f g h
    ext m
    have h1 := congrArg (PowerSeries.coeff (2 * m)) h
    simpa using h1
  · refine ⟨fun f hf => ?_⟩
    rw [PowerSeries.isUnit_iff_constantCoeff] at hf ⊢
    simpa using hf
  · classical
    letI inst : Module (PowerSeries K) (PowerSeries K) :=
      (PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom.toAlgebra.toModule
    have hs : Submodule.span (PowerSeries K) ({1, PowerSeries.X} : Set (PowerSeries K)) = ⊤ := by
      rw [eq_top_iff]
      intro f _
      rw [Submodule.mem_span_pair]
      refine ⟨PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f,
        PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f, ?_⟩
      change PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f) * 1 +
        PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f) *
          PowerSeries.X = f
      ext n
      rw [mul_one, map_add (f := _), ← pow_one (PowerSeries.X (R := K)), PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      simp only [PowerSeries.coeff_mk]
      split_ifs <;> first | omega | (simp only [add_zero, zero_add]; congr; omega)
    exact ⟨⟨{1, PowerSeries.X}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact hs⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ResSqField
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.resSq_fin {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [Module.Finite K K'] : (PowerSeries.map (algebraMap K K')).Finite := by
  classical
  letI := (PowerSeries.map (algebraMap K K')).toAlgebra
  let b := Module.finBasis K K'
  show Module.Finite (PowerSeries K) (PowerSeries K')
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_map, PowerSeries.coeff_mk]
    simp_rw [← Algebra.smul_def]
    exact (b.sum_repr _).symm
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

private theorem UpperTheory.V.Pa.Det.resSq_field (K : Type) [Field K] [Finite K] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K'),
      ∀ a : K, IsSquare (algebraMap K K' a) := by
  classical
  letI := Fintype.ofFinite K
  let p : Polynomial K := ∏ a : K, (Polynomial.X ^ 2 - Polynomial.C a)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) a
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  have hs := Polynomial.SplittingField.splits p
  have hd : (Polynomial.X ^ 2 - Polynomial.C a) ∣ p := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
  have hs' : ((Polynomial.X ^ 2 - Polynomial.C a).map (algebraMap K p.SplittingField)).Splits :=
    hs.of_dvd (Polynomial.map_ne_zero hp) (Polynomial.map_dvd _ hd)
  obtain ⟨x, hx⟩ := hs'.exists_eval_eq_zero (by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  refine ⟨x, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
  rw [← sq]; exact (sub_eq_zero.mp hx).symm

theorem UpperTheory.V.Pa.Det.resSq :
    ∀ {K : Type} [Field K] [Finite K], ∃ (K' : Type) (_ : Field K') (_ : Finite K') (j : PowerSeries K →+* PowerSeries K'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j c)) := by
  intro K _ _
  obtain ⟨K', _, _, _, hsq⟩ := UpperTheory.V.Pa.Det.resSq_field K
  haveI : Finite K' := Module.finite_of_finite K
  have hcc : ∀ φ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map (algebraMap K K') φ) =
      algebraMap K K' (PowerSeries.constantCoeff φ) := by
    intro φ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine ⟨K', inferInstance, inferInstance, PowerSeries.map (algebraMap K K'),
    PowerSeries.map_injective _ (algebraMap K K').injective, ⟨fun φ hφ => ?_⟩,
    UpperTheory.V.Pa.Det.resSq_fin, fun c => ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ (algebraMap K K').injective] at hφ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hφ
  · obtain ⟨r, hr⟩ := hsq (PowerSeries.constantCoeff (c : PowerSeries K))
    refine ⟨residue (PowerSeries K') (PowerSeries.C r), ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, hcc, hr, map_mul,
      PowerSeries.constantCoeff_C, sub_self]
    exact not_isUnit_zero
end

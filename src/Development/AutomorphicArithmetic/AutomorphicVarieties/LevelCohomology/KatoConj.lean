module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.conj :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → BlochKatoSelmerVanishes l (Loc.colRep r) → BlochKatoSelmerVanishes l (Loc.colRep r') := by
  intro l _ F Ω _ _ _ _ n r r' ⟨P, hP⟩ h c hc hbk
  let f : (Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → Qbar l) :=
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).restrictScalars ℚ_[l]
  have hfa : ∀ x, f x = ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ => rfl
  have hcol : ∀ (ρ : G F Ω →* GL (Fin n) (Qbar l)) g x,
      Loc.colRep ρ g x = (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ _ _ => rfl
  have hf : ∀ g x, f (Loc.colRep r' g x) = Loc.colRep r g (f x) := by
    intro g x
    rw [hfa, hfa, hcol, hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hP]
    congr 2
    group
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec) hxy
    rwa [hfa, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec y, ?_⟩
    rw [hfa, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcont : Continuous (fun g => f (c g)) := by
    simp only [hfa]
    exact continuous_const.matrix_mulVec hc.1
  have hz : (fun g => f (c g)) ∈ Z1 (Loc.colRep r) := by
    refine ⟨hcont, fun g g' => ?_⟩
    have h1 := congrArg f (hc.2 g g')
    simpa only [map_add (f := _), hf] using h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h _ hz (UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ f hf c hcont hbk))
  obtain ⟨m', rfl⟩ := hsurj m
  refine (mem_coboundaries1 _ _).2 ⟨m', fun g => hinj ?_⟩
  have := hm g
  simp only [map_sub, hf]
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpKer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem not_dvd_index_ker {H k ι : Type} [Group H] [Field k] [Finite k] [Fintype ι] {l : ℕ} [hl : Fact l.Prime]
    (h0 : (l : k) = 0) (φ : H →* (ι → kˣ)) : ¬ l ∣ φ.ker.index := by
  classical
  haveI := Fintype.ofFinite k
  intro hd
  rw [Subgroup.index_ker] at hd
  have h1 : Nat.card φ.range ∣ Nat.card (ι → kˣ) := Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (ι → kˣ) = (Fintype.card k - 1) ^ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_units]
  have hc : ringChar k = l := by
    rcases (Nat.dvd_prime hl.out).1 (ringChar.dvd h0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  haveI : CharP k l := by
    rw [← hc]
    exact ringChar.charP k
  obtain ⟨n, -, hn⟩ := FiniteField.card k l
  have hq : l ∣ Fintype.card k := by
    rw [hn]
    exact dvd_pow_self _ (PNat.ne_zero n)
  have hpos : 0 < Fintype.card k := Fintype.card_pos
  have h3 : l ∣ Fintype.card k - 1 := hl.out.dvd_of_dvd_pow (h2 ▸ dvd_trans hd h1)
  have h6 : Fintype.card k - 1 + 1 = Fintype.card k := by omega
  rw [← h6] at hq
  have h4 : l ∣ 1 := (Nat.dvd_add_right h3).1 hq
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h4)

theorem UpperTheory.V.X.spKer :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.rbar.ker.Normal ∧ ¬ l ∣ D.rbar.ker.index ∧ ∀ (j : ℤ × ℤ), ∀ g ∈ D.rbar.ker, Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) g = 1 := by
  intro Ω _ _ _ l _ c D
  classical
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, hfin, hl, -⟩ := abelian₂.dvr_finite l c.O
  have key : ∀ g, D.rbar g = 1 ↔ ∀ i, residue c.O ↑(D.ps i g) = 1 := by
    intro g
    have e : D.rbar g = Matrix.diagonal fun i => residue c.O ↑(D.ps i g) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Raw.rbar, Raw.r0, mapRep, diagRep]
      · simp [Raw.rbar, Raw.r0, mapRep, diagRep, Matrix.diagonal_apply, h]
    rw [e, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  let φ : G ℚ Ω →* (Fin 4 → (ResidueField c.O)ˣ) :=
    Pi.monoidHom fun i => (Units.map (residue c.O : c.O →* ResidueField c.O)).comp (D.ps i)
  have hφ : ∀ g, φ g = 1 ↔ ∀ i, residue c.O ↑(D.ps i g) = 1 := by
    intro g
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    rw [Pi.one_apply, Units.ext_iff]
    exact Iff.rfl
  have hker : D.rbar.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, key, hφ]
  have h0 : ((l : ℕ) : ResidueField c.O) = 0 := by
    have h := (IsLocalRing.residue_eq_zero_iff _).2 hl
    simpa using h
  refine ⟨by rw [hker]; infer_instance, by rw [hker]; exact not_dvd_index_ker h0 φ, ?_⟩
  intro j g hg
  have hk := (key g).1 hg
  have a1 : Units.map (residue c.O : c.O →* ResidueField c.O) (D.Psi g) = 1 := by
    ext
    simpa [Raw.ps] using hk 1
  have a2 : Units.map (residue c.O : c.O →* ResidueField c.O) (D.al g) = 1 := by
    ext
    simpa [Raw.ps] using hk 2
  have hu : Units.map (residue c.O : c.O →* ResidueField c.O) ((D.al ^ j.1 * D.Psi ^ j.2) g) = 1 := by
    simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow, a1, a2, one_zpow, mul_one]
  exact congrArg Units.val hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalTail
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPtTail
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X
open UpperTheory.V.Loc GlobalTheory.Published GlobalTheory.Published.PoitouTate

section Transport

variable {R R' Γ M : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R' Γ M) (h : ∀ g m, ρ' g m = ρ g m)

include h in
private theorem mem_Z2_iff (f : Γ × Γ → M) : f ∈ Z2 ρ ↔ f ∈ Z2 ρ' := by
  simp only [mem_cocycles2, h]

include h in
private theorem mem_B2_iff (f : Γ × Γ → M) : f ∈ B2 ρ ↔ f ∈ B2 ρ' := by
  have : ∀ c, d1 ρ c = d1 ρ' c := fun c => funext fun ⟨g, g'⟩ => by simp only [d1_apply, h]
  simp only [separated_dvr_second_cohomology_mem, this]

private def h2EquivOfRepEq : H2 ρ ≃ H2 ρ' :=
  Quotient.congr (Equiv.subtypeEquivRight (mem_Z2_iff ρ ρ' h)) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
    exact mem_B2_iff ρ ρ' h _

include h in
private theorem nonempty_sha2_equiv_sha2 {I : Type} {D : I → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) :
    Nonempty (Sha2 ρ φ hφ ≃ Sha2 ρ' φ hφ) := by
  refine ⟨(h2EquivOfRepEq ρ ρ' h).subtypeEquiv fun x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall_congr' fun i => ?_
    change Submodule.Quotient.mk (restrictCocycles2 ρ (φ i) (hφ i) z) = 0 ↔
      Submodule.Quotient.mk (restrictCocycles2 ρ' (φ i) (hφ i) ⟨z.1, (mem_Z2_iff ρ ρ' h _).1 z.2⟩) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap]
    exact mem_B2_iff (ρ.comp (φ i)) (ρ'.comp (φ i)) (fun g m => h _ m) _

end Transport

private theorem card_ker_range {R A B : Type} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) : Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]

private theorem card_exact {R A B C : Type} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g)
    (hg : Function.Surjective g) :
    Nat.card (LinearMap.ker f) * Nat.card B = Nat.card A * Nat.card C := by
  rw [card_ker_range f, card_ker_range g, LinearMap.exact_iff.1 h, LinearMap.range_eq_top.2 hg, mul_assoc,
    Nat.card_congr (Submodule.topEquiv (R := R) (M := C)).toEquiv]

private theorem card_H0dual {R k Γ Γ' M : Type} [Field R] [Field k] [Finite k] [Algebra R k] [Group Γ] [Group Γ']
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] [Finite M]
    (ρ : Representation k Γ M) (ρ' : Representation R Γ' M) (e : Γ' ≃* Γ) (h : ∀ g m, ρ' g m = ρ (e g) m)
    (χ : Γ →* kˣ) (χ' : Γ' →* Rˣ) (hχ : ∀ g, (χ (e g) : k) = algebraMap R k (χ' g)) :
    Nat.card (H0dual χ ρ) = Nat.card (H0dual χ' ρ') := by
  haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective
  let T : Module.Dual k M →+ Module.Dual R M :=
    { toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R)
      map_zero' := by ext; simp
      map_add' := fun f f' => by ext; simp }
  have hT : ∀ f m, T f m = Algebra.trace R k (f m) := fun _ _ => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext m
    refine (traceForm_nondegenerate R k).1 (f m) fun a => ?_
    have := hT f (a • m)
    rw [hf, f.map_smul, smul_eq_mul, mul_comm] at this
    exact this.symm
  haveI : Finite (Module.Dual R M) := DFunLike.finite _
  have hbij : Function.Bijective T := hinj.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank])
  refine Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)
  rw [Equiv.ofBijective_apply]
  constructor
  · intro hf g x
    rw [hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro hf g x
    obtain ⟨g, rfl⟩ := e.surjective g
    have : f.comp (ρ (e g)) = (χ (e g) : k) • f := hinj (LinearMap.ext fun y => by
      have := hf g y
      rw [hT, hT, h] at this
      rw [hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def,
        map_smul, smul_eq_mul])
    exact LinearMap.congr_fun this x

private theorem card_twDual {R Γ Γ' M : Type} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (π : Γ' →* Γ) (hπ : Function.Surjective π) :
    Nat.card (H0 (twDual χ ρ)) = Nat.card (H0dual (χ.comp π) (ρ.comp π)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)
  constructor
  · intro hy g m
    have e := congrArg (fun φ : TDual R M => φ (ρ (π g) m)) (hy (π g))
    simp only [twDual_apply] at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e
    exact e.symm
  · intro hy g
    obtain ⟨g, rfl⟩ := hπ g
    refine LinearMap.ext fun m => ?_
    have := hy g (ρ (π g)⁻¹ m)
    simp only [MonoidHom.comp_apply] at this
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem UpperTheory.V.X.ptTail :
    LocalFiniteness → GlobalFiniteness → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) → ∀ (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → finrank k (Sha2 ρ (fun v => locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (A v)) fun v => continuous_locHom _ (A v)) + ∑ v, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (A v)))) = finrank k (H2 ρ) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω _))) := by
  intro hL _ hP Ω _ _ _ l _ h2 S hS A hA k _ _ _ M _ _ _ _ _ ρ hρ
  have hl : l.Prime := Fact.out
  let χ := cycK Ω l k
  let c : ZMod (l ^ 1) →+* k := ZMod.castHom (dvd_pow_self l one_ne_zero) k
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) _ M := resCoef (ZMod (l ^ 1)) ρ
  have h : ∀ g m, ρ' g m = ρ g m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ
  have hS' : ContainsAbove S l := hS
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_pow ℚ Ω l 1
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := 1) hS'
  obtain ⟨inv, -, hN⟩ := hP ℚ Ω l 1 (Or.inl h2) one_pos ζ hζ
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hex, hsurj⟩, ⟨⟨-, hfs, -⟩, -⟩, -⟩ := hN S hS' A hA μ hμ M ρ' hρ'
  have hc := card_exact _ _ hex hsurj
  have hker : LinearMap.ker (loc2 S A ρ') = Sha2 ρ' (locFam S A) (continuous_locFam S A) := LinearMap.ker_pi _
  haveI f2 : ∀ v : S, Finite (H2 (ρ'.comp (locFam S A v))) := fun v => by
    obtain ⟨-, -, f2, -⟩ := hL ℚ Ω l 1 M (A v) (ρ'.comp (locFam S A v)) v.1 one_pos (hA v)
      (hρ'.comp' (continuous_locFam S A v))
    exact f2
  haveI : Finite (H2 ρ') := by
    apply Nat.finite_of_card_ne_zero
    rw [card_ker_range (loc2 S A ρ'), hker]
    exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  obtain ⟨eS⟩ := nonempty_sha2_equiv_sha2 ρ ρ' h (locFam S A) (continuous_locFam S A)
  have e2 := h2EquivOfRepEq ρ ρ' h
  have e3 : ∀ v : S, H2 (ρ.comp (locFam S A v)) ≃ H2 (ρ'.comp (locFam S A v)) := fun v =>
    h2EquivOfRepEq _ _ fun g m => h _ m
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  haveI : Finite (Sha2 ρ (locFam S A) (continuous_locFam S A)) := Subtype.finite
  haveI : Module.Finite k (Sha2 ρ (locFam S A) (continuous_locFam S A)) := .of_finite
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S A v))) := fun v => Finite.of_equiv _ (e3 v).symm
  haveI : Module.Finite k (H2 ρ) := .of_finite
  haveI : ∀ v : S, Module.Finite k (H2 (ρ.comp (locFam S A v))) := fun _ => .of_finite
  haveI : Finite (Module.Dual k M) := DFunLike.finite _
  haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  haveI : Finite (H0 (twDual μ ρ')) := Subtype.finite
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hd : Nat.card (Module.Dual (ZMod (l ^ 1)) (H0 (twDual μ ρ'))) =
      Nat.card (H0dual χ (ρ.comp (toGS Ω _))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)), Subspace.dual_finrank_eq,
      ← Module.natCard_eq_pow_finrank, card_twDual μ ρ' (toGS Ω _) (QuotientGroup.mk'_surjective _), hμ]
    refine (card_H0dual (ρ.comp (toGS Ω _)) (ρ'.comp (toGS Ω _)) (MulEquiv.refl (G ℚ Ω)) (fun _ _ => rfl) χ
      (cycMod ℚ Ω l 1) fun g => ?_).symm
    exact RingHom.congr_fun (Subsingleton.elim c (algebraMap _ k)) _
  change finrank k (Sha2 ρ (locFam S A) (continuous_locFam S A)) +
    ∑ v, finrank k (H2 (ρ.comp (locFam S A v))) = _
  apply Nat.pow_right_injective hk
  beta_reduce
  rw [pow_add, pow_add, ← Finset.prod_pow_eq_pow_sum]
  simp only [← Module.natCard_eq_pow_finrank]
  rw [Nat.card_congr eS, Nat.card_congr e2, ← hd, ← hc, hker, Nat.card_pi]
  exact congrArg _ (Finset.prod_congr rfl fun v _ => Nat.card_congr (e3 v))
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galTail :
    LocalFiniteness → GlobalFiniteness → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω SP) M), ContAction ρ → finrank k (shaF (galFrame SP T Q v0 pl K) ρ) + ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) = finrank k (H2 ρ) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro lf gf pt Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ _ _ ρ hρ
  obtain ⟨S, e, rfl, hl, hT, hQ⟩ := galIdx Ω l v0 hD
  let B : T ⊕ Q → ValuationSubring Ω := Sum.elim (fun v => pl v) (fun q => pl q)
  have hB : ∀ x, IsPlaceOver (B x) (e x).1 := by
    rintro (v | q)
    · exact hT v
    · exact hQ q
  have hA : ∀ v : S, IsPlaceOver (B (e.symm v)) v.1 := fun v => by
    have := hB (e.symm v)
    rwa [e.apply_symm_apply] at this
  have h := ptTail lf gf pt Ω l hD.l_odd S hl (fun v => B (e.symm v)) hA k M ρ hρ
  have hsum : ∑ v : S, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v))))) =
      ∑ v : T, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl v)))) +
        ∑ q : Q, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl q)))) := by
    rw [e.symm.sum_comp (fun x => finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x))))),
      Fintype.sum_sum_type]
    rfl
  have hsha : Sha2 ρ (fun v => locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v)))
      (fun v => continuous_locHom _ (B (e.symm v))) = shaF (galFrame (S : Set (HeightOneSpectrum (𝓞 ℚ))) T Q v0 pl K) ρ := by
    have h1 := e.symm.iInf_comp (g := fun x => LinearMap.ker (resH2 ρ (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x)) (continuous_locHom _ (B x))))
    rw [iInf_sum] at h1
    exact h1
  rw [hsum, hsha, ← add_assoc] at h
  exact h
end

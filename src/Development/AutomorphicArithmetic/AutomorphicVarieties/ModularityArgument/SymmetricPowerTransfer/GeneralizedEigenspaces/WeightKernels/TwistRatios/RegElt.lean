module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.UfFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.SymmetricFourthPowerMatrix

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.RegElt
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem regElt_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hI : Ideal.span {((p : ℕ) : (Int.castRingHom Ω).range)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, c, rfl⟩, hc⟩
    have h1 : ((p : ℕ) : Ω) * ((c : ℤ) : Ω) = 1 := congrArg Subtype.val hc
    have h2 : ((p : ℕ) : ℤ) * c = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : (Int.castRingHom Ω).range), Ideal.mem_span_singleton_self _, by simp⟩)⟩

private theorem regElt_zpow_ne {G : Type} [Group G] (e : G) (he : ¬ IsOfFinOrder e) (n : ℤ) (hn : 0 < n) : e ^ n ≠ 1 := by
  intro h
  refine he (isOfFinOrder_iff_pow_eq_one.2 ⟨n.toNat, by omega, ?_⟩)
  rw [← zpow_natCast, Int.toNat_of_nonneg hn.le, h]

private theorem regElt_key {K : Type} [Field K] (e x : Kˣ) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k)
    (hx : x ^ k = (e ^ (m : ℤ)) ^ k) (he : ¬ IsOfFinOrder e) :
    ¬ IsOfFinOrder x ∧ ∀ i : ℤ, |i| ≤ 2 →
      ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 ≠ (e : K) ^ i + (e : K) ^ (-i) := by
  have hsq : ∀ j : ℤ, |j| ≤ 2 → x ^ 2 ≠ e ^ j := by
    intro j hj h
    have hj' := (abs_le.1 hj).2
    have hpos : 0 < (2 * (m : ℤ) - j) * (k : ℤ) := by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm
      apply mul_pos <;> omega
    refine regElt_zpow_ne e he _ hpos ?_
    have h1 : (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k = (e ^ j) ^ k := by
      rw [← hx, ← h, ← pow_add, ← pow_mul, two_mul]
    have h2 : e ^ ((2 * (m : ℤ) - j) * (k : ℤ)) = (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k * ((e ^ j) ^ k)⁻¹ := by
      simp only [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [h2, h1, mul_inv_cancel]
  refine ⟨fun hf => ?_, fun i hi h => ?_⟩
  · obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    have hpos : 0 < (m : ℤ) * k * n := by
      have a : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
      have b : (0 : ℤ) < k := by exact_mod_cast hk
      have c : (0 : ℤ) < n := by exact_mod_cast hn
      positivity
    refine regElt_zpow_ne e he _ hpos ?_
    rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hx, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  · have hx0 : (x : K) ≠ 0 := x.ne_zero
    have hE0 : ((e : K) ^ i) ≠ 0 := zpow_ne_zero _ e.ne_zero
    have hz : ((x : K) ^ 2 - (e : K) ^ i) * ((x : K) ^ 2 - ((e : K) ^ i)⁻¹) = 0 := by
      rw [Units.val_inv_eq_inv_val, zpow_neg] at h
      field_simp at h ⊢
      linear_combination (exp := 1) h
    rcases mul_eq_zero.1 hz with h0 | h0
    · refine hsq i hi (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      exact sub_eq_zero.1 h0
    · refine hsq (-i) (by rwa [abs_neg]) (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_neg]
      exact sub_eq_zero.1 h0

theorem UpperTheory.V.Z.Sym.Ga.regElt :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)), AdIn ι M m r → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∉ Ga.Bad r ∧ ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧ (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) := by
  intro L Ω _ _ _ _ _ _ l _ ι M m r hr H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨A, hA⟩ := regElt_place (Ω := Ω) l (Fact.out)
  obtain ⟨b0, k, κ, hk, ⟨g, hg⟩, hκ⟩ := hr.above A hA
  obtain ⟨s, hsH, hsI, hinf⟩ := UpperTheory.V.Z.Sym.Ga.ineInf L Ω l A hA H hH
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hsI⟩
  obtain ⟨h0, h1⟩ := hκ t hsI
  have hcp : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C ((κ 0 t : (Qbar l)ˣ) : Qbar l)) * (X - C ((κ 1 t : (Qbar l)ˣ) : Qbar l)) := by
    have e : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj g _
    rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg t).1 i j hij), Fin.prod_univ_two]
    have e0 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((κ 0 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 0
    have e1 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = ((κ 1 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 1
    rw [e0, e1]
  have hx : (κ 0 t / κ 1 t) ^ k = (cycBar L Ω l s ^ (m : ℤ)) ^ k := by
    rw [div_pow, h0, h1, zpow_add, mul_pow]
    exact mul_div_cancel_left _ _
  have key := regElt_key (cycBar L Ω l s) (κ 0 t / κ 1 t) m k hr.gap hk hx hinf
  refine ⟨s, hsH, ?_, κ 0 t, κ 1 t, key.1, hcp⟩
  rintro ⟨i, hi, hb⟩
  have huf := (UpperTheory.V.Z.Sym.Ga.ufFacts _ (r s)).1 _ _ hcp
  rw [huf] at hb
  exact key.2 i hi hb
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.NoKappa
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TraceSym4M
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_sym4M {k : Type} [Field k] (g : Matrix (Fin 2) (Fin 2) k) :
    Matrix.trace (UpperTheory.V.Z.Sym.Ga.symmetricFourthPowerMatrix k g) = g.trace ^ 4 - 3 * g.trace ^ 2 * g.det + g.det ^ 2 := by
  simp only [UpperTheory.V.Z.Sym.Ga.symmetricFourthPowerMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.trace, Matrix.diag,
    Fin.sum_univ_five, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  ring

theorem UpperTheory.V.Z.Sym.Ga.trSym4 :
    ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) k) (s : Γ), Ga.tr (Ga.sym4 ρ s) = Ga.uf (ρ s) ^ 2 + Ga.uf (ρ s) - 1 := by
  intro k _ Γ _ ρ s
  have hD : ((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det ≠ 0 :=
    ((ρ s).isUnit.map Matrix.detMonoidHom).ne_zero
  simp only [Ga.tr, Ga.uf, Ga.sym4, UpperTheory.V.Af.tw_val, Matrix.trace_smul, Units.coe_map,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_coe, trace_sym4M]
  simp only [MonoidHom.pow_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
    Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    smul_eq_mul]
  field_simp
  ring
end
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def phiB {k : Type} [Field k] {H : Type} [Group H] (a b : H →* GL (Fin 3) k) :
    H →* (Matrix (Fin 3) (Fin 3) k × Matrix (Fin 3) (Fin 3) k × k) where
  toFun h := ((a h : Matrix (Fin 3) (Fin 3) k), (b h : Matrix (Fin 3) (Fin 3) k), 1)
  map_one' := by simp
  map_mul' x y := by simp

private def fB {k : Type} [Field k] (A B : Matrix (Fin 3) (Fin 3) k) :
    (Matrix (Fin 3) (Fin 3) k × Matrix (Fin 3) (Fin 3) k × k) →ₗ[k] k :=
  (Matrix.traceLinearMap (Fin 3) k k ∘ₗ LinearMap.mulLeft k A ∘ₗ LinearMap.fst k _ _) +
    (Matrix.traceLinearMap (Fin 3) k k ∘ₗ LinearMap.mulLeft k B ∘ₗ LinearMap.fst k _ _ ∘ₗ LinearMap.snd k _ _) -
    (LinearMap.snd k _ _ ∘ₗ LinearMap.snd k _ _)

private theorem fB_apply {k : Type} [Field k] (A B X Y : Matrix (Fin 3) (Fin 3) k) (z : k) :
    fB A B (X, Y, z) = (A * X).trace + (B * Y).trace - z := by
  simp [fB]

theorem UpperTheory.V.Z.Sym.Ga.noKappa :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (r r' : Γ →* GL (Fin 2) (Qbar l)), IrrOpen (Ga.sym4 r) → ∀ V : Set Γ, IsOpen V → V.Nonempty → (∀ g ∈ V, Ga.uf (r' g) = Ga.uf (r g) ^ 2 - 2) → False := by
  intro l _ Γ _ _ _ _ _ r r' hirr V hV ⟨g, hg⟩ hu
  obtain ⟨H, -, hHo, hH⟩ := Ga.coset Γ V hV g hg
  have hR : IsIrr ((Ga.sym4 r).comp H.subtype) := hirr H hHo
  have key := Ga.kerLe (Qbar l) H 5 ((Ga.sym4 r).comp H.subtype) hR (Ga.sym4 r g)
    (Matrix (Fin 3) (Fin 3) (Qbar l) × Matrix (Fin 3) (Fin 3) (Qbar l) × Qbar l)
    (phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype))
    (fB (ad0 r g : Matrix (Fin 3) (Fin 3) (Qbar l)) (ad0 r' g)) ?_
  · have h1 := key.1
    have h2 : Module.finrank (Qbar l) ↥(Algebra.adjoin (Qbar l)
        (Set.range ⇑(phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype)))) ≤ 19 := by
      refine (Submodule.finrank_le (Subalgebra.toSubmodule (Algebra.adjoin (Qbar l)
        (Set.range ⇑(phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype)))))).trans ?_
      simp [Module.finrank_prod, Module.finrank_matrix]
    omega
  · intro h
    have hgh := hu (g * h) (hH h h.2)
    have e1 : Ga.tr (Ga.sym4 r g * ((Ga.sym4 r).comp H.subtype) h) = Ga.tr (Ga.sym4 r (g * h)) := by
      simp [map_mul]
    have e2 : ((ad0 r g : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 r (h : Γ))).trace
        = Ga.uf (r (g * h)) + 1 := by
      rw [← (Ga.ufFacts (Qbar l) (r (g * h))).2.2.2.2 Γ r (g * h), map_mul]
      rfl
    have e3 : ((ad0 r' g : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 r' (h : Γ))).trace
        = Ga.uf (r' (g * h)) + 1 := by
      rw [← (Ga.ufFacts (Qbar l) (r' (g * h))).2.2.2.2 Γ r' (g * h), map_mul]
      rfl
    rw [e1, Ga.trSym4]
    show _ = fB _ _ ((((ad0 r).comp H.subtype) h : Matrix (Fin 3) (Fin 3) (Qbar l)),
      (((ad0 r').comp H.subtype) h : Matrix (Fin 3) (Fin 3) (Qbar l)), 1)
    rw [fB_apply]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [e2, e3, hgh]
    ring
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TwistOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ConjOn
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.conjOn :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (H : Type) [Group H] (n : ℕ) (R R' : H →* GL (Fin n) k), IsIrr R → ∀ x₀ y₀ : GL (Fin n) k, (∀ h, Ga.tr (x₀ * R h) = Ga.tr (y₀ * R' h)) → RepIso R R' := by
  intro k _ _ H _ n R R' hR x₀ y₀ htr
  classical
  let φ : H →* Matrix (Fin n) (Fin n) k := (Units.coeHom _).comp R'
  let ψ : H →* Matrix (Fin n) (Fin n) k := (Units.coeHom _).comp R
  let f : Matrix (Fin n) (Fin n) k →ₗ[k] k :=
    (Matrix.traceLinearMap (Fin n) k k) ∘ₗ LinearMap.mulLeft k (y₀ : Matrix (Fin n) (Fin n) k)
  obtain ⟨hdim, hker⟩ := Ga.kerLe k H n R hR x₀ (Matrix (Fin n) (Fin n) k) φ f
    (fun h => by simpa [f, φ, Ga.tr] using htr h)
  have htop : Algebra.adjoin k (Set.range φ) = ⊤ := by
    apply Subalgebra.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    simpa [Module.finrank_matrix, sq] using hdim
  let P : MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k := MonoidAlgebra.lift k _ H φ
  let Q : MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k := MonoidAlgebra.lift k _ H ψ
  have hs : Function.Surjective P := by
    have hle : Algebra.adjoin k (Set.range φ) ≤ P.range :=
      Algebra.adjoin_le (by
        rintro _ ⟨h, rfl⟩
        exact ⟨MonoidAlgebra.of k H h, by simp [P]⟩)
    intro m
    have hm : m ∈ P.range := hle (htop ▸ Algebra.mem_top)
    exact hm
  have hk : ∀ a ∈ RingHom.ker P, Q a = 0 := fun a ha => hker a ha
  let T : Matrix (Fin n) (Fin n) k →ₐ[k] Matrix (Fin n) (Fin n) k :=
    (Ideal.Quotient.liftₐ (RingHom.ker P) Q hk).comp
      (Ideal.quotientKerAlgEquivOfSurjective hs).symm.toAlgHom
  have hT : ∀ h, T (φ h) = ψ h := by
    intro h
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective hs).symm (φ h) =
        Ideal.Quotient.mk (RingHom.ker P) (MonoidAlgebra.of k H h) := by
      rw [AlgEquiv.symm_apply_eq]
      simp [P]
    change Ideal.Quotient.liftₐ (RingHom.ker P) Q hk
      ((Ideal.quotientKerAlgEquivOfSurjective hs).symm (φ h)) = ψ h
    rw [h1]
    change Q (MonoidAlgebra.of k H h) = ψ h
    simp [Q]
  obtain ⟨J, hJ⟩ := KStar.Tree.exists_conj_of_algHom T
  refine ⟨J⁻¹, fun s => ?_⟩
  have h2 := hJ (φ s)
  rw [hT] at h2
  have h3 : R s * J = J * R' s := Units.ext h2
  rw [inv_inv, mul_assoc, h3, inv_mul_cancel_left]
end
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem twistOf_schur {k H : Type} [Field k] [IsAlgClosed k] [Group H] {n : ℕ} (R : H →* GL (Fin n) k)
    (hR : IsIrr R) (A : Matrix (Fin n) (Fin n) k)
    (hA : ∀ h, A * (R h : Matrix (Fin n) (Fin n) k) = (R h : Matrix (Fin n) (Fin n) k) * A) :
    ∃ c : k, A = c • (1 : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨h0, -, h2⟩ := hR
  haveI : Nontrivial (Fin n → k) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h0 (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  refine ⟨c, ?_⟩
  have hinv : IsInv R (Module.End.eigenspace (Matrix.toLin' A) c) := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rcases h2 _ le_top hinv with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' A) c := by rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    simp

private theorem twistOf_ratio {k Γ : Type} [Field k] [IsAlgClosed k] [Group Γ] {n : ℕ} (R S : Γ →* GL (Fin n) k)
    (H : Subgroup Γ) (hN : H.Normal) (hR : IsIrr (R.comp H.subtype)) (hS : ∀ h ∈ H, S h = R h) :
    ∃ ξ : Γ →* kˣ, H ≤ ξ.ker ∧ ∀ g, S g = tw R ξ g := by
  have hn : Nonempty (Fin n) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    exact hR.1 (Subsingleton.elim _ _)
  have inj : ∀ (X : GL (Fin n) k) (a b : k),
      a • (X : Matrix (Fin n) (Fin n) k) = b • (X : Matrix (Fin n) (Fin n) k) → a = b := by
    intro X a b hab
    exact smul_left_injective k X.ne_zero hab
  have key : ∀ g, ∃ u : kˣ, (S g : Matrix (Fin n) (Fin n) k) = (u : k) • (R g : Matrix (Fin n) (Fin n) k) := by
    intro g
    obtain ⟨c, hc⟩ := twistOf_schur (R.comp H.subtype) hR ((R g)⁻¹ * S g : GL (Fin n) k) (by
      intro h
      have e : (R g)⁻¹ * S g * R h = R h * ((R g)⁻¹ * S g) := by
        have e1 := hS _ (hN.conj_mem h h.2 g)
        have e2 := hS _ h.2
        simp only [map_mul, map_inv, e2] at e1
        calc (R g)⁻¹ * S g * R h = (R g)⁻¹ * (S g * R h * (S g)⁻¹) * S g := by group
          _ = _ := by rw [e1]; group
      exact congrArg Units.val e)
    have h1 : (S g : Matrix (Fin n) (Fin n) k) = c • (R g : Matrix (Fin n) (Fin n) k) := by
      have : S g = R g * ((R g)⁻¹ * S g) := by group
      rw [this, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one]
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h1
      exact (S g).ne_zero h1
    exact ⟨Units.mk0 c hc0, h1⟩
  choose u hu using key
  have hmul : ∀ a b, u (a * b) = u a * u b := by
    intro a b
    apply Units.ext
    apply inj (R (a * b))
    rw [← hu, map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul, hu, hu, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
  refine ⟨MonoidHom.mk' u hmul, ?_, ?_⟩
  · intro h hh
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply inj (R h)
    have := hu h
    rw [hS h hh] at this
    simpa using this.symm
  · intro g
    apply Units.ext
    rw [tw_val, hu]
    rfl

theorem UpperTheory.V.Z.Sym.Ga.twistOf :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (n : ℕ) (R R' : Γ →* GL (Fin n) (Qbar l)), IrrOpen R → ∀ V : Set Γ, IsOpen V → V.Nonempty → (∀ g ∈ V, Ga.tr (R' g) = Ga.tr (R g)) → ∃ ξ : Γ →* (Qbar l)ˣ, IsOpen (ξ.ker : Set Γ) ∧ RepIso (tw R ξ) R' := by
  intro l _ Γ _ _ _ _ _ n R R' hR V hV hne htr
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨H, hN, hO, hH⟩ := Ga.coset Γ V hV g₀ hg₀
  obtain ⟨P, hP⟩ := Ga.conjOn (Qbar l) H n (R.comp H.subtype) (R'.comp H.subtype) (hR H hO) (R g₀) (R' g₀) (by
    intro h
    have := htr _ (hH h h.2)
    rw [map_mul, map_mul] at this
    exact this.symm)
  obtain ⟨ξ, h1, h2⟩ := twistOf_ratio R ((MulAut.conj P⁻¹).toMonoidHom.comp R') H hN (hR H hO) (by
    intro h hh
    have : R' h = P * R h * P⁻¹ := hP ⟨h, hh⟩
    change P⁻¹ * R' h * P⁻¹⁻¹ = R h
    rw [this]; group)
  refine ⟨ξ, Subgroup.isOpen_mono h1 hO, P, fun s => ?_⟩
  rw [← h2]
  change R' s = P * (P⁻¹ * R' s * P⁻¹⁻¹) * P⁻¹
  group
end
end

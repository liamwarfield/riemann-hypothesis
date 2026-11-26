module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.IdealNormClassCongr
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped nonZeroDivisors

namespace UpperTheory.V.Tower

section Norm

variable (K : Type) {K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

def idNorm : (Ideal (𝓞 K'))⁰ →* (Ideal (𝓞 K))⁰ where
  toFun I := ⟨Ideal.relNorm (𝓞 K) I.1, mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero I.2 (Ideal.relNorm_eq_bot_iff.1 h)⟩
  map_one' := Subtype.ext (map_one (Ideal.relNorm (𝓞 K)))
  map_mul' I J := Subtype.ext (map_mul (Ideal.relNorm (𝓞 K)) I.1 J.1)

theorem ideal_norm_class_congr {I J : (Ideal (𝓞 K'))⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (idNorm K I) = ClassGroup.mk0 (idNorm K J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, h⟩ := h
  refine ⟨Algebra.intNorm (𝓞 K) (𝓞 K') x, Algebra.intNorm (𝓞 K) (𝓞 K') y, fun h => hx (Algebra.intNorm_eq_zero.1 h),
    fun h => hy (Algebra.intNorm_eq_zero.1 h), ?_⟩
  have := congrArg (Ideal.relNorm (𝓞 K)) h
  rw [map_mul, map_mul, Ideal.relNorm_singleton, Ideal.relNorm_singleton] at this
  exact this

def nFun (c : ClassGroup (𝓞 K')) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (idNorm K (ClassGroup.mk0_surjective c).choose)

private theorem norm_function_mk (I : (Ideal (𝓞 K'))⁰) : nFun K (ClassGroup.mk0 I) = ClassGroup.mk0 (idNorm K I) :=
  ideal_norm_class_congr K (ClassGroup.mk0_surjective _).choose_spec

def clNorm : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K) :=
  MonoidHom.mk' (nFun K) fun a b => by
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective b
    rw [← map_mul, norm_function_mk, norm_function_mk, norm_function_mk, map_mul, map_mul]

end Norm

section Lim

variable (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

omit [IsAlgClosure L Ω] in
theorem Fn_le_succ (n : ℕ) : Fn L Ω l n ≤ Fn L Ω l (n + 1) := by
  refine IntermediateField.adjoin.mono _ _ _ fun x hx => ?_
  have h0 : ∀ m : ℕ, (Polynomial.X ^ l ^ m - 1 : Polynomial L) ≠ 0 := fun m =>
    Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos m) 1
  rw [Polynomial.mem_rootSet_of_ne (h0 _)] at hx ⊢
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at hx ⊢
  rw [pow_succ, pow_mul, hx, one_pow]

def normStep (n : ℕ) : ClassGroup (𝓞 (Fn L Ω l (n + 1))) →* ClassGroup (𝓞 (Fn L Ω l n)) :=
  letI : Algebra (Fn L Ω l n) (Fn L Ω l (n + 1)) := (IntermediateField.inclusion (Fn_le_succ l L Ω n)).toRingHom.toAlgebra
  clNorm (Fn L Ω l n)

variable (k : Type) [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]

theorem galOf_Fn (n : ℕ) : galOf k (Fn L Ω l n) Ω = levU l (galOf k L Ω) n :=
  haveI := (fnCyc L Ω l n).1
  galOfCyc k Ω l n L (Fn L Ω l n)

theorem cycU_le_Fn (n : ℕ) : cycU l (galOf k L Ω) ≤ galOf k (Fn L Ω l n) Ω :=
  (galOf_Fn l L Ω k n).symm ▸ cycU_le_levU l _ n

abbrev pullN (n : ℕ) : (ClassGroup (𝓞 (Fn L Ω l n)) → QZ l) →ₗ[ℤ_[l]] (cycU l (galOf k L Ω) → QZ l) :=
  clPull (Fn L Ω l n) (cycU_le_Fn l L Ω k n) ℤ_[l] (QZ l)

end Lim

section Desc

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

variable (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure L Ω]

def IsDesc {l : ℕ} [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal]
    (Φ : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e) : Prop :=
  ∀ (x : Sha D e) (u : Uinf L Ω l) (u' : cycU l U), u'.1 = galEmb k L Ω u.1 → (Φ x).1.1 u' = resInf D e x.1 u

variable [Normal k L]

variable (k Ω) (l : ℕ) [Fact l.Prime] (N : ℕ)

end Desc

end UpperTheory.V.Tower

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.layerGen :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, (layU l L Ω m).index = l ^ m) ∧
        ∀ γ : G L Ω, IsGen l ⊤ γ → PropA.IsLevel l (cycZ L Ω l γ : ℤ_[l]ˣ) (cZero l L) ∧ γ ∈ levU l ⊤ 1 ∧ ∀ m, IsGen l (layU l L Ω m) (γ ^ l ^ m) := by
  intro L Ω _ _ _ _ _ l _ hmu
  obtain ⟨-, h2, h3, -⟩ := muQ L Ω l
  have hq := h3.1 hmu
  have hr := cycRange L Ω l hmu
  obtain ⟨p1, p2, p3⟩ := princGen l _ hq
  have h0 : ∀ g, cycZ L Ω l g ∈ KStar.TotallyRealRoots.princ l (cZero l L) := fun g => hr ▸ ⟨g, rfl⟩
  have hU : ∀ n, Un L Ω l n = (KStar.TotallyRealRoots.princ l n).comap (cycZ L Ω l) := fun n =>
    Subgroup.ext fun g => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  have h1 : 1 ≤ cZero l L := by
    refine le_trans ?_ hq
    unfold qExp
    split_ifs <;> omega
  refine ⟨fun m => ?_, fun γ hγ => ?_⟩
  · rw [layU, hU, Subgroup.index_comap, hr, p3]
  · have hn : cycZ L Ω l γ ∉ KStar.TotallyRealRoots.princ l (cZero l L + 1) := by
      refine (p1 _ (h0 γ)).1 ?_
      rw [← hr, MonoidHom.range_eq_map]
      exact hγ.2
    obtain ⟨q1, q2⟩ := p2 _ (h0 γ) hn
    refine ⟨q1, ?_, fun m => ⟨?_, ?_⟩⟩
    · have : γ ∈ Un L Ω l 1 := by rw [(h2 1).2 h1]; trivial
      exact this
    · rw [layU, hU, Subgroup.mem_comap, map_pow]
      exact (q2 m).1
    · rw [layU, hU, map_pow]
      exact (Subgroup.map_comap_le _ _).trans
        (((princGen l (cZero l L + m) (hq.trans (Nat.le_add_right _ _))).1 _ (q2 m).1).2 (q2 m).2)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTors
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.dinfTors :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)), (IsClosed (U : Set (G k Ω)) → ∀ φ : Dinf l N U, ∃ r : ℕ, (l : ℤ_[l]) ^ r • φ = 0) ∧
        Dinf l N U ≤ Dinf l 1 U ∧ xRank l N U ≤ xRank l 1 U ∧
        ∀ [U.Normal] (e : ℤ), ∀ g ∈ cycU l U, dRep l N U g = 1 ∧ xRep l N U g = 1 ∧ dTw l N U e g = 1 ∧ xTw l N U e g = 1 := by
  intro k Ω _ _ _ _ _ l _ N U
  have hQ : ∀ q : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0 := by
    intro q
    revert q
    show ∀ q : ℚ_[l] ⧸ ZlSub l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ‖x‖ hl
      refine ⟨r, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hn : ‖(l : ℚ_[l]) ^ r * x‖ ≤ 1 := by
        rw [norm_mul, norm_pow, Padic.norm_p]
        have hp : (0 : ℝ) < (l : ℝ) ^ r := by positivity
        rw [inv_pow, inv_mul_le_iff₀ hp, mul_one]
        exact hr.le
      refine ⟨⟨(l : ℚ_[l]) ^ r * x, hn⟩, ?_⟩
      simp [Algebra.smul_def]
      rfl
  have hconj : ∀ [U.Normal] (g : G k Ω), g ∈ cycU l U → ∀ φ : Dinf l N U, dRep l N U g φ = φ := by
    intro _ g hg φ
    have hadd := φ.2.2.1
    have h1 : (φ : cycU l U → QZ l) 1 = 0 := by
      have := hadd 1 1
      rw [mul_one] at this
      simpa using this
    apply Subtype.ext
    funext u
    have e1 : conjHom (cycU l U) g u = (⟨g, hg⟩ : cycU l U)⁻¹ * u * ⟨g, hg⟩ := rfl
    change (φ : cycU l U → QZ l) (conjHom (cycU l U) g u) = _
    rw [e1, hadd, hadd]
    have h2 := hadd (⟨g, hg⟩ : cycU l U)⁻¹ ⟨g, hg⟩
    rw [inv_mul_cancel, h1] at h2
    rw [add_comm ((φ : cycU l U → QZ l) _) ((φ : cycU l U → QZ l) u), add_assoc, ← h2, add_zero]
  have hmono : Dinf l N U ≤ Dinf l 1 U := fun φ hφ =>
    ⟨hφ.1, hφ.2.1, hφ.2.2.1, fun A hA => by simp at hA⟩
  refine ⟨fun hU φ => ?_, hmono, ?_, ?_⟩
  · classical
    have hC : IsClosed ((cycU l U : Subgroup (G k Ω)) : Set (G k Ω)) :=
      hU.inter (isClosed_singleton.preimage (continuous_cycZ k Ω l))
    haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact
    have hfin := IsLocallyConstant.range_finite φ.2.1
    choose r hr using hQ
    refine ⟨∑ q ∈ hfin.toFinset, r q, ?_⟩
    apply Subtype.ext
    funext u
    have hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset := by simp
    change (l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0
    rw [← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]
  · refine Module.length_le_of_injective
      (LinearMap.restrict (Submodule.inclusion hmono)
        (p := Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]))
        (q := Submodule.torsionBy ℤ_[l] (Dinf l 1 U) (l : ℤ_[l])) fun x hx => ?_) ?_
    · rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← LinearMap.map_smul, hx, map_zero]
    · intro a b hab
      apply Subtype.ext
      apply Submodule.inclusion_injective hmono
      exact congrArg Subtype.val hab
  · intro _ e g hg
    have hc : cycZ k Ω l g = 1 := hg.2
    have hd : dRep l N U g = 1 := LinearMap.ext fun φ => hconj g hg φ
    have hx : xRep l N U g = 1 := by
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro φ
      change ((dRep l N U).linHom (Representation.trivial ℤ_[l] (G k Ω) (QZ l)) g f) φ = f φ
      rw [Representation.linHom_apply]
      simp [hconj g⁻¹ (inv_mem hg)]
    refine ⟨hd, hx, ?_, ?_⟩
    · show ((cycZ k Ω l ^ (-e)) g : ℤ_[l]) • dRep l N U g = 1
      simp [hc, hd]
    · show ((cycZ k Ω l ^ e) g : ℤ_[l]) • xRep l N U g = 1
      simp [hc, hx]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DualKer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.dualKer :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (M' : Type) [AddCommGroup M'] [Module ℤ_[l] M'] (T : M →ₗ[ℤ_[l]] M'),
        LinearMap.range (LinearMap.lcomp ℤ_[l] (QZ l) T) = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker T).subtype) ∧
        ∀ p : Submodule ℤ_[l] M, Function.Surjective (LinearMap.lcomp ℤ_[l] (QZ l) p.subtype) := by
  intro l _ M _ _ M' _ _ T
  have hI := PropA.qzInj l
  refine ⟨?_, fun p g => ?_⟩
  · ext f
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨g, rfl⟩
      ext ⟨x, hx⟩
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.zero_apply]
      rw [LinearMap.mem_ker.mp hx, map_zero]
    · intro hf
      have hle : LinearMap.ker T ≤ LinearMap.ker f := by
        intro x hx
        have := LinearMap.congr_fun hf ⟨x, hx⟩
        simpa using this
      let g0 : LinearMap.range T →ₗ[ℤ_[l]] QZ l :=
        ((LinearMap.ker T).liftQ f hle).comp (LinearMap.quotKerEquivRange T).symm.toLinearMap
      obtain ⟨h, hh⟩ := hI.out (LinearMap.range T).subtype Subtype.val_injective g0
      refine ⟨h, ?_⟩
      ext x
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply]
      have := hh ⟨T x, LinearMap.mem_range_self T x⟩
      simp only [Submodule.subtype_apply] at this
      rw [this]
      simp [g0, LinearMap.quotKerEquivRange_symm_apply_image]
  · obtain ⟨h, hh⟩ := hI.out p.subtype Subtype.val_injective g
    refine ⟨h, ?_⟩
    ext x
    simpa using hh x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTransport
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem dt_val_lt_one {Ω Ω' : Type} [Field Ω] [Field Ω'] {σ : Ω ≃+* Ω'} {A : ValuationSubring Ω}
    {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A') (x : Ω) :
    A.valuation x < 1 ↔ A'.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω'), ← hA, ← map_inv₀, ← hA,
    map_eq_zero_iff _ σ.injective]

private theorem dt_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] {σ : Ω ≃+* Ω'}
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A')
    {g : G F Ω} {g' : G F' Ω'} (h : ∀ x, σ (g x) = g' (σ x)) (hg : g' ∈ Dec (F := F') A') :
    g ∈ Dec (F := F) A := by
  have h' : ∀ x, σ (g⁻¹ x) = g'⁻¹ (σ x) := fun x => by
    show σ (g.symm x) = g'.symm (σ x)
    rw [eq_comm, AlgEquiv.symm_apply_eq, ← h, AlgEquiv.apply_symm_apply]
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hA, hA, h']
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F') A').inv_mem hg) _

private theorem dt_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] {σ : Ω ≃+* Ω'}
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A')
    {g : G F Ω} {g' : G F' Ω'} (h : ∀ x, σ (g x) = g' (σ x)) (hg : g' ∈ Ine (F := F') A') :
    g ∈ Ine (F := F) A := by
  refine ⟨dt_dec hA h hg.1, fun x hx => ?_⟩
  rw [dt_val_lt_one hA, map_sub, h]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).1 ((A.valuation_le_one_iff _).1 hx)))

private theorem dt_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] (σ : Ω ≃+* Ω') (N : ℕ)
    {V : Subgroup (G F Ω)} {V' : Subgroup (G F' Ω')} (e : V' →* V) (he : Continuous e)
    (h : ∀ (u : V') x, σ ((e u).1 x) = u.1 (σ x)) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {ψ : V → M} (hψ : ψ ∈ XDual N V R M) : ψ ∘ e ∈ XDual N V' R M := by
  have hA : ∀ (A' : ValuationSubring Ω') x, x ∈ A'.comap σ.toRingHom ↔ σ x ∈ A' := fun _ _ => Iff.rfl
  obtain ⟨h1, h2, h3, h4⟩ := hψ
  refine ⟨h1.comp_continuous he, fun a b => ?_, fun A u hu => ?_, fun A hN u hu => ?_⟩
  · simp only [Function.comp_apply, map_mul, h2]
  · exact h3 (A.comap σ.toRingHom) _ (dt_ine (hA A) (h u) hu)
  · refine h4 (A.comap σ.toRingHom) ?_ _ (dt_dec (hA A) (h u) hu)
    rw [dt_val_lt_one (hA A), map_natCast]
    exact hN

theorem UpperTheory.V.Tower.dinfTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
        ∀ φ : G F' Ω' →* G F Ω, (∀ g x, σ (φ g x) = g (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) (U' : Subgroup (G F' Ω')),
          (cycU l U').map φ = cycU l U → ∃ Ψ : Dinf l N U ≃ₗ[ℤ_[l]] Dinf l N U', ∀ (ψ : Dinf l N U) (u' : cycU l U') (u : cycU l U), u.1 = φ u'.1 → (Ψ ψ).1 u' = ψ.1 u := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ h φ hφ l _ N U U' hU
  obtain ⟨φ₀, hc, hφ₀, -, hi, -⟩ := galTransport F Ω F' Ω' f σ h
  obtain rfl : φ₀ = φ := MonoidHom.ext fun g => AlgEquiv.ext fun x => σ.injective (by rw [hφ, hφ₀])
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : IsGalois F' Ω' := IsAlgClosure.isGalois F' Ω'
  have hemb : Topology.IsInducing φ₀ := (hc.isClosedEmbedding hi).isInducing
  let e : cycU l U' ≃* cycU l U := ((cycU l U').equivMapOfInjective φ₀ hi).trans (MulEquiv.subgroupCongr hU)
  have he : ∀ u, (e u).1 = φ₀ u.1 := fun _ => rfl
  have he' : ∀ u, φ₀ (e.symm u).1 = u.1 := fun u => by rw [← he, MulEquiv.apply_symm_apply]
  have c1 : Continuous e.toMonoidHom := (hc.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous e.symm.toMonoidHom := by
    refine continuous_induced_rng.2 (hemb.continuous_iff.2 ?_)
    exact continuous_subtype_val.congr fun u => (he' u).symm
  refine ⟨{ toFun := fun ψ => ⟨ψ.1 ∘ e.toMonoidHom, dt_mem σ N e.toMonoidHom c1 (fun u x => hφ u.1 x) ψ.2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun ψ => ⟨ψ.1 ∘ e.symm.toMonoidHom, dt_mem σ.symm N e.symm.toMonoidHom c2 (fun u x => ?_) ψ.2⟩
            left_inv := fun ψ => Subtype.ext (funext fun u => congrArg ψ.1 (e.apply_symm_apply u))
            right_inv := fun ψ => Subtype.ext (funext fun u => congrArg ψ.1 (e.symm_apply_apply u)) }, ?_⟩
  · show σ.symm ((e.symm u).1 x) = u.1 (σ.symm x)
    rw [RingEquiv.symm_apply_eq, ← he' u, hφ, RingEquiv.apply_symm_apply]
  · intro ψ u' u hu
    exact congrArg ψ.1 (Subtype.ext hu.symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Imports
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.desc :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal], e ≠ 0 → Procyc L Ω l → cycU l U = cycU l (galOf k L Ω) →
        ∃ Φ : Sha D e ≃ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e, IsDesc L D e U Φ.toLinearMap := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e U _ he hpro hcyc
  have hfam := galEmbFam k L Ω l
  have hcycE : ∀ h : G L Ω, cycZ k Ω l (galEmb k L Ω h) = cycZ L Ω l h := fun h => by
    rw [← MonoidHom.comp_apply, hfam.2.2.1]
  have hlift : ∀ σ ∈ galOf k L Ω, ∃ h : G L Ω, galEmb k L Ω h = σ := by
    intro σ hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, by ext x; rfl⟩
  have hmap : Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) = cycU l U := by
    rw [hcyc]
    ext σ
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · intro x
        exact g.commutes x
      · rw [MonoidHom.mem_ker, hcycE]
        exact (Subgroup.mem_inf.1 hg).2
    · intro hσ
      obtain ⟨hσG, hσK⟩ := Subgroup.mem_inf.1 hσ
      obtain ⟨h, rfl⟩ := hlift σ hσG
      refine ⟨h, Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker, ← hcycE]
      exact hσK
  obtain ⟨Ψ, hΨ⟩ := dinfTransport k Ω L Ω (algebraMap k L) (RingEquiv.refl Ω)
    (fun x => IsScalarTower.algebraMap_apply k L Ω x) (galEmb k L Ω) (fun g x => rfl)
    l l U ⊤ hmap
  have hdTw : ∀ (g : G k Ω) (χ : Dinf l l U) (w : cycU l U),
      ((dTw l l U e g χ : Dinf l l U) : cycU l U → QZ l) w =
        (((cycZ k Ω l ^ (-e)) g : ℤ_[l]ˣ) : ℤ_[l]) • (χ : cycU l U → QZ l) (conjHom (cycU l U) g w) := by
    intro g χ w
    rfl
  have hq : ∀ (h : G L Ω) (m : QZ l),
      qzG L Ω l e h m = (((cycZ L Ω l ^ (-e)) h : ℤ_[l]ˣ) : ℤ_[l]) • m := fun h m => rfl
  have hqE : ∀ (h : G L Ω) (m : QZ l),
      (((cycZ k Ω l ^ (-e)) (galEmb k L Ω h) : ℤ_[l]ˣ) : ℤ_[l]) • m = qzG L Ω l e h m := by
    intro h m
    rw [← hfam.2.2.2 e]
    rfl
  have hmemE : ∀ u : cycU l (⊤ : Subgroup (G L Ω)), galEmb k L Ω u ∈ cycU l U := fun u =>
    hmap ▸ Subgroup.mem_map_of_mem _ u.2
  let E : cycU l (⊤ : Subgroup (G L Ω)) → cycU l U := fun u => ⟨galEmb k L Ω u, hmemE u⟩
  have hEsurj : ∀ w : cycU l U, ∃ u, E u = w := by
    intro w
    have hw : (w : G k Ω) ∈ Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) := by
      rw [hmap]
      exact w.2
    obtain ⟨u, hu, huw⟩ := hw
    exact ⟨⟨u, hu⟩, Subtype.ext huw⟩
  have key : ∀ χ : Dinf l l U, χ ∈ ShaD l l U (galOf k L Ω) e ↔
      ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro χ
    have hX : ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        XDual l (Uinf L Ω l) ℤ_[l] (QZ l) := (Ψ χ).2
    have hΨE : ∀ u, ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) :
        cycU l (⊤ : Subgroup (G L Ω)) → QZ l) u = (χ : cycU l U → QZ l) (E u) :=
      fun u => hΨ χ u (E u) rfl
    constructor
    · intro hinv
      refine Submodule.mem_inf.2 ⟨hX, (Submodule.mem_iInf _).2 fun h => ?_⟩
      intro u u' huu
      rw [hΨE, hΨE]
      have hg : galEmb k L Ω h ∈ galOf k L Ω := fun x => h.commutes x
      have hinvg := (Representation.mem_invariants _ _).1 hinv ⟨_, hg⟩
      have h2 : ((dTw l l U e (galEmb k L Ω h) χ : Dinf l l U) : cycU l U → QZ l) (E u') =
          (χ : cycU l U → QZ l) (E u') :=
        congrArg (fun y : Dinf l l U => (y : cycU l U → QZ l) (E u')) hinvg
      rw [hdTw] at h2
      have hconj : conjHom (cycU l U) (galEmb k L Ω h) (E u') = E u := by
        apply Subtype.ext
        show (galEmb k L Ω h)⁻¹ * galEmb k L Ω u' * galEmb k L Ω h = galEmb k L Ω u
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        ext x
        show h⁻¹ ((u' : G L Ω) (h x)) = (u : G L Ω) x
        rw [show (u' : G L Ω) (h x) = h ((u : G L Ω) x) from huu x, AlgEquiv.aut_inv,
          AlgEquiv.symm_apply_apply]
      rw [hconj, hqE] at h2
      exact h2.symm
    · intro hE
      obtain ⟨_, hC⟩ := Submodule.mem_inf.1 hE
      rw [Submodule.mem_iInf] at hC
      refine (Representation.mem_invariants _ _).2 fun g => ?_
      obtain ⟨h, hh⟩ := hlift g g.2
      apply Subtype.ext
      funext w
      show ((dTw l l U e (g : G k Ω) χ : Dinf l l U) : cycU l U → QZ l) w = (χ : cycU l U → QZ l) w
      rw [hdTw]
      obtain ⟨u', rfl⟩ := hEsurj w
      have hu : h⁻¹ * (u' : G L Ω) * h ∈ cycU l (⊤ : Subgroup (G L Ω)) := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
          MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 u'.2).2, mul_one, inv_mul_cancel]
      have hcond := hC h ⟨_, hu⟩ u' (fun x => by
        show (u' : G L Ω) (h x) = h ((h⁻¹ * (u' : G L Ω) * h) x)
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      rw [hΨE, hΨE] at hcond
      have hconj : conjHom (cycU l U) (g : G k Ω) (E u') = E ⟨_, hu⟩ := by
        apply Subtype.ext
        show (g : G k Ω)⁻¹ * galEmb k L Ω u' * (g : G k Ω) = galEmb k L Ω (h⁻¹ * (u' : G L Ω) * h)
        rw [← hh, map_mul, map_mul, map_inv]
      rw [hconj, ← hh, hqE]
      exact hcond.symm
  have hR : ∀ x : Sha D e, resInf D e (x : H1 (qzTw D e)) ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro x
    rw [← resInfOnto L Ω l D e he hpro]
    exact Submodule.mem_map_of_mem x.2
  have hED : ∀ f, f ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) → f ∈ Dinf l l (⊤ : Subgroup (G L Ω)) :=
    fun f hf => (Submodule.mem_inf.1 hf).1
  let R0 : Sha D e →ₗ[ℤ_[l]] Dinf l l (⊤ : Subgroup (G L Ω)) :=
    LinearMap.codRestrict _ ((resInf D e).comp (Sha D e).subtype) (fun x => hED _ (hR x))
  let f : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e :=
    LinearMap.codRestrict _ (Ψ.symm.toLinearMap.comp R0) (fun x => (key _).2 (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hR x))
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : Ψ.symm (R0 x) = Ψ.symm (R0 y) := congrArg Subtype.val hxy
    have h2 : R0 x = R0 y := Ψ.symm.injective h1
    have h3 : resInf D e x = resInf D e y := congrArg Subtype.val h2
    exact Subtype.ext (resInfInj L Ω l D e he hpro h3)
  have hfsurj : Function.Surjective f := by
    intro χ
    have hm := (key (χ : Dinf l l U)).1 χ.2
    rw [← resInfOnto L Ω l D e he hpro] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    show Ψ.symm (R0 ⟨x, hx⟩) = χ
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hxe
  refine ⟨LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩, ?_⟩
  intro x u u' hu
  show ((Ψ.symm (R0 x) : Dinf l l U) : cycU l U → QZ l) u' = resInf D e x u
  rw [← hΨ (Ψ.symm (R0 x)) u u' hu, LinearEquiv.apply_symm_apply]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerUniq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem lu_key (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ)
    [Fact l.Prime] (hmu : HasMuQ l L) (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω]
    [IsScalarTower L L₁ Ω] [IsCyclotomicExtension {l ^ n} L L₁] :
    galOf L L₁ Ω = layU l L Ω (n - cZero l L) ∧ Module.finrank L L₁ = l ^ (n - cZero l L) := by
  haveI : IsAlgClosure L₁ Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.tower_top (K := L) L₁⟩
  have h1 : galOf L L₁ Ω = Un L Ω l n := by
    rw [galOfCyc L Ω l n L L₁, galOf_self]
  have h2 : Un L Ω l n = layU l L Ω (n - cZero l L) := by
    rcases le_total n (cZero l L) with h | h
    · rw [((muQ L Ω l).2.1 n).2 h, layU, ((muQ L Ω l).2.1 _).2 (by omega)]
    · rw [layU, Nat.add_sub_cancel' h]
  refine ⟨h1.trans h2, ?_⟩
  rw [← (galEmbTop L L₁ Ω).2.2, h1, h2, (layerGen L Ω l hmu).1]

theorem UpperTheory.V.Tower.layerUniq :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, IsLayer l m L (layF l L Ω m)) ∧
        (∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω] [IsScalarTower L L₁ Ω], IsLayer l m L L₁ → galOf L L₁ Ω = layU l L Ω m) ∧
        ∀ (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁], IsCyclotomicExtension {l ^ n} L L₁ → IsLayer l (n - cZero l L) L L₁ := by
  intro L Ω _ _ _ _ _ l hl hmu
  refine ⟨fun m => ?_, fun m L₁ _ _ _ _ _ h => ?_, fun n L₁ _ _ _ h => ?_⟩
  · haveI h := (fnCyc L Ω l (cZero l L + m)).1
    refine ⟨⟨_, h⟩, ?_⟩
    have := (lu_key L Ω l hmu (cZero l L + m) (layF l L Ω m)).2
    rwa [Nat.add_sub_cancel_left] at this
  · obtain ⟨⟨k, hk⟩, hf⟩ := h
    obtain ⟨h1, h2⟩ := lu_key L Ω l hmu k L₁
    rw [h1, Nat.pow_right_injective hl.out.two_le (h2.symm.trans hf)]
  · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
    haveI : FiniteDimensional L L₁ := Module.Finite.of_restrictScalars_finite ℚ L L₁
    let f : L₁ →ₐ[L] Ω := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    letI : Algebra L₁ Ω := f.toRingHom.toAlgebra
    haveI : IsScalarTower L L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    exact ⟨⟨n, h⟩, (lu_key L Ω l hmu n L₁).2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CokerDual
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LenDual
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.QzSep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem exists_qz_ne_zero_annihilators_of_ne_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (m : M) (hm : m ≠ 0) : ∃ x : QZ l, x ≠ 0 ∧ ∀ a : ℤ_[l], a • m = 0 → a • x = 0 := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hdec : ∀ (N : Type) [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) (ha : a ≠ 0) (y : N),
      a • y = 0 ↔ (l : ℤ_[l]) ^ a.valuation • y = 0 := by
    intro N _ _ a ha y
    conv_lhs => rw [PadicInt.unitCoeff_spec ha, mul_smul]
    exact (PadicInt.unitCoeff ha).isUnit.smul_eq_zero
  by_cases hex : ∃ r : ℕ, (l : ℤ_[l]) ^ r • m = 0
  · classical
    set r := Nat.find hex with hrdef
    have hr : (l : ℤ_[l]) ^ r • m = 0 := Nat.find_spec hex
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_smul] at hr
      exact hm hr
    obtain ⟨ι, hinj, hrange, hlin⟩ := zmodToQZ l r
    haveI : Fact (1 < l ^ r) := ⟨Nat.one_lt_pow hr0 hl1⟩
    have hι0 : ι 0 = 0 := by simpa using hlin 0 0
    refine ⟨ι 1, fun h => one_ne_zero (hinj (h.trans hι0.symm)), ?_⟩
    have hx : (l : ℤ_[l]) ^ r • ι 1 = 0 := by
      have := (hrange (ι 1)).mp ⟨1, rfl⟩
      exact_mod_cast this
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, zero_smul]
    · rw [hdec _ a a0] at ha ⊢
      have hle : r ≤ a.valuation := Nat.find_min' hex ha
      rw [← Nat.add_sub_cancel' hle, pow_add, mul_comm, mul_smul, hx, smul_zero]
  · push_neg at hex
    obtain ⟨ι, hinj, hrange, hlin⟩ := zmodToQZ l 1
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl1⟩
    have hι0 : ι 0 = 0 := by simpa using hlin 0 0
    refine ⟨ι 1, fun h => one_ne_zero (hinj (h.trans hι0.symm)), ?_⟩
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, zero_smul]
    · exact absurd ((hdec _ a a0 m).mp ha) (hex _)

theorem UpperTheory.V.Tower.qzSep :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (m : M), m ≠ 0 → ∃ f : M →ₗ[ℤ_[l]] QZ l, f m ≠ 0 := by
  intro l _ M _ _ m hm
  obtain ⟨x, hx0, hx⟩ := exists_qz_ne_zero_annihilators_of_ne_zero l M m hm
  set K := LinearMap.ker (LinearMap.toSpanSingleton ℤ_[l] M m) with hK
  have hle : K ≤ LinearMap.ker (LinearMap.toSpanSingleton ℤ_[l] (QZ l) x) := by
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha ⊢
    exact hx a ha
  let f := K.liftQ (LinearMap.toSpanSingleton ℤ_[l] M m) le_rfl
  let g := K.liftQ (LinearMap.toSpanSingleton ℤ_[l] (QZ l) x) hle
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot _ _ le_rfl)
  haveI := UpperTheory.V.PropA.qzInj l
  obtain ⟨h, hh⟩ := Module.Injective.out f hf g
  refine ⟨h, ?_⟩
  have h1 := hh (K.mkQ 1)
  simp only [f, g, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
    one_smul] at h1
  rw [h1]
  exact hx0
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem le_dual (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] :
    Module.length ℤ_[l] N ≤ Module.length ℤ_[l] (N →ₗ[ℤ_[l]] QZ l) := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length, ← Order.krullDim_orderDual]
  refine Order.krullDim_le_of_strictMono
    (fun p : (Submodule ℤ_[l] N)ᵒᵈ =>
      LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (OrderDual.ofDual p).subtype)) ?_
  intro a b hab
  change OrderDual.ofDual b < OrderDual.ofDual a at hab
  obtain ⟨hle, m, hmp, hmq⟩ := SetLike.lt_iff_le_and_exists.mp hab
  refine lt_of_le_of_ne ?_ ?_
  · intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    ext ⟨x, hx⟩
    have h := LinearMap.congr_fun hφ ⟨x, hle hx⟩
    simpa using h
  · intro heq
    have hm0 : (OrderDual.ofDual b).mkQ m ≠ 0 := by
      rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := qzSep l _ _ hm0
    have hmem : ψ ∘ₗ (OrderDual.ofDual b).mkQ ∈
        LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (OrderDual.ofDual b).subtype) := by
      rw [LinearMap.mem_ker]
      ext ⟨x, hx⟩
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hx]
    have hmem' := hmem
    simp only at heq
    rw [← heq, LinearMap.mem_ker] at hmem'
    exact hψ (by simpa using LinearMap.congr_fun hmem' ⟨m, hmp⟩)

private theorem exact_dual (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N] [Module ℤ_[l] N]
    (p : Submodule ℤ_[l] N) :
    Function.Exact (LinearMap.lcomp ℤ_[l] (QZ l) p.mkQ) (LinearMap.lcomp ℤ_[l] (QZ l) p.subtype) := by
  rw [LinearMap.exact_iff]
  have h := (dualKer l N (N ⧸ p) p.mkQ).1
  have hq := Submodule.ker_mkQ p
  generalize LinearMap.ker p.mkQ = q at h hq
  subst hq
  exact h.symm

private theorem simple_dual (l : ℕ) [hl : Fact l.Prime]
    (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [hN : IsSimpleModule ℤ_[l] N] :
    IsSimpleModule ℤ_[l] (N →ₗ[ℤ_[l]] QZ l) := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial ℤ_[l] N
  have hnu : (l : ℤ_[l]) ∈ nonunits ℤ_[l] :=
    (IsLocalRing.mem_maximalIdeal _).mp
      (by rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _)
  have hspan : ∀ s : N, s ≠ 0 → ∀ x : N, ∃ c : ℤ_[l], c • s = x := by
    intro s hs x
    have htop : Submodule.span ℤ_[l] {s} = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
        (by simpa [Submodule.span_singleton_eq_bot] using hs)
    exact Submodule.mem_span_singleton.mp (htop ▸ Submodule.mem_top)
  have hkill : ∀ s : N, (l : ℤ_[l]) • s = 0 := by
    intro s
    by_contra h
    obtain ⟨c, hc⟩ := hspan _ h s
    have hu : IsUnit (1 - c * (l : ℤ_[l])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mul_mem_nonunits_right hnu)
    have h0 : (1 - c * (l : ℤ_[l])) • s = 0 := by
      rw [sub_smul, one_smul, mul_smul, hc, sub_self]
    have hs0 : s = 0 := (hu.smul_eq_zero).mp h0
    exact h (by rw [hs0, smul_zero])
  obtain ⟨s, hs⟩ := exists_ne (0 : N)
  obtain ⟨φ0, hφ0⟩ := qzSep l N s hs
  obtain ⟨ι, hιinj, hιrange, hιsmul⟩ := zmodToQZ l 1
  haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact hl.out⟩
  have hrange : ∀ φ : N →ₗ[ℤ_[l]] QZ l, ∃ a, ι a = φ s := by
    intro φ
    refine (hιrange (φ s)).mpr ?_
    rw [pow_one, ← LinearMap.map_smul_of_tower, hkill, map_zero]
  have key : ∀ φ ψ : N →ₗ[ℤ_[l]] QZ l, φ ≠ 0 → ∃ z : ℤ_[l], ψ = z • φ := by
    intro φ ψ hφ
    have hφs : φ s ≠ 0 := by
      intro h
      apply hφ
      ext x
      obtain ⟨c, rfl⟩ := hspan s hs x
      simp [h]
    obtain ⟨a, ha⟩ := hrange φ
    obtain ⟨b, hb⟩ := hrange ψ
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hφs (by rw [← ha, map_zero])
    obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (b * a⁻¹)
    have hb' : b = PadicInt.toZModPow 1 (k : ℤ_[l]) * a := by
      rw [map_natCast, hk, inv_mul_cancel_right₀ ha0]
    refine ⟨(k : ℤ_[l]), ?_⟩
    ext x
    obtain ⟨c, rfl⟩ := hspan s hs x
    rw [map_smul, LinearMap.smul_apply, map_smul, ← hb, ← ha, hb', hιsmul, smul_comm]
  haveI : Nontrivial (N →ₗ[ℤ_[l]] QZ l) := ⟨⟨φ0, 0, fun h => hφ0 (by rw [h]; rfl)⟩⟩
  refine { eq_bot_or_eq_top := fun P => ?_ }
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    obtain ⟨φ, hφP, hφ0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    rw [eq_top_iff]
    intro ψ _
    obtain ⟨z, rfl⟩ := key φ ψ hφ0'
    exact P.smul_mem z hφP

theorem UpperTheory.V.Tower.lenDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M], Module.length ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) = Module.length ℤ_[l] M := by
  intro l _ M _ _
  by_cases hM : IsFiniteLength ℤ_[l] M
  · induction hM with
    | @of_subsingleton M' _ _ _ =>
      haveI : Subsingleton (M' →ₗ[ℤ_[l]] QZ l) :=
        ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      simp [Module.length_eq_zero]
    | @of_simple_quotient M' _ _ N _ _ ih =>
      have hS := simple_dual l (M' ⧸ N)
      have e1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
        N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      have e2 := Module.length_eq_add_of_exact (LinearMap.lcomp ℤ_[l] (QZ l) N.mkQ)
        (LinearMap.lcomp ℤ_[l] (QZ l) N.subtype)
        (fun f g h => by
          ext x
          exact LinearMap.congr_fun h x)
        ((dualKer l M' M' (LinearMap.id)).2 N) (exact_dual l N)
      rw [e1, e2, ih, Module.length_eq_one (R := ℤ_[l]) (M := M' ⧸ N),
        Module.length_eq_one (R := ℤ_[l]) (M := (M' ⧸ N) →ₗ[ℤ_[l]] QZ l), add_comm]
  · have h1 : Module.length ℤ_[l] M = ⊤ := by
      rw [← not_ne_iff, Module.length_ne_top_iff]
      exact hM
    have h2 := le_dual l M
    rw [h1, top_le_iff] at h2
    rw [h1, h2]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.cokerDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (g : Module.End ℤ_[l] M) (t : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)), (∀ x φ, t x φ = x (g φ)) →
        cokerLen t = Module.length ℤ_[l] (LinearMap.ker g) := by
  intro l _ M _ _ g t h
  have ht : t = LinearMap.lcomp ℤ_[l] (QZ l) g := LinearMap.ext fun x => LinearMap.ext fun φ => h x φ
  obtain ⟨h1, h2⟩ := UpperTheory.V.Tower.dualKer l M M g
  have hr : LinearMap.range t
      = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker g).subtype) := by
    rw [ht]; exact h1
  rw [← UpperTheory.V.Tower.lenDual l (LinearMap.ker g)]
  exact ((Submodule.quotEquivOfEq _ _ hr).trans
    (LinearMap.quotKerEquivOfSurjective _ (h2 (LinearMap.ker g)))).length_eq
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ShaDGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.shaDGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U V : Subgroup (G k Ω)) [U.Normal] (e : ℤ) (γ : G k Ω), IsClosed (U : Set (G k Ω)) → V ≤ U → IsGen l V γ →
        ShaD l N U V e = LinearMap.ker (dTw l N U e γ - 1) ∧ ShaD l N U V e = LinearMap.ker (dTw l N U e γ⁻¹ - 1) := by
  intro k Ω _ _ _ _ _ l hl N U V _ e γ hU hVU hγ
  have key : ∀ φ : Dinf l N U, dTw l N U e γ φ = φ → ∀ v ∈ V, dTw l N U e v φ = φ := by
    intro φ hφ v hv
    obtain ⟨n, hn⟩ := (dinfNil k Ω l N U hU φ.1 φ.2).1
    obtain ⟨r, hr⟩ := (dinfTors k Ω l N U).1 hU φ
    have hlev : ∀ w ∈ U, cycZ k Ω l w ∈ KStar.TotallyRealRoots.princ l (max n r) → dTw l N U e w φ = φ := by
      intro w hw hc
      have h1 : dRep l N U w φ = φ :=
        Subtype.ext (hn w ⟨hw, KStar.TotallyRealRoots.princ_anti (le_max_left n r) hc⟩)
      have h2 : cycZ k Ω l w ^ (-e) ∈ KStar.TotallyRealRoots.princ l r :=
        Subgroup.zpow_mem _ (KStar.TotallyRealRoots.princ_anti (le_max_right n r) hc) _
      rw [KStar.TotallyRealRoots.mem_princ] at h2
      obtain ⟨c, hc'⟩ := h2
      rw [dTw_apply, LinearMap.smul_apply, h1, sub_eq_iff_eq_add.1 hc', add_smul, one_smul, mul_comm, mul_smul, hr,
        smul_zero, zero_add]
    have hz : ∀ j : ℤ, dTw l N U e (γ ^ j) φ = φ := by
      intro j
      let S : Subgroup (G k Ω) :=
        { carrier := {g | dTw l N U e g φ = φ}
          mul_mem' := fun {a b} ha hb => by
            show dTw l N U e (a * b) φ = φ
            rw [map_mul, Module.End.mul_apply, show dTw l N U e b φ = φ from hb]; exact ha
          one_mem' := by
            show dTw l N U e 1 φ = φ
            rw [map_one]; rfl
          inv_mem' := fun {a} ha => by
            show dTw l N U e a⁻¹ φ = φ
            conv_lhs => rw [← show dTw l N U e a φ = φ from ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
      exact S.zpow_mem (show γ ∈ S from hφ) j
    have hcl : cycZ k Ω l v ∈ closure ((Subgroup.zpowers (cycZ k Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
      hγ.2 ⟨v, hv, rfl⟩
    have hop : IsOpen ((fun x : ℤ_[l]ˣ => x⁻¹ * cycZ k Ω l v) ⁻¹' (KStar.TotallyRealRoots.princ l (max n r) : Set ℤ_[l]ˣ)) :=
      (KStar.TotallyRealRoots.isOpen_princ _).preimage (by fun_prop)
    obtain ⟨x, hx, j, rfl⟩ := mem_closure_iff.1 hcl _ hop (by simp [one_mem])
    have h3 := hlev ((γ ^ j)⁻¹ * v) (U.mul_mem (U.inv_mem (U.zpow_mem (hVU hγ.1) j)) (hVU hv))
      (by rw [map_mul, map_inv, map_zpow]; exact hx)
    have h4 : v = γ ^ j * ((γ ^ j)⁻¹ * v) := by group
    rw [h4, map_mul, Module.End.mul_apply, h3, hz]
  constructor
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    exact ⟨fun h => h ⟨γ, hγ.1⟩, fun h v => key φ h v.1 v.2⟩
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    refine ⟨fun h => h ⟨γ⁻¹, V.inv_mem hγ.1⟩, fun h v => key φ ?_ v.1 v.2⟩
    conv_lhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.GenGal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.existsGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∃ γ, IsGen l U γ := by
  intro k Ω _ _ _ _ _ l _ U hU hcond
  have hclosed : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hU.isCompact.image (continuous_cycZ k Ω l)).isClosed
  have hc : l ≠ 2 ∨ U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l 2 := by
    by_cases hl : l = 2
    · rcases hcond with h | h
      · exact absurd hl h
      · right
        rw [Subgroup.map_le_iff_le_comap]
        intro x hx
        have hx' := h hx
        simp only [gamU, levU, qExp, if_pos hl, Subgroup.mem_inf] at hx'
        exact hx'.2
    · exact Or.inl hl
  obtain ⟨γ', hγ', hle⟩ := UpperTheory.V.Kum.existsGen l (U.map (cycZ k Ω l)) hclosed hc
  obtain ⟨γ, hγU, rfl⟩ := Subgroup.mem_map.mp hγ'
  exact ⟨γ, hγU, hle⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.genGal :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], IsClosed (galOf k L Ω : Set (G k Ω)) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤) ∧
        (Procyc L Ω l → ∃ γ, IsGen l (galOf k L Ω) γ) := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hcl : IsClosed (galOf k L Ω : Set (G k Ω)) :=
    Subgroup.isClosed_of_isOpen _ (galEmbTop k L Ω).2.1
  have hχ : ∀ g : G L Ω, cycZ k Ω l (galEmb k L Ω g) = cycZ L Ω l g := fun g =>
    DFunLike.congr_fun (galEmbFam k L Ω l).2.2.1 g
  have hiff : Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤ := by
    by_cases h : l = 2
    · subst h
      refine or_congr_right ?_
      rw [← range_galEmb]
      constructor
      · rintro h _ ⟨g, rfl⟩
        refine ⟨trivial, ?_⟩
        show cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2
        rw [hχ]
        exact h g
      · intro h g
        have h' : cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2 := (h ⟨g, rfl⟩).2
        rw [hχ] at h'
        exact h'
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  exact ⟨hcl, hiff, fun h => UpperTheory.V.Tower.existsGen k Ω l _ hcl (hiff.1 h)⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

noncomputable section

namespace UpperTheory.V.Tower

section Step0

variable {l : ℕ} [Fact l.Prime] {L₀ : Type} [Field L₀] [NumberField L₀] {Ω : Type} [Field Ω] [Algebra L₀ Ω] [IsAlgClosure L₀ Ω]

theorem step0 (hμ : HasMuQ l L₀) {γ : G L₀ Ω} (hγ : IsGen l ⊤ γ) {e : ℤ} (he : e ≠ 0) (m : ℕ) (L₁ : Type) [Field L₁]
    [NumberField L₁] [Algebra L₀ L₁] (hL : IsLayer l m L₀ L₁) :
    shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L₀
  haveI : FiniteDimensional L₀ L₁ := Module.Finite.of_restrictScalars_finite ℚ L₀ L₁
  let j : L₁ →ₐ[L₀] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra L₁ Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Algebra.IsAlgebraic L₀ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := L₀) L₁⟩
  obtain ⟨D⟩ := Formalism.GaloisCohomology.ldataExists L₁ Ω l
  have hμ₁ : HasMuQ l L₁ := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨_, hζ.map_of_injective (algebraMap L₀ L₁).injective⟩
  have hU := (layerUniq L₀ Ω l hμ).2.1 m L₁ hL
  obtain ⟨Φ, -⟩ := desc L₀ L₁ Ω l D e ⊤ he ((muQ L₁ Ω l).2.2.2.1 hμ₁).2 (by rw [hU, cycU_levU])
  have hg := ((layerGen L₀ Ω l hμ).2 γ hγ).2.2 m
  rw [← hU] at hg
  rw [← shaLen_eq_shaInv D, shaLen, Φ.length_eq, (shaDGen L₀ Ω l l ⊤ _ e _ isClosed_univ le_top hg).2, ← map_pow]
  exact (cokerDual l _ _ _ fun x φ => by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, xTw_apply_apply]; rfl).symm


variable (l L₀ Ω) in
theorem exists_descends (hμ : HasMuQ l L₀) : ∃ γ : G L₀ Ω, IsGen l ⊤ γ ∧
    PropA.IsLevel l (cycZ L₀ Ω l γ : ℤ_[l]ˣ) (cZero l L₀) ∧ (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ cZero l L₀)) ∧
    ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  obtain ⟨γ, hγ⟩ := (genGal L₀ L₀ Ω l).2.2 ((muQ L₀ Ω l).2.2.2.1 hμ).2
  rw [galOf_self] at hγ
  exact ⟨γ, hγ, ((layerGen L₀ Ω l hμ).2 γ hγ).1, ((muQ L₀ Ω l).1 _).2 le_rfl, fun e he m L₁ _ _ _ hL =>
    step0 hμ hγ (by omega) m L₁ hL⟩


end Step0

end UpperTheory.V.Tower

end

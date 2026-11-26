module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLattice

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
noncomputable section

namespace GlobalTheory.CompanionTheory.DictLoc

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

def Cp (A : Type) : Type := A

section Model

theorem exists_model_field {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [Field A] [Algebra K A] [FiniteDimensional K A] [TopologicalSpace A] [IsModuleTopology K A] :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ := by
  haveI : CompleteSpace K := inferInstance
  letI fL : Field (Cp A) := ‹Field A›
  letI aL : Algebra K (Cp A) := ‹Algebra K A›
  haveI : FiniteDimensional K (Cp A) := ‹FiniteDimensional K A›
  haveI : Algebra.IsAlgebraic K (Cp A) := Algebra.IsAlgebraic.of_finite K (Cp A)
  letI nL : NontriviallyNormedField (Cp A) := spectralNorm.nontriviallyNormedField K (Cp A)
  letI mL : NormedAlgebra K (Cp A) := spectralNorm.normedAlgebra K (Cp A)
  haveI uL : IsUltrametricDist (Cp A) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := Cp A))
  haveI pL : ProperSpace (Cp A) := FiniteDimensional.proper K (Cp A)
  haveI : IsModuleTopology K (Cp A) := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  let f : A ≃ₗ[K] Cp A := LinearEquiv.refl K A
  refine ⟨Cp A, nL, uL, pL, RingEquiv.refl A, IsModuleTopology.continuous_of_linearMap f.toLinearMap,
    IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap, fun c x => ?_⟩
  exact (spectralNorm_eq_of_equiv (K := K) (L := Cp A) c x).symm

theorem isField_tensor_of_no_algHom {F K E : Type} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    (h2 : Module.finrank F E = 2) (hn : IsEmpty (E →ₐ[F] K)) : IsField (K ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hA : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, h2]
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] E)
  by_cases hb : m = ⊥
  · subst hb
    exact ((RingEquiv.quotientBot (K ⊗[F] E)).symm.toMulEquiv.isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient ⊥).1 hm))
  · exfalso
    letI := Ideal.Quotient.field m
    let φ : (K ⊗[F] E) →ₐ[K] (K ⊗[F] E) ⧸ m := Ideal.Quotient.mkₐ K m
    have hs : Function.Surjective φ := Ideal.Quotient.mkₐ_surjective K m
    have h3 := LinearMap.finrank_range_add_finrank_ker φ.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, hA] at h3
    have hk : 0 < Module.finrank K (LinearMap.ker φ.toLinearMap) := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      haveI : Nontrivial (LinearMap.ker φ.toLinearMap) :=
        ⟨⟨⟨x, (Ideal.Quotient.eq_zero_iff_mem.2 hx)⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
      exact Module.finrank_pos
    haveI : Module.Finite K ((K ⊗[F] E) ⧸ m) := Module.Finite.of_surjective φ.toLinearMap hs
    have hq : 0 < Module.finrank K ((K ⊗[F] E) ⧸ m) := Module.finrank_pos
    have h1 : Module.finrank K ((K ⊗[F] E) ⧸ m) = 1 := by omega
    have hbj : Function.Bijective (Algebra.ofId K ((K ⊗[F] E) ⧸ m)) :=
      ⟨(algebraMap K _).injective, fun y => by
        have : (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
        have hy : y ∈ (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) := this ▸ Algebra.mem_top
        obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
        exact ⟨a, ha⟩⟩
    let ε : K ≃ₐ[K] (K ⊗[F] E) ⧸ m := AlgEquiv.ofBijective _ hbj
    exact hn.false (((ε.symm.toAlgHom.comp φ).restrictScalars F).comp Algebra.TensorProduct.includeRight)

end Model

section Main

theorem exists_model {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [TopologicalSpace A] [IsModuleTopology K A] (hA : IsField A) :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ :=
  letI := hA.toField
  exists_model_field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

def sigEquiv (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) : (K ⊗[F] E) ≃ₐ[K] (K ⊗[F] E) :=
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) σ) (Algebra.TensorProduct.map (AlgHom.id K K) σ)
    (by ext x; simp [h]) (by ext x; simp [h])

theorem sigEquiv_apply (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigEquiv K h y = sigR K σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem sigR_sigR (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigR K σ (sigR K σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h x)

theorem properSpace_Fv (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (Fv F v) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.tjcosets_finite v

theorem charZero_Fv : CharZero (Fv F v) :=
  ((algebraMap F (Fv F v)).charZero_iff (algebraMap F (Fv F v)).injective).1 inferInstance

end Main

section Dict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}


open Formalism.UG (bc UJ cT) in
theorem exists_equiv_UG {L : Type} [Field L] [TopologicalSpace L] (e : (Fv F v ⊗[F] E) ≃+* L) (he : Continuous e)
    (he' : Continuous e.symm) :
    Nonempty (GLoc σ J v ≃ₜ* CompanionTheory.Rg.Fl.UG (e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom))
      ((JR (Fv F v) J).map e)) := by
  set s : L →+* L := e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom) with hs
  have e1 : ∀ x : GL (Fin n) L, bc e.toRingHom (bc e.symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.apply_symm_apply _)
  have e2 : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), bc e.symm.toRingHom (bc e.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.symm_apply_apply _)
  have key : ∀ x : GL (Fin n) (Fv F v ⊗[F] E),
      (cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1).map e =
        (((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1) := fun x => by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    exact Matrix.ext fun i j => by simp [cT, hs, bc]
  have mem : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), x ∈ HR (Fv F v) σ J ↔
      bc e.toRingHom x ∈ CompanionTheory.Rg.Fl.UG s ((JR (Fv F v) J).map e) := fun x => by
    change cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1 = JR (Fv F v) J ↔
      ((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1 = (JR (Fv F v) J).map e
    rw [← key]
    exact (Matrix.map_injective e.injective).eq_iff.symm
  have c1 : Continuous (bc (n := Fin n) e.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he
  have c2 : Continuous (bc (n := Fin n) e.symm.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he'
  have hemb := isEmbedding_matHom (Fv F v) σ J
  exact ⟨{ toFun := fun g => ⟨bc e.toRingHom (matHom _ σ J g), (mem _).1 g.2⟩
           invFun := fun u => (⟨bc e.symm.toRingHom u.1, (mem _).2 (by rw [e1]; exact u.2)⟩ : HR (Fv F v) σ J)
           left_inv := fun g => matHom_injective _ σ J (e2 _)
           right_inv := fun u => Subtype.ext (e1 _)
           map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul])
           continuous_toFun := (c1.comp hemb.continuous).subtype_mk _
           continuous_invFun := hemb.continuous_iff.2 (c2.comp continuous_subtype_val) }⟩

end Dict


open GlobalTheory.LFun.InertChart in
theorem stDict : CompanionTheory.Rg.Fl.StDict := by
  intro F E _ _ _ _ _ σ h n J hJ v
  letI nf : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI pf : ProperSpace (Fv F v) := properSpace_Fv v
  haveI uf : IsUltrametricDist (Fv F v) := inferInstance
  haveI cf : CharZero (Fv F v) := charZero_Fv
  by_cases hs : Nonempty (E →ₐ[F] Fv F v)
  · obtain ⟨τ⟩ := hs
    exact ⟨Fv F v, nf, uf, pf, cf, Or.inl ⟨splitEquiv h hJ τ⟩⟩
  · have hf : IsField (Fv F v ⊗[F] E) := isField_tensor_of_no_algHom h.2.2.1 (not_nonempty_iff.1 hs)
    haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    obtain ⟨L, nL, uL, pL, e, he, he', hn⟩ := exists_model (K := Fv F v) (A := Fv F v ⊗[F] E) hf
    have hcc : ∀ x, σ (σ x) = x := conj_conj h
    have hss : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := sigR_sigR _ hcc
    have hi : ∀ x : E, sigR (Fv F v) σ (inclR (Fv F v) x) = inclR (Fv F v) (σ x) := fun _ => rfl
    have hinj : Function.Injective (e.toRingHom.comp (inclR (Fv F v))) := RingHom.injective (e.toRingHom.comp (inclR (Fv F v)))
    have hL : CharZero L :=
      let ϕ : Fv F v →+* L := e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
      (ϕ.charZero_iff ϕ.injective).1 cf
    refine ⟨L, nL, uL, pL, hL, Or.inr ⟨_, (JR (Fv F v) J).map e, fun x => ?_, fun x => ?_, ?_, ?_, ?_,
      exists_equiv_UG e he he'⟩⟩
    · simp [hss]
    · have := hn (sigEquiv (Fv F v) hcc) (e.symm x)
      simpa [sigEquiv_apply] using this
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := not_forall.1 (conj_ne h)
      refine ⟨e (inclR (Fv F v) x), fun ee => hx (hinj ?_)⟩
      simpa [hi] using ee
    · refine Matrix.ext fun i j => ?_
      simp [JR, hi, hJ.1 i j]
    · have : ((JR (Fv F v) J).map e).det = (e.toRingHom.comp (inclR (Fv F v))) J.det := by
        rw [RingHom.map_det]; rfl
      rw [this]
      exact (map_ne_zero_iff _ hinj).2 hJ.2

end GlobalTheory.CompanionTheory.DictLoc

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DictionaryStatement : StDict := by
  first | exact @GlobalTheory.CompanionTheory.DictLoc.stDict | exact GlobalTheory.CompanionTheory.DictLoc.stDict | (intros; apply GlobalTheory.CompanionTheory.DictLoc.stDict <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatement
noncomputable section

open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult

namespace GlobalTheory.CompanionTheory.FactorIso

theorem stIso : StIso := by
  intro G G₁ H _ _ _ _ _ _ π hπ j p hj hpj hc W hW
  haveI := hπ.complete
  have hu : IsUnitaryRep (π.comp j) := isUnitaryRep_comp hπ.unitary hj
  refine ⟨⟨W, hW.1.rep, isIrrUnitary_rep hu hW⟩, ?_⟩
  show isoPart hW.1.rep (π.comp j) ⊤ = ⊤
  have hsub : IsSubrep (π.comp j) (isoPart hW.1.rep (π.comp j) ⊤) := isSubrep_isoPart
  have hker : ∀ k, p k = 1 → ∀ v ∈ isoPart hW.1.rep (π.comp j) ⊤,
      π k v ∈ isoPart hW.1.rep (π.comp j) ⊤ := by
    intro k hk v hv
    have hle : isoPart hW.1.rep (π.comp j) ⊤ ≤
        (isoPart hW.1.rep (π.comp j) ⊤).comap (π k : H →ₗ[ℂ] H) :=
      isoPart_le (hsub.1.preimage (π k).continuous) fun T hT x =>
        apply_mem_isoPart (T := (π k).comp T) (mem_homIn_top.2 fun g y => by
          have hcomm : π k * π (j g) = π (j g) * π k := by
            rw [← map_mul, ← map_mul, (hc g k hk).eq]
          have hT' := hT.2 g y
          simp only [ContinuousLinearMap.comp_apply, hT', MonoidHom.comp_apply]
          exact DFunLike.congr_fun hcomm (T y)) x
    exact hle hv
  have hinv : IsSubrep π (isoPart hW.1.rep (π.comp j) ⊤) := by
    refine ⟨hsub.1, fun g v hv => ?_⟩
    have hg : g = j (p g) * ((j (p g))⁻¹ * g) := by group
    have h1 := hsub.2 (p g) _ (hker ((j (p g))⁻¹ * g) (by simp [hpj]) v hv)
    rw [hg, map_mul]
    simpa using h1
  rcases hπ.irred.2 _ hinv with h | h
  · exfalso
    apply hW.2.1
    rw [eq_bot_iff]
    intro w hw
    have hm : W.subtypeL ∈ homIn hW.1.rep (π.comp j) ⊤ := mem_homIn_top.2 fun _ _ => rfl
    have := apply_mem_isoPart hm ⟨w, hw⟩
    rw [h] at this
    simpa using this
  · exact h

end GlobalTheory.CompanionTheory.FactorIso

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IsomorphismStatement : StIso := by
  first | exact @GlobalTheory.CompanionTheory.FactorIso.stIso | exact GlobalTheory.CompanionTheory.FactorIso.stIso | (intros; apply GlobalTheory.CompanionTheory.FactorIso.stIso <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatement
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

variable {G G' : Type} [Group G] [Group G']

def cosetEquiv (e : G ≃* G') (K : Subgroup G) : G ⧸ K ≃ G' ⧸ K.map e.toMonoidHom :=
  Quotient.congr (ra := QuotientGroup.leftRel K) (rb := QuotientGroup.leftRel (K.map e.toMonoidHom))
    e.toEquiv (by
      intro a b
      have h : (e.toEquiv a)⁻¹ * e.toEquiv b = e.toMonoidHom (a⁻¹ * b) := by simp
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, h]
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm)

lemma cosetEquiv_smul (e : G ≃* G') (K : Subgroup G) (g : G) (x : G ⧸ K) :
    cosetEquiv e K (g • x) = e g • cosetEquiv e K x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change ((e (g * a) : G') : G' ⧸ K.map e.toMonoidHom) = ((e g * e a : G') : G' ⧸ K.map e.toMonoidHom)
    rw [map_mul]

theorem stSepMove : StSepMove := by
  intro G G' _ _ e K hK S
  classical
  let φ := cosetEquiv e K
  obtain ⟨Γ', hfin, hstab, hsep⟩ := hK (S.image φ)
  let Γ : Subgroup G := Γ'.comap e.toMonoidHom
  have hmem : ∀ γ : Γ, e (γ : G) ∈ Γ' := fun γ => γ.2
  have hsymm : ∀ γ' : Γ', e.symm (γ' : G') ∈ Γ := fun γ' => by
    change e (e.symm (γ' : G')) ∈ Γ'
    simpa using γ'.2
  have hact : ∀ (γ : Γ) (x : G ⧸ K), φ (γ • x) = (⟨e (γ : G), hmem γ⟩ : Γ') • φ x := fun γ x =>
    cosetEquiv_smul e K (γ : G) x
  refine ⟨Γ, ?_, ?_, ?_⟩
  · let f : MulAction.orbitRel.Quotient Γ' (G' ⧸ K.map e.toMonoidHom) →
        MulAction.orbitRel.Quotient Γ (G ⧸ K) :=
      Quotient.map' φ.symm (by
        rintro a b ⟨γ', rfl⟩
        refine ⟨⟨e.symm (γ' : G'), hsymm γ'⟩, ?_⟩
        apply φ.injective
        change φ (_ • φ.symm b) = φ (φ.symm (γ' • b))
        rw [hact]
        have h : (⟨e (e.symm (γ' : G')), hmem ⟨e.symm (γ' : G'), hsymm γ'⟩⟩ : Γ') = γ' :=
          Subtype.ext (e.apply_symm_apply _)
        rw [h, φ.apply_symm_apply, φ.apply_symm_apply])
    refine Finite.of_surjective f ?_
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      exact ⟨Quotient.mk'' (φ x),
        congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel Γ (G ⧸ K))) (φ.symm_apply_apply x)⟩
  · intro x
    let f : MulAction.stabilizer Γ x → MulAction.stabilizer Γ' (φ x) := fun γ =>
      ⟨⟨e ((γ : Γ) : G), hmem γ⟩, by
        rw [MulAction.mem_stabilizer_iff, ← hact, MulAction.mem_stabilizer_iff.mp γ.2]⟩
    refine Finite.of_injective f ?_
    intro a b hab
    have h := congrArg (fun c : MulAction.stabilizer Γ' (φ x) => ((c : Γ') : G')) hab
    exact Subtype.ext (Subtype.ext (e.injective h))
  · intro x hx y hy γ hxy
    apply φ.injective
    exact hsep (φ x) (Finset.mem_image_of_mem φ hx) (φ y) (Finset.mem_image_of_mem φ hy)
      ⟨e (γ : G), hmem γ⟩ (by rw [← hact, hxy])

end GlobalTheory.CompanionTheory.RgFl
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SeparatedMovingStatement : StSepMove := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSepMove | exact GlobalTheory.CompanionTheory.RgFl.stSepMove | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSepMove <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OperatorStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OperatorStatement
open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgFl

variable {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)}

def evalHom (δ : G →* (X →L[ℂ] X)) (ρ : G →* (H →L[ℂ] H)) (u : X) : homIn δ ρ ⊤ →ₗ[ℂ] H where
  toFun T := T.1 u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_evalHom (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) (y : X)
    (T : homIn δ ρ ⊤) : ‖evalHom δ ρ y T‖ = ‖y‖ * ‖evalHom δ ρ u T‖ := by
  change ‖T.1 y‖ = ‖y‖ * ‖T.1 u‖
  rw [norm_apply_eq hδ hρ T.2 y, norm_apply_eq hδ hρ T.2 u, hu, mul_one, mul_comm]

theorem evalHom_injective (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) :
    Function.Injective (evalHom δ ρ u) := by
  refine (injective_iff_map_eq_zero _).2 fun T hT => Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  have h := norm_evalHom hδ hρ hu x T
  rw [hT, norm_zero, mul_zero] at h
  exact norm_eq_zero.1 h

theorem exists_op_unit (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y : X) {u : X} (hu : ‖u‖ = 1) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪u, x⟫_ℂ • T y := by
  have hinj := evalHom_injective hδ hρ hu
  let S : Submodule ℂ H := LinearMap.range (evalHom δ ρ u)
  let e := LinearEquiv.ofInjective (evalHom δ ρ u) hinj
  let L : S →ₗ[ℂ] H := evalHom δ ρ y ∘ₗ e.symm.toLinearMap
  have hL : ∀ v : S, ‖L v‖ ≤ ‖y‖ * ‖v‖ := fun v => by
    have h := norm_evalHom hδ hρ hu y (e.symm v)
    have h2 : evalHom δ ρ u (e.symm v) = v := congrArg Subtype.val (e.apply_symm_apply v)
    rw [h2] at h
    exact h.le
  have hLe : ∀ T : homIn δ ρ ⊤, L ⟨T.1 u, T, rfl⟩ = T.1 y := fun T => by
    have h : e.symm ⟨T.1 u, T, rfl⟩ = T := e.symm_apply_apply T
    change evalHom δ ρ y (e.symm ⟨T.1 u, T, rfl⟩) = T.1 y
    rw [h]
    rfl
  let K : Submodule ℂ H := S.topologicalClosure
  haveI : IsClosed (K : Set H) := S.isClosed_topologicalClosure
  haveI : CompleteSpace K := IsClosed.completeSpace_coe (s := (K : Set H))
  let i : S →ₗᵢ[ℂ] K := ⟨Submodule.inclusion S.le_topologicalClosure, fun _ => rfl⟩
  have hd : DenseRange i.toContinuousLinearMap := by
    refine Topology.IsInducing.subtypeVal.dense_iff.2 fun w => closure_mono (fun z hz => ?_) w.2
    exact ⟨⟨z, S.le_topologicalClosure hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  let B : K →L[ℂ] H := (L.mkContinuous ‖y‖ hL).extend i.toContinuousLinearMap
  have hB : ∀ v : S, B (i v) = L v := fun v =>
    ((L.mkContinuous ‖y‖ hL).extend_eq hd i.isometry.isUniformInducing v)
  refine ⟨B ∘L K.orthogonalProjection, fun T hT x => ?_⟩
  have hmem : ⟪u, x⟫_ℂ • T u ∈ K := K.smul_mem _ (S.le_topologicalClosure ⟨⟨T, hT⟩, rfl⟩)
  have horth : T x - ⟪u, x⟫_ℂ • T u ∈ Kᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    rintro _ ⟨T', rfl⟩
    change ⟪T'.1 u, T x - ⟪u, x⟫_ℂ • T u⟫_ℂ = 0
    rw [inner_sub_right, inner_smul_right, inner_eq_be hδ hρ hT T'.2, inner_eq_be hδ hρ hT T'.2,
      inner_self_eq_norm_sq_to_K, hu]
    simp [mul_comm]
  have hproj : K.orthogonalProjection (T x) = ⟪u, x⟫_ℂ • i ⟨T u, ⟨T, hT⟩, rfl⟩ :=
    Subtype.ext (Submodule.eq_starProjection_of_mem_orthogonal hmem horth)
  change B (K.orthogonalProjection (T x)) = _
  rw [hproj, map_smul, hB, hLe ⟨T, hT⟩]

theorem exists_op (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y ξ : X) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪ξ, x⟫_ℂ • T y := by
  by_cases h0 : ξ = 0
  · exact ⟨0, fun T _ x => by simp [h0]⟩
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hn' : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨A, hA⟩ := exists_op_unit hδ hρ y (u := (‖ξ‖ : ℂ)⁻¹ • ξ) (by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn])
  refine ⟨(‖ξ‖ : ℂ) • A, fun T hT x => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hA T hT, inner_smul_left, smul_smul, map_inv₀, Complex.conj_ofReal,
    ← mul_assoc, mul_inv_cancel₀ hn', one_mul]

theorem stOp : StOp := by
  intro G X H _ _ _ _ _ _ _ δ ρ hδ hρ _
  choose A hA using fun y ξ : X => exists_op (H := H) hδ hρ y ξ
  exact ⟨A, hA⟩

end GlobalTheory.CompanionTheory.RgFl
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OperatorStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.OperatorStatement : StOp := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stOp | exact GlobalTheory.CompanionTheory.RgFl.stOp | (intros; apply GlobalTheory.CompanionTheory.RgFl.stOp <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter Matrix
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DefiniteForm

open CompanionTheory.Rg.Fl

theorem cT_congr {R : Type} [CommRing R] (s : R →+* R) {n : ℕ}
    (Q Qi D J J' Δ : Matrix (Fin n) (Fin n) R) (hQ : Q * Qi = 1)
    (h1 : Formalism.UG.cT s Q * J * Q = Δ) (h2 : Formalism.UG.cT s D * J' * D = Δ) :
    Formalism.UG.cT s (D * Qi) * J' * (D * Qi) = J := by
  calc Formalism.UG.cT s (D * Qi) * J' * (D * Qi)
      = Formalism.UG.cT s Qi * (Formalism.UG.cT s D * J' * D) * Qi := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT s Qi * (Formalism.UG.cT s Q * J * Q) * Qi := by rw [h1, h2]
    _ = Formalism.UG.cT s (Q * Qi) * J * (Q * Qi) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_large_sq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (a : Fin n → F) (ha : ∀ i, a i ≠ 0) (B : ℝ) :
    ∃ N : ℕ, B < N ∧ ∀ i, ∃ c : v.adicCompletion F,
      c * c * algebraMap F (v.adicCompletion F) (a i) = algebraMap F (v.adicCompletion F) (a i + N) := by
  set M : ℕ := Ideal.absNorm v.asIdeal with hM
  have hM0 : M ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hM1 : M ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hM2 : 1 < M := by omega
  have hmem : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  have hval : Valued.v ((M : ℕ) : v.adicCompletion F) < 1 := by
    have e : ((M : ℕ) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ((M : ℕ) : 𝓞 F)) := by simp
    have e2 : ∀ y : F, Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y :=
      fun y => v.valuedAdicCompletion_eq_valuation' y
    rw [e, e2]
    exact (v.valuation_lt_one_iff_mem _).2 hmem
  have h4 : Valued.v (4 : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 (by
    have h : algebraMap F (v.adicCompletion F) 4 ≠ 0 := (map_ne_zero _).2 (by norm_num)
    rwa [map_ofNat] at h)
  have hA : ∀ i, algebraMap F (v.adicCompletion F) (a i) ≠ 0 := fun i =>
    (map_ne_zero _).2 (ha i)
  have hev : ∀ i, ∀ᶠ k : ℕ in atTop, Valued.v ((M : ℕ) : v.adicCompletion F) ^ k <
      Valued.v (4 : v.adicCompletion F) * Valued.v (algebraMap F (v.adicCompletion F) (a i)) := by
    intro i
    have hne : Valued.v (4 : v.adicCompletion F) * Valued.v (algebraMap F (v.adicCompletion F) (a i)) ≠ 0 :=
      mul_ne_zero h4 ((Valuation.ne_zero_iff _).2 (hA i))
    obtain ⟨K, hK⟩ := exists_pow_lt₀ hval (Units.mk0 _ hne)
    exact eventually_atTop.2 ⟨K, fun k hk => lt_of_le_of_lt (pow_le_pow_right_of_le_one' hval.le hk) hK⟩
  have hbig : ∀ᶠ k : ℕ in atTop, B < ((M ^ k : ℕ) : ℝ) := by
    have : Tendsto (fun k : ℕ => ((M : ℝ)) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hM2)
    filter_upwards [this.eventually_gt_atTop B] with k hk
    push_cast
    exact hk
  obtain ⟨k, hk1, hk2⟩ := (hbig.and (eventually_all.2 hev)).exists
  refine ⟨M ^ k, hk1, fun i => ?_⟩
  obtain ⟨c, hc⟩ := GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v
    (1 + ((M : ℕ) : v.adicCompletion F) ^ k / algebraMap F (v.adicCompletion F) (a i)) (by
      rw [add_sub_cancel_left, map_div₀, map_pow]
      exact (div_lt_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hA i)))).2 (hk2 i))
  refine ⟨c, ?_⟩
  rw [← hc, map_add (f := _), map_natCast]
  have := hA i
  push_cast
  field_simp

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}

theorem isHermND_diagonal (e : Fin n → F) (he : ∀ i, e i ≠ 0) :
    IsHermND σ (diagonal fun i => algebraMap F E (e i)) := by
  refine ⟨fun i j => ?_, ?_⟩
  · by_cases h : i = j
    · subst h
      simp
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h), map_zero]
  · rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 (he i)

theorem isPosDef_diagonal (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : Fin n → F)
    (he : ∀ (τ : E →+* ℂ) i, 0 < (τ (algebraMap F E (e i))).re) :
    IsPosDef σ (diagonal fun i => algebraMap F E (e i)) := by
  intro x hx τ
  have hre : ∀ i, (τ (σ (x i) * (algebraMap F E (e i) * x i))).re =
      Complex.normSq (τ (x i)) * (τ (algebraMap F E (e i))).re := by
    intro i
    rw [map_mul, map_mul, hσ τ]
    have : star (τ (x i)) * (τ (algebraMap F E (e i)) * τ (x i)) =
        ((Complex.normSq (τ (x i)) : ℝ) : ℂ) * τ (algebraMap F E (e i)) := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
      ring
    rw [this, Complex.re_ofReal_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec_diagonal, map_sum, Complex.re_sum, hre]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _) (he τ j).le)
    ⟨i, Finset.mem_univ _, mul_pos (Complex.normSq_pos.2 ?_) (he τ i)⟩
  simpa using hi

end Forms

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]

theorem sigR_includeLeft (x : R) :
    sigR R σ (Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) x) =
      Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) x := by
  simp [sigR]

theorem sigR_inclR (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem inclR_algebraMap (f : F) :
    inclR R (algebraMap F E f) =
      Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) (algebraMap F R f) := by
  change Algebra.TensorProduct.includeRight (algebraMap F E f) = _
  rw [AlgHom.commutes, AlgHom.commutes]

end Tensor

theorem locIso {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hinv : ∀ x, σ (σ x) = x) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (hP : P.det ≠ 0) (a e : Fin n → F)
    (hPd : Pᵀ * J * P.map σ = diagonal fun i => algebraMap F E (a i)) (v : HeightOneSpectrum (𝓞 F))
    (c : Fin n → Fv F v) (hc0 : ∀ i, c i ≠ 0)
    (hc : ∀ i, c i * c i * algebraMap F (Fv F v) (a i) = algebraMap F (Fv F v) (e i)) :
    Nonempty (GlobalTheory.AdelicU.GLoc σ J v ≃ₜ* GlobalTheory.AdelicU.GLoc σ (diagonal fun i => algebraMap F E (e i)) v) := by
  set φ : E →+* Fv F v ⊗[F] E := inclR (Fv F v) with hφ
  set s : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E := sigR (Fv F v) σ with hs
  let ι : Fv F v →ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.includeLeft
  have hsι : ∀ x, s (ι x) = ι x := sigR_includeLeft σ (Fv F v)
  have hsφ : ∀ x, s (φ x) = φ (σ x) := sigR_inclR σ (Fv F v)
  have hφι : ∀ f : F, φ (algebraMap F E f) = ι (algebraMap F (Fv F v) f) := inclR_algebraMap (Fv F v)
  set Q : Matrix (Fin n) (Fin n) E := P.map σ with hQdef
  have hQdet : Q.det ≠ 0 := by
    have h := RingHom.map_det (σ : E →+* E) P
    rw [RingHom.mapMatrix_apply] at h
    change Q.det ≠ 0 at *
    have h' : Q.det = σ P.det := h.symm
    rw [h']
    exact (map_ne_zero (σ : E →+* E)).2 hP
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.2 hQdet)
  have hQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.2 hQdet)
  set D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := diagonal fun i => ι (c i)⁻¹ with hD
  set D' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := diagonal fun i => ι (c i) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    rw [← map_mul, inv_mul_cancel₀ (hc0 i), map_one]
  have hDD' : D' * D = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    rw [← map_mul, mul_inv_cancel₀ (hc0 i), map_one]
  have hm : ∀ A B : Matrix (Fin n) (Fin n) E, (A * B).map φ = A.map φ * B.map φ := fun A B =>
    Matrix.map_mul
  have hone : (1 : Matrix (Fin n) (Fin n) E).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have hQr : Q.map φ * Q⁻¹.map φ = 1 := by rw [← hm, hQ, hone]
  have hQr' : Q⁻¹.map φ * Q.map φ = 1 := by rw [← hm, hQ', hone]
  have h1 : Formalism.UG.cT s (Q.map φ) * JR (F := F) (Fv F v) J * Q.map φ =
      diagonal fun i => φ (algebraMap F E (a i)) := by
    have e1 : Formalism.UG.cT s (Q.map φ) = Pᵀ.map φ := by
      ext i j
      simp [Formalism.UG.cT, hQdef, hsφ, hinv]
    have e2 : JR (F := F) (Fv F v) J = J.map φ := rfl
    rw [e1, e2, ← hm, ← hm, hPd, Matrix.diagonal_map (map_zero φ)]
  have h2 : Formalism.UG.cT s D * JR (F := F) (Fv F v) (diagonal fun i => algebraMap F E (e i)) * D =
      diagonal fun i => φ (algebraMap F E (a i)) := by
    have e1 : Formalism.UG.cT s D = D := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Formalism.UG.cT, hD, hsι]
      · simp [Formalism.UG.cT, hD, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]
    have e2 : JR (F := F) (Fv F v) (diagonal fun i => algebraMap F E (e i)) =
        diagonal fun i => ι (algebraMap F (Fv F v) (e i)) := by
      change (diagonal fun i => algebraMap F E (e i)).map φ = _
      rw [Matrix.diagonal_map (map_zero φ)]
      congr 1
      ext i
      exact hφι _
    rw [e1, e2, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    rw [hφι, ← map_mul, ← map_mul, ← hc i]
    congr 1
    field_simp [hc0 i]
  obtain ⟨Φ, -⟩ := GlobalTheory.LocIsoConj.exists_locIso σ J (diagonal fun i => algebraMap F E (e i)) v
    (D * Q⁻¹.map φ) (Q.map φ * D') (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (Q.map φ), hQr', Matrix.one_mul, hDD]) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc D', hDD', Matrix.one_mul, hQr])
    (cT_congr s _ _ _ _ _ _ hQr h1 h2)
  exact ⟨Φ⟩

theorem stDefinite : StDefinite := by
  intro F E _ _ _ _ _ σ hc n J hJ v
  obtain ⟨hinv, hfix⟩ := GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hc
  obtain ⟨P, d, hP, hPd, hdf, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) (G := J) two_ne_zero
    (fun t => hinv t) (fun a b => hJ.1 b a)
  choose a ha using fun i => hfix (d i) (hdf i)
  have had : d = fun i => algebraMap F E (a i) := funext fun i => (ha i).symm
  have ha0 : ∀ i, a i ≠ 0 := fun i h => hd0 hJ.2 i (by rw [← ha i, h, map_zero])
  obtain ⟨N, hN, hsq⟩ := exists_large_sq v a ha0 (∑ i, ∑ τ : E →+* ℂ, |(τ (d i)).re|)
  have hpos : ∀ (τ : E →+* ℂ) i, 0 < (τ (algebraMap F E (a i + N))).re := by
    intro τ i
    have hle : |(τ (d i)).re| ≤ ∑ i, ∑ τ : E →+* ℂ, |(τ (d i)).re| :=
      (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ (d i)).re|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (f := fun i => ∑ τ : E →+* ℂ, |(τ (d i)).re|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    have h3 := neg_abs_le (τ (d i)).re
    rw [map_add (f := _), map_add (f := _), ha i, map_natCast, map_natCast, Complex.add_re, Complex.natCast_re]
    linarith
  have he0 : ∀ i, a i + N ≠ 0 := by
    intro i h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hpos τ i
    rw [h, map_zero, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  choose c hc' using hsq
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h
    have := hc' i
    rw [h, zero_mul, zero_mul] at this
    exact (map_ne_zero _).2 (he0 i) this.symm
  refine ⟨diagonal fun i => algebraMap F E (a i + N), isHermND_diagonal σ _ he0,
    isPosDef_diagonal σ hc.2.2.2 _ hpos, ?_⟩
  rw [had] at hPd
  exact locIso σ hinv J P hP a _ hPd v c hc0 hc'

end GlobalTheory.CompanionTheory.DefiniteForm

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DefinitenessStatement : StDefinite := by
  first | exact @GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | exact GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | (intros; apply GlobalTheory.CompanionTheory.DefiniteForm.stDefinite <;> assumption)
end
end

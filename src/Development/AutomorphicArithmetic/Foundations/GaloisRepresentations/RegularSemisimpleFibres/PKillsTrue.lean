module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIsCharEqAddOfPairNeZeroStatement

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PKillsTrue
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem JD_cons' {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (p : ℕ × ℕ) (D L : List (ℕ × ℕ))
    (b n : ℕ) (h : deg D + deg L = b) :
    JD θ (p :: D) L n = hc p.1 b (detc θ p.1 p.2) (JD θ D L b) n := by
  subst h; rfl

private theorem isCl_detc {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t k : ℕ) : IsCl (detc θ t k) := by
  intro x y
  have hd : ((y⁻¹ * x * y : GL (Fin t) F) : Matrix (Fin t) (Fin t) F).det =
      (x : Matrix (Fin t) (Fin t) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      mul_comm (Matrix.det ((y⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F)), mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]
  simp only [detc, hd]

private theorem gen_of_frob {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ z, s z = z ^ Nat.card F) (t : F' ≃ₐ[F] F') : t ∈ Subgroup.zpowers s := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Fintype F := Fintype.ofFinite F
  have hs' : s = FiniteField.frobeniusAlgEquivOfAlgebraic F F' := by
    ext z
    simp [hs z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t
  rw [hs']
  exact ⟨(n.1 : ℤ), by simpa using hn⟩

private theorem card_lift {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Nat.card F ^ Module.finrank F F' = Nat.card F' := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  exact Module.natCard_eq_pow_finrank.symm

private theorem step (hLH : LiftHc) (hKH : KillsHc) (hNE : NormEx) (hJE : JDEq) (hJC : JDChar) (hLD : LiftDet)
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] [Finite F] (s : F' ≃ₐ[F] F')
    (hs : ∀ z, s z = z ^ Nat.card F) (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ) (hθ : Inj θ) (p : ℕ × ℕ) (D L D' L' : List (ℕ × ℕ)) (b n : ℕ)
    (hn : n = p.1 + b) (h₁ : deg D + deg L = b) (h₂ : deg D' + deg L' = b)
    (hB : GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' b))
    (IH : Kills (shLift s (JD (pullθ ι θ) D L b)) (JD θ D' L' b)) :
    Kills (shLift s (JD (pullθ ι θ) (p :: D) L n))
      (JD θ ((p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i) :: D') L' n) := by
  have hg : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := gen_of_frob s hs
  rw [JD_cons' (pullθ ι θ) p D L b n h₁, JD_cons' θ _ D' L' b n h₂]
  rw [hLH F F' s hg p.1 b n hn _ _ (isCl_detc _ _ _) ((hJE F (pullθ ι θ)).2.2 D L b)]
  rw [hLD F F' s hs ι θ p.1 p.2 (hNE F F' s hs p.1)]
  exact hKH F' (s : F' →+* F') p.1 b n hn _ _ _ _ ((hJC F' θ hθ).1 _ _) hB
    (kills_self _ _ ((hJC F' θ hθ).1 _ _)) IH

theorem UpperTheory.Gal.InertialTypesAlt.killsTrue :
    (KillsOn fun a => a.D = []) → LiftHc → KillsHc → NormEx → LiftOk → JDEq → JDChar → LiftDet → KillsOn fun _ => True := by
  intro h0 hLH hKH hNE hLO hJE hJC hLD F F' _ _ _ _ s hl hs ι θ hθ a _ hok hq
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have hlift := hLO a (Module.finrank F F') hl hok
  obtain ⟨q, D0, L0⟩ := a
  change q = Nat.card F at hq
  subst hq
  have hok' := hok
  unfold Lbl.Ok at hok'
  obtain ⟨hq2, hDpos, hLok⟩ := hok'
  have hl1 := hlift.1
  unfold Lbl.Ok at hl1
  obtain ⟨hq2', _, hLok'⟩ := hl1
  have hdegmap : ∀ D : List (ℕ × ℕ),
      deg (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i)) =
        deg D := by
    intro D
    simp [GlobalTheory.Shin.deg, List.map_map, Function.comp_def]
  have hdegL : deg (liftAll (Nat.card F) (Module.finrank F F') L0) = deg L0 := by
    have h := hlift.2
    simp only [Lbl.rk, Lbl.lift, hdegmap] at h
    omega
  have key : ∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1) →
      Kills (shLift s (JD (pullθ ι θ) D L0 (deg D + deg L0)))
        (JD θ (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i))
          (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0)) := by
    intro D
    induction D with
    | nil =>
      intro _
      exact h0 F F' s hl hs ι θ hθ ⟨Nat.card F, [], L0⟩ rfl
        (by unfold Lbl.Ok; exact ⟨hq2, by simp, hLok⟩) rfl
    | cons p D ih =>
      intro hD
      have hD' : ∀ x ∈ D, 0 < x.1 := fun x hx => hD x (List.mem_cons_of_mem _ hx)
      have tr : ∀ (D' L' : List (ℕ × ℕ)) (n m : ℕ), n = m →
          GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' n) → GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' m) := by
        intro D' L' n m h
        subst h
        exact id
      have hB : GlobalTheory.BI.IsChar ℂ ℂ (JD θ
          (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i))
          (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0)) := by
        have hc := (hJC F' θ hθ).2 ⟨Nat.card F ^ Module.finrank F F',
          D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i),
          liftAll (Nat.card F) (Module.finrank F F') L0⟩
          (by
            unfold Lbl.Ok
            refine ⟨hq2', ?_, hLok'⟩
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
            exact hD' y hy) card_lift
        refine tr _ _ _ _ ?_ hc
        show deg _ + deg _ = _
        rw [hdegmap, hdegL]
      exact step hLH hKH hNE hJE hJC hLD s hs ι θ hθ p D L0 _ _ (deg D + deg L0) _
        (by simp only [GlobalTheory.Shin.deg, List.map_cons, List.sum_cons]; omega) rfl
        (by rw [hdegmap, hdegL]) hB (ih hD')
  exact key D0 hDpos
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PJdPair
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma deg_app (a b : List (ℕ × ℕ)) : deg (a ++ b) = deg a + deg b := by
  simp [GlobalTheory.Shin.deg]

private lemma deg_rep (t c : ℕ) : deg (List.replicate t ((1 : ℕ), c)) = t := by
  simp [GlobalTheory.Shin.deg]

private lemma expand_cons' (p : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    expand (p :: D) = List.replicate p.1 (1, p.2) ++ expand D := by
  simp [UpperTheory.Gal.InertialTypesAlt.expand]

private lemma cusp_one_ne {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ)
    (hm : 0 < m) : cusp θ m k 1 ≠ 0 := by
  have h := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico F (Fin m → F) (GlobalTheory.CuspGL.rootSum θ k) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).2 (by simpa using hm)
  simp only [cusp, psiG, Units.val_one, Matrix.toLin'_one]
  erw [h]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  rw [sub_ne_zero]
  intro heq
  have h2 : ((Nat.card F ^ i : ℕ) : ℂ) = 1 := by
    push_cast
    exact heq.symm
  norm_cast at h2
  have h3 := Nat.one_lt_pow (by omega : i ≠ 0) hq
  omega

private lemma pairs_self {G : Type} [Group G] [Finite G] (Y : G → ℂ) (h : Y 1 ≠ 0) : Pairs Y Y := by
  haveI : Fintype G := Fintype.ofFinite G
  unfold Pairs
  rw [finsum_eq_sum_of_fintype]
  intro h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ g : G, 0 ≤ (star (Y g) * Y g).re := by
    intro g
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  have hpos : 0 < (star (Y 1) * Y 1).re := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr h
  have : 0 < ∑ g : G, (star (Y g) * Y g).re :=
    Finset.sum_pos' (fun g _ => hnn g) ⟨1, Finset.mem_univ _, hpos⟩
  linarith

private lemma happ (hA : JAppend) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (R M : List (ℕ × ℕ)) (t b n : ℕ) (hR : deg R = t) (hM : deg M = b) (hn : n = t + b) :
    J θ (R ++ M) n = hc t b (J θ R t) (J θ M b) n := by
  subst hR hM hn
  exact hA F θ R M _ rfl

private lemma char_cast {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (M : List (ℕ × ℕ)) {n m : ℕ}
    (e : n = m) (h : GlobalTheory.BI.IsChar ℂ ℂ (J θ M n)) : GlobalTheory.BI.IsChar ℂ ℂ (J θ M m) := by
  subst e
  exact h

private lemma J_one_ne (h1 : HcOne) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (M : List (ℕ × ℕ)) (hM : ∀ p ∈ M, 0 < p.1) : J θ M (deg M) 1 ≠ 0 := by
  induction M with
  | nil =>
    rw [J_nil]
    exact one_ne_zero
  | cons p M ih =>
    have hp : 0 < p.1 := hM p (by simp)
    have hM' : ∀ x ∈ M, 0 < x.1 := fun x hx => hM x (by simp [hx])
    rw [J_cons]
    exact h1 F p.1 (deg M) _ (by simp [GlobalTheory.Shin.deg]) _ _ (cusp_one_ne θ p.1 p.2 hp) (ih hM')

theorem UpperTheory.Gal.InertialTypesAlt.jdPair :
    JAppend → HcOne → HcPair → DetPair → JDChar → JDPair := by
  intro hA h1 hP hD hC F _ _ θ hθ a ha hq
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq2, hDp, hLp⟩ := ha
  have hL0 : ∀ x ∈ L, 0 < x.1 := fun x hx => (hLp x hx).1
  have charJ : ∀ M : List (ℕ × ℕ), (∀ x ∈ M, 0 < x.1 ∧ Reg q x.1 x.2) → ∀ n, n = deg M →
      GlobalTheory.BI.IsChar ℂ ℂ (J θ M n) := by
    intro M hM n hn
    have hc := (hC F θ hθ).2 ⟨q, [], M⟩ ⟨hq2, by simp, hM⟩ hq
    simp only [Lbl.D, Lbl.L, Lbl.rk] at hc
    rw [JD_nil] at hc
    exact char_cast θ M (by simp [GlobalTheory.Shin.deg] at hn ⊢; omega) hc
  have key : ∀ E : List (ℕ × ℕ), (∀ x ∈ E, 0 < x.1) →
      deg (expand E ++ L) = deg E + deg L ∧
        Pairs (J θ (expand E ++ L) (deg E + deg L)) (JD θ E L (deg E + deg L)) := by
    intro E
    induction E with
    | nil =>
      intro _
      have e1 : expand [] ++ L = L := by simp [UpperTheory.Gal.InertialTypesAlt.expand]
      have e2 : deg ([] : List (ℕ × ℕ)) = 0 := by simp [GlobalTheory.Shin.deg]
      rw [e1, e2, zero_add, JD_nil]
      exact ⟨rfl, pairs_self _ (J_one_ne h1 θ L hL0)⟩
    | cons p E ih =>
      intro hp
      have hp1 : 0 < p.1 := hp p (by simp)
      have hE : ∀ x ∈ E, 0 < x.1 := fun x hx => hp x (by simp [hx])
      obtain ⟨hdeg, hpair⟩ := ih hE
      have hdc : deg (p :: E) = p.1 + deg E := by simp [GlobalTheory.Shin.deg]
      have hexp : ∀ x ∈ expand E ++ L, 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · simp only [UpperTheory.Gal.InertialTypesAlt.expand, List.mem_flatMap, List.mem_replicate] at h
          obtain ⟨y, -, -, rfl⟩ := h
          exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
        · exact hLp x h
      have hrep : ∀ x ∈ List.replicate p.1 ((1 : ℕ), p.2), 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rw [List.mem_replicate] at hx
        rw [hx.2]
        exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
      rw [expand_cons', List.append_assoc, deg_app, deg_rep, hdeg, hdc]
      refine ⟨by omega, ?_⟩
      rw [happ hA θ _ _ p.1 (deg E + deg L) _ (deg_rep _ _) hdeg (by omega), JD_cons]
      refine hP F p.1 _ _ (by omega) _ _ _ _ ((hC F θ hθ).1 _ _)
        (charJ _ hrep _ (deg_rep _ _).symm) ((hC F θ hθ).2 ⟨q, E, L⟩ ⟨hq2, hE, hLp⟩ hq)
        (charJ _ hexp _ hdeg.symm) (hD F θ p.1 p.2) hpair
  exact key D hDp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PInertOf
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tr_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin m) k) V)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) (u : 𝒪[k]ˣ) :
    LinearMap.trace ℂ _ (levelZero π (Matrix.GeneralLinearGroup.scalar (Fin m) (unitRes k u))) =
      (ω (unitIncl k u) : ℂ) * LinearMap.trace ℂ _ (levelZero π 1) := by
  have key : ∀ g : KO k (Fin m), (g : GL (Fin m) k) = Matrix.GeneralLinearGroup.scalar (Fin m) (unitIncl k u) →
      levelZero π (redK k (Fin m) g) = ((ω (unitIncl k u) : ℂˣ) : ℂ) • (1 : Module.End ℂ _) := by
    intro g hg
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [levelZero_apply, hg, h]
    simp
  rw [← redK_scalar, key _ rfl, map_one, map_smul, smul_eq_mul]

private theorem inflates_twist {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V) (τ : FDRep ℂ (GlobalTheory.GLq.Gn g m))
    {μ : (w.adicCompletion E)ˣ →* ℂˣ} (hμ : IsUnram μ)
    (h : GlobalTheory.SerSys.TameGen.Inflates (ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    GlobalTheory.SerSys.TameGen.Inflates ((twist ρ (detChar _ μ)).comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ := by
  obtain ⟨φ, h0, hφ⟩ := h
  refine ⟨φ, h0, fun κ x => ?_⟩
  rw [hφ]
  have h1 := detChar_of_mem_KO hμ (DiscreteGroups.sglob.DzIso.map_inc_mem_KO i hi κ)
  show _ = (twist ρ (detChar _ μ)) (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m κ)) (φ x)
  rw [twist_apply, h1]
  simp

private theorem map_surj {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') {m : ℕ} (δ : GL (Fin m) F') :
    ∃ γ : GL (Fin m) F, Matrix.GeneralLinearGroup.map r.toRingHom γ = δ :=
  ⟨Matrix.GeneralLinearGroup.map r.symm.toRingHom δ, by ext a b; simp⟩

private theorem exists_unr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : ℕ} (hm : 0 < m) {ω ω' : kˣ →* ℂˣ} (h : ∀ u : 𝒪[k]ˣ, ω (unitIncl k u) = ω' (unitIncl k u)) :
    ∃ μ : kˣ →* ℂˣ, IsUnram μ ∧ ω * μ ^ m = ω' := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hχu : IsUnram (ω⁻¹ * ω') := by
    intro x hx
    obtain ⟨u, rfl⟩ := valuation_eq_one_iff.mp hx
    simp [h u]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (((ω⁻¹ * ω') ϖ : ℂˣ) : ℂ) hm
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz
    exact ((ω⁻¹ * ω') ϖ).ne_zero hz.symm
  have hα : (Units.mk0 z hz0) ^ m = (ω⁻¹ * ω') ϖ := Units.ext (by simpa using hz)
  have hχe := eq_unrChar hχu hϖ
  refine ⟨GlobalTheory.SmGL.unrChar k (Units.mk0 z hz0), isUnram_unrChar k _, ?_⟩
  have hpow : GlobalTheory.SmGL.unrChar k (Units.mk0 z hz0) ^ m = ω⁻¹ * ω' := by
    rw [hχe]
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.pow_apply, GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.unrChar_apply, ← hα,
      ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [hpow, mul_inv_cancel_left]

theorem UpperTheory.Gal.InertialTypesAlt.inertOf :
    TypeChar → BaseQ → InertOf := by
  intro hTC hBQ E Ω _ _ _ _ _ A v hv g _ i hi m x y hxc hyc hxd hyd htr
  obtain ⟨-, -, ⟨r⟩⟩ := hBQ E v g i hi
  have hcls : ∀ c : IrrCl (GL (Fin m) (v.adicCompletion E)), GlobalTheory.LocLanglands.cls c.rep = ⟨m, c⟩ := by
    intro c
    unfold GlobalTheory.LocLanglands.cls
    rw [IrrCl.cl_rep]
  have hm : 0 < m := (UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, x⟩).2.2.2.1 hxc
  obtain ⟨τx, hτx, hinfx⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A v hv g i hi m hm x.rep).1
    (by rw [hcls]; exact hxc) (by rw [hcls]; exact hxd)
  obtain ⟨τy, hτy, hinfy⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A v hv g i hi m hm y.rep).1
    (by rw [hcls]; exact hyc) (by rw [hcls]; exact hyd)
  have hch : τx.character = τy.character := by
    funext δ
    obtain ⟨γ, hγ⟩ := map_surj r (δ : GL (Fin m) (ZMod g))
    subst hγ
    have e1 := hTC E v g i hi r ⟨m, x⟩ τx hτx hinfx γ
    have e2 := hTC E v g i hi r ⟨m, y⟩ τy hτy hinfy γ
    exact e1.trans ((htr γ).trans e2.symm)
  obtain ⟨ωx, -, hωx, -⟩ := (UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, x⟩).1
  obtain ⟨ωy, -, hωy, -⟩ := (UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, y⟩).1
  have hT : LinearMap.trace ℂ _ (levelZero x.rep.ρ 1) ≠ 0 := by
    have e1 := hTC E v g i hi r ⟨m, x⟩ τx hτx hinfx 1
    simp only [map_one, FDRep.char_one] at e1
    have hinf := hinfx
    unfold GlobalTheory.SerSys.TameGen.Inflates at hinf
    obtain ⟨φ, hφ, -⟩ := hinf
    have : Nontrivial τx.V := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hφ (LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, LinearMap.zero_apply])
    rw [map_one]
    refine fun h0 => ?_
    have h1 : (Module.finrank ℂ τx.V : ℂ) = 0 := e1.trans h0
    exact (Module.finrank_pos (R := ℂ) (M := τx.V)).ne' (by exact_mod_cast h1)
  have hωu : ∀ u, ωx (unitIncl _ u) = ωy (unitIncl _ u) := by
    intro u
    have a1 := tr_scalar x.rep.ρ hωx u
    have a2 := tr_scalar y.rep.ρ hωy u
    have e := htr (Matrix.GeneralLinearGroup.scalar (Fin m) (unitRes _ u))
    have e1 := htr 1
    rw [a1, a2, ← e1] at e
    exact Units.ext (mul_right_cancel₀ hT e)
  obtain ⟨μ, hμ, hμω⟩ := exists_unr hm hωu
  have hμs := isSmoothChar_of_isUnram hμ
  let σ' : IrrRep (GL (Fin m) (v.adicCompletion E)) :=
    IrrRep.mk x.rep.V (twist x.rep.ρ (detChar (Fin m) μ))
      (isSmooth_twist x.rep.smooth hμs.detChar) (isIrreducible_twist x.rep.irr _)
  have hinfσ : GlobalTheory.SerSys.TameGen.Inflates (MonoidHom.comp σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)) τx :=
    inflates_twist i hi x.rep.ρ τx hμ hinfx
  have hωσ : HasCentralChar σ'.ρ ωy := by
    have := hasCentralChar_twist hωx μ
    rw [Fintype.card_fin, hμω] at this
    exact this
  have hcl := UpperTheory.Zero.LLC.detByType E Ω A v hv g i hi m hm y.rep σ' τy τx ωy hτy hch hinfy hinfσ hωy hωσ
  unfold IrrGL.Inert
  refine ⟨μ, hμ, ?_⟩
  have e3 : IrrGL.tw (⟨m, x⟩ : IrrGL (k := _)) μ hμs = GlobalTheory.LocLanglands.cls σ' := by
    conv_lhs => rw [← IrrGL.of_rep ⟨m, x⟩]
    rw [IrrGL.tw_of]
    rfl
  exact (hcls y).symm.trans (hcl.symm.trans e3.symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PHcPair
noncomputable section

open GlobalTheory.BI GlobalTheory.Shin

namespace UpperTheory.Gal.InertialTypesAlt

section Group

variable {G : Type} [Group G] [Finite G]

private theorem sum_eq_pair {χ : G → ℂ} (ψ : G → ℂ) (hχ : IsChar ℂ ℂ χ) :
    (∑ᶠ g, star (χ g) * ψ g) = (Nat.card G : ℂ) * pair ψ χ := by
  have h := GlobalTheory.T.star_virtualCharacter_eq_apply_inv G χ (AddSubgroup.subset_closure hχ)
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  unfold pair
  rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  exact finsum_congr fun g => by rw [h, mul_comm]

private theorem pairs_iff {χ : G → ℂ} (ψ : G → ℂ) (hχ : IsChar ℂ ℂ χ) : Pairs χ ψ ↔ pair ψ χ ≠ 0 := by
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Pairs
  rw [sum_eq_pair ψ hχ, mul_ne_zero_iff]
  tauto

private theorem pair_add_ne {a u b v : G → ℂ} (ha : IsChar ℂ ℂ a) (hu : IsChar ℂ ℂ u) (hb : IsChar ℂ ℂ b)
    (hv : IsChar ℂ ℂ v) (h : pair a b ≠ 0) : pair (a + u) (b + v) ≠ 0 := by
  obtain ⟨hadd, hnat, -, hsymm⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  obtain ⟨n1, h1⟩ := hnat b a hb ha
  obtain ⟨n2, h2⟩ := hnat v a hv ha
  obtain ⟨n3, h3⟩ := hnat b u hb hu
  obtain ⟨n4, h4⟩ := hnat v u hv hu
  have e : pair (a + u) (b + v) = pair b a + pair v a + (pair b u + pair v u) := by
    rw [hadd, hsymm a (b + v), hsymm u (b + v), hadd b v a, hadd b v u]
  have hn1 : n1 ≠ 0 := by
    rintro rfl
    exact h (by rw [hsymm, h1]; simp)
  rw [e, h1, h2, h3, h4]
  exact_mod_cast (by omega : n1 + n2 + (n3 + n4) ≠ 0)

private theorem isChar_of_irr {φ : G → ℂ} (h : IsIrrChar ℂ ℂ φ) : IsChar ℂ ℂ φ := by
  obtain ⟨n, ρ, -, e⟩ := h
  exact ⟨n, ρ, e⟩

private theorem common {A : G → ℂ} (hA : IsChar ℂ ℂ A) {α : G → ℂ} (hα : IsChar ℂ ℂ α) (h : pair A α ≠ 0) :
    ∃ φ R R' : G → ℂ, IsIrrChar ℂ ℂ φ ∧ IsChar ℂ ℂ R ∧ IsChar ℂ ℂ R' ∧ A = φ + R ∧ α = φ + R' := by
  obtain ⟨hadd, -, -, hsymm⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  obtain ⟨-, hcadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G
  have hzero : ∀ c : G → ℂ, pair 0 c = 0 := by
    intro c
    have := hadd 0 0 c
    rw [add_zero] at this
    linear_combination -this
  revert h
  refine GlobalTheory.T.isCharacterOverSubfield_induction_irreducible ℂ ℂ G (fun α => pair A α ≠ 0 → ∃ φ R R' : G → ℂ, IsIrrChar ℂ ℂ φ ∧ IsChar ℂ ℂ R ∧
    IsChar ℂ ℂ R' ∧ A = φ + R ∧ α = φ + R') ?_ ?_ α hα
  · intro h0
    exact absurd (by rw [hsymm, hzero] : pair A 0 = 0) h0
  · intro φ c hφ hc ih hne
    have hsplit : pair A (φ + c) = pair A φ + pair A c := by
      rw [hsymm A (φ + c), hadd, hsymm φ A, hsymm c A]
    by_cases h1 : pair A φ = 0
    · rw [hsplit, h1, zero_add] at hne
      obtain ⟨ψ, R, R', hψ, hR, hR', hA', hc'⟩ := ih hne
      refine ⟨ψ, R, φ + R', hψ, hR, hcadd _ _ (isChar_of_irr hφ) hR', hA', ?_⟩
      rw [hc']
      abel
    · obtain ⟨R, hR, hAR⟩ := GlobalTheory.T.exists_isChar_eq_add_of_pair_ne_zero' ℂ ℂ G φ A hφ hA h1
      exact ⟨φ, R, c, hφ, hR, hc, hAR, rfl⟩

private theorem irr_one_ne {φ : G → ℂ} (h : IsIrrChar ℂ ℂ φ) : φ 1 ≠ 0 := by
  obtain ⟨n, ρ, hirr, hφ⟩ := h
  rw [hφ, Representation.char_one]
  simp only [Module.finrank_fin_fun, Algebra.algebraMap_self, RingHom.id_apply, ne_eq, Nat.cast_eq_zero]
  rintro rfl
  apply hirr.bot_ne_top
  ext v
  rw [Subsingleton.elim v 0]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

private theorem pair_self_ne {x : G → ℂ} (hx : IsChar ℂ ℂ x) (h : x 1 ≠ 0) : pair x x ≠ 0 := by
  obtain ⟨-, -, hirr, -⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  have hx0 : x ≠ 0 := fun e => h (by simp [e])
  obtain ⟨φ, c, hφ, hc, rfl⟩ := GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero ℂ ℂ G x hx hx0
  obtain ⟨n, hn, hpn⟩ := hirr φ hφ
  refine pair_add_ne (isChar_of_irr hφ) hc (isChar_of_irr hφ) hc ?_
  rw [hpn]
  exact_mod_cast hn.ne'

end Group

section Hc

variable {F : Type} [Field F] [Finite F]

private theorem hc_add_left (a b n : ℕ) (α α' : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    hc a b (α + α') β n = hc a b α β n + hc a b α' β n := by
  funext x
  simp only [hc, hcTw, Pi.add_apply]
  rw [← mul_add, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  refine finsum_congr fun y => ?_
  split_ifs <;> simp [add_mul]

private theorem hc_add_right (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β β' : GL (Fin b) F → ℂ) :
    hc a b α (β + β') n = hc a b α β n + hc a b α β' n := by
  funext x
  simp only [hc, hcTw, Pi.add_apply]
  rw [← mul_add, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  refine finsum_congr fun y => ?_
  split_ifs <;> simp [mul_add]

end Hc

theorem hcPair : HcChar → HcOne → HcPair := by
  intro hC hO F _ _ a b n hn α A β B hα hA hβ hB hAα hBβ
  have hcC : ∀ (x : GL (Fin a) F → ℂ) (y : GL (Fin b) F → ℂ), IsChar ℂ ℂ x → IsChar ℂ ℂ y →
      IsChar ℂ ℂ (hc a b x y n) :=
    fun x y hx hy => hC F a b n hn x y hx hy
  obtain ⟨-, hcadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ (GL (Fin n) F)
  rw [pairs_iff _ (hcC A B hA hB)]
  rw [pairs_iff _ hA] at hAα
  rw [pairs_iff _ hB] at hBβ
  obtain ⟨φ, R, R', hφ, hR, hR', rfl, rfl⟩ := common hα hA hAα
  obtain ⟨ψ, S, S', hψ, hS, hS', rfl, rfl⟩ := common hβ hB hBβ
  have hφ' := isChar_of_irr hφ
  have hψ' := isChar_of_irr hψ
  have e1 : hc a b (φ + R) (ψ + S) n =
      hc a b φ ψ n + (hc a b φ S n + (hc a b R ψ n + hc a b R S n)) := by
    rw [hc_add_left, hc_add_right, hc_add_right]
    abel
  have e2 : hc a b (φ + R') (ψ + S') n =
      hc a b φ ψ n + (hc a b φ S' n + (hc a b R' ψ n + hc a b R' S' n)) := by
    rw [hc_add_left, hc_add_right, hc_add_right]
    abel
  rw [e1, e2]
  refine pair_add_ne (hcC _ _ hφ' hψ')
    (hcadd _ _ (hcC _ _ hφ' hS) (hcadd _ _ (hcC _ _ hR hψ') (hcC _ _ hR hS)))
    (hcC _ _ hφ' hψ')
    (hcadd _ _ (hcC _ _ hφ' hS') (hcadd _ _ (hcC _ _ hR' hψ') (hcC _ _ hR' hS'))) ?_
  exact pair_self_ne (hcC _ _ hφ' hψ') (hO F a b n hn φ ψ (irr_one_ne hφ) (irr_one_ne hψ))

end UpperTheory.Gal.InertialTypesAlt
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PIndMap
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.InertialTypesAlt.indMap :
    UpperTheory.Gal.TypesAndIwahori.IndSupp → UpperTheory.Gal.TypesAndIwahori.ParaFactor → IndMap := by
  intro hSupp hPara k _ _ _ _ N s d hd W Z _ _ _ _ ρ κ j hj hjκ
  set e := stdBlocks d hd with he
  let σ := (twist ρ (deltaHalf k fun a : Fin s => Fin (d a))).comp (leviProj k e)
  have hσ : ∀ (p : parab k e), leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a)) →
      ∀ w : W, σ p w = ρ (leviProj k e p) w := by
    intro p hK w
    have h3 := deltaHalf_of_mem_leviK hK
    simp only [σ, MonoidHom.comp_apply, twist, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, h3,
      Units.val_one, one_smul]
  have key : ∀ z : Z, ∀ p : parab k e, (p : GL (Fin N) k) ∈ KOne k (Fin N) → σ p (j z) = j z := by
    intro z p hp
    have hl := (hPara k e).2 p hp
    have hK : leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a)) := by
      rw [leviK, Subgroup.mem_pi]
      rw [leviKOne, Subgroup.mem_pi] at hl
      intro a ha
      exact GlobalTheory.StepData.KOne_le_KO (hl a ha)
    have h1 := (redLevi_eq_one_iff ⟨_, hK⟩).2 hl
    have h2 := hjκ ⟨_, hK⟩ z
    rw [h1, map_one] at h2
    rw [hσ p hK]
    exact h2.symm
  choose F hF1 hF0 using fun z => hSupp (GL (Fin N) k) W (parab k e) (KOne k (Fin N)) σ (j z)
    GlobalTheory.StepData.isOpen_KOne (key z)
  have uniq : ∀ (u : W) (f f' : GL (Fin N) k → W),
      (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f ((p : GL (Fin N) k) * c) = σ p u) →
      (∀ g, (¬∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c) → f g = 0) →
      (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f' ((p : GL (Fin N) k) * c) = σ p u) →
      (∀ g, (¬∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c) → f' g = 0) →
      f = f' := by
    intro u f f' h1 h0 h1' h0'
    funext g
    by_cases hg : ∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [h1 p c hc, h1' p c hc]
    · rw [h0 g hg, h0' g hg]
  have hfix : ∀ z, F z ∈ fixed (parInd e ρ) (KOne k (Fin N)) := by
    intro z
    rw [GlobalTheory.Parabolic.mem_fixed]
    intro c hc
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (F z).1.1 (g * c) = (F z).1.1 g
    by_cases hg : ∃ (p : parab k e), ∃ c' ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hg
      rw [mul_assoc, hF1 z p _ (mul_mem hc' hc), hF1 z p c' hc']
    · rw [hF0 z g hg, hF0 z (g * c)]
      rintro ⟨p, c', hc', h⟩
      exact hg ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  let Φ : Z →ₗ[ℂ] fixed (parInd e ρ) (KOne k (Fin N)) :=
    { toFun := fun z => ⟨F z, hfix z⟩
      map_add' := by
        intro z z'
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change (F (z + z')).1.1 = (F z).1.1 + (F z').1.1
        refine uniq (j (z + z')) _ _ (hF1 _) (hF0 _) ?_ ?_
        · intro p c hc
          simp only [Pi.add_apply, hF1 z p c hc, hF1 z' p c hc, map_add (f := _)]
        · intro g hg
          simp only [Pi.add_apply, hF0 z g hg, hF0 z' g hg, add_zero]
      map_smul' := by
        intro a z
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change (F (a • z)).1.1 = a • (F z).1.1
        refine uniq (j (a • z)) _ _ (hF1 _) (hF0 _) ?_ ?_
        · intro p c hc
          simp only [Pi.smul_apply, hF1 z p c hc, map_smul]
        · intro g hg
          simp only [Pi.smul_apply, hF0 z g hg, smul_zero] }
  let ev : fixed (parInd e ρ) (KOne k (Fin N)) →ₗ[ℂ] W :=
    { toFun := fun v => v.1.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ z, (F z).1.1 1 = j z := by
    intro z
    have := hF1 z 1 1 (one_mem _)
    simpa using this
  refine ⟨Φ, ev, ?_, ?_, ?_⟩
  · intro p z
    obtain ⟨g, hg⟩ := redK_surjective (k := k) (n := Fin N) (p : GL (Fin N) 𝓀[k])
    have hgP : (g : GL (Fin N) k) ∈ parahoric k e := (coe_mem_levelPre g).2 (by rw [hg]; exact p.2)
    obtain ⟨p', x, hp'KO, hpx, hxred, c, hc, hgc⟩ := (hPara k e).1 ⟨g, hgP⟩
    have hgc' : (g : GL (Fin N) k) = (p' : GL (Fin N) k) * c := hgc
    have hproj : parahoricProj k e ⟨g, hgP⟩ = leviProj 𝓀[k] e p := by
      show leviProj 𝓀[k] _ _ = _
      exact congrArg _ (Subtype.ext (by exact hg))
    have hz' : j (κ (leviProj 𝓀[k] e p) z) = ρ x (j z) := by
      rw [← hproj, ← hxred]
      exact hjκ x z
    have hσp' : σ p' (j z) = j (κ (leviProj 𝓀[k] e p) z) := by
      rw [hz', hσ p' (by rw [hpx]; exact x.2), hpx]
    have hn := KO_le_normalizer (k := k) (n := Fin N) hp'KO
    rw [← hg]
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [levelZero_apply]
    change (F _).1.1 = fun h => (F z).1.1 (h * (g : GL (Fin N) k))
    refine uniq (j (κ (leviProj 𝓀[k] e p) z)) _ _ (hF1 _) (hF0 _) ?_ ?_
    · intro q c1 hc1
      have hc2 : (p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c ∈ KOne k (Fin N) := by
        refine mul_mem ?_ hc
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) c1).1 hc1
        simpa using this
      have heq : (q : GL (Fin N) k) * c1 * (g : GL (Fin N) k) =
          ((q * p' : parab k e) : GL (Fin N) k) * ((p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c) := by
        rw [hgc', Subgroup.coe_mul]
        group
      show (F z).1.1 ((q : GL (Fin N) k) * c1 * (g : GL (Fin N) k)) = _
      rw [heq, hF1 z (q * p') _ hc2, map_mul, Module.End.mul_apply, hσp']
    · intro h hh
      show (F z).1.1 (h * (g : GL (Fin N) k)) = 0
      apply hF0
      rintro ⟨q, c2, hc2, hq⟩
      apply hh
      refine ⟨q * p'⁻¹, (p' : GL (Fin N) k) * (c2 * c⁻¹) * (p' : GL (Fin N) k)⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hn (c2 * c⁻¹)).1 (mul_mem hc2 (inv_mem hc))
      · calc h = (h * (g : GL (Fin N) k)) * (g : GL (Fin N) k)⁻¹ := by group
          _ = _ := by
            rw [hq, hgc', Subgroup.coe_mul, Subgroup.coe_inv]
            group
  · intro γ hγ z
    obtain ⟨g, rfl⟩ := redK_surjective (k := k) (n := Fin N) γ
    show ((levelZero (parInd e ρ) (redK k (Fin N) g)) (Φ z)).1.1.1 1 = 0
    rw [levelZero_apply]
    change (F z).1.1 (1 * (g : GL (Fin N) k)) = 0
    rw [one_mul]
    apply hF0 z
    rintro ⟨p, c, hc, hpc⟩
    apply hγ
    have hcKO : c⁻¹ ∈ KO k (Fin N) := inv_mem (GlobalTheory.StepData.KOne_le_KO hc)
    have hpKO : (p : GL (Fin N) k) ∈ KO k (Fin N) := by
      have : (p : GL (Fin N) k) = g * c⁻¹ := by rw [hpc, mul_inv_cancel_right]
      rw [this]
      exact mul_mem g.2 hcKO
    have hred : redK k (Fin N) ⟨p, hpKO⟩ = redK k (Fin N) g := by
      have : (⟨p, hpKO⟩ : KO k (Fin N)) = g * ⟨c⁻¹, hcKO⟩ := by
        apply Subtype.ext
        show (p : GL (Fin N) k) = g * c⁻¹
        rw [hpc, mul_inv_cancel_right]
      rw [this, map_mul, (redK_eq_one_iff ⟨c⁻¹, hcKO⟩).2 (inv_mem hc), mul_one]
    rw [← hred, mem_parab_iff]
    intro a b i i' hab
    rw [redK_eq_zero_iff]
    have := (mem_parab_iff.1 p.2) a b i i' hab
    simp [this]
  · intro z hz
    apply hj
    rw [map_zero, ← hev z]
    exact hz
end

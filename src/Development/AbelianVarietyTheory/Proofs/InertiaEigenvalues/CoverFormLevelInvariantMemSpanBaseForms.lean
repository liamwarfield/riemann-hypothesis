module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGKSubmoduleISupGelfandJointEigenspaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.ThetaValuation.CongruenceSpanLevel
section -- merged from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ArchimedeanGluing
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrincipalCongruenceGamma
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrincipalCongruenceGamma

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsPrinc (X : Data E r) (M : ℕ) (γ : GL (Fin r) E) : Prop :=
  IsUStab X.Gm X.Λ γ ∧
    ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = M • y

def princ (X : Data E r) (M : ℕ) : Subgroup (GL (Fin r) E) where
  carrier := {γ | IsPrinc X M γ}
  one_mem' := by
    refine ⟨⟨fun x y => by simp, fun x => by simp⟩, fun x _ => ⟨0, X.Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨ha1, ha2⟩, ha3⟩ ⟨⟨hb1, hb2⟩, hb3⟩
    refine ⟨⟨fun x y => ?_, fun x => ?_⟩, fun x hx => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha1, hb1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha2, ← hb2]
    · obtain ⟨y, hy, e⟩ := hb3 x hx
      obtain ⟨z, hz, e'⟩ := ha3 _ ((hb2 x).1 hx)
      refine ⟨z + y, X.Λ.add_mem hz hy, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, smul_add, ← e, ← e']
      abel
  inv_mem' := by
    rintro a ⟨⟨ha1, ha2⟩, ha3⟩
    have hc : ∀ x : Fin r → E, Matrix.mulVec (a : Matrix (Fin r) (Fin r) E)
        (Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hm : ∀ x, x ∈ X.Λ ↔ Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x ∈ X.Λ := by
      intro x
      rw [ha2 (Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x), hc]
    refine ⟨⟨fun x y => ?_, hm⟩, fun x hx => ?_⟩
    · rw [← ha1, hc, hc]
    · obtain ⟨y, hy, e⟩ := ha3 _ ((hm x).1 hx)
      refine ⟨-y, X.Λ.neg_mem hy, ?_⟩
      rw [hc] at e
      rw [smul_neg, ← e]
      abel

end Model

variable {D : D7}

def GamAt (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Prop :=
  ∀ k : (T.U j σ).Comp, princ ((T.U j σ).X k) T.Q.l.M ≤ ((T.U j σ).X k).Γ

def Gam (T : Core D) : Prop :=
  ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → GamAt T j σ

end GlobalTheory.IndefiniteRowSideFullHecke.PrincipalCongruenceGamma
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory.Survey.ArchimedeanCompatibility

open GlobalTheory.IndefiniteRowSideFullHecke.PrincipalCongruenceGamma GlobalTheory.PrincCore

theorem gam_iff {D : D7} (T : Core D) : Gam T ↔ GlobalTheory.RunIn.GamAt T := by
  constructor
  · intro h j hj σ hσ k γ h1 h2
    refine h j hj σ hσ k ⟨h1, fun x hx => ?_⟩
    obtain ⟨y, hy, e⟩ := h2 x hx
    exact ⟨y, hy, by rw [e, Nat.cast_smul_eq_nsmul]⟩
  · intro h j hj σ hσ k γ hγ
    refine h j hj σ hσ k γ hγ.1 fun x hx => ?_
    obtain ⟨y, hy, e⟩ := hγ.2 x hx
    exact ⟨y, hy, by rw [e, Nat.cast_smul_eq_nsmul]⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ArchGlue {D : D7} (V : HSp D) : Prop :=
  ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) →
    (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧
      (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧
    ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) →
      ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ


set_option maxHeartbeats 800000 in
theorem root_eq_one_of_glue {D : D7} (V : HSp D) (hglue : ArchGlue V) {r : ℕ} (hr : V.rank = r) (hr0 : 0 < r) {Comp : Type}
    (X : Comp → Data D.host.E r) (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ)
    (Kf : Subgroup (GA D V)) (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr) (hmu : MuUnit V dict mu)
    (M : ℕ) (hM : 3 ≤ M) (hK : IsLevelK V M Kf) (k : Comp) (γ γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (X k).Γ)
    (hc : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, (γ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ x - x = (M : D.host.E) • y)
    (u : D.host.E) (n : ℕ) (hn : 0 < n) (hu : u ^ n = 1)
    (he : (γ' : Matrix (Fin r) (Fin r) D.host.E) = u • (γ : Matrix (Fin r) (Fin r) D.host.E)) : u = 1 := by
  classical
  subst hr
  obtain ⟨-, -, ⟨x0, hx0, heq⟩, -, -, hfib⟩ := hD
  obtain ⟨hdom, g, hg⟩ := hx0 k
  obtain ⟨hrat, hsur⟩ := hglue (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := heq g
    rw [hg] at this
    exact this
  have hun : ∀ τ : (X k).Ψ, ((γ'.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ'.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    refine unitary_of_first_minor hr0 τ.1 (X k).Gm (X k).Gm_herm _ (mat (x0 k) τ) ?_ ?_ ?_ _ ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, HSpace.gram]
      rw [← V.herm.eq (V.frame b) (V.frame a)]
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ τ.1.injective).2 (gram_det_ne V)
    · intro w hw
      obtain ⟨h, hh, hw'⟩ := hsur (Function.update (fun _ => 1) τ w) (by
        intro τ'
        by_cases e : τ' = τ
        · subst e
          simpa using hw
        · simp [Function.update_of_ne e])
      obtain ⟨γ'', h1, h2⟩ := key h hh
      have h3 := hmu.2.2.2 (g * h)
      rw [h2] at h3
      have h4 := h3 τ ⟨1, by omega⟩
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.dmin_lact (X k) h1] at h4
      unfold dmin at h4
      rw [hact, hw', Function.update_self] at h4
      exact h4
    · have hcc : (γ'.1.map τ.1).map (starRingEnd ℂ) =
          (γ'.1.map cc).map τ.1 := by
        ext a b
        exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
      rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ']
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  obtain ⟨γ'', h1, h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ', mul_mem h1 hγ', ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ').1.map τ.1 * mat (x0 k) τ
    rw [hact, hw, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀
  obtain ⟨hκ1, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have h0 : finHom V h = 1 := hh
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := hκ1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  let f : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.toLinearMap.restrictScalars _
  have hhat : latHat V = GlobalTheory.AdLat.hat D.host.F (V.L0.map f : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hspan : Submodule.span D.host.E (V.L0.map f : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      by_contra hspan
      obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
      obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis V.hT V.nondeg V.frame
      let μ : V.V := ∑ j, star (φ (V.frame j)) • bs j
      have hμ : V.hT μ = φ := by
        apply V.frame.ext
        intro i
        rw [show μ = ∑ j, star (φ (V.frame j)) • bs j from rfl, map_sum, LinearMap.sum_apply]
        have hs : ∀ j, V.hT (star (φ (V.frame j)) • bs j) (V.frame i) =
            φ (V.frame j) * (if i = j then 1 else 0) := by
          intro j
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
          congr 1
          rw [← V.herm.eq (V.frame i) (bs j), hbs]
          split_ifs <;> simp
        simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hμ₀ : μ ≠ 0 := by
        intro h
        apply hφ₀
        rw [← hμ, h, map_zero]
      have hline (a : D.host.E) : a • μ ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
        simp [← V.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ μ).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hline
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E hμ₀ (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (V.L0.map f : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  rw [hhat] at hκ2
  obtain ⟨Λ', g1, g2, g3⟩ := exists_lattice_congr D.host.F D.host.E V.rank M (by omega) (V.L0.map f)
    (V.standardTuple_isLattice.fg.map f) hspan (finHom V g) (finHom V κ⁻¹).1 δ.1 hκ2 (by
      rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul])
  obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases e : τ ∈ (X k).Ψ
    · exact ⟨⟨τ, e⟩⟩
    · exact ⟨⟨_, not_not.1 (fun e' => e (((X k).cmType τ).2 e'))⟩⟩
  have hm : ∀ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h1' : archM V (th k τ) 1 = 1 := by
    unfold archM
    rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.root_of_unity_eq_one_of_conj_congruence D.host.E V.rank M n (X k).Λ Λ' γ.1 δ.1 u τ.1
    (archM V (th k τ) g⁻¹) hr0 hM hn hu (X k).Λ_fg g1 (X k).Λ_span g2 hc g3 ?_ ?_
  · have := congrArg Matrix.det (hm g⁻¹ g)
    rw [inv_mul_cancel, h1', Matrix.det_one, Matrix.det_mul] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  · rw [← he, ← hw τ, ← hδ1 τ, ← hm, ← hm]
    have e : infHom V (h * g⁻¹) = infHom V (g⁻¹ * γ₀) := by
      rw [map_mul, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hinf, mul_inv_cancel_right]
    unfold archM
    rw [e]

theorem gam_of_lawsM {D : D7} (hglue : ∀ V : HSp D, ArchGlue V) (T : Core D) (h : LawsM T) : Gam T := by
  rw [gam_iff]
  intro j hj σ hσ k γ hγ hc
  obtain ⟨hgood, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hnum j hj).2.1
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (h.unf j hj σ hσ) hA hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hK := h.levelK j hj σ hσ
  rw [← h.pins.2.1.1] at hK
  have h1 := root_eq_one_of_glue (T.V j σ) (hglue _) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
    (h.muUnit j hj σ hσ) _ T.Q.l.three_le hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

theorem archGlue {D : D7} (V : HSp D) : ArchGlue V := fun Ψ th h1 h2 =>
  ⟨((GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ th h1 h2).2.1, ((GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ th h1 h2).2.2.2⟩

theorem gam_of_laws {D : D7} (T : Core D) (h : LawsM T) : Gam T := gam_of_lawsM archGlue T h

end GlobalTheory.Survey.ArchimedeanCompatibility
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.Survey.CongruenceSpanLevel

open GlobalTheory.RunIn

theorem gamAt_of_lawsM {D : D7} (T : Core D) (h : LawsM T) : GamAt T :=
  (GlobalTheory.Survey.ArchimedeanCompatibility.gam_iff T).1 (GlobalTheory.Survey.ArchimedeanCompatibility.gam_of_laws T h)

end GlobalTheory.Survey.CongruenceSpanLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseForms
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDescSpan

open NumberField IsDedekindDomain CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open GlobalTheory.DictMove (Carries)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def realFr (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (u : GA D V) (Ψ : Finset (D.host.E →+* ℂ)) : Frame Ψ r :=
  fun τ => ((x₀ τ.1)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V (θ τ.1) u) * x₀ τ.1 :
    Matrix (Fin r) (Fin r) ℂ)

def IsOrthFr {r : ℕ} (X : Data D.host.E r) (y : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat y τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

theorem IsOrthFr.mem_dom {r : ℕ} {X : Data D.host.E r} {y : Frame X.Ψ r} (h : IsOrthFr X y) : y ∈ X.dom :=
  ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1 y h).1

theorem IsOrthFr.lact {r : ℕ} {X : Data D.host.E r} {y : Frame X.Ψ r} (h : IsOrthFr X y) {γ : GL (Fin r) D.host.E}
    (hγ : γ ∈ X.Γ) : IsOrthFr X (lact γ y) := fun τ => by
  rw [← h τ]
  ext p q
  exact (GlobalTheory.LevelCusp.isMatch_of_isUStab X (X.Γ_stab γ hγ)).hermC_eq τ.1 (col (mat y τ) p) (col (mat y τ) q)

theorem det_ne_zero_of_orth {r p : ℕ} (τ : D.host.E →+* ℂ) (G : Matrix (Fin r) (Fin r) D.host.E)
    (x : Matrix (Fin r) (Fin r) ℂ) (h : gram τ G x = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    IsUnit x.det := by
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  have h2 := congrArg Matrix.det h
  rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h2
  refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
  unfold sgn
  split_ifs <;> simp

section Dict

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ} {hr : V.rank = r} {U : Unf Xo c σ r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
  {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}


set_option maxHeartbeats 1000000 in
theorem exists_carries (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hθ : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀) (h δ u : GA D V) (hδ : δ ∈ GQ V)
    (hu : u ∈ GinfC V) :
    ∃ (a : GL (Fin r) D.host.E) (hc : Carries φ LinearMap.id (dict h).1 (dict (δ * h * u)).1 a),
      (dict (δ * h * u)).2 = lact a (castFr hc.mt.psi (rmul (dict h).2 (realFr V hr θ x₀ u _))) := by
  subst hr
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hfr₁⟩ := hD.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hfr₂⟩ := hD.2 (δ * h * u)
  obtain ⟨a, hau, haf, haa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * δ * γ₁⁻¹) (mul_mem (mul_mem hγ₂ hδ) (inv_mem hγ₁))
  have hu1 : finHom V u = 1 := hu
  have hκ' : latGHat V u = latGHat V 1 := ((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.1 _ _ (by rw [hu1, map_one])).2
  have hprod : γ₂ * δ * γ₁⁻¹ * (γ₁ * h) * u = γ₂ * (δ * h * u) := by group
  obtain ⟨gam, e₁, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (δ * h * u)).1) _ _
    (φ _) (φ _) (F.t _) (F.t _) LinearMap.id (γ₁ * h) (γ₂ * δ * γ₁⁻¹) u (hW _) (hW _) (hD.1.1 _) (hD.1.1 _) a hau haf hκ'
    (fun a _ => ⟨0, zero_mem _, by
      rw [hu1, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) ⟨hΛ₁, hm₁⟩
    (by rw [hprod]; exact ⟨hΛ₂, hm₂⟩)
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hli : ∀ v, (a⁻¹).1 *ᵥ (a.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hm : IsMatch (U.X (dict h).1) (U.X (dict (δ * h * u)).1) a := by
    refine ⟨Finset.ext fun τ => ?_, ?_, (hW _).2.trans (hW _).2.symm, fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [(hU.2.1 _).2 τ, (hU.2.1 _).2 τ]
    · rw [(hU.2.1 _).1, (hU.2.1 _).1]
    · rw [hG, hG]
      exact hau u v
    · have := hgam ((φ _).symm ⟨v, hv⟩)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this ▸ (φ _ _).2
    · have := hgam (gam.symm ((φ _).symm ⟨_, hv⟩))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      have e₁ := congrArg (fun w => (a⁻¹).1 *ᵥ w) this
      simp only [hli] at e₁
      exact e₁ ▸ (φ _ _).2
  refine ⟨a, ⟨hm, (hG _).trans (hG _).symm, gam, e₁, t₁, hgam⟩, funext fun τ => ?_⟩
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have h1 := hfr₁ ⟨τ.1, hm.mem τ⟩
  have h2 := hfr₂ τ
  rw [GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth _ ⟨τ.1, hm.mem τ⟩) (hθ τ.1)] at h1
  rw [GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth _ τ) (hθ τ.1), ← hprod, (hAr τ.1).2.1, (hAr τ.1).2.1,
    haa τ.1 _ (hθ τ.1)] at h2
  have hx := det_ne_zero_of_orth _ _ _ (hx₀ _ τ.1 τ.2)
  change mat (dict (δ * h * u)).2 τ = a.1.map τ.1 * (mat (dict h).2 ⟨τ.1, hm.mem τ⟩ *
    ((x₀ τ.1)⁻¹ * archM V (θ τ.1) u * x₀ τ.1))
  rw [h1, h2]
  change a.1.map τ.1 * archM V (θ τ.1) (γ₁ * h) * archM V (θ τ.1) u * x₀ τ.1 =
    a.1.map τ.1 * (archM V (θ τ.1) (γ₁ * h) * x₀ τ.1 * ((x₀ τ.1)⁻¹ * archM V (θ τ.1) u * x₀ τ.1))
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hx]


set_option maxHeartbeats 1000000 in
theorem orth_and_onto (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hθ : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀) (hι : GlobalTheory.Member.IotaOK Dw V io)
    (h : GA D V) :
    IsOrthFr (U.X (dict h).1) (dict h).2 ∧ ∀ y, IsOrthFr (U.X (dict h).1) y →
      ∃ u ∈ GinfC V, y = rmul (dict h).2 (realFr V hr θ x₀ u _) := by
  subst hr
  obtain ⟨γ, -, -, -, hfr⟩ := hD.2 h
  obtain ⟨hAr, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hfr' : ∀ τ, mat (dict h).2 τ = archM V (θ τ.1) (γ * h) * x₀ τ.1 := fun τ => by
    rw [hfr τ, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1)]
    rfl
  refine ⟨fun τ => ?_, fun y hy => ?_⟩
  · rw [hfr', ← hx₀ _ τ.1 τ.2]
    refine (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank 0 ∅ _
      (U.X (dict h).1).Gm_herm).2.2 τ.1 _ _ ?_
    rw [hG]
    exact (hAr τ.1).2.2.2.2 (γ * h)
  let k := (dict h).1
  obtain ⟨-, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  have hmem : ∀ (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
    intro τ
    rw [(hU.2.1 k).2 τ, hι.rt, hι.rt0]
  have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (U.X k).Ψ,
      uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat y ⟨τ, hτ⟩ = u * x₀ τ := by
    intro τ
    by_cases hτ : τ ∈ (U.X k).Ψ
    · obtain ⟨u, hu⟩ := h4 τ (x₀ τ) (mat y ⟨τ, hτ⟩) (hx₀ k τ hτ) ((hy ⟨τ, hτ⟩).trans (hx₀ k τ hτ).symm)
      rw [hG] at hu
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hτ⟩
  choose u hu using hex
  obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem τ).2 hτ)).1
  obtain ⟨a₀, ha₀, f, hf, hs⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 (γ * h)
  refine ⟨a₀⁻¹ * a, mul_mem (inv_mem ha₀) ha, funext fun τ => ?_⟩
  have hx := det_ne_zero_of_orth _ _ _ (hx₀ _ τ.1 τ.2)
  change mat y τ = mat (dict h).2 τ * ((x₀ τ.1)⁻¹ * archM V (θ τ.1) (a₀⁻¹ * a) * x₀ τ.1)
  rw [hfr', hs, (hAr τ.1).2.1 a₀ f, (hAr τ.1).2.2.1 f hf, Matrix.mul_one]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hx]
  rw [← Matrix.mul_assoc, ← (hAr τ.1).2.1, mul_inv_cancel_left, hau τ.1 ((hmem τ.1).1 τ.2)]
  exact (hu τ.1 τ.2).2

theorem exists_idMove (Xo : Moduli Dw l) (c : Coeff l) : ∃ ν₀ : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X),
    IsLevMove (𝟙 Xo.X) ν₀ LinearMap.id LinearMap.id ∧
      ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)), FrMove (𝟙 Xo.X) ν₀ y y ∧
        ∀ y', FrMove (𝟙 Xo.X) ν₀ y y' → y' = y := by
  obtain ⟨ν₀, hν₀, hy₀⟩ := (GlobalTheory.MoveCalc.frMove_calculus _ H Dw l Xo c).1
  exact ⟨ν₀, ⟨Category.id_comp _, fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm,
      fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm⟩, fun σ y => ⟨hy₀ _ y,
    fun y' hy => (GlobalTheory.exists_unique_frMove _ H Dw l Xo c _ ν₀ (Category.id_comp _) _ y).2 _ _ ν₀ rfl hy (hy₀ _ y)⟩⟩

theorem of_carries_id (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hP : GlobalTheory.DictMove.HasPeriods φ) {k k' : U.Comp} {a : GL (Fin r) D.host.E} (hc : Carries φ LinearMap.id k k' a) :
    k = k' ∧ IsUStab (U.X k').Gm (U.X k').Λ a ∧
      ∀ v ∈ (U.X k').Λ, ∃ u ∈ (U.X k').Λ, a.1 *ᵥ v = v + l.M • u := by
  obtain ⟨ν₀, h₀, hy⟩ := exists_idMove Xo c
  obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected _ r (U.X k)).nonempty
  obtain ⟨h1, h2⟩ := GlobalTheory.DictMove.carries_unique hσ hU hpq hA hP (GlobalTheory.DictMove.carries_one φ k) hc h₀ ⟨x, hx⟩
    (hy σ _).1
  have h3 := h2 h1
  rw [inv_one, mul_one] at h3
  exact ⟨h1, h3⟩

theorem rdU_of_carries_id (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hP : GlobalTheory.DictMove.HasPeriods φ) (hE : ∀ k, GlobalTheory.UnitConst.ExactAt (Formalism.L2.PjFree.Unf.ofPj U) k)
    {k k' : U.Comp} {a : GL (Fin r) D.host.E} (hc : Carries φ LinearMap.id k k' a)
    {w : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hw : Dom w n) {f : Rul Xo c} (hf : f ∈ sec Xo c w n)
    {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    rdU U f k' (lact a (castFr hc.mt.psi x)) = rdU U f k x := by
  obtain ⟨ν₀, h₀, hy⟩ := exists_idMove Xo c
  exact (GlobalTheory.UnitConst.rdU_eq_of_comp_eq (U := Formalism.L2.PjFree.Unf.ofPj U) hE h₀.1 hw hf hf
    (fun y y' h => by rw [(hy σ y).2 y' h]) (h := hc.mt) (of_carries_id hσ hU hpq hA hP hc).1.symm
    (fun z y' hm => GlobalTheory.DictMove.move_eq hσ hpq hA hP hc h₀ z hm) hx).symm

end Dict

section Core

open GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.FinalJoin

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}
  {θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem base_real (hT : LawsJ T) (hj : InR D j) (hσ : GoodEmb T.Q.c σ) (hr : (T.V j σ).rank = D.R.r)
    (hθ : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) (h u : GA D (T.V j σ)) (hu : u ∈ GinfC (T.V j σ)) :
    ∃ γ ∈ ((T.U j σ).X (T.dict j σ h).1).Γ, T.dict j σ (h * u) =
      ⟨(T.dict j σ h).1, lact γ (rmul (T.dict j σ h).2 (realFr (T.V j σ) hr θ (T.x₀ j σ) u _))⟩ := by
  obtain ⟨hr', m, e, F, ik, φ, th, -, -, hth, hd⟩ := hT.adPin j hj σ hσ
  obtain ⟨_, hW⟩ := hT.modelW j hj σ hσ
  have hU := hT.unf j hj σ hσ
  have h0 := exists_carries hU hW hth hd hθ (hT.familyUniformisationBasePointOrthogonal j hj σ hσ) h 1 u (one_mem _) hu
  rw [one_mul] at h0
  generalize T.dict j σ (h * u) = p at h0 ⊢
  obtain ⟨k', x'⟩ := p
  obtain ⟨a, hc, hx⟩ := h0
  obtain ⟨h1, h2, h3⟩ := of_carries_id hσ hU (GlobalTheory.UnitConst.one_le_rank hT hj) hT.pins.2.1.2 hd.1.2 hc
  dsimp only at h1 h2 h3 hx hc
  subst h1
  refine ⟨a, GlobalTheory.Survey.CongruenceSpanLevel.gamAt_of_lawsM _ hT.toLawsM j hj σ hσ _ a h2 fun v hv => ?_, ?_⟩
  · obtain ⟨y, hy, e⟩ := h3 v hv
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  · rw [hx]
    rfl

theorem base_orth (hT : LawsJ T) (hj : InR D j) (hσ : GoodEmb T.Q.c σ) (hr : (T.V j σ).rank = D.R.r)
    (hθ : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) (h : GA D (T.V j σ)) :
    IsOrthFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2 ∧ ∀ y, IsOrthFr ((T.U j σ).X (T.dict j σ h).1) y →
      ∃ u ∈ GinfC (T.V j σ), y = rmul (T.dict j σ h).2 (realFr (T.V j σ) hr θ (T.x₀ j σ) u _) := by
  obtain ⟨hr', m, e, F, ik, φ, th, -, -, hth, hd⟩ := hT.adPin j hj σ hσ
  obtain ⟨_, hW⟩ := hT.modelW j hj σ hσ
  exact orth_and_onto (hT.unf j hj σ hσ) hW hth hd hθ (hT.familyUniformisationBasePointOrthogonal j hj σ hσ)
    (GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr).1 h


set_option maxHeartbeats 1000000 in
theorem cover_real (hT : LawsJ T) (hj : InR D j) (hσ : GoodEmb T.Q.c σ) (hr : (T.V j σ).rank = D.R.r)
    (hθ : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) (C : Cover T j σ) (hC : C.IsUnif) (h δ u : GA D (T.V j σ))
    (hδ : δ ∈ GQ (T.V j σ)) (hu : u ∈ GinfC (T.V j σ)) :
    (C.dict₂ (δ * h * u)).1 = (C.dict₂ h).1 ∧ ∀ a n, Dom a n → ∀ f ∈ sec C.d.Xo₂ C.d.c₂ a n,
      rdU C.U₂ f (C.dict₂ (δ * h * u)).1 (C.dict₂ (δ * h * u)).2 =
        rdU C.U₂ f (C.dict₂ h).1 (rmul (C.dict₂ h).2 (realFr (T.V j σ) hr θ (T.x₀ j σ) u _)) := by
  obtain ⟨-, hA, hinc, hU, hdom, hr', g, e, F, ik, φ, th, hW, hth, hD⟩ := hC
  obtain ⟨hio, hx⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := GlobalTheory.UnitConst.one_le_rank hT hj
  have hσ₂ : GoodEmb C.d.c₂ C.σ₂ := by
    rw [← hinc] at hσ
    exact hσ
  have hx₀ : ∀ k, IsOrthogonalFrame (C.U₂.X k) (T.x₀ j σ) := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  have hE : ∀ k, GlobalTheory.UnitConst.ExactAt (Formalism.L2.PjFree.Unf.ofPj C.U₂) k := fun k => by
    obtain ⟨hxi, φD, h1, h2, h3⟩ := GlobalTheory.GeoLevel.model_space_of_lawsJ D T hT j hj σ hσ (T.dict j σ 1).1
    obtain ⟨_, hW₁⟩ := hT.modelW j hj σ hσ
    rw [(hW₁ _).2, ← (hW k).2] at hxi h3
    rw [(hW₁ _).1, ← (hW k).1] at h3
    obtain ⟨h4, h5⟩ := GlobalTheory.GeoLevel.four_dvd_finrank_and_det_eq_pm_one D
    intro δ hm
    exact GlobalTheory.GeoLevel.rdU_move_eq _ _ _ _ _ _ C.σ₂ _ (Formalism.L2.PjFree.Unf.ofPj C.U₂) hσ₂ hU k φD h1 h2 h3 hxi δ hm
      ((h5 _ _ δ hm).imp_right fun e => ⟨e, h4⟩)
  obtain ⟨a, hc, hfr⟩ := exists_carries hU hW hth hD hθ hx₀ h δ u hδ hu
  refine ⟨(of_carries_id hσ₂ hU hpq hA hD.1.2 hc).1.symm, fun w n hw f hf => ?_⟩
  have hy := (GlobalTheory.UnitConst.isMatch_symm hc.mt).mem_dom (hdom (δ * h * u))
  rw [hfr, GlobalTheory.UnitConst.lact_cast_lact, inv_mul_cancel, GlobalTheory.UnitConst.lact_one_cast] at hy
  rw [hfr]
  exact rdU_of_carries_id hσ₂ hU hpq hA hD.1.2 hE hc hw hf hy

end Core

section Descent

open GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.FinalJoin

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}
  {θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem exists_match (hT : LawsJ T) (hj : InR D j) (hσ : GoodEmb T.Q.c σ) (C : Cover T j σ) (hC : C.IsUnif)
    (h : GA D (T.V j σ)) :
    ∃ (γ : GL (Fin D.R.r) D.host.E) (hm : IsMatch (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) γ),
      (T.dict j σ h).2 = lact γ (castFr hm.psi (C.dict₂ h).2) := by
  obtain ⟨γ, hΛ, hiso, hfr⟩ := GlobalTheory.CoverFrameMove.frames_differ D T hT j hj σ hσ C hC h
  obtain ⟨-, -, -, hU₂, -, hr', g, e, F, ik, φ, th, hW, -⟩ := hC
  obtain ⟨_, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hm : IsMatch (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) γ := by
    refine ⟨Finset.ext fun τ => ?_, ?_, (hW _).2.trans (hW₁ _).2.symm, hiso, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [(hU₂.2.1 _).2 τ, (hU₁.2.1 _).2 τ]
    · rw [(hU₂.2.1 _).1, (hU₁.2.1 _).1]
    · rw [← SetLike.mem_coe, hΛ]
      exact ⟨v, hv, rfl⟩
    · rw [← SetLike.mem_coe, hΛ] at hv
      obtain ⟨w, hw, e⟩ := hv
      have : w = v := by rw [← GlobalTheory.Dict.Pull.inv_mulVec γ w, e, GlobalTheory.Dict.Pull.inv_mulVec]
      exact this ▸ hw
  exact ⟨γ, hm, funext fun τ => hfr τ.1 (hm.mem τ) τ.2⟩

theorem laU_eq (hT : LawsJ T) (hj : InR D j) (hσ : GoodEmb T.Q.c σ) (C : Cover T j σ) (hC : C.IsUnif)
    (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : D.host.E →+* ℂ)
    (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ) (i : Fin D.R.r) :
    laU C.U₂ a n k₂ ⟨τ, h₂⟩ i = laU (T.U j σ) a n k ⟨τ, h₁⟩ i := by
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hT.unf j hj σ hσ
  have hrel : relab C.d.c₂ C.σ₂ = relab T.Q.c σ := by
    funext τ
    ext x
    have e := congrArg (fun φ : T.Q.c.F →+* ℂ => φ (embF T.Q.c τ x)) hC.2.2.1
    simp only [RingHom.comp_apply] at e
    show C.σ₂ (embF C.d.c₂ τ x) = σ (embF T.Q.c τ x)
    rw [← e]
    congr 1
  unfold laU
  rw [(hU₂.2.1 k₂).1, (hU₁.2.1 k).1, hrel]


set_option maxHeartbeats 1000000 in
theorem descent_comp (hT : LawsJ T) (hj : InR D j) (hσ : GoodEmb T.Q.c σ) (hr : (T.V j σ).rank = D.R.r)
    (hθ : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) (C : Cover T j σ) (hC : C.IsUnif)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hDom : Dom a n) (Φ₂ : FDSec C.U₂.X)
    (hSS : ∀ k, Φ₂ k ∈ (C.U₂.X k).SS (laU C.U₂ a n k))
    (hinv : ∀ h δ u, δ ∈ GQ (T.V j σ) → u ∈ GinfC (T.V j σ) →
      Φ₂ (C.dict₂ (δ * h * u)).1 (C.dict₂ (δ * h * u)).2 =
        Φ₂ (C.dict₂ h).1 (rmul (C.dict₂ h).2 (realFr (T.V j σ) hr θ (T.x₀ j σ) u _)))
    (hK : ∀ κ ∈ T.Kf j σ, ∀ h, C.cc₂ (C.dict₂ (h * κ)).1 * Φ₂ (C.dict₂ (h * κ)).1 (C.dict₂ (h * κ)).2 =
      C.cc₂ (C.dict₂ h).1 * Φ₂ (C.dict₂ h).1 (C.dict₂ h).2) (k : (T.U j σ).Comp) :
    ∃ P ∈ ((T.U j σ).X k).SS (laU (T.U j σ) a n k), (∀ x, x ∉ ((T.U j σ).X k).dom → P x = 0) ∧
      ∀ h x, T.dict j σ h = ⟨k, x⟩ → P x = C.cc₂ (C.dict₂ h).1 * Φ₂ (C.dict₂ h).1 (C.dict₂ h).2 := by
  classical
  obtain ⟨th, hr', -, -, -, -, -, hsurj, hfib⟩ := hT.dictU j hj σ hσ
  obtain ⟨h₀, rfl⟩ : ∃ h₀, (T.dict j σ h₀).1 = k := by
    obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected _ _ ((T.U j σ).X k)).nonempty
    obtain ⟨g, _, -, _, -, hg⟩ := hsurj k x hx
    exact ⟨g, congrArg Sigma.fst hg⟩
  obtain ⟨γ, hm, hfr⟩ := exists_match hT hj hσ C hC h₀
  have hm' := GlobalTheory.UnitConst.isMatch_symm hm
  have hback : lact γ⁻¹ (castFr hm'.psi (T.dict j σ h₀).2) = (C.dict₂ h₀).2 := by
    rw [hfr, GlobalTheory.UnitConst.lact_cast_lact, inv_mul_cancel, GlobalTheory.UnitConst.lact_one_cast]
  let G : GA D (T.V j σ) → ℂ := fun h => C.cc₂ (C.dict₂ h).1 * Φ₂ (C.dict₂ h).1 (C.dict₂ h).2
  have hG : ∀ h δ u, δ ∈ GQ (T.V j σ) → u ∈ GinfC (T.V j σ) → G (δ * h * u) = C.cc₂ (C.dict₂ h).1 *
      Φ₂ (C.dict₂ h).1 (rmul (C.dict₂ h).2 (realFr (T.V j σ) hr θ (T.x₀ j σ) u _)) := fun h δ u hδ hu => by
    simp only [G]
    rw [hinv h δ u hδ hu, (cover_real hT hj hσ hr hθ C hC h δ u hδ hu).1]
  have hGfib : ∀ g g' x γ', γ' ∈ ((T.U j σ).X (T.dict j σ h₀).1).Γ → T.dict j σ g = ⟨(T.dict j σ h₀).1, x⟩ →
      T.dict j σ g' = ⟨(T.dict j σ h₀).1, lact γ' x⟩ → G g' = G g := fun g g' x γ' hγ' hg hg' => by
    obtain ⟨δ, hδ, κ, hκ, rfl⟩ := hfib g g' (by rw [hg]; exact ⟨γ', hγ', hg'⟩)
    have e1 := hG g δ 1 hδ (one_mem _)
    have e2 := hG g 1 1 (one_mem _) (one_mem _)
    rw [mul_one] at e1
    rw [mul_one, one_mul] at e2
    exact (hK κ hκ _).trans (e1.trans e2.symm)
  let Q : Frame ((T.U j σ).X (T.dict j σ h₀).1).Ψ D.R.r → ℂ := fun x =>
    C.cc₂ (C.dict₂ h₀).1 * Φ₂ (C.dict₂ h₀).1 (lact γ⁻¹ (castFr hm'.psi x))
  let P : Frame ((T.U j σ).X (T.dict j σ h₀).1).Ψ D.R.r → ℂ := fun x =>
    if x ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom then Q x else 0
  have hPQ : ∀ x ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom, P x = Q x := fun x hx => if_pos hx
  have hval : ∀ y, IsOrthFr ((T.U j σ).X (T.dict j σ h₀).1) y → ∀ h γ', γ' ∈ ((T.U j σ).X (T.dict j σ h₀).1).Γ →
      T.dict j σ h = ⟨(T.dict j σ h₀).1, lact γ' y⟩ → Q y = G h := fun y hy h γ' hγ' hh => by
    obtain ⟨u, hu, e⟩ := (base_orth hT hj hσ hr hθ h₀).2 y hy
    obtain ⟨γa, hγa, ea⟩ := base_real hT hj hσ hr hθ h₀ u hu
    rw [← e] at ea
    rw [hGfib (h₀ * u) h _ (γ' * γa⁻¹) (mul_mem hγ' (inv_mem hγa)) ea
      (by rw [hh, GlobalTheory.Dict.Extend.lact_lact, inv_mul_cancel_right])]
    have e1 := hG h₀ 1 u (one_mem _) hu
    rw [one_mul] at e1
    rw [e1, e]
    simp only [Q]
    rw [GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul, hback]
    rfl
  have hla : ∀ (τ : (C.U₂.X (C.dict₂ h₀).1).Ψ) i, laU C.U₂ a n (C.dict₂ h₀).1 τ i =
      laU (T.U j σ) a n (T.dict j σ h₀).1 ⟨τ.1, hm'.mem τ⟩ i := fun τ i => laU_eq hT hj hσ C hC _ _ a n τ.1 τ.2 _ i
  obtain ⟨hd₂, hb₂, -⟩ := (hSS (C.dict₂ h₀).1).1.1
  have hQb : ∀ x ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom, ∀ b ∈ Bor ((T.U j σ).X (T.dict j σ h₀).1).Ψ D.R.r,
      Q (rmul x b) = bchar (laU (T.U j σ) a n (T.dict j σ h₀).1) b * Q x := fun x hx b hb => by
    simp only [Q]
    rw [GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul, hb₂ _ (hm'.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor hm'.psi hb),
      GlobalTheory.Dict.Pull.cast_bchar hm'.psi hla, mul_left_comm]
  have hQγ : ∀ γ' ∈ ((T.U j σ).X (T.dict j σ h₀).1).Γ, ∀ x ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom,
      lact γ' x ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom ∧ Q (lact γ' x) = Q x := fun γ' hγ' x hx => by
    have hx' : lact γ' x ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
      (GlobalTheory.LevelCusp.isMatch_of_isUStab _ (Data.Γ_stab _ γ' hγ')).mem_dom hx
    refine ⟨hx', ?_⟩
    obtain ⟨y, b, hb, hy, e⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E _ _ _ _
      ((T.U j σ).X (T.dict j σ h₀).1).Gm_herm).1 x hx
    have hy' := IsOrthFr.lact hy hγ'
    obtain ⟨u, hu, e'⟩ := (base_orth hT hj hσ hr hθ h₀).2 _ hy'
    obtain ⟨γa, hγa, ea⟩ := base_real hT hj hσ hr hθ h₀ u hu
    rw [← e'] at ea
    have v1 := hval _ hy' _ _ hγa ea
    have v2 := hval _ hy (h₀ * u) _ (mul_mem hγa hγ') (by rw [ea, GlobalTheory.Dict.Extend.lact_lact])
    have v3 := v1.trans v2.symm
    rw [e, GlobalTheory.Dict.Extend.lact_rmul, hQb _ hx' b hb, hQb _ hx b hb] at v3
    exact mul_left_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne _ _ hb) v3
  have hsec : ((T.U j σ).X (T.dict j σ h₀).1).IsSec (laU (T.U j σ) a n (T.dict j σ h₀).1) P := by
    refine ⟨DifferentiableOn.congr (f := Q) ?_ hPQ, fun x hx b hb => ?_, fun γ' hγ' x hx => ?_⟩
    · exact (hd₂.comp ((GlobalTheory.Dict.Extend.differentiable_lact γ⁻¹).comp
        (GlobalTheory.Dict.Pull.cast_diff hm'.psi)).differentiableOn fun x hx => hm'.mem_dom hx).const_mul _
    · rw [hPQ _ (OrthogonalFrameDomain.rmul_mem_dom _ hx hb), hPQ _ hx, hQb x hx b hb]
    · rw [hPQ _ (hQγ γ' hγ' x hx).1, hPQ _ hx, (hQγ γ' hγ' x hx).2, hT.chiTriv j hj σ hσ a n hDom _ γ' hγ', one_mul]
  refine ⟨P, GlobalTheory.LevelCusp.mem_SS_of_isMatch _ _ _ _ γ⁻¹ hm' _ _ hla P _ _ hsec (hSS _) hPQ,
    fun x hx => if_neg hx, fun h x hh => ?_⟩
  have hx : IsOrthFr ((T.U j σ).X (T.dict j σ h₀).1) x := by
    have := (base_orth hT hj hσ hr hθ h).1
    rw [hh] at this
    exact this
  rw [hPQ _ hx.mem_dom]
  exact hval x hx h 1 (one_mem _) (by rw [hh, GlobalTheory.Dict.Extend.lact_one])

end Descent

open GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin


set_option maxHeartbeats 1000000 in
theorem exists_descent : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ Φ₂ ∈ Formalism.L2.Pj.holSub0 C.U₂.X (laU C.U₂ a n), Φ₂ ∈ Submodule.span ℂ (rdU C.U₂ '' (sec C.d.Xo₂ C.d.c₂ a n : Set (Rul C.d.Xo₂ C.d.c₂))) → (∀ k ∈ T.Kf j σ, ∀ h, adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂) Φ₂ (h * k) = adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂) Φ₂ h) → ∃ Φ ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) a n), adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂) Φ₂ = adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) Φ := by
  intro D T hT j hj σ hσ C hC a n hDom hmu Φ₂ hΦ₂ hsp hK
  obtain ⟨hr, -⟩ := hT.modelW j hj σ hσ
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have hinv : ∀ h δ u, δ ∈ GQ (T.V j σ) → u ∈ GinfC (T.V j σ) →
      Φ₂ (C.dict₂ (δ * h * u)).1 (C.dict₂ (δ * h * u)).2 =
        Φ₂ (C.dict₂ h).1 (rmul (C.dict₂ h).2 (realFr (T.V j σ) hr θ (T.x₀ j σ) u _)) := fun h δ u hδ hu => by
    clear hK hΦ₂
    induction hsp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact (cover_real hT hj hσ hr hθ C hC h δ u hδ hu).2 a n hDom f hf
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c * ·) hx
  have hmu0 : ∀ h, T.mu j σ h ≠ 0 := fun h => norm_ne_zero_iff.1 (by rw [(hT.muVal j hj σ hσ).norm]; exact one_ne_zero)
  have hc0 : ∀ k, T.cE j σ k ≠ 0 := fun k => norm_ne_zero_iff.1 (by rw [hT.cUnit j hj σ hσ k]; exact one_ne_zero)
  choose P hP hP0 hPv using descent_comp hT hj hσ hr hθ C hC hDom Φ₂
    (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hΦ₂.1) hinv (fun κ hκ h => by
      have e := hK κ hκ h
      rw [adel_muPin, adel_muPin, hmu κ hκ] at e
      apply mul_left_cancel₀ (hmu0 h)
      linear_combination e)
  refine ⟨fun k => (T.cE j σ k)⁻¹ • P k, ⟨holCusp_mem_holSub _ _ fun k => ?_, fun k x hx => ?_⟩, funext fun h => ?_⟩
  · exact (siegelSpaceAlgebra_holds (E := D.host.E) _ ((T.U j σ).X k) (laU (T.U j σ) a n k) (laU (T.U j σ) a n k) 0).1.2.2 _ _ (hP k)
  · show (T.cE j σ k)⁻¹ * P k x = 0
    rw [hP0 k x hx, mul_zero]
  · rw [adel_muPin, adel_muPin]
    show _ = _ * ((T.cE j σ (T.dict j σ h).1)⁻¹ * P (T.dict j σ h).1 (T.dict j σ h).2)
    rw [hPv _ h _ rfl]
    have := hc0 (T.dict j σ h).1
    field_simp

theorem mem_span_baseForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → φ ∈ Submodule.span ℂ (baseForms T j σ a n) := by
  intro D T hL j hj σ hσ C hC a n hDom _ hspan hmu φ hφ hinv
  obtain ⟨f₂, ⟨hs₂, hf₂⟩, rfl⟩ := hφ
  by_cases h0 : (lieFac (T.Q.Dw j) (xiR D) a : ℂ) = 0
  · have : C.rd a f₂ = 0 := by
      unfold Cover.rd
      rw [h0, zero_smul]
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨Φ, hΦ, hEq⟩ := exists_descent D T hL j hj σ hσ C hC a n hDom hmu (rdU C.U₂ f₂) hf₂
    (Submodule.subset_span ⟨f₂, hs₂, rfl⟩) (by
    intro k hk h
    have e := hinv k hk h
    unfold Cover.rd at e
    simp only [Pi.smul_apply, smul_eq_mul] at e
    exact mul_left_cancel₀ h0 e)
  have hrd : C.rd a f₂ = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) Φ := by
    unfold Cover.rd
    rw [hEq]
  rw [hrd]
  have hΦs := hspan hΦ
  clear hEq hrd hΦ
  induction hΦs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact Submodule.subset_span ⟨f, hf, rfl⟩
  | zero =>
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.CoverDescSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseFormsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverForm_levelInvariant_mem_span_baseForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → φ ∈ Submodule.span ℂ (baseForms T j σ a n) := by
  first | exact @GlobalTheory.CoverDescSpan.mem_span_baseForms | exact GlobalTheory.CoverDescSpan.mem_span_baseForms | (intros; apply GlobalTheory.CoverDescSpan.mem_span_baseForms <;> assumption)
end

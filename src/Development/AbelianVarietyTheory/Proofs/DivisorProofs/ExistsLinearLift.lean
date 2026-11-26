module

public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem zeta_eval {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μW : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μW 𝓖 (HW.e x) (HW.e y)) (θ : Datum.InfFam D)
    {J : Set (GA D W)} {χ : GA D W → ℂ} (U₁ U₂ : HW.H) (hU : HW.e U₁ ∈ Mult θ M J χ) (v : M.Vec) (K : Subgroup (GA D W))
    {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓧 : Set X) (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (φ f : X → ℂ)
    (Fr : Frames W) (hFr : ∀ ρ b, realMat W Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (mR : ∀ ρ, Measure (Upq W ρ))
    (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) (c0 z : ℂ)
    (hF : ∀ x ∈ GfC W, ∀ g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) →
      l2 μ 𝓧 (ω (1, x * realElt θ W g) φ) φ =
        c0 * (∏ ρ, ⟪(v ρ : M.H ρ), M.rep ρ (g ρ) (v ρ : M.H ρ)⟫_ℂ) * 1 * l2 μ 𝓧 (ω (1, x) f) f)
    (hZ : ∀ v₁ v₂ : M.Vec, HasSum (fun y : FinCos W K =>
        l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (l2 μW 𝓖 (rTr W y.rep (HW.e U₁ v₁)) (HW.e U₂ v₂)))
      (z * starRingEnd ℂ (l2 μW 𝓖 (HW.e U₁ v₁) (HW.e U₂ v₂)))) :
    ∫ b : ∀ ρ, Upq W ρ, ∑' x : FinCos W K, l2 μ 𝓧 (ω (1, x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) φ) φ *
        starRingEnd ℂ (l2 μW 𝓖 (rTr W (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) (HW.e U₁ v)) (HW.e U₂ v))
        ∂(Measure.pi mR) =
      c0 * z * starRingEnd ℂ (ipM M μW 𝓖 (HW.e U₂) (HW.e U₁)) *
        ((∏ ρ, ∫ b, ‖⟪(v ρ : M.H ρ), M.rep ρ (realMat W Fr ρ b) (v ρ : M.H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) : ℝ) : ℂ) := by
  have hIP : IsMultIP M μW 𝓖 (HW.e U₂) (HW.e U₁) (ipM M μW 𝓖 (HW.e U₂) (HW.e U₁)) := by
    have existsIP (x y : HW.H) (hxy : inner ℂ x y ≠ 0) : ∃ c, IsMultIP M μW 𝓖 (HW.e x) (HW.e y) c := by
      by_contra h
      apply hxy
      rw [hW, ipM, dite_eq_right h, mul_zero]
    apply ipM_spec
    by_cases hx : U₂ = 0
    · subst U₂
      exact ⟨0, fun v₁ v₂ => by simp⟩
    by_cases hxy : inner ℂ U₂ U₁ = 0
    · obtain ⟨c, hc⟩ := existsIP U₂ (U₂ + U₁) (by
        rw [inner_add_right, hxy, add_zero]
        exact inner_self_ne_zero.2 hx)
      obtain ⟨c', hc'⟩ := existsIP U₂ U₂ (inner_self_ne_zero.2 hx)
      refine ⟨c - c', fun v₁ v₂ => ?_⟩
      have hsub : (fun x => star (HW.e U₂ v₁ x) * HW.e U₁ v₂ x) =
          fun x => star (HW.e U₂ v₁ x) * HW.e (U₂ + U₁) v₂ x - star (HW.e U₂ v₁ x) * HW.e U₂ v₂ x := by
        funext x
        simp [mul_add]
      rw [hsub]
      exact ⟨(hc v₁ v₂).1.sub (hc' v₁ v₂).1, by
        rw [integral_sub (hc v₁ v₂).1 (hc' v₁ v₂).1, (hc v₁ v₂).2, (hc' v₁ v₂).2, sub_mul]⟩
    · exact existsIP U₂ U₁ hxy
  have := fun ρ => sigmaFinite_haar (mR ρ) (hmR ρ).1
  refine integral_pi_eval mR (fun ρ b => ⟪(v ρ : M.H ρ), M.rep ρ (realMat W Fr ρ b) (v ρ : M.H ρ)⟫_ℂ) _ c0 z _ fun b => ?_
  let g := fun ρ => realMat W Fr ρ (b ρ)
  have hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) := fun ρ => hFr ρ (b ρ)
  let w : M.Vec := fun ρ => ⟨_, rep_mem_sm M ρ (g ρ) (hg ρ) _ (v ρ).2⟩
  have hTranslate (U : MMap M) (hU : U ∈ Mult θ M J χ) : U w = rTr W (realElt θ W g) (U v) := by
    classical
    induction hU using Submodule.span_induction with
    | mem U hU =>
      change IsMultMap θ M J χ U at hU
      have hList (l : List D.what₂.Tau) (hl : l.Nodup) :
          U (fun ρ => if ρ ∈ l then w ρ else v ρ) =
            rTr W (l.map fun ρ => atTau θ W ρ (g ρ)).prod (U v) := by
        induction l with
        | nil =>
          funext x
          simp [rTr]
        | cons a l ih =>
          rw [List.nodup_cons] at hl
          have he := hU.equiv a (g a) (hg a) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w a) (by
            simp only [ite_eq_right hl.1]
            rfl)
          rw [ih hl.2] at he
          rw [List.map_cons, List.prod_cons, rTr_mul, ← he]
          congr 1
          funext ρ
          by_cases hρ : ρ = a
          · subst hρ
            simp
          · rw [Function.update_of_ne hρ]
            simp [hρ]
      unfold realElt
      rw [← hList _ (Finset.nodup_toList _)]
      congr 1
      funext ρ
      simp
    | zero =>
      funext x
      simp [rTr]
    | add U U' _ _ h₁ h₂ =>
      funext x
      have he₁ := congrFun h₁ x
      have he₂ := congrFun h₂ x
      simp only [rTr, add_apply, Pi.add_apply] at he₁ he₂ ⊢
      rw [he₁, he₂]
    | smul c U _ h =>
      funext x
      have he := congrFun h x
      simp only [rTr, smul_apply, Pi.smul_apply] at he ⊢
      rw [he]
  have h2 : l2 μW 𝓖 (HW.e U₁ w) (HW.e U₂ v) =
      ipM M μW 𝓖 (HW.e U₂) (HW.e U₁) * ∏ ρ, ⟪(v ρ : M.H ρ), M.rep ρ (g ρ) (v ρ : M.H ρ)⟫_ℂ :=
    (l2_eq_star μW 𝓖 _ _).trans (hIP v w).2
  rw [← h2]
  refine tsum_eval _ _ _ _ _ (fun x => ?_) (hZ w v)
  rw [hF x.rep x.out.2 _ hg, rTr_mul, ← hTranslate (HW.e U₁) hU]

theorem eventually_grpOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), ∃ h : (finHom V).rangeRestrict κ ∈ grpOf V β L, chrOf V β L ⟨_, h⟩ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  have hk : Lev.finE V κ ∈ lev D.sp.cm V.gram β L :=
    Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩
  exact ⟨hk, GlobalTheory.ThetaIntegrand.levFn_eq_one β (Lev.finE V κ) L (fun PP hP => h3 PP (Finset.mem_union_left _ hP))
    fun PP hP => h3 PP (Finset.mem_union_right _ hP)⟩


open scoped ComplexOrder in
theorem integrableOn_lift {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω) (hs : V.SigOK)
    (hp : V.IsPosDef) (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {x : Bridge.Gf V → c.W} (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L))
    (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w)) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V K ν 𝓕) (g : GA D W) :
    IntegrableOn (fun h => Datum.thetaKO ω h g (φ (c.ext x h))) 𝓕 ν := by
  have hpos : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hω.std V W χS χT ω hω hpos c.W φ hφ _
    (GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1 (eventually_grpOf V β L) hx)
    (GlobalTheory.ThetaIntegrand.ext_invariant c hx) ν 𝓕 hν.1.1 hν.2 g

theorem exists_linear_lift {X X' Y B W Z κ₁ κ₂ : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    [AddCommGroup Y] [Module ℂ Y] [MeasurableSpace B]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z] (ν : Measure B) (𝓕 : Set B) (e : Y →ₗ[ℂ] Z)
    (val : κ₁ → κ₂ → Z → ℂ) (hadd : ∀ a b z z', val a b (z + z') = val a b z + val a b z')
    (hsm : ∀ a b (t : ℂ) z, val a b (t • z) = t * val a b z)
    (E₁ : X →ₗ[ℂ] X') (E₂ : X' →ₗ[ℂ] (B → W)) (k : κ₁ → κ₂ → B → W → ℂ)
    (kadd : ∀ a b h z z', k a b h (z + z') = k a b h z + k a b h z') (ksm : ∀ a b h (t : ℂ) z, k a b h (t • z) = t * k a b h z)
    (hint : ∀ x a b, IntegrableOn (fun h => k a b h (E₂ (E₁ x) h)) 𝓕 ν)
    (hex : ∀ x, ∃ y, ∀ a b, val a b (e y) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν) :
    ∃ th : X →ₗ[ℂ] Y, ∀ x a b, IntegrableOn (fun h => k a b h (E₂ (E₁ x) h)) 𝓕 ν ∧
      val a b (e (th x)) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν := by
  have k0 : ∀ a b h, k a b h 0 = 0 := fun a b h => by simpa using ksm a b h 0 0
  obtain ⟨th, h⟩ := exists_linear_section (fun x y => ∀ a b, val a b (e y) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν)
    (fun a b => by simpa [k0] using hsm a b 0 0)
    (fun x x' y y' h h' a b => by
      rw [map_add (f := _), hadd, h, h', ← integral_add (hint x a b) (hint x' a b)]
      simp only [map_add (f := _), Pi.add_apply, kadd])
    (fun t x y h a b => by
      rw [map_smul, hsm, h, ← integral_const_mul]
      simp only [map_smul, Pi.smul_apply, ksm]) hex
  exact ⟨th, fun x a b => ⟨hint x a b, h x a b⟩⟩

theorem form_algebra {κ : Type} [Fintype κ] (N Vol H P nrm dO J : ℝ) (E x y cb c0 : ℂ) (t : κ → ℂ) (hc : c0 = H)
    (hx : x = (N : ℂ) ^ 2 * ∑ k, t k) (ht : ∀ k, t k = (Vol : ℂ) * (c0 * ((P : ℂ) * (nrm : ℂ) * (E / (dO : ℂ))) * cb * (J : ℂ)))
    (hy : y = (N : ℂ) * cb) : x = (((P * (N * Fintype.card κ * Vol * H * nrm / dO * J) : ℝ) : ℂ) * E) * y := by
  rw [hx, hy]
  simp only [ht, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem scalar_adjLev {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) {X Y : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥) (a : ℝ) (E : ℂ) (ha : 0 < a * ‖E‖)
    (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') =
      (((((Nat.card P.H : ℕ) : ℝ) * a : ℝ) : ℂ) * E) * inner ℂ y y') :
    ∀ y ∈ U, th (adjLev P th y) = ((a * ‖E‖ : ℝ) : ℂ) • y := by
  intro y hy
  have hP : 0 < Nat.card P.H := Nat.card_pos
  have ha0 : 0 ≤ a := by
    by_contra hneg
    exact absurd ha (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hneg).le (norm_nonneg E)))
  rw [adjLev, LinearMap.smul_apply, map_smul, scalar_of_form th U hU _ h y hy, smul_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  congr 1
  have : ((Nat.card P.H : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  push_cast
  field_simp

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ptL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (u : X →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : X →ₗ[ℂ] (Datum.WO (Vc D i) (Wc D i) → ℂ) where
  toFun w := ptAt R i σ BW f (u w)
  map_add' w w' := by rw [map_add (f := _)]; exact map_add _ _ _
  map_smul' a w := by rw [map_smul]; exact map_smul _ _ _

theorem ptL_apply (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (u : X →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : X) : ptL R i σ BW f u w = ptAt R i σ BW f (u w) := rfl

variable {R} {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftData R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)

end Main

end GlobalTheory.AdelicScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.HeckeExtend

theorem exists_int_of_mem_intF : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  intro F _ _ y m hm hy
  obtain ⟨c, hc, e⟩ := hy
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y / m) ≤ 1 := by
    intro v
    have h1 : (y : v.adicCompletion F) = ((m : F) : v.adicCompletion F) * c v := by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) e
      simp only [nsmul_eq_mul] at this
      have hL : (algebraMap F (AF F) y).2 v = (y : v.adicCompletion F) := rfl
      have hm' : ((m : FiniteAdeleRing (𝓞 F) F)) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) :=
        (map_natCast _ m).symm
      have hR : ((m : FiniteAdeleRing (𝓞 F) F) * c) v = ((m : F) : v.adicCompletion F) * c v := by
        rw [hm']; rfl
      rw [← hL, ← hR]
      exact this
    have h2 : v.valuation F y = v.valuation F (m : F) * Valued.v (c v) := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h1, map_mul,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hv0 : v.valuation F (m : F) ≠ 0 := (Valuation.ne_zero_iff _).2 hmF
    rw [map_div₀, h2, mul_div_cancel_left₀ _ hv0]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hc v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y / (m : F)) key
  refine ⟨r, ?_⟩
  have : ((r : 𝓞 F) : F) = y / m := hr
  rw [this, mul_div_cancel₀ _ hmF]

end GlobalTheory.HeckeExtend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultipleStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  first | exact @GlobalTheory.HeckeExtend.exists_int_of_mem_intF | exact GlobalTheory.HeckeExtend.exists_int_of_mem_intF | (intros; apply GlobalTheory.HeckeExtend.exists_int_of_mem_intF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOne
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.ExpFrame.CharUnit

open NumberField Polynomial in
private theorem le_one_of_forall_pow_le {a C : ℝ} (h : ∀ n : ℕ, a ^ n ≤ C) : a ≤ 1 := by
  by_contra ha
  push_neg at ha
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ha
  exact absurd (h n) (not_le.mpr hn)


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [NormedField K] (χ : Γ →* Kˣ) (hc : Continuous fun g => ((χ g : Kˣ) : K)) (g : Γ) :
    ‖((χ g : Kˣ) : K)‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hb : ∀ h : Γ, ∀ n : ℕ, ‖((χ h : Kˣ) : K)‖ ^ n ≤ C := fun h n => by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow]
    exact hC _ ⟨h ^ n, rfl⟩
  have h1 := le_one_of_forall_pow_le (hb g)
  have h2 := le_one_of_forall_pow_le (hb g⁻¹)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ g : Kˣ) : K)‖ := norm_pos_iff.mpr (χ g).ne_zero
  have : 1 ≤ ‖((χ g : Kˣ) : K)‖ := by
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ hpos |>.mpr hlt
    linarith
  linarith


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (PadicAlgCl l)ˣ), Continuous (_root_.GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ χ hχ g
  refine _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact χ ?_ g
  have h := (Units.continuous_val.comp hχ).matrix_elem 0 0
  convert h using 1
  funext x
  simp [_root_.GlobalTheory.TripleGal.rk1]

end GlobalTheory.ExpFrame.CharUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOneStatement
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_galoisCharacter_padicAlgClosure_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : G E Ω →* (PadicAlgCl l)ˣ), Continuous (GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  first | exact @GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | exact GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | (intros; apply GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrders
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrders
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPartsF

theorem exists_real_finite_mul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J) :
    ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hi : ∀ x y : AEF F E, infPartF F E x = infPartF F E y → finPartF F E x = finPartF F E y → x = y :=
    fun x y h1 h2 => GlobalTheory.AdelicOrbit.parts_inj x y h1 h2
  have hs : ∀ a b, ∃ x : AEF F E, infPartF F E x = a ∧ finPartF F E x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  set g : GL (Fin n) (AEF F E) := matHomF σ J p with hg
  have hgm : g ∈ HR (AF F) σ J := p.2
  have hparts := (GlobalTheory.AdelicOrbit.mem_parts σ J g).1 hgm
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs (Formalism.UG.bc (infPartF F E) g) 1
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs 1 (Formalism.UG.bc (finPartF F E) g)
  have ha : a ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J a).2 ⟨a1 ▸ hparts.1, a2 ▸ one_mem _⟩
  have hk : k ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J k).2 ⟨k1 ▸ one_mem _, k2 ▸ hparts.2⟩
  refine ⟨⟨a, ha⟩, ?_, ⟨k, hk⟩, ?_, ?_, ?_⟩
  · exact MonoidHom.mem_ker.2 a2
  · exact MonoidHom.mem_ker.2 k1
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (a * k)
      rw [map_mul, a1, k1, mul_one]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (a * k)
      rw [map_mul, a2, k2, one_mul]
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (k * a)
      rw [map_mul, a1, k1, one_mul]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (k * a)
      rw [map_mul, a2, k2, mul_one]

end GlobalTheory.WeilPartsF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrdersStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J), ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  first | exact @GlobalTheory.WeilPartsF.exists_real_finite_mul | exact GlobalTheory.WeilPartsF.exists_real_finite_mul | (intros; apply GlobalTheory.WeilPartsF.exists_real_finite_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenOfSpecializesIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

open Set Topology

namespace GlobalTheory.SpecGenClopen

theorem isClosed_of_stable (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Set X)
    (hs : StableUnderSpecialization T) (hg : StableUnderGeneralization T) : IsClosed T := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let T' : Set (U : Set X) := Subtype.val ⁻¹' T
  have key : ∀ Z : Set (U : Set X), IsIrreducible Z → (Z ∩ T').Nonempty → Z ⊆ T' := by
    rintro Z hZ ⟨t, htZ, htT⟩ z hz
    have hI : IsIrreducible (closure (Subtype.val '' Z : Set X)) :=
      (hZ.image _ continuous_subtype_val.continuousOn).closure
    obtain ⟨g₀, hg₀⟩ := QuasiSober.sober hI isClosed_closure
    have h1 : g₀ ⤳ (t : X) := hg₀.specializes (subset_closure ⟨t, htZ, rfl⟩)
    have h2 : g₀ ⤳ (z : X) := hg₀.specializes (subset_closure ⟨z, hz, rfl⟩)
    exact hs h2 (hg h1 htT)
  have hT' : T' = ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set X) | (Z ∩ T').Nonempty}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t,
      ⟨t, mem_irreducibleComponent, ht⟩⟩ mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨hZ, hZT⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact key Z hZ.1 hZT htZ
  have hc : IsClosed T' := by
    rw [hT']
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  refine ⟨Subtype.val '' T'ᶜ, ?_, U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hc.isOpen_compl, ⟨x, hxU⟩, hx, rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isClopen_of_specializes_iff : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Z : Set X),
    (∀ x y : X, x ⤳ y → (x ∈ Z ↔ y ∈ Z)) → IsClopen Z := by
  intro X _ Z h
  have hs : StableUnderSpecialization Z := fun x y hxy hx => (h x y hxy).1 hx
  have hg : StableUnderGeneralization Z := fun x y hxy hx => (h y x hxy).2 hx
  exact ⟨isClosed_of_stable X Z hs hg, isClosed_compl_iff.1 (isClosed_of_stable X Zᶜ
    (stableUnderSpecialization_compl_iff.2 hg) (stableUnderGeneralization_compl_iff.2 hs))⟩

end GlobalTheory.SpecGenClopen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FinEtPoints

theorem epi_spMap_field (k L : Type) [Field k] [Field L] (f : k →+* L) : Epi (spMap f) := by
  exact Flat.epi_of_flat_of_surjective _

theorem exists_point_of_finite_etale (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K]
    [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀) : IsFinite p → Etale p →
    ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) →
      ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  intro hf he x hx
  let Ω := AlgebraicClosure K
  let i : K →+* Ω := algebraMap K Ω
  let j : k₀ →+* K := algebraMap k₀ K
  let t : Sp Ω ⟶ Sp k₀ := spMap (i.comp j)
  have ht : spMap i ≫ spMap j = t := by
    simp only [t, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hti : Epi t := epi_spMap_field _ _ _
  have hii : Epi (spMap i) := epi_spMap_field _ _ _
  obtain ⟨zΩ⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨z₀⟩ : Nonempty (Sp k₀) := inferInstance
  obtain ⟨hfin₁, hc₁⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t zΩ
  obtain ⟨hfin₀, hc₀⟩ := GlobalTheory.FinEt.card_points_eq_finrank p (𝟙 (Sp k₀)) z₀
  let F : {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} → {y : Sp Ω ⟶ X // y ≫ p = t} :=
    fun y ↦ ⟨t ≫ y.1, by rw [Category.assoc, y.2, Category.comp_id]⟩
  have hFi : Function.Injective F := by
    intro a b hab
    exact Subtype.ext ((cancel_epi t).mp congr(($hab).1))
  have hcard : Nat.card {y : Sp Ω ⟶ X // y ≫ p = t} ≤ Nat.card {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} := by
    rw [hc₁, hc₀, Subsingleton.elim (t zΩ) ((𝟙 (Sp k₀) : Sp k₀ ⟶ Sp k₀) z₀)]
  have hFb : Function.Bijective F := hFi.bijective_of_nat_card_le hcard
  obtain ⟨⟨x₀, hx₀⟩, hF⟩ := hFb.2 ⟨spMap i ≫ x, by rw [Category.assoc, hx, ht]⟩
  refine ⟨x₀, hx₀, ?_⟩
  have h1 : spMap i ≫ (spMap j ≫ x₀) = spMap i ≫ x := by
    rw [← Category.assoc, ht]
    exact congr(($hF).1)
  exact (cancel_epi (spMap i)).mp h1

end GlobalTheory.FinEtPoints
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_point_of_finite_etale_over_algClosed : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀), IsFinite p → Etale p → ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) → ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  first | exact @GlobalTheory.FinEtPoints.exists_point_of_finite_etale | exact GlobalTheory.FinEtPoints.exists_point_of_finite_etale | (intros; apply GlobalTheory.FinEtPoints.exists_point_of_finite_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigen
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem zc_eq_scL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) :
    zc E N = lie E N (Central.scL N 1) := by
  unfold zc
  congr 1

theorem splitCentre_eq_scalar {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (t : ℝ) :
    splitCentre E N t = Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E)))) := by
  have e : (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) := by
    funext w; simp
  unfold splitCentre
  rw [e]
  exact cornerGL_scalar _ _

theorem zc_comm_mem_eigen : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ N
  rw [zc_eq_scL]
  refine ⟨fun o => (Central.lie_act 1 o).eq, Central.lie_mem_Zalg 1, fun φ c => ⟨fun h t g => ?_, fun h => ?_⟩⟩
  · have e : Central.scL N (t • (1 : Cinf E)) = t • Central.scL N (1 : Cinf E) := by
      funext i j
      change Matrix.diagonal (fun _ => t • (1 : Cinf E)) i j = t • Matrix.diagonal (fun _ => (1 : Cinf E)) i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h1 : lie E N (Central.scL N (t • (1 : Cinf E))) φ = (c * t) • φ := by
      rw [e, map_smul, LinearMap.smul_apply, h, mul_comm, mul_smul, Complex.coe_smul]
    have h2 := congrFun (congrArg Subtype.val (Central.rs_exp _ _ φ h1)) g
    rw [splitCentre_eq_scalar, scalar_comm]
    exact h2
  · refine Subtype.ext <| funext fun g => ?_
    have h1 := Central.hasDerivAt_scalar (1 : Cinf E) φ g
    have e : ∀ t : ℝ, φ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E))))) =
        Complex.exp (c * t) * φ.1 g := fun t => by rw [← scalar_comm, ← splitCentre_eq_scalar, h]
    simp only [e] at h1
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * t) * φ.1 g) (c * φ.1 g) 0 := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul c).cexp).mul_const (φ.1 g)
    exact h1.unique h2

end GlobalTheory.ResW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigenStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCentreDerivative_commute_central_eigen : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  exact GlobalTheory.ResW.zc_comm_mem_eigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardMulLeOfQuotEmbed
open Filter Topology GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_of_quot_embed : ∀ (G : Type) [AddCommGroup G] (Λ Λ' Λ₀ Λ₀' : AddSubgroup G) (B E : ℝ → Set G)
    (T : G →+ G), IsBallFam Λ B → IsBallFam Λ' E → (∀ u ∈ B 1, T u ∈ E 1) → (∀ u ∈ Λ, T u ∈ Λ₀' → u ∈ Λ₀) →
    (B 1).Finite → (B 1).encard * (E 1 ∩ Λ₀').encard ≤ (B 2 ∩ Λ₀).encard * (E 2).encard := by
  intro G _ Λ Λ' Λ₀ Λ₀' B E T hB hE hT hpull _
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  let q : G → G ⧸ Λ₀ := QuotientAddGroup.mk
  let R : Set (G ⧸ Λ₀) := q '' B 1
  let s : G ⧸ Λ₀ → G := Function.invFunOn q (B 1)
  have hs_mem : ∀ c ∈ R, s c ∈ B 1 := fun c hc => Function.invFunOn_mem hc
  have hs_eq : ∀ c ∈ R, q (s c) = c := fun c hc => Function.invFunOn_eq hc

  have h1 : (B 1).encard ≤ R.encard * (B 2 ∩ Λ₀ : Set G).encard := by
    rw [← Set.encard_prod]
    refine le_trans (Set.encard_le_encard (s := B 1)
      (t := (fun p : (G ⧸ Λ₀) × G => s p.1 + p.2) '' (R ×ˢ (B 2 ∩ (Λ₀ : Set G)))) ?_) (Set.encard_image_le _ _)
    intro x hx
    have hqx : q x ∈ R := ⟨x, hx, rfl⟩
    refine ⟨(q x, x - s (q x)), ⟨hqx, ?_, ?_⟩, by simp⟩
    · have := hB.sub_mem 1 1 x (s (q x)) hx (hs_mem _ hqx)
      rwa [h2] at this
    · have he : q (s (q x)) = q x := hs_eq _ hqx
      have := (QuotientAddGroup.eq).mp he
      show x - s (q x) ∈ Λ₀
      rwa [sub_eq_neg_add]

  have h3 : R.encard * (E 1 ∩ Λ₀' : Set G).encard ≤ (E 2).encard := by
    rw [← Set.encard_prod]
    refine Set.encard_le_encard_of_injOn (f := fun p : (G ⧸ Λ₀) × G => T (s p.1) - p.2) ?_ ?_
    · rintro ⟨c, v⟩ ⟨hc, hv, -⟩
      have := hE.sub_mem 1 1 _ _ (hT _ (hs_mem c hc)) hv
      rwa [h2] at this
    · rintro ⟨c, v⟩ ⟨hc, hv, hv'⟩ ⟨c', w⟩ ⟨hc', hw, hw'⟩ heq
      simp only at heq
      have hd : T (s c - s c') ∈ Λ₀' := by
        have : T (s c - s c') = v - w := by rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp heq
        rw [this]; exact Λ₀'.sub_mem hv' hw'
      have hΛ : s c - s c' ∈ Λ := Λ.sub_mem (hB.subset 1 (hs_mem c hc)) (hB.subset 1 (hs_mem c' hc'))
      have h0 : s c - s c' ∈ Λ₀ := hpull _ hΛ hd
      have hqq : q (s c) = q (s c') := by
        apply (QuotientAddGroup.eq).mpr
        have := Λ₀.neg_mem h0
        rwa [neg_sub, sub_eq_neg_add] at this
      have hcc : c = c' := by rw [← hs_eq c hc, ← hs_eq c' hc', hqq]
      subst hcc
      have : v = w := by simpa using heq
      rw [this]
  calc (B 1).encard * (E 1 ∩ Λ₀' : Set G).encard
      ≤ (R.encard * (B 2 ∩ Λ₀ : Set G).encard) * (E 1 ∩ Λ₀' : Set G).encard := by gcongr
    _ = (B 2 ∩ Λ₀ : Set G).encard * (R.encard * (E 1 ∩ Λ₀' : Set G).encard) := by ring
    _ ≤ (B 2 ∩ Λ₀ : Set G).encard * (E 2).encard := by gcongr

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkReducedClosedGenericPointEqRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkReducedClosedGenericPointEqRank
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory.StalkLength

theorem length_stalk_pushforward {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i]
    (F : Y.Modules) (y : Y) :
    Module.length (X.presheaf.stalk (i y))
        (((Scheme.Modules.pushforward i).obj F).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (F.presheaf.stalk y :) := by
  let G := (Scheme.Modules.pushforward i).obj F
  let φ := i.stalkMap y
  letI : Algebra (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) := φ.hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk y :) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk (i y)) (Y.presheaf.stalk y))
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (F.presheaf.stalk y :) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Ψ : (G.presheaf.stalk (i y) :) →+ (F.presheaf.stalk y :) :=
    (F.presheaf.stalkPushforward _ i.base y).hom
  have hΨ (U : X.Opens) (hU : i y ∈ U) (s : Γ(G, U)) :
      Ψ (G.presheaf.germ U _ hU s) = F.presheaf.germ (i ⁻¹ᵁ U) y hU s :=
    congr($(TopCat.Presheaf.stalkPushforward_germ _ i.base F.presheaf U y hU).hom s)
  have hiso := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
    (f := i.base) i.isClosedEmbedding.isInducing F.presheaf y
  have hbij : Function.Bijective Ψ :=
    ConcreteCategory.bijective_of_isIso (F.presheaf.stalkPushforward _ i.base y)
  have hsmul (a : X.presheaf.stalk (i y)) (m : (G.presheaf.stalk (i y) :)) :
      Ψ (a • m) = φ.hom a • Ψ m := by
    obtain ⟨U₁, hU₁, r, rfl⟩ := X.presheaf.germ_exist a
    obtain ⟨U₂, hU₂, s, rfl⟩ := G.presheaf.germ_exist m
    have hU : i y ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU,
      ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]
    generalize X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'
    generalize G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'
    rw [← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]
    refine (GlobalTheory.QCoh.germ_smul F (U := i ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (i.app _ r') s').trans ?_
    congr 1
    exact congr($(Scheme.Hom.germ_stalkMap i (U₁ ⊓ U₂) y hU).hom r').symm
  let e : (G.presheaf.stalk (i y) :) ≃ₗ[X.presheaf.stalk (i y)] (F.presheaf.stalk y :) :=
    { AddEquiv.ofBijective Ψ hbij with map_smul' := hsmul }
  exact e.length_eq.trans (Module.length_eq_of_surjective (i.stalkMap_surjective y))

theorem length_stalk_pushforward_genericPoint : ∀ (X : Scheme.{0}) (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G],
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) := by
  intro X Z _ G _
  rw [length_stalk_pushforward]
  exact Module.length_eq_finrank (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.functionField
    (GlobalTheory.VB.genStalk G)

end GlobalTheory.StalkLength
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkReducedClosedGenericPointEqRankStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_stalk_reducedClosed_genericPoint_eq_rank : ∀ (X : Scheme.{0}) (Z : Closeds X) [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme] (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G], Module.length (X.presheaf.stalk (redι Z (genericPoint _))) (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) = (GlobalTheory.VB.genRank G : ℕ∞) := by
  first | exact @GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint | exact GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint | (intros; apply GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenBaseChangePreimage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenBaseChangePreimage
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isEtCoord_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  intro R R' _ _ φ X X' f f' π U d t H hU ht
  refine ⟨GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback H hU, ?_⟩
  letI := φ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := R) (S := R') (σ := Fin d)
  have h₁ := (CommRingCat.isPushout_of_isPushout R R' (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R')).flip
  have hx : (MvPolynomial.eval₂Hom (algX f U) t).Etale := ht
  have key : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U),
      IsPushout (CommRingCat.ofHom (algX f U)) (CommRingCat.ofHom (algebraMap R R'))
        (π.appLE U W hle) (CommRingCat.ofHom (algX f' W)) →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale := by
    intro W hle h₂
    have e₁ : CommRingCat.ofHom (algX f U) = CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R)) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f U) t) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have e₂ : CommRingCat.ofHom (algX f' W) =
        CommRingCat.ofHom (algebraMap R' (MvPolynomial (Fin d) R')) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have hw := h₂.w
    rw [e₁, e₂] at h₂
    have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
    · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
      exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.C a))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact congrArg (fun g => (CommRingCat.Hom.hom g) a) hw
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.X a))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  have h₄ := key _ inf_le_left (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.isPushout_sections f f' π H U hU)
  have tr : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale →
      IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
    rintro W hle rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  exact tr _ _ (inf_top_eq _) h₄

end GlobalTheory.LogPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenBaseChangePreimageStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_baseChange_preimage : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_baseChange | exact GlobalTheory.LogPair.isEtCoord_baseChange | (intros; apply GlobalTheory.LogPair.isEtCoord_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinity
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section
namespace GlobalTheory.HeckeExtend.AtInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def uInf (F : Type) [Field F] [NumberField F] : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def uFin (F : Type) [Field F] [NumberField F] : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

theorem uInf_add_uFin : uInf F + uFin F = 1 := by
  show ((1 : InfiniteAdeleRing F) + 0, (0 : FiniteAdeleRing (𝓞 F) F) + 1) = 1
  simp

theorem evI_uFin : evI F (uFin F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem pure_mem (N : ℕ) (hN : 0 < N) (a : AF F) (e : E) :
    ((uInf F * a) ⊗ₜ[F] e : AF F ⊗[F] E) ∈ CE F E N := by
  have halg : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral (R := ℚ) e).isAlgebraic
  obtain ⟨d, hd, hint⟩ := halg.exists_integral_multiple
  let o : 𝓞 E := ⟨d • e, hint⟩
  have ho : (o : E) = (d : E) * e := by simp [o, zsmul_eq_mul]
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd
  let c : F := ((N : F) * (d : F))⁻¹
  let s : AF F := algebraMap F (AF F) c * (uInf F * a)
  have hs : s ∈ intF F 1 := by
    refine ⟨0, fun v => zero_mem _, ?_⟩
    show (algebraMap F (AF F) c).2 * ((uInf F).2 * a.2) = 1 • 0
    simp [uInf]
  refine mem_CE.2 ⟨algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o,
    AddSubgroup.subset_closure ⟨s, hs, o, rfl⟩, ?_⟩
  have h1 : algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
    simp [incAF, inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  have h2 : s = c • (uInf F * a) := (Algebra.smul_def c _).symm
  rw [h1, h2, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul]
  congr 1
  rw [ho, Algebra.smul_def c, nsmul_eq_mul]
  simp only [c, map_inv₀, map_mul, map_natCast, map_intCast]
  field_simp

theorem uInf_smul_mem (N : ℕ) (hN : 0 < N) (w : AF F ⊗[F] E) : uInf F • w ∈ CE F E N := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero]; exact zero_mem _
  | tmul a e => rw [TensorProduct.smul_tmul', smul_eq_mul]; exact pure_mem N hN a e
  | add x y hx hy => rw [smul_add]; exact add_mem hx hy

theorem mem_CE_of_atInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  intro F E _ _ _ _ _ N hN w hw
  have h0 : uFin F • w = 0 := hw (uFin F) evI_uFin
  have : w = uInf F • w := by
    conv_lhs => rw [← one_smul (AF F) w, ← uInf_add_uFin, add_smul, h0, add_zero]
  rw [this]
  exact uInf_smul_mem N hN w

end GlobalTheory.HeckeExtend.AtInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinityStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  first | exact @GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | exact GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | (intros; apply GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf <;> assumption)
end
end

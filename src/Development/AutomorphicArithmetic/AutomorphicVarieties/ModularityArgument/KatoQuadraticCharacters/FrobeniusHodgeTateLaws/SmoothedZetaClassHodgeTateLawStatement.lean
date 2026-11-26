module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.HtLawCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def KatoEulerSystemIwasawaClassStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
      (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e →
      (∃ x, cw x ≠ 0) → AdmWn ι e g A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
      ∃ (c₀ m : ℕ) (cf' : Coef l) (S' : Finset Pl) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
        (y : G ℚ Ω → Fin 2 → Qbar l),
        IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
        (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧
        (∀ r y i, Continuous fun s => Y r s y i) ∧
        (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) ∧ (∀ r s y i, Y r s y i ∈ cf.O) ∧ (∀ z, z ∈ cf.O → z ∈ cf'.O) ∧
        (∀ r s, Cv r (y s) (GlobalTheory.KA.spec (fun u : (ZMod (l ^ r))ˣ => ((((u : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r u) (Y r) s)) ∧
        Sys W cf' (fun s => ((l : Qbar l) ^ m) • y s) S' ∧
        IwSys2 cf' A (nuD W e ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) ∧
        SpLink A e (chiK l ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) (fun s => ((l : Qbar l) ^ m) • y s)

def SmoothedZetaClassHodgeTateLawStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
      AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
    ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
    ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
      IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
      (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
      (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
      (∀ r s y, Y r s y 1 ∈ cf.O) →
    ∀ (χd : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χd δ)) → (∀ a b : ℕ, χd (a * b) = χd a * χd b) →
      (∀ a b : ℕ, a % N = b % N → χd a = χd b) → ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χd j pr cf lam →
    ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
    ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
      HTLawCsOfCoef A cf (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) j m₀ c₁
        (fun m ψ z => (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (GlobalTheory.KummerEisensteinGalois.up (l ^ m) (fun i => ∑ x : ZMod N, cw x *
            GlobalTheory.LambdaValuationPowers.chiProj N l m (2 * e + 1) ψ (fun n => ((χd n : ℤ_[l]) : Qbar l)) (c : ℤ) (d : ℤ) (x.val : ℤ) i)))

def AdmTop2 : Prop :=
  ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
    [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
    (j : Ω →+* Qbar l),
    Nf e S A W → 1 ≤ e →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    (∀ x ∈ A, ‖j x‖ ≤ 1) →
    ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
    (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
    ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
    ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
      (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
    P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
    (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
    (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
    (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
    (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
    (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
    (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
    ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
    (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
      Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
    ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
      c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
      (∀ b b', pr (b + b') = pr b + pr b') ∧
      (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
      (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
      (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
      IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam)

def Glue2 : Prop :=
  KatoEulerSystemIwasawaClassStatement → SmoothedZetaClassHodgeTateLawStatement → AdmFR → TowerEx → GlobalTheory.EisM.CuspidalUnitaryTwistsClaim → Meas3 → JEx → CoefUb → Mono → PsiEx → FrobU → DetIne → HatW → PinOf → SmNz →
    GmEx → ExplSmul → AvgEq → AvgMF → RhsEq → SmSys → ChiFix → ExistsZetaEulerSystemIwasawaData Pin7

end UpperTheory.V.Z.Kato.Joint

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AqBdPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open UpperTheory.V.Z.Kato.Joint
open scoped Pointwise

private theorem aqBd_place {q : ℕ} (hq : q.Prime) : ∃ w : Pl, ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have hn : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) = q := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hne : Ideal.span {((q : ℕ) : 𝓞 ℚ)} ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hn
    exact hq.one_lt.ne hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ M := (Ideal.span_singleton_le_iff_mem M).1 hle
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hq.ne_zero (Nat.cast_eq_zero.1 hmem)

private theorem aqBd_frob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {q : ℕ} (hq : q.Prime) :
    ∃ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s := by
  obtain ⟨w, hw⟩ := aqBd_place hq
  obtain ⟨V, hV⟩ := exists_isPlaceOver (F := ℚ) Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hV
  rw [GlobalTheory.RhoAdm.normV_ratPrime hq w hw] at hσ
  refine ⟨σ, V, ?_, fun x hx => ⟨?_, hσ.2 x ((V.valuation_le_one_iff x).2 hx)⟩⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    simpa using (hV _).2 hw
  · have h : σ • V = V := MulAction.mem_stabilizer_iff.1 hσ.1
    rw [← h]
    exact ValuationSubring.smul_mem_pointwise_smul σ x V hx

theorem UpperTheory.V.Z.Kato.Joint.aqBd :
    UpperTheory.V.Z.Kato.Joint.AqBd := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hχ hatt
  obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
  have hc := (Continuous.matrix_trace
    (Units.continuous_val.comp (GlobalTheory.RhoAdm.untw_cont e W χ hN.cont hχ))).norm
  haveI : CompactSpace (Ω ≃ₐ[ℚ] Ω) := inferInstance
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  obtain ⟨k, hk⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l (max C (∑ q ∈ S0, ‖ι.symm (g.a q)‖))
  refine ⟨k, fun q hq => le_trans ?_ hk⟩
  by_cases hqS : q ∈ S0
  · exact le_max_of_le_right
      (Finset.single_le_sum (f := fun q => ‖ι.symm (g.a q)‖) (fun _ _ => norm_nonneg _) hqS)
  · obtain ⟨s, hs⟩ := aqBd_frob Ω hq
    rw [← (hS0 q hq hqS s hs).1]
    exact le_max_of_le_left (hC ⟨s, rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AdmissibleFunctionalOfProjection
open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

private theorem norm_l_lt (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends (p := l) ((l : ℕ) : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

private theorem sq_ne {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (α c : ℂ) (hα : ‖ι.symm α‖ = 1) (hc : c = 1 ∨ c = -1)
    (n : ℕ) (hn : n ≠ 0) : α ^ 2 ≠ c * (l : ℂ) ^ n := by
  intro h
  have h1 := congrArg (fun z => ‖ι.symm z‖) h
  have h2 : ‖ι.symm c‖ = 1 := by rcases hc with rfl | rfl <;> simp
  simp only [map_pow, map_mul, map_natCast, norm_pow, norm_mul, hα, h2, one_pow, one_mul] at h1
  have h3 := pow_lt_one₀ (norm_nonneg _) (norm_l_lt l) hn
  rw [← h1] at h3
  exact lt_irrefl _ h3

private theorem alg_eq {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) :
    algebraMap ℤ_[l] (Qbar l) z = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) :=
  IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) z

private theorem norm_alg {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ := by
  rw [alg_eq]
  exact PadicAlgCl.norm_extends (p := l) (z : ℚ_[l])

private theorem tmul_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) : ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) ∈ X.VB N l w (Qbar l) :=
  ⟨(1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : X.B N l w), by simp⟩

theorem UpperTheory.V.Z.Kato.Joint.admissibleFunctional_of_projection :
    UpperTheory.V.Z.Kato.Joint.AdmOf2 := by
  classical
  intro hAdm hK3 hRho _ hFrob hUnif hForm hFin hUb hLin hOp hStab hThP hEig hQuad hInt
  intro l _ Ω _ _ _ ι e S A W g hNf χg ψ₀ hlM hal hK hAtt hIne hψ j hj ε X N _ χ α B cc c₀ hN hMN hlN hχ hα hαe hE
  have hp : l.Prime := Fact.out
  have he := hNf.e_pos
  have hl2 := hNf.l_odd
  obtain ⟨ρ, hρ, hρc, hρ10, hρ11, F, hρ00⟩ := hRho l Ω ι e S A W g ψ₀ hNf ⟨hlM, hal, χg, hK, hAtt, hIne⟩ ⟨χg, hK, hIne, hψ⟩
  have hρ' : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = (eps l s ^ e * (χg s : Qbar l)⁻¹) • mat W s := by
    intro s
    rw [hρ, hψ s, rhoK, thK, mul_inv, inv_inv]
    rfl
  obtain ⟨⟨S0, hS0⟩, hirr⟩ := hFrob l Ω ι e S A W g χg hNf hK hAtt ρ hρ'
  have hq := hQuad l Ω ι e S A W g χg hNf hK hlM hAtt
  have hcop : ∀ d : ℕ, d.Coprime N → d.Coprime g.M := fun d hd => Nat.Coprime.coprime_dvd_right hMN hd
  have hlcN : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hlN
  have hjl : (l : Ω) ∈ A.nonunits := (‹JEx› l Ω A hNf.atL).1
  have hjA : ∀ x ∈ A, ‖j x‖ ≤ 1 := fun x hx => (hj x).1 hx
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  let lamC : Letter → ℂ := fun T => match T with
    | Letter.T q => g.a q
    | Letter.U => α
    | Letter.D d => g.χ (d : ZMod g.M)
  have hcm : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hρc
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hw1 : 2 * e - 1 + 1 = 2 * e := by omega
  have hw2 : 2 * e - 1 + 2 = 2 * e + 1 := by omega
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have h3 := hK3 ε X ε.injective ⟨φ, hφ2, hφ1⟩ (2 * e + 1) g N l hl2 hMN hN hlcN.symm ⟨e, rfl⟩ (by omega) α
    (by rw [← hχ l hlcN]; exact hαe) (sq_ne ι α _ hα (hq l (hcop l hlcN)) _ (by omega))
    (sq_ne ι α _ hα (hq l (hcop l hlcN)) _ (by omega)) lamC (fun _ _ _ => rfl) rfl (fun _ _ => rfl) (E := Qbar l) norm_alg ι
  simp only [hw] at h3
  obtain ⟨m, π, σ, P, hP, hP1, -, hσ, hπg, hσg, hσT, hπT, hπσ, hPx⟩ := h3 ρ S0
    (hUnif l Ω _ hcm.matrix_trace) (hUnif l Ω _ hcm.matrix_det)
    (fun q hq hS s hs => by rw [hw1]; exact hS0 q hq hS s hs) hirr
  let χd : ℕ → ℤ_[l] := fun d => if g.χ (d : ZMod g.M) = 1 then 1 else -1
  have hχd : ∀ d : ℕ, d.Coprime N → ι.symm (g.χ (d : ZMod g.M)) = ((χd d : ℤ_[l]) : Qbar l) := by
    intro d hd
    by_cases h : g.χ (d : ZMod g.M) = 1
    · simp [χd, h]
    · have h' := (hq d (hcop d hd)).resolve_left h
      simp only [χd, if_neg h]
      rw [h']
      simp
  have hχd' : ∀ d : ℕ, d.Coprime N → ι ((χd d : ℤ_[l]) : Qbar l) = χ d := by
    intro d hd
    rw [← hχd d hd, RingEquiv.apply_symm_apply, hχ d hd]
  obtain ⟨lam₀, lam, c, hc, hf0, hf, hfix, hl0, hl⟩ := hFin hUb l ι (2 * e + 1) N B cc (fun d => ((χd d : ℤ_[l]) : Qbar l)) c₀ P hP
  have hev : ∃ k : ℕ, ∀ T, GlobalTheory.KZ.admitted N l T → ‖ι.symm (lamC T)‖ ≤ (l : ℝ) ^ k := by
    obtain ⟨k, hk⟩ := hInt l Ω ι e S A W g χg hNf hK hAtt
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
    refine ⟨k, ?_⟩
    rintro (q | _ | d) hT
    · exact hk q hT.1
    · exact hα.le.trans h1
    · rcases hq d (hcop d hT) with h | h <;> simpa [lamC, h] using h1
  have heig := hEig hLin hOp hStab hThP l Ω ε X A N (2 * e - 1) j χd (fun T => ι.symm (lamC T))
    ⟨hjl, hl2, hlN, hN, hodd, hjA⟩ hev P hP
    (fun T hT b hb => by
      have hb' := GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, hφ2, hφ1⟩ N l (2 * e - 1) hl2 hN hlcN.symm hodd T hT b hb
      rw [hPx _ (tmul_mem X N l _ _ hb'), hPx _ (tmul_mem X N l _ _ hb), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_smul, ← hπT i T hT _ (tmul_mem X N l _ _ hb)]
      rfl)
    lam₀ lam hf0 (by rw [hw2]; exact hl)
  obtain ⟨pr, a, cf, hcf, -, hadd, hsm, hint, hgal, hT, hD, hU, hlam⟩ :=
    hAdm ε X A N l e S W ψ₀ ι g j hNf he ⟨φ, hφ1, hφ2⟩ hjl hl2 hlN hN hjA (fun T => ι.symm (lamC T)) ρ F hρ hρ10 hρ11
      (by rw [hw1]; exact hρ00) (fun _ _ _ => rfl) χd hχd m π σ P hP hP1 hσ hπg hσg hσT hπT hπσ hPx c lam hf hfix heig
  refine ⟨pr, cf, χd, (((l : ℕ) : Qbar l) ^ a) • lam, ((l : ℕ) : Qbar l) ^ a, hc.trans hcf,
    pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero), hadd, hsm, hint, hgal,
    ⟨fun q => ((χd q : ℤ_[l]) : Qbar l), fun q hq hql b hb => ⟨hT q hq hql b hb,
      hD q ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hql (h.mul_left l)) b hb⟩⟩, hU, hχd',
    fun b hb d hd => hD d hd b hb, hlam, fun s hs => ?_⟩
  have hF := hForm l ι (2 * e + 1) N χ (fun q => g.a q) α B cc (fun d => ((χd d : ℤ_[l]) : Qbar l)) (fun T => ι.symm (lamC T))
    (by omega) hE hχd' (fun _ _ _ => ι.apply_symm_apply _) (ι.apply_symm_apply _) hχd P hP s hs
  rw [LinearMap.smul_apply, smul_eq_mul, hl, hl0, hF, hP1, map_one, one_mul]
end

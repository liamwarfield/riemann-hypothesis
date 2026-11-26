module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ExpLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.expLoss :
    ∀ (D : D7) (S : Finset ℕ) (h : ℕ → ℝ) (B : ℝ), GlobalTheory.NormSum.Exponents S h B →
      Loss (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (GlobalTheory.SumSize.TopInt.primeUnder w)) B := by
  intro D S h B hE
  have e : (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) *
      h (GlobalTheory.SumSize.TopInt.primeUnder w)) = Formalism.PairingDivisionLocalBalance.wt (K := D.what₂.LL) S h := by
    funext w
    rw [hE.wt_eq (TopInt.primeUnder_prime w) w (TopInt.primeUnder_mem w), mul_comm]
  rw [e]
  refine ⟨hE.wt_size.1, ?_, hE.wt_size.2⟩
  have hf : ∀ l : ℕ, {w : PlL D | vw w (l : D.what₂.LL) ≠ 0}.Finite := fun l => by
    have hf := FractionalIdeal.finite_factors (K := D.what₂.LL)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) (l : D.what₂.LL))
    rw [Filter.eventually_cofinite] at hf
    exact hf
  refine (S.finite_toSet.biUnion fun l _ => hf l).subset fun w hw => ?_
  obtain ⟨l, hl, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine Set.mem_biUnion (Finset.mem_coe.2 hl) fun h1 => h0 ?_
  rw [h1]; simp
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatMove
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lin_rat {ι κ V W : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Subfield ℂ) (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℂ W) (f : V →ₗ[ℂ] W)
    (hf : ∀ i j, c.repr (f (b j)) i ∈ A) (v : V) (hv : ∀ j, b.repr v j ∈ A) (i : κ) : c.repr (f v) i ∈ A := by
  rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hv j) (hf i j)

private theorem rho_rat {ι E : Type} [Fintype ι] [Field E] {n : ℕ} (A : Subfield ℂ) (emb : ι → E →+* ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (lam : ι → DomWeight n) (g : GL (Fin n) E) (i j : VVIdx lam) :
    (bVV ℂ lam).repr (rhoVr emb lam g (bVV ℂ lam j)) i ∈ A := by
  refine actionRational_holds ℂ ι n lam A (invTrK (embGL emb g)) (fun τ a b => ?_) i j
  show ((((Formalism.UG.bc (emb τ) g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
  rw [← map_inv]
  exact hA τ _

theorem UpperTheory.WildA.ratMove :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (f f' : VV ℂ lam →ₗ[ℂ] VV ℂ lam')
      (g : GL (Fin n) D.host.E) (g' : GL (Fin n') D.host.E), f' ∘ₗ rhoVr (tauE D) lam g = rhoVr (tauE D) lam' g' ∘ₗ f →
      (∀ i j, (bVV ℂ lam').repr (f (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL) →
      ∀ i j, (bVV ℂ lam').repr (f' (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL := by
  intro D n n' lam lam' f f' g g' h hf i j
  have hlab : ∀ τ x, tauE D τ x ∈ D.what₂.embLL.fieldRange := fun τ x =>
    ⟨labLL D τ x, DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x⟩
  have e : f' (bVV ℂ lam j) = rhoVr (tauE D) lam' g' (f (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))) := by
    have h1 := LinearMap.congr_fun h (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h1
    exact h1
  rw [e]
  exact lin_rat D.what₂.embLL.fieldRange _ _ _ (rho_rat _ _ hlab lam' g') _
    (lin_rat D.what₂.embLL.fieldRange _ _ f hf _ fun k => rho_rat _ _ hlab lam g⁻¹ k j) i
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatMove
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem inLat_gl (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (a : ℝ)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (γ : GL (Fin n) D.host.E) (v : VV ℂ lam) (h : InLat lam w a Λ v) :
    InLat lam w a (Λ.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)))
      (rhoVr (tauE D) lam γ v) := by
  obtain ⟨u, s, rfl, hs, ha, hu⟩ := h
  refine ⟨rhoVr (labLL D) lam γ u, s, (TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.rhoVr_mapVV lam γ u).symm, hs, ha, ?_⟩
  rw [← map_smul]
  exact TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.nabAtr_map _ lam γ Λ _ hu

theorem UpperTheory.WildA.latMove :
    ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (a : ℝ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
      (U : Matrix.unitaryGroup (Fin n) D.host.E) (v : VV ℂ lam),
      InLat lam w a (SDLat.smulLat U.1 Λ) (rhoVr (tauE D) lam (Unitary.toUnits U) v) ↔ InLat lam w a Λ v := by
  intro D n lam w a Λ U v
  have e : SDLat.smulLat U.1 Λ = Λ.map ((Matrix.mulVecLin ((Unitary.toUnits U : GL (Fin n) D.host.E) :
      Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) := rfl
  rw [e]
  generalize (Unitary.toUnits U : GL (Fin n) D.host.E) = γ
  refine ⟨fun h => ?_, inLat_gl D lam w a Λ γ v⟩
  have h2 := inLat_gl D lam w a _ γ⁻¹ _ h
  have e1 : rhoVr (tauE D) lam γ⁻¹ (rhoVr (tauE D) lam γ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : (Λ.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E))).map
      ((Matrix.mulVecLin ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) = Λ := by
    rw [← Submodule.map_comp]
    have e3 : ((Matrix.mulVecLin ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)).comp
        ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show (γ⁻¹).1 *ᵥ (γ.1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e3, Submodule.map_id]
  rwa [e1, e2] at h2
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Imports
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepthDrop
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.HalfUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.halfUnit :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (p : GlobalTheory.ChiGrid.Pair T) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ c : ℕ, (∀ w ∈ P, ((c : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ u ∈ pairLat G p, IsHalf e u → ∃ u' ∈ pairLat G p, IsHalf e u' ∧ c • u' = u := by
  intro D T L sc G p P e he c hc u hu hhalf
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hc0 : c = 0
  · subst hc0
    have hS : ∑ PP ∈ P, es PP = 0 :=
      Finset.sum_eq_zero fun PP hPP => (hc PP hPP (by simp)).elim
    have hu0 : u = 0 := by
      ext i j
      have h := hhalf i j
      rw [hS, zero_mul] at h
      exact h.symm
    subst hu0
    exact ⟨0, (pairLat G p).zero_mem, fun i j => by simp, by simp⟩
  · have hx : ((c : 𝓞 D.host.E)) ≠ 0 := by exact_mod_cast hc0
    let w : AE D := (∑ PP ∈ P, es PP) * incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹
    have hw : finPart D w ∈ intAE D := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ ?_
      intro PP hPP
      by_contra hn
      exact hc PP hPP (((hes PP hPP).2 _ hx).mpr hn)
    have h1 : incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← map_mul]
      have hce : (((c : 𝓞 D.host.E) : D.host.E)) = (c : D.host.E) := by simp
      rw [hce, inv_mul_cancel₀ (by exact_mod_cast hc0), map_one]
    have hcw : (c : AE D) * w = ∑ PP ∈ P, es PP := by
      calc (c : AE D) * w
          = (∑ PP ∈ P, es PP) * (incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D)) := by
            simp only [w]; ring
        _ = ∑ PP ∈ P, es PP := by rw [h1, mul_one]
    refine ⟨w • u, GlobalTheory.LatticeStable.smul_mem_latO _ _ _ _ _ _ w hw u hu, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm _ w, mul_assoc, hhalf i j]
    · ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rw [← mul_assoc, hcw, hhalf i j]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem mx_eq_of_nsmul_eq_of_ne_zero {D : D7} {m n : ℕ} (c : ℕ) (hc : c ≠ 0) {x y : Mx D m n}
    (h : c • x = c • y) : x = y := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply] at h1
  have hF : ((c : ↥D.host.F)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [← Nat.cast_smul_eq_nsmul (↥D.host.F), ← Nat.cast_smul_eq_nsmul (↥D.host.F)] at h1
  calc x i j = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • x i j) := (inv_smul_smul₀ hF _).symm
    _ = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • y i j) := by rw [h1]
    _ = y i j := inv_smul_smul₀ hF _

theorem UpperTheory.WildA.depthDrop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p) (l : ℕ), l.Prime → (∀ w ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ k : ℕ, 0 < k → IsCosetDatum k d → ∃ k' : ℕ, 0 < k' ∧ ¬ l ∣ k' ∧ IsCosetDatum k' d := by
  intro D T L sc G t p d l hl hP k hk hcos
  obtain ⟨x₀, hx₀, hkx, hfn⟩ := hcos
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' l hl.one_lt.ne'
  have hc : ∀ w ∈ d.P, (((l ^ a : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro w hw h
    rw [Nat.cast_pow] at h
    exact hP w hw (w.isPrime.mem_of_pow_mem _ h)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hhalf : ∀ (c : ℕ) (u : Mx D (G.pT p).rank (G.pS p).rank), IsHalf d.e u → IsHalf d.e (c • u) := by
    intro c u hu i j
    simp only [Matrix.smul_apply, mul_smul_comm, hu i j]
  obtain ⟨v, hvL, hvH, hv⟩ :=
    UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc _ hkx (hhalf _ _ hx₀)
  have hmx : m • x₀ = v := by
    apply mx_eq_of_nsmul_eq_of_ne_zero (l ^ a) (pow_ne_zero _ hl.ne_zero)
    rw [hv, smul_smul]
  refine ⟨m, hm0, hm, x₀, hx₀, by rw [hmx]; exact hvL, ?_⟩
  rw [hfn]
  congr 1
  ext x
  simp only [GlobalTheory.RowTest.halfCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, huH, rfl⟩
    refine ⟨(l ^ a) • u, AddSubgroup.nsmul_mem _ hu _, hhalf _ _ huH, ?_⟩
    rw [smul_smul, mul_comm m]
  · rintro ⟨u, hu, huH, rfl⟩
    obtain ⟨u', hu', hu'H, rfl⟩ := UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc u hu huH
    exact ⟨u', hu', hu'H, by rw [smul_smul, mul_comm m]⟩
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.PrimeEqOfMemPrimeIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.WildA.prime_eq_of_mem_prime_ideal {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (ha : a.Prime)
    (hb : b.Prime) (hai : (a : R) ∈ I) (hbi : (b : R) ∈ I) : a = b := by
  by_contra hne
  have h : Nat.Coprime a b := (Nat.coprime_primes ha hb).2 hne
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hai) (Ideal.mul_mem_left _ _ hbi)

private theorem UpperTheory.WildA.split_of_split_class {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : GlobalTheory.NormSum.SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem UpperTheory.WildA.small_set_primes_split :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := by
  intro D T L sc G large₂ hS v hv l hl hlv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS
  have key : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := fun p hp hm h => by
    rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal v.isPrime hl hp hlv h]
    exact UpperTheory.WildA.split_of_split_class (Pm.level_split p hm)
  rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
  · rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal G.pl.v0.isPrime hl (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1 hlv G.pl.basePlace_over_qZero]
    exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
  · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
    · exact key _ (D.host.g_prime 0) (D.host.g_level 0) h
    · exact key _ (D.host.g_prime 1) (D.host.g_level 1) h
    · exact key _ D.host.pde_prime D.host.pde_level.1 h
    · exact key _ D.host.pde'_prime D.host.pde_level.2 h
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.depth :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p), d.P = locPl G t →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w → ∀ k : ℕ, 0 < k → IsCosetDatum k d →
      ∃ k' : ℕ, 0 < k' ∧ IsCosetDatum k' d ∧ padicValNat l k' ≤ padicValNat l k ∧ (l ∣ k' → GlobalTheory.NormSum.SplitIn D l) := by
  classical
  intro D T L sc G large₂ hS t p d hP w l hl hlw hA k hk hc
  by_cases h : ∃ PP ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨PP, hPP, hlPP⟩ := h
    have key : ((l : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast]
      exact hlPP
    have hsplit : GlobalTheory.NormSum.SplitIn D l := by
      rw [hP] at hPP
      unfold locPl at hPP
      rcases Finset.mem_union.mp hPP with h0 | hQ
      · unfold GlobalTheory.ChiGrid.Places.W0 at h0
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h0
        rw [G.pl.w_over v hv] at key
        exact UpperTheory.WildA.small_set_primes_split large₂ hS v hv l hl key
      · rcases hA PP hQ with hS0 | hno
        · exact UpperTheory.WildA.small_set_primes_split large₂ hS _ hS0 l hl key
        · exact absurd hlw (hno l hl hlPP)
    exact ⟨k, hk, hc, le_rfl, fun _ => hsplit⟩
  · obtain ⟨k', hk', hnd, hc'⟩ := UpperTheory.WildA.depthDrop d l hl (fun w hw hlw' => h ⟨w, hw, hlw'⟩) k hk hc
    refine ⟨k', hk', hc', ?_, fun hd => absurd hd hnd⟩
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnd]
    exact Nat.zero_le _
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BvvInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem sum_map_apply {ι σ : Type} [Fintype ι] (m : ι → σ →₀ ℕ) (i : ι) (x : σ) :
    (∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j)) (i, x) = m i x := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact Finsupp.mapDomain_apply_of_injective (fun a b h => (Prod.mk.inj h).2) _ _
  · intro j _ hj
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hj (Prod.mk.inj hy).1
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem coeff_prod' {ι σ C : Type} [DecidableEq ι] [DecidableEq σ] [CommRing C] (f : ι → MvPolynomial σ C)
    (d : σ →₀ ℕ) (s : Finset ι) :
    AddMonoidAlgebra.coeff (∏ j ∈ s, f j) d = ∑ l ∈ Finset.finsuppAntidiag s d, ∏ j ∈ s, AddMonoidAlgebra.coeff (f j) (l j) := by
  have h := MvPowerSeries.coeff_prod (fun j => (f j : MvPowerSeries σ C)) d s
  have hp : ((∏ j ∈ s, f j : MvPolynomial σ C) : MvPowerSeries σ C) = ∏ j ∈ s, (f j : MvPowerSeries σ C) :=
    map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := C)) f s
  rw [← hp] at h
  simpa only [MvPolynomial.coeff_coe] using h

private theorem coeff_prod_ren {ι σ C : Type} [Fintype ι] [CommRing C] (m : ι → σ →₀ ℕ)
    (G : ι → MvPolynomial σ C) :
    AddMonoidAlgebra.coeff (∏ j, MvPolynomial.rename (fun v : σ => (j, v)) (G j))
        (∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j)) =
      ∏ j, AddMonoidAlgebra.coeff (G j) (m j) := by
  classical
  set D := ∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j) with hD
  have inj : ∀ j : ι, Function.Injective (fun v : σ => (j, v)) := fun j a b h => (Prod.mk.inj h).2
  rw [coeff_prod', Finset.sum_eq_single
    (Finsupp.equivFunOnFinite.symm fun j => Finsupp.mapDomain (fun v : σ => (j, v)) (m j))]
  · refine Finset.prod_congr rfl fun j _ => ?_
    exact MvPolynomial.coeff_rename_mapDomain _ (inj j) _ _
  · intro l hl hne
    by_contra hprod
    apply hne
    have hu : ∀ k, ∃ u : σ →₀ ℕ, Finsupp.mapDomain (fun v : σ => (k, v)) u = l k := by
      intro k
      by_contra hk
      push_neg at hk
      apply hprod
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      apply MvPolynomial.coeff_rename_eq_zero
      intro u hu'
      exact absurd hu' (hk u)
    choose u hu using hu
    have hsum : ∑ k, Finsupp.mapDomain (fun v : σ => (k, v)) (u k) = D := by
      rw [Finset.mem_finsuppAntidiag] at hl
      simp only [hu]
      exact hl.1
    have hum : u = m := by
      funext k
      ext x
      have hx := congrArg (fun F => F (k, x)) hsum
      simp only [hD, sum_map_apply] at hx
      exact hx
    ext1 k
    show l k = Finsupp.mapDomain (fun v : σ => (k, v)) (m k)
    rw [← hu k, hum]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    show ∑ k ∈ Finset.univ, Finsupp.mapDomain (fun v : σ => (k, v)) (m k) = D
    rw [hD]

private theorem unitri {I P C : Type} [Fintype I] [PartialOrder P] [CommRing C] (S : Subring C) (e : I → P)
    (he : Function.Injective e) (A : I → I → C) (c : I → C) (hA : ∀ i j, A i j ∈ S) (h1 : ∀ i, A i i = 1)
    (hle : ∀ i j, A i j ≠ 0 → e j ≤ e i) (hc : ∀ j, ∑ i, c i * A i j ∈ S) (j : I) : c j ∈ S := by
  classical
  suffices key : ∀ n, ∀ j, (Finset.univ.filter fun i => e j < e i).card = n → c j ∈ S from key _ j rfl
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro j hj
  have hrest : ∀ i ∈ Finset.univ.erase j, c i * A i j ∈ S := by
    intro i hi
    by_cases h0 : A i j = 0
    · rw [h0, mul_zero]
      exact S.zero_mem
    · have hlt : e j < e i :=
        lt_of_le_of_ne (hle i j h0) (fun h => (Finset.ne_of_mem_erase hi) (he h).symm)
      refine S.mul_mem ?_ (hA i j)
      refine ih _ ?_ i rfl
      rw [← hj]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨i, ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact lt_trans hlt hk
      · simp [hlt]
      · simp
  have hsum := hc j
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1, mul_one] at hsum
  have hfin := S.sub_mem hsum (sum_mem hrest)
  simpa using hfin

theorem UpperTheory.WildA.bvvInt :
    ∀ {ι : Type} [Fintype ι] {b : ℕ} (lam : ι → DomWeight b) (v : VV ℂ lam),
      (∀ m, ∃ z : ℤ, AddMonoidAlgebra.coeff (v : Pol ℂ ι b) m = (z : ℂ)) → ∀ i, ∃ z : ℤ, (bVV ℂ lam).repr v i = (z : ℂ) := by
  intro ι _ b lam v hv i
  classical
  let L : VVIdx lam → (ι × Fin b × Fin b →₀ ℕ) := fun j =>
    ∑ τ, Finsupp.mapDomain (fun x : Fin b × Fin b => (τ, x)) ((j τ : Fin b × Fin b →₀ ℕ))
  let A : VVIdx lam → VVIdx lam → ℂ := fun i j => AddMonoidAlgebra.coeff (bVVfun ℂ lam i) (L j)
  let e : VVIdx lam → (ι → (Formalism.GradedWeylDivisibility.colLex b b).syn) := fun i τ =>
    (Formalism.GradedWeylDivisibility.colLex b b).toSyn ((i τ : Fin b × Fin b →₀ ℕ))
  have hspec : ∀ {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν),
      (Formalism.GradedWeylDivisibility.colLex n n).degree (ssB ℂ ν m) = m ∧ (Formalism.GradedWeylDivisibility.colLex n n).leadingCoeff (ssB ℂ ν m) = 1 := by
    intro n ν m
    have h := (Formalism.L2.DIV.ssB._proof_1 ℂ ν).choose_spec.2 m
    exact ⟨h.1, h.2.1⟩
  have hAprod : ∀ i j, A i j =
      ∏ τ, AddMonoidAlgebra.coeff (ssB ℂ (lam τ).natW (i τ)) (j τ : Fin b × Fin b →₀ ℕ) := by
    intro i j
    exact coeff_prod_ren (fun τ => (j τ : Fin b × Fin b →₀ ℕ)) (fun τ => ssB ℂ (lam τ).natW (i τ))
  have hdiag : ∀ i, A i i = 1 := by
    intro i
    rw [hAprod]
    apply Finset.prod_eq_one
    intro τ _
    have h := hspec (lam τ).natW (i τ)
    simpa [MonomialOrder.leadingCoeff, h.1] using h.2
  have hexp : (v : Pol ℂ ι b) = ∑ k ∈ ((bVV ℂ lam).repr v).support,
      ((bVV ℂ lam).repr v k) • bVVfun ℂ lam k := by
    have h0 := (bVV ℂ lam).linearCombination_repr v
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at h0
    conv_lhs => rw [← h0]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, bVV_coe]
  by_cases hi : i ∈ ((bVV ℂ lam).repr v).support
  swap
  · simp only [Finsupp.mem_support_iff, not_not] at hi
    exact ⟨0, by simp [hi]⟩
  have key : (bVV ℂ lam).repr v i ∈ (Int.castRingHom ℂ).range := by
    refine unitri (I := {x // x ∈ ((bVV ℂ lam).repr v).support}) (Int.castRingHom ℂ).range
      (fun x => e x.1) ?_ (fun x y => A x.1 y.1) (fun x => (bVV ℂ lam).repr v x.1) ?_ ?_ ?_ ?_ ⟨i, hi⟩
    · intro x y hxy
      apply Subtype.ext
      funext τ
      apply Subtype.ext
      exact (Formalism.GradedWeylDivisibility.colLex b b).toSyn.injective (congrFun hxy τ)
    · intro x y
      obtain ⟨P, hP⟩ := bVVfun_int ℂ lam x.1
      refine RingHom.mem_range.mpr ⟨AddMonoidAlgebra.coeff P (L y.1), ?_⟩
      show _ = AddMonoidAlgebra.coeff (bVVfun ℂ lam x.1) (L y.1)
      rw [hP, MvPolynomial.coeff_map]
    · intro x
      exact hdiag x.1
    · intro x y hxy τ
      have hne : ∀ τ ∈ Finset.univ,
          AddMonoidAlgebra.coeff (ssB ℂ (lam τ).natW (x.1 τ)) (y.1 τ : Fin b × Fin b →₀ ℕ) ≠ 0 := by
        rw [← Finset.prod_ne_zero_iff, ← hAprod]
        exact hxy
      have hd := (Formalism.GradedWeylDivisibility.colLex b b).le_degree
        (MvPolynomial.mem_support_iff.mpr (hne τ (Finset.mem_univ τ)))
      rw [(hspec (lam τ).natW (x.1 τ)).1] at hd
      exact hd
    · intro j
      have hcoef : AddMonoidAlgebra.coeff (v : Pol ℂ ι b) (L j.1) =
          ∑ x : {x // x ∈ ((bVV ℂ lam).repr v).support}, (bVV ℂ lam).repr v x.1 * A x.1 j.1 := by
        rw [hexp, MvPolynomial.coeff_sum, ← Finset.sum_coe_sort]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [MvPolynomial.coeff_smul, smul_eq_mul] <;> rfl
      show ∑ x : {x // x ∈ ((bVV ℂ lam).repr v).support}, (bVV ℂ lam).repr v x.1 * A x.1 j.1 ∈ _
      rw [← hcoef]
      obtain ⟨z, hz⟩ := hv (L j.1)
      exact RingHom.mem_range.mpr ⟨z, by simp [hz]⟩
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp key
  exact ⟨z, by simpa using hz.symm⟩
end

module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalThetaCorrespondenceInertPlaceOfHowe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateThetaLiftMatchedHeckeCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumFockVectorsIsVacuumOffLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumFockVectorsIsVacuumOffLevel
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacua

open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem delta_orth {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
    {P Q : HeightOneSpectrum (𝓞 D.host.E)} {a b : AE D} (ha : IsDelta Φ P a) (hb : IsDelta Φ Q b) (h : P ≠ Q) :
    a * b = 0 := by
  refine hΦ.ext' (by rw [RingHom.map_mul, ha.1, zero_mul, RingHom.map_zero]) fun Q' => ?_
  rw [ev_mul, ev_zero]
  by_cases hQ : Q' = P
  · rw [hb.2.2 Q' (hQ ▸ h), mul_zero]
  · rw [ha.2.2 Q' hQ, zero_mul]

theorem half_orth {m n : ℕ} {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {u : Matrix (Fin m) (Fin n) (AE D)}
    (hu : IsHalf e u ∨ IsHalf (cA D e) u) :
    u.map (infPart D) = 0 ∧ ∀ (S : Finset (Pl D.host.E)) (e' : AE D), IsIdemSum e' S →
      (∀ PP ∈ S, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ i j, e' * u i j = 0 ∧ cA D e' * u i j = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := (of_isPrimeIdem hΦ h).1
  obtain ⟨Q, a, hQ, ha, hu⟩ : ∃ Q a, (Q = P ∨ Q = cP P) ∧ IsDelta Φ Q a ∧ ∀ i j, a * u i j = u i j := by
    rcases hu with hu | hu
    exacts [⟨P, e, Or.inl rfl, hd, hu⟩, ⟨cP P, cA D e, Or.inr rfl, delta_conj hΦ hd, hu⟩]
  refine ⟨Matrix.ext fun i j => ?_, ?_⟩
  · rw [Matrix.map_apply, ← hu, RingHom.map_mul, ha.1, zero_mul, Matrix.zero_apply]
  · rintro S e' ⟨⟨es, hes, rfl⟩, -⟩ hS i j
    have key : ∀ PP ∈ S, PP ≠ Q ∧ cP PP ≠ Q := fun PP hPP => by
      obtain ⟨h1, h2⟩ := hS PP hPP
      rw [isConjPl_iff] at h2
      rcases hQ with rfl | rfl
      · exact ⟨h1, Ne.symm h2⟩
      · exact ⟨fun e => h2 (by rw [e, cP_cP]), fun e => h1 (by rw [← cP_cP PP, e, cP_cP])⟩
    have k1 : (∑ PP ∈ S, es PP) * a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP => delta_orth hΦ (delta_of_isIdemAt hΦ (hes PP hPP)) ha (key PP hPP).1
    have k2 : cA D (∑ PP ∈ S, es PP) * a = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP =>
        delta_orth hΦ (delta_conj hΦ (delta_of_isIdemAt hΦ (hes PP hPP))) ha (key PP hPP).2
    rw [← hu, ← mul_assoc, ← mul_assoc, k1, k2, zero_mul]
    exact ⟨rfl, rfl⟩

theorem isVacAt_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ φ, GlobalTheory.Hk3.IsVacAt R.ψ _ _ P (GlobalTheory.GalLift.ptAt R i σ B f φ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hθ i σ f₀ f B hV P hP φ
  obtain ⟨⟨-, hvac⟩, e, he, hth⟩ := hV.vec
  obtain ⟨c, hc⟩ := hL.βV i
  obtain ⟨c', hc'⟩ := hL.βW i
  rw [one_pow] at hc hc'
  have h0 : GlobalTheory.Hk3.IsVacAt R.ψ _ _ P f₀ :=
    GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level R.ψ _ _ (R.βV i) (R.βW i) (R.ΛV i) (R.ΛW i) 1 1 hc hc' P
      (by rw [mul_one, Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)) f₀ hvac.theta hvac.lat
  refine ⟨hV.theta φ, fun e' f' h' u hu hh => ?_⟩
  obtain ⟨h1, h2⟩ := half_orth h' hh
  refine GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors R.ψ R.θ _ _ hθ _ _ _ _ f hV.theta u h1 ?_ φ
  refine GlobalTheory.T.heisenbergOperator_fix_thetaDatum_away_splitPlaces R.ψ _ _ _ _ _ f₀ _ f hth u (fun a b => ?_) (h0.2 e' f' h' u hu hh)
  have := h2 _ e he (fun PP hPP => hP PP (Or.inl (by simpa using hPP))) a b
  rw [cA_cA]
  exact this.symm

end GlobalTheory.ConjVacua
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumFockVectorsIsVacuumOffLevelStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateDatum_fockVectors_isVacuum_off_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ φ, GlobalTheory.Hk3.IsVacAt R.ψ _ _ P (GlobalTheory.GalLift.ptAt R i σ B f φ) := by
  first | exact @GlobalTheory.ConjVacua.isVacAt_ptAt | exact GlobalTheory.ConjVacua.isVacAt_ptAt | (intros; apply GlobalTheory.ConjVacua.isVacAt_ptAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFormsSpherical
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSph

open GlobalTheory.Hk3

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem adForms_iff {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) :
    F ∈ Bridge.AdForms ι ρ J χ ↔
      (∀ h (k : J), F (h * k) = ((χ k : ℂˣ) : ℂ) • F h) ∧ ∀ γ h, F (ι γ * h) = ρ γ (F h) := by
  change (∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = ((χ k : ℂˣ) : ℂ) • ρ γ (F h)) ↔ _
  constructor
  · intro hF
    refine ⟨fun h k => ?_, fun γ h => ?_⟩
    · simpa using hF 1 h k
    · simpa using hF γ h 1
  · rintro ⟨hR, hL⟩ γ h k
    rw [hR, hL]

def hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : G → W) : G → W :=
  fun h => c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ)

theorem dual_hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (l : W →ₗ[ℂ] ℂ) (c : List ℤ →₀ ℂ)
    (F : G → W) (x : GA D V) : l (hkG φ P c F (φ x)) = hk V P c (fun y => l (F (φ y))) x := by
  rw [GlobalTheory.LevOp.hk_apply]
  show l (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (φ x * φ γ)) = _
  rw [map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  show _ = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, l (F (φ (x * γ)))
  simp only [map_mul]

theorem hkG_left {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (c : List ℤ →₀ ℂ)
    (F : G → W) (g : G) (T : W →ₗ[ℂ] W) (hF : ∀ h, F (g * h) = T (F h)) (h : G) :
    hkG φ P c F (g * h) = T (hkG φ P c F h) := by
  show (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * h * φ γ)) =
    T (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ))
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun d _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_assoc, hF]

theorem hkG_right {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (hφ : Function.Surjective φ)
    {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ) (F : G → W)
    (hF : ∀ k ∈ hyp V P, ∀ h, F (h * φ k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (z : ℂ) (hz : ∀ h, F (h * φ (k₁ * k₂)) = z • F h) (h : G) :
    hkG φ P c F (h * φ (k₁ * k₂)) = z • hkG φ P c F h := by
  obtain ⟨x, rfl⟩ := hφ h
  rw [← map_mul φ x (k₁ * k₂), ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, dual_hkG, dual_hkG, sub_eq_zero, smul_eq_mul]
  have hinv : ∀ k ∈ hyp V P, ∀ y, (fun y => l (F (φ y))) (y * k) = (fun y => l (F (φ y))) y := by
    intro k hk y
    show l (F (φ (y * k))) = l (F (φ y))
    rw [map_mul, hF k hk]
  rw [GlobalTheory.LevOp.hk_translate hP hJ c hinv hk₁ s₁ s₂ x]
  have hsc : (fun y => (fun y => l (F (φ y))) (y * (k₁ * k₂))) = z • fun y => l (F (φ y)) := by
    funext y
    show l (F (φ (y * (k₁ * k₂)))) = z * l (F (φ y))
    rw [map_mul φ y (k₁ * k₂), hz, map_smul, smul_eq_mul]
  rw [hsc, map_smul]
  rfl


set_option maxHeartbeats 1000000 in
theorem adForms_spherical (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : GQ V →* Module.End ℂ W)
    (χ' : (levEnv V β L).J →* ℂˣ) (hχ' : ∀ k, (((levEnv V β L).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1)
    {F : Bridge.Gf V → W} (hF : F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ') (c : List ℤ →₀ ℂ) :
    (∀ k ∈ hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h) ∧
      hkF V P c F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ' := by
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  have hPf := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  obtain ⟨hJf, hχf, hsplit⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N (flag1L L) hB).2 P e f hP hN hPP
  have hFl := (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' F).1 hF
  have hinv : ∀ k ∈ hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h := by
    rintro k ⟨hkK, e', f', hP', hk⟩ h
    obtain ⟨-, rfl⟩ := hPf.2.2.2.1 e' f' hP'
    have hkJ : k ∈ levG V β (flag1L L) := (hJf k hk).2 hkK
    have hmem : (finHom V).rangeRestrict k ∈ (levEnv V β L).J :=
      (GlobalTheory.SplitHeckeAdj.mem_J V β L (hPf.2.2.1 k hk)).2 hkJ
    have h1 : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = 1 := by
      rw [GlobalTheory.SplitHeckeAdj.chi_eq V β L hmem]
      exact hχf k hkJ hk
    rw [hFl.1 h ⟨_, hmem⟩, hχ' _ h1, one_smul]
  refine ⟨hinv, (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' _).2 ⟨fun h k => ?_, fun γ h => ?_⟩⟩
  · obtain ⟨g, hgG, hg⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V (k : Bridge.Gf V)
    have hgJ : g ∈ levG V β (flag1L L) := by
      refine (GlobalTheory.SplitHeckeAdj.mem_J V β L hgG).1 ?_
      rw [hg]
      exact k.2
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hsplit g hgJ
    have hz : ∀ h', F (h' * (finHom V).rangeRestrict (k₁ * k₂)) = ((χ' k : ℂˣ) : ℂ) • F h' := by
      intro h'
      rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg]
      exact hFl.1 h' k
    have key := hkG_right (P := P) (finHom V).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hP
      (J := levG V β (flag1L L)) hJf c F hinv hk₁ s₁ s₂ _ hz h
    rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg] at key
    exact key
  · exact hkG_left (P := P) (finHom V).rangeRestrict c F (Bridge.ratF V γ) (ρ γ) (hFl.2 γ) h


set_option maxHeartbeats 1000000 in
theorem conjForms_spherical : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ c₀, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ c₀ c c₁ H j → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ cV (y : H.H), (∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom _).rangeRestrict k) = H.e y h) ∧ ∃ y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i σ c c₁ H j c₀ hC P hG cV y
  obtain ⟨χ', hχc, hIs⟩ := hC.model
  obtain ⟨-, hrange, -⟩ := hIs
  have hSD : ∃ c, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) (1 ^ c) := hR.βV i
  obtain ⟨n, hB⟩ := hSD
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have htriv : ∀ k, (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1 := by
    intro k hk
    obtain ⟨a, ha, hb⟩ := hχc k
    have ha1 : a = 1 := D.what₂.embLL.injective (by rw [ha, hk, map_one])
    rw [← hb, ha1, map_one]
  have hPP : ∀ PP, PP ∈ (R.datVt i A.μ0).Pg ∨ PP ∈ (R.datVt i A.μ0).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := hG
  have key := adForms_spherical (V := Vc D i) (P := P) (R.βV i) (R.ΛV i) (1 ^ n) (R.datVt i A.μ0) hB hN hPP c.coef.ρ χ' htriv (F := H.e y) (by
      have h0 := LinearMap.mem_range_self H.e y
      rw [hrange] at h0
      exact h0) cV
  have k1 : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom (Vc D i)).rangeRestrict k) = H.e y h := by
    intro k hk h
    exact key.1 k hk h
  refine ⟨fun k hk h => Eq.trans ?_ (k1 k hk h), ?_⟩
  · congr! 2
  have h3 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levJ R i A.μ0) χ' := key.2
  have h4 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ LinearMap.range H.e := (SetLike.ext_iff.mp hrange _).mpr h3
  obtain ⟨y', hy'⟩ := h4
  exact ⟨y', hy'⟩

end GlobalTheory.ConjSph

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateThetaLiftMatchedHeckeCombination
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjLiftHecke

variable {D : D7}

theorem theta_form_conj {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} (hW : IsWeilDatumO ψ S T χS χT om)
    (hs : S.SigOK) (hp : S.IsPosDef) {Kf : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {ν : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hν : IsMeasDef S Kf ν 𝓕) (hfix : GlobalTheory.Hk3.VacFix ψ om P) {cS cT : List ℤ →₀ ℂ}
    (hM : GlobalTheory.Hk3.Match ψ om P (GlobalTheory.Hk3.dualC cS) cT) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    (hG : ∀ k ∈ GlobalTheory.Hk3.hyp S P, k ∈ GfC S) {f f' : Bridge.Gf S → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (hsph : ∀ k ∈ GlobalTheory.Hk3.hyp S P, ∀ h, f (h * (finHom S).rangeRestrict k) = f h) (hf' : f' = GlobalTheory.Hk3.hkF S P cS f)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ φ, GlobalTheory.Hk3.IsVacAt ψ S T P (pt φ))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {u u' : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f h))) ∂ν)
    (hu' : ∀ g, u' g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f' h))) ∂ν) : u' = GlobalTheory.Hk3.hk T P cT u := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  funext g
  have key := GlobalTheory.DefLiftHecke.theta_comb hW hpos hν.1.1 hν.2 hfix hM (pt ∘ₗ io) (fun w => hpt _) (c.ext f)
    (GlobalTheory.ConjThetaIntegral.ext_continuous c hc β L χ' hχ hf) (GlobalTheory.ThetaIntegrand.ext_invariant c hf)
    (fun k hk h => by
      rw [GlobalTheory.DefLiftHecke.ext_mul c hc f (hG k hk) h, hsph k hk]
      rfl) g
  rw [hu', funext hu, hf']
  simp only [GlobalTheory.DefLiftHecke.ext_hkF c hc]
  exact key

theorem theta_right_hyp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {P : Pl D.host.E} (hfix : GlobalTheory.Hk3.VacFix ψ om P) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)}
    {φ : GA D S → (WO S T → ℂ)} (hφ : ∀ h, GlobalTheory.Hk3.IsVacAt ψ S T P (φ h)) {u : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (φ h) ∂ν) : ∀ k ∈ GlobalTheory.Hk3.hyp T P, ∀ g, u (g * k) = u g := by
  intro k hk g
  rw [hu, hu]
  refine congrArg (fun w : GA D S → ℂ => ∫ h in 𝓕, w h ∂ν) (funext fun h => ?_)
  unfold thetaKO
  rw [show ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) by simp, map_mul, Module.End.mul_apply,
    hfix _ (hφ h) 1 (GlobalTheory.DefLiftHecke.one_mem_hyp _ P) k hk]

theorem gaL_hk_of_hyp {G : Type} [Group G] [Fintype G] {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (eG : G ≃* G0 L.Pg L.r) (z : G → ℂ) (c : List ℤ →₀ ℂ) {Φ : GA D V → ℂ}
    (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    gaL V β L eG z (GlobalTheory.Hk3.hk V P c Φ) = GlobalTheory.Hk3.hk V P c (gaL V β L eG z Φ) := by
  obtain ⟨n, hB⟩ := hβ
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.LevOp.level_operators V β Λ _ L hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP
  exact GlobalTheory.DefLiftHecke.gaL_hk eG z fun g0 => h4 c g0 _ hΦ

theorem eq_of_eval {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {Hh : Type} [NormedAddCommGroup Hh]
    [InnerProductSpace ℂ Hh] (e : Hh →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hip : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) {Wa : Submodule ℂ (MMap M)} (hr : LinearMap.range e = Wa)
    (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) {a : Hh} {U : MMap M} (hU : U ∈ Wa) (h : e a v = U v) : e a = U := by
  rw [← hr] at hU
  obtain ⟨b, rfl⟩ := hU
  exact congrArg e (GlobalTheory.EvalAtUnitVector.eval_injective M Hh e d μ 𝓕 hip v hv h)

set_option maxHeartbeats 1000000 in
theorem lift_match : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L hT i σ c c₁ H j hK hj μ' η' th ω f₀ f B io thP hD hPr P hG hfix cV cW hM y y' hy
  have hW := hD.1
  have hV := hD.2.1
  have hIo := hD.2.2.1
  have hTh := hD.2.2.2
  refine hj.model.elim fun χ' hm => ?_
  have hχ := hm.1
  have hH := hm.2
  have hvac := GlobalTheory.T.conjugateDatum_fockVectors_isVacuum_off_level R hC.lev hC.models.inf i σ f₀ f B hV P hG
  have hform : ∀ x, H.e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).J χ' :=
    fun x => hH.2.1.le (LinearMap.mem_range_self _ x)
  have hχ1 : ∀ k, (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k = 1 → χ' k = 1 := fun k hk =>
    Units.ext (GlobalTheory.ConjThetaIntegral.conjVal_one (hχ k) (congrArg Units.val hk))
  have hsph := (GlobalTheory.ConjSph.conjForms_spherical R hC.lev i σ c c₁ H j _ hj P hG cV y).1
  refine (hC.lev.βV i).elim fun nV hBV => ?_
  have hlevV := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (R.datVt i A.μ0) hBV P
    (GlobalTheory.DefLiftHecke.one_pow_notMem P nV) hG).1
  have hStep : ∀ w : LowT (R.MW i σ), thP ((c.ext ∘ₗ H.e).rangeRestrict y') w =
      GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w) := fun w => by
    refine theta_form_conj hW (D.sp.V_sig _) (hC.models.vpos i) (hC.models.νV i A.μ0) hfix hM c hj.coef (R.βV i)
      (R.datVt i A.μ0) χ' hχ1 (fun k hk => (hlevV k hk).1.1) (hform y) hsph hy
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) hvac (io w)
      (fun g => hTh.eq _ w g) (fun g => hTh.eq _ w g)
  have hWinv : ∀ (w : LowT (R.MW i σ)), ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P, ∀ g,
      thP ((c.ext ∘ₗ H.e).rangeRestrict y) w (g * k) = thP ((c.ext ∘ₗ H.e).rangeRestrict y) w g := fun w =>
    theta_right_hyp hfix (fun h => hvac _) (fun g => hTh.eq _ w g)
  have hGW : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P :=
    fun PP h => hG PP (h.imp_right fun h => absurd h (Finset.notMem_empty _))
  have hcomm : ∀ w : LowT (R.MW i σ), R.eWf i σ (GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) =
      GlobalTheory.Hk3.hk (Wc D i) P cW (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) := fun w =>
    gaL_hk_of_hyp (hC.lev.βW i) hGW R.eG _ cW (hWinv w)
  have hmod := hC.models.HW i σ
  have hU : (R.HW i σ).e (th y) ∈ R.Wall i σ := hmod.2.1.le (LinearMap.mem_range_self _ _)
  have hU' : postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) ∈ R.Wall i σ :=
    (GlobalTheory.DefLiftHecke.mult_laws hC.models.inf (R.MW i σ) (hC.lev.βW i) (L := R.datWp i R.triv) hGW R.eG
      (RealDat.eC (A := A) σ) cW hU).1
  refine hIo.2.2.elim fun v hv => hv.elim fun _ hw => ?_
  refine eq_of_eval (R.MW i σ) (R.HW i σ).e _ (R.νW i) (R.fdW i) hmod.2.2 hmod.2.1 (fun ρ => v ρ) hw.1 hU' ?_
  exact (hPr y' v).trans ((congrArg (R.eWf i σ) (hStep _)).trans ((hcomm _).trans
    ((congrArg (GlobalTheory.Hk3.hk (Wc D i) P cW) (hPr y v).symm).trans (postOn_apply _ _ _ _).symm)))

end GlobalTheory.ConjLiftHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateThetaLiftMatchedHeckeCombinationStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_theta_lift_matched_hecke_combination : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  first | exact @GlobalTheory.ConjLiftHecke.lift_match | exact GlobalTheory.ConjLiftHecke.lift_match | (intros; apply GlobalTheory.ConjLiftHecke.lift_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePart
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.LiftPart
open GlobalTheory.Hk3

theorem tri_solve {X : Type} [AddCommGroup X] [Module ℂ X] (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) (m : ℕ) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X), (∀ k, k < m → ∑ j ∈ Finset.range (k + 1), z k j • T j = α k • F) →
      ∀ k, k < m → T k = β k • F := _root_.GlobalTheory.DownEigen.tri_solve (X := X) z α hz m

variable {D : D7}

theorem rep_of_not {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) : GlobalTheory.Hk3.rep V P d = ∅ := by
  unfold GlobalTheory.Hk3.rep; rw [dite_eq_right h]

theorem hkF_evC (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (a : List ℤ → ℂ)
    (Φ : Bridge.Gf V → W) (h : ∀ d, IsLab V P d → hkF V P (Finsupp.single d 1) Φ = a d • Φ) (c : List ℤ →₀ ℂ) :
    hkF V P c Φ = evC V P a c • Φ := by
  classical
  funext g
  have e : ∀ d, ∑ γ ∈ GlobalTheory.Hk3.rep V P d, Φ (g * (finHom V).rangeRestrict γ) = (if IsLab V P d then a d else 0) • Φ g := by
    intro d
    by_cases hd : IsLab V P d
    · have := congrFun (h d hd) g
      unfold hkF at this
      rw [Finsupp.sum_single_index (by simp), one_smul] at this
      rw [if_pos hd, this]; rfl
    · rw [if_neg hd, rep_of_not hd, Finset.sum_empty, zero_smul]
  unfold Hk3.evC
  simp only [hkF, Finsupp.sum, Pi.smul_apply, Finset.sum_smul, e, smul_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem hk_splitC (V : HSp D) (P : Pl D.host.E) (n : ℕ) (z : ℕ → ℂ) :
    hk V P (splitC n z) = ∑ j ∈ Finset.range (n + 1), z j • hk V P (Finsupp.single (splitLab n j) 1) := by
  unfold splitC hk
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), one_smul]

theorem postOn_sum {V : HSp D} {S : _} (M : DSModel V S) (s : Finset ℕ) (w : ℕ → ℂ)
    (L : ℕ → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ j ∈ s, w j • L j) T = ∑ j ∈ s, w j • postOn M (L j) T := by
  ext v
  simp [postOn]

theorem tri_solve' {X : Type} [AddCommGroup X] [Module ℂ X] (n : ℕ) (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X),
      (∀ k, k ≤ n → α k • F = ∑ j ∈ Finset.range (n + 1), (if j ≤ k then z k j else 0) • T j) →
      ∀ k, k ≤ n → T k = β k • F := by
  obtain ⟨β, hβ⟩ := tri_solve (X := X) z α hz (n + 1)
  refine ⟨β, fun F T h k hk => hβ F T (fun k' hk' => ?_) k (by omega)⟩
  rw [h k' (by omega)]
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul]

theorem exists_split_data {P : Pl D.host.E} (hc : Formalism.DivisionValues.conjPl P ≠ P) : ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ),
    Formalism.L2.NTheta.IsIdemAt e P ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt hc
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ P.asIdeal, ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  exact ⟨e, ϖ, Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), he, h1, h2, by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩

theorem diag_ne_zero (P : Pl D.host.E) (χS χT : (AE D)ˣ →* Circle) (x : (AE D)ˣ) (nS nT t k : ℕ) :
    (Ideal.absNorm P.asIdeal : ℂ) ^ ((nT - k) * (k - k)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - k) : ℂ) *
      ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nT)⁻¹ ^ k *
      ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nS) ^ k ≠ 0 := by
  have hq0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have hs0 : (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by exact_mod_cast Nat.pos_of_ne_zero hq0))
  have hT : (χT x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hS : (χS x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [Nat.sub_self, mul_zero, pow_zero, one_mul, GlobalTheory.KerRangeCount.gaussBin_zero_right, Nat.cast_one, one_mul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (mul_ne_zero hT (pow_ne_zero _ hs0))))
    (pow_ne_zero _ (mul_ne_zero hS (pow_ne_zero _ hs0)))

theorem dualC_dualC' (c : List ℤ →₀ ℂ) : dualC (dualC c) = c := by
  unfold dualC
  rw [← Finsupp.mapDomain_comp]
  have : dualLab ∘ dualLab = id := by
    funext d
    simp [dualLab, List.map_reverse]
  rw [this, Finsupp.mapDomain_id]

section Loc

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) {c : CoefA (Vc D i)}
  {H : HMod (Bridge.Gf (Vc D i) → c.W)} (th : H.H →ₗ[ℂ] (R.HW i σ).H) (μ' η' : (AE D)ˣ →* Circle)
  (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (P : Pl D.host.E)
  (a : Pl D.host.E → List ℤ → ℂ)


set_option maxHeartbeats 2000000 in
theorem loc_inert (hHowe : HoweUnram) (hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) (hP : Good R A.μ0 P)
    (hvac : VacFix R.ψ ω P) (hc : Formalism.DivisionValues.conjPl P = P)
    (step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
      (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y))) (d : List ℤ) :
    ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
  have hsc := GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω P hW hc hvac
  have hcorr := hsc.2.1
  obtain ⟨cS, hM⟩ := hcorr (Finsupp.single d 1)
  refine ⟨evC (Vc D i) P (a P) (dualC cS), fun u hu => ?_⟩
  have hM' : Match R.ψ ω P (dualC (dualC cS)) (Finsupp.single d 1) := by rwa [dualC_dualC']
  have hy : H.e (evC (Vc D i) P (a P) (dualC cS) • u) = hkF (Vc D i) P (dualC cS) (H.e u) := by
    rw [map_smul, hkF_evC (Vc D i) P (a P) (H.e u) (fun d' hd' => hu P d' hP (Or.inr ⟨hc, hd'⟩))]
  have := step (dualC cS) (Finsupp.single d 1) hM' u _ hy
  rw [map_smul, map_smul] at this
  exact this.symm


set_option maxHeartbeats 2000000 in
theorem loc_split (hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) (hP : Good R A.μ0 P)
    (hu1 : UnrPl P μ') (hu2 : UnrPl P (μ' * η'⁻¹)) (hc : Formalism.DivisionValues.conjPl P ≠ P)
    (step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
      (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y))) (d : List ℤ)
    (hd : RelLab (Wc D i) P d) :
    ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
  have hd' : ∃ k, k ≤ (Wc D i).rank ∧ d = splitLab (Wc D i).rank k := by
    rcases hd with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hc
  obtain ⟨k, hkr, rfl⟩ := hd'
  have hdat := exists_split_data hc
  obtain ⟨e, ϖ, x, he, h1, h2, hx⟩ := hdat
  have hrk : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rank_Wc]; rfl
  have hms0 := GlobalTheory.Hk3.SplitMatch.match_split R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω P hW hc hu1 hu2
  have hms := (hms0.2 e ϖ x D.R.t he h1 h2 hx).2 hrk
  have htri := tri_solve' (X := MMap (R.MW i σ)) (Wc D i).rank
    (fun k j => (Ideal.absNorm P.asIdeal : ℂ) ^ (((Wc D i).rank - j) * (k - j)) *
      (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) D.R.t (k - j) : ℂ) *
      ((((μ' * η'⁻¹) x : Circle) : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Wc D i).rank)⁻¹ ^ k *
      (((μ' x : Circle) : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Vc D i).rank) ^ j)
    (fun k => a P (splitLab (Vc D i).rank k))
    (fun k => diag_ne_zero P μ' (μ' * η'⁻¹) x (Vc D i).rank (Wc D i).rank D.R.t k)
  obtain ⟨β, hβ⟩ := htri
  refine ⟨β k, fun u hu => hβ ((R.HW i σ).e (th u))
    (fun j => postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single (splitLab (Wc D i).rank j) 1)) ((R.HW i σ).e (th u)))
    (fun k' hk' => ?_) k hkr⟩
  have hy : H.e (a P (splitLab (Vc D i).rank k') • u) =
      hkF (Vc D i) P (Finsupp.single (splitLab (Vc D i).rank k') 1) (H.e u) := by
    rw [map_smul, hu P _ hP (Or.inl ⟨hc, k', by omega, rfl⟩)]
  have := step _ _ (hms k' (by omega)) u _ hy
  rw [map_smul, map_smul, hk_splitC, postOn_sum] at this
  exact this

end Loc


set_option maxHeartbeats 4000000 in
theorem lift_eig_mem_part : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ a : Pl D.host.E → List ℤ → ℂ, ∃ ev, ∀ u : H.H, GlobalTheory.ConjScalar.EigF R i a (H.e u) → th u ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro hHowe D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L tie i σ c c₁ H j hK μ' η' th hD hyp a
  have hforms := hD.2.2.1
  have hlift := hD.2.2.2
  have h2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hlift
  obtain ⟨ω, f₀, f, B, io, thP, hh⟩ := h2
  have hLD := hh.1
  have hproj := hh.2
  have hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω := hLD.1
  have hVec : GlobalTheory.GalLift.VecData R i σ f₀ f B := hLD.2.1
  have loc : ∀ P, Good R A.μ0 P → ∀ d, RelLab (Wc D i) P d → ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
    intro P hP d hd
    have h38 := GlobalTheory.T.conjugateSplitting_unramified_hyperspecial_fix R F hC i σ μ' η' hyp ω hW f₀ f B hVec P hP
    obtain ⟨hu1, hu2, hvac⟩ := h38
    have step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
        (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y)) :=
      GlobalTheory.T.conjugate_theta_lift_matched_hecke_combination R F hC gramR c0R c0L tie i σ c c₁ H j hK hforms μ' η' th ω f₀ f B io thP hLD hproj P hP hvac
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · exact loc_inert R i σ th μ' η' ω P a hHowe hW hP hvac hc step d
    · exact loc_split R i σ th μ' η' ω P a hW hP hu1 hu2 hc step d hd
  classical
  let b : Pl D.host.E → List ℤ → ℂ := fun P d =>
    if h : Good R A.μ0 P ∧ RelLab (Wc D i) P d then (loc P h.1 d h.2).choose else 0
  obtain ⟨ev, hev⟩ := GlobalTheory.T.thetaForm_eigen_mem_single_part R hC.lev hC.models.HW i σ b
  refine ⟨ev, fun u hu => hev (th u) fun P d hP hd => ?_⟩
  simp only [b, dif_pos (And.intro hP hd)]
  exact (loc P hP d hd).choose_spec u hu

end GlobalTheory.ConjScalar.LiftPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePartStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateDatumLift_jointEigenspace_into_one_part : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ a : Pl D.host.E → List ℤ → ℂ, ∃ ev, ∀ u : H.H, GlobalTheory.ConjScalar.EigF R i a (H.e u) → th u ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  first | exact @GlobalTheory.ConjScalar.LiftPart.lift_eig_mem_part | exact GlobalTheory.ConjScalar.LiftPart.lift_eig_mem_part | (intros; apply GlobalTheory.ConjScalar.LiftPart.lift_eig_mem_part <;> assumption)
end

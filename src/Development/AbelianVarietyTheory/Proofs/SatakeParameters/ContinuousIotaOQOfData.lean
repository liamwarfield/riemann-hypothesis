module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Formalism.LocalToGlobal.KernelLattices.TopLawQ

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.CoeffEmbedding

theorem continuous_iotaOQ_of_data : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) :=
  fun {R H what₂} N A i => continuous_iotaOQ R H what₂ N A i

end GlobalTheory.CoeffEmbedding
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimple
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SSComplement

section Rep

variable {Γ k : Type} [Group Γ] [Field k]

def blockM {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k) (ρ₂ : Γ →* GL (Fin b) k) :
    Γ →* Matrix (Fin n) (Fin n) k where
  toFun g := Matrix.reindex e0 e0
    (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k))
  map_one' := by simp
  map_mul' g g' := by simp [Matrix.fromBlocks_multiply]

def diagM {t : ℕ} (χ : Fin t → Γ →* kˣ) : Γ →* Matrix (Fin t) (Fin t) k where
  toFun g := Matrix.diagonal fun c => ((χ c g : kˣ) : k)
  map_one' := by simp
  map_mul' g h := by simp [Matrix.diagonal_mul_diagonal]

theorem blockM_ss {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep (blockM e0 ρ₁ ρ₂).toHomUnits := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k e0).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h₁ h₂
  show _ = _
  ext i <;> simp [blockM, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

theorem ss_of_scalar {a : ℕ} (ρ : Γ →* GL (Fin a) k) (c : Γ → k)
    (h : ∀ g v, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v = c g • v) : IsSSRep ρ := by
  intro W _
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  exact ⟨W', fun g v hv => by rw [h]; exact W'.smul_mem _ hv, hW'⟩

theorem diagM_ss : ∀ {t : ℕ} (χ : Fin t → Γ →* kˣ), IsSSRep (diagM χ).toHomUnits := by
  intro t
  induction t with
  | zero =>
    intro χ
    exact ss_of_scalar _ (fun _ => 0) fun g v => funext fun c => c.elim0
  | succ t ih =>
    intro χ
    refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod (ρ₁ := (diagM fun c : Fin t => χ (Fin.castAdd 1 c)).toHomUnits)
      (ρ₂ := (diagM fun c : Fin 1 => χ (Fin.natAdd t c)).toHomUnits)
      ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) (ih _)
      (ss_of_scalar _ (fun g => ((χ (Fin.last t) g : kˣ) : k)) fun g v => ?_)
    · show _ = _
      ext i <;> simp [diagM, Matrix.mulVec_diagonal, LinearMap.funLeft]
    · funext c
      obtain rfl : c = 0 := Subsingleton.elim _ _
      change (Matrix.diagonal fun c : Fin 1 => ((χ (Fin.natAdd t c) g : kˣ) : k)).mulVec v 0 = _
      exact Matrix.mulVec_diagonal _ _ _

end Rep

end GlobalTheory.SSComplement
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.InertCompare

section Emb

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom

def rhoH (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem rhoH_apply (τ : D.what₂.Tau) (x : D.host.E) : rhoH D lam τ x = lamC lam (embT D τ x) := by
  unfold lamC
  rw [dite_eq_left (embT_mem D τ x)]
  rfl

theorem coe_rhoH (τ : D.what₂.Tau) : (rhoH D lam τ : D.host.E → ℂ_[l]) = tauEmb D lam τ :=
  funext fun x => rhoH_apply D lam τ x

def rhoC (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] := (rhoH D lam τ).comp (D.host.conj : D.host.E →+* D.host.E)

end Emb

def SamePrime {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ ρ' : E →+* ℂ_[l]) : Prop :=
  ∀ a : 𝓞 E, ‖ρ (a : E)‖ < 1 ↔ ‖ρ' (a : E)‖ < 1

theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) := by
  have hinj := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h1 : plGG D (b, t) = plGG D (b', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases b <;> cases b' <;> simp only [plGG, if_true, if_false, Bool.false_eq_true] at h1
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
    · exact absurd h1 (hP.2 _ _)
    · exact absurd h1.symm (hP.2 _ _)
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨(false, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])
    · refine ⟨(true, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])

def plEquiv (D : D7) : (Bool × HH D) ≃ D.what₂.Tau := Equiv.ofBijective _ (tauPl_bijective D)

end GlobalTheory.InertCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
namespace GlobalTheory.HkB

open Formalism.IndefR.Bridge

theorem isDC_of_mem_doubleCoset {G : Type} [Group G] {J : Subgroup G} {x x' : G} {A : Finset G}
    (hA : IsDC J x' A) (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) : IsDC J x A := by
  obtain ⟨k₁, k₂, rfl⟩ := hx
  constructor
  · intro a ha
    obtain ⟨u, v, rfl⟩ := hA.1 a ha
    exact ⟨u * k₁, k₂ * v, by simp [mul_assoc]⟩
  · rintro _ ⟨u, v, rfl⟩
    exact hA.2 _ ⟨u * k₁⁻¹, k₂⁻¹ * v, by simp [mul_assoc]⟩

theorem dcOp_eq_and_level {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J L : Subgroup G) (χ : J →* ℂˣ) (x x' : G) (A A' : Finset G) (F : G → W)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) (hAL : ∀ a ∈ A, a ∈ L) (hAL' : ∀ a ∈ A', a ∈ L)
    (hA : IsDC J x A) (hA' : IsDC J x' A') (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂)
    (hF : ∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) :
    dcOp A F = dcOp A' F ∧ (∀ (k : J) (h : G), (dcOp A F) (h * k) = (χ k : ℂ) • (dcOp A F) h) := by
  have hF' : F ∈ AdForms (1 : G →* G) (1 : G →* Module.End ℂ W) J χ := by
    intro γ h k
    simpa using hF k h
  refine ⟨dcOp_eq_of_isDC _ _ hχ hA (isDC_of_mem_doubleCoset hA' hx) hAL hAL' hF', fun k h => ?_⟩
  have h1 := LocSplit.dcOp_mem (1 : G →* G) (1 : G →* Module.End ℂ W) hs hχ hA hAL hF' 1 h k
  simpa using h1

end GlobalTheory.HkB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
open GlobalTheory.CuspRep

namespace GlobalTheory.KinfCompactness

theorem norm_entry_le_one {E : Type} [Field E] {a : ℕ} {M : Matrix (Fin a) (Fin a) (Cinf E)}
    (hM : star M * M = 1) (i j : Fin a) (w : NumberField.InfinitePlace E) : ‖M i j w‖ ≤ 1 := by
  have h := congrFun (congrFun (congrFun hM j) j) w
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Pi.one_apply, Complex.star_def, Complex.conj_mul'] at h
  have h2 : ∑ x, ‖M x j w‖ ^ 2 = 1 := by exact_mod_cast h
  have h3 : ‖M i j w‖ ^ 2 ≤ 1 :=
    h2 ▸ Finset.single_le_sum (f := fun x => ‖M x j w‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (M i j w)]

theorem isClosed_unitaryGroup (E : Type) [Field E] (a : ℕ) :
    IsClosed (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) := by
  have e : (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) =
      {M | star M * M = 1} := by
    ext M; exact Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const

theorem compactSpace_Kinf (E : Type) [Field E] (a : ℕ) : CompactSpace (Kinf E a) := by
  let B : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hsub : (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) ⊆ B := by
    intro M hM i _ j _ w _
    simpa [Metric.mem_closedBall, dist_zero_right] using
      norm_entry_le_one (Matrix.mem_unitaryGroup_iff'.1 hM) i j w
  exact isCompact_iff_compactSpace.1 (hB.of_isClosed_subset (isClosed_unitaryGroup E a) hsub)

end GlobalTheory.KinfCompactness
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfiniteStatement
open GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite : ∀ (E : Type) [Field E] (a : ℕ), CompactSpace (Kinf E a) := by
  first | exact @GlobalTheory.KinfCompactness.compactSpace_Kinf | exact GlobalTheory.KinfCompactness.compactSpace_Kinf | (intros; apply GlobalTheory.KinfCompactness.compactSpace_Kinf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRBasisOfLocBasis
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetEntries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries

def JetsIntegral {σ : Type} {l : ℕ} [Fact l.Prime] (F : MvPowerSeries σ ℂ_[l]) : Prop :=
  ∀ a : σ →₀ ℕ, ‖(a.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff a F‖ ≤ 1

def IsRBasis (D : D7) {l : ℕ} [Fact l.Prime] (ρ : D.host.E → ℂ_[l]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (g : Matrix (Fin N) (Fin N) ℂ_[l]) : Prop :=
  g.det ≠ 0 ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range fun a : Fin N => fun k => g k a) =
      Submodule.span 𝓞_ℂ_[l] ((fun (x : Fin N → D.host.E) k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))


end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace GlobalTheory.JetTieCompare

open GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries (IsRBasis)

variable {p : ℕ} [Fact p.Prime]

theorem mem_int_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl), Valuation.embedding_restrict]
  exact_mod_cast Iff.rfl

theorem norm_int_le {E : Type} [Field E] (ρ : E →+* ℂ_[p]) (x : 𝓞 E) : ‖ρ (x : E)‖ ≤ 1 := by
  have h : IsIntegral 𝓞_ℂ_[p] (ρ (x : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _) x.isIntegral_coe
  exact (mem_int_iff _).1 ((PadicComplexInt.integers p).mem_of_integral h)

theorem exists_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) (x : E) (hx : ‖ρ x‖ ≤ 1) :
    ∃ s n : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ (s : E) * x = n := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ‖ρ (y : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le ρ c) (norm_nonneg _) ha }
  have hI : ∀ y : 𝓞 E, y ∉ I ↔ ‖ρ (y : E)‖ = 1 := fun y =>
    ⟨fun h => le_antisymm (norm_int_le ρ y) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩
  have hp : I.IsPrime := by
    refine ⟨(Ideal.ne_top_iff_one _).2 ((hI 1).2 (by simp)), fun {a b} hab => ?_⟩
    by_contra hc
    rw [not_or, hI, hI] at hc
    exact (hI (a * b)).2 (by simp [hc.1, hc.2]) hab
  have hpI : ((p : ℕ) : 𝓞 E) ∈ I := by
    change ‖ρ (((p : ℕ) : 𝓞 E) : E)‖ < 1
    have : ρ (((p : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hne : I ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpI
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpI)
  obtain ⟨n, d, h | h⟩ := (⟨I, hp, hne⟩ : HeightOneSpectrum (𝓞 E)).exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · exact ⟨d, n, (hI _).1 d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, le_antisymm (norm_int_le ρ n) ?_, by rw [mul_comm]; exact h⟩
    have h1 : ‖ρ x‖ * ‖ρ (n : E)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← (hI _).1 d.2]
      exact congrArg (fun y => ‖ρ y‖) h
    nlinarith [norm_nonneg (ρ (n : E)), norm_nonneg (ρ x)]

theorem exists_common_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) {N : ℕ} (x : Fin N → E)
    (hx : ∀ a, ‖ρ (x a)‖ ≤ 1) : ∃ (s : 𝓞 E) (n : Fin N → 𝓞 E), ‖ρ (s : E)‖ = 1 ∧ ∀ a, (s : E) * x a = n a := by
  classical
  choose s n hs hn using fun a => exists_denom ρ (x a) (hx a)
  refine ⟨∏ a, s a, fun a => (∏ b ∈ Finset.univ.erase a, s b) * n a, ?_, fun a => ?_⟩
  · have : ((∏ a, s a : 𝓞 E) : E) = ∏ a, (s a : E) := map_prod (algebraMap (𝓞 E) E) _ _
    rw [this, map_prod, norm_prod]
    exact Finset.prod_eq_one fun a _ => hs a
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    change algebraMap (𝓞 E) E (_ * _) * _ = algebraMap (𝓞 E) E (_ * _)
    rw [map_mul, map_mul, mul_assoc]
    exact congrArg _ (hn a)

theorem exists_locBasis (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hfg : L.FG) (hsp : Submodule.span D.host.E (L : Set (Fin N → D.host.E)) = ⊤) :
    ∃ P, TaylorLogMetric.LocBasisW D ρ L P := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  let M : (Fin N → s) → Matrix (Fin N) (Fin N) D.host.E := fun f => Matrix.of fun k a => (f a).1 k
  obtain ⟨f₀, hf₀⟩ : ∃ f, (M f).det ≠ 0 := by
    obtain ⟨b, hbs, hb, hli⟩ := exists_linearIndependent D.host.E (s : Set (Fin N → D.host.E))
    let B : Module.Basis b D.host.E (Fin N → D.host.E) := Module.Basis.mk hli (by simp [hb, hsp])
    let e := B.indexEquiv (Pi.basisFun D.host.E (Fin N))
    refine ⟨fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩, ?_⟩
    have h := (Matrix.linearIndependent_cols_iff_isUnit (A := M fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩)).1
      (hli.comp _ e.symm.injective)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero
  haveI : Nonempty (Fin N → s) := ⟨f₀⟩
  obtain ⟨f, hf⟩ := Finite.exists_max fun f => ‖ρ (M f).det‖
  have hpos : 0 < ‖ρ (M f).det‖ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero ρ).2 hf₀)) (hf f₀)
  have hdet : (M f).det ≠ 0 := (map_ne_zero ρ).1 (norm_pos_iff.1 hpos)
  refine ⟨M f, hdet, fun a => ⟨1, by simp, ?_⟩, fun x hx => ?_⟩
  · rw [one_smul]
    exact Submodule.subset_span (f a).2
  · have key : ∃ c : Fin N → D.host.E, (∀ a, ‖ρ (c a)‖ ≤ 1) ∧ x = (M f).mulVec c := by
      induction hx using Submodule.span_induction with
      | mem y hy =>
        refine ⟨((M f).det)⁻¹ • (M f).cramer y, fun a => ?_, ?_⟩
        · have h1 : (M f).updateCol a y = M (Function.update f a ⟨y, hy⟩) := by
            ext k b
            by_cases hb : b = a
            · subst hb; simp [M]
            · simp [M, Matrix.updateCol_ne hb, Function.update_of_ne hb]
          rw [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, h1, map_mul, map_inv₀, norm_mul, norm_inv,
            inv_mul_le_iff₀ hpos, mul_one]
          exact hf _
        · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
      | zero => exact ⟨0, by simp, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨c, hc, rfl⟩ := hy
        obtain ⟨c', hc', rfl⟩ := hz
        refine ⟨c + c', fun a => ?_, by rw [Matrix.mulVec_add]⟩
        rw [Pi.add_apply, map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc a) (hc' a))
      | smul r y _ hy =>
        obtain ⟨c, hc, rfl⟩ := hy
        refine ⟨(r : D.host.E) • c, fun a => ?_, by rw [Matrix.mulVec_smul]; rfl⟩
        rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
        exact mul_le_one₀ (norm_int_le ρ r) (norm_nonneg _) (hc a)
    obtain ⟨c, hc, rfl⟩ := key
    obtain ⟨t, n, ht, hn⟩ := exists_common_denom ρ c hc
    refine ⟨t, ht, n, ?_⟩
    funext k
    rw [Finset.sum_apply]
    change (t : D.host.E) * (∑ a, M f k a * c a) = ∑ a, (n a : D.host.E) * M f k a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [← hn a]; ring

theorem exists_tauHom (D : D7) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ ρ : D.host.E →+* ℂ_[p], TaylorLogMetric.tauEmb D lam τ = ρ := by
  have h : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  refine ⟨lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar h), funext fun x => ?_⟩
  rw [TaylorLogMetric.tauEmb, TaylorLogMetric.lamC, dite_eq_left (h x)]
  rfl

end GlobalTheory.JetTieCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.LocFactor

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem glAf_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) :
    x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_)
  have := congrArg (fun m : GL (Fin a) (v.adicCompletion E) => (m.val : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (h v)
  exact this

theorem locGL_comm_away (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (h : GL (Fin a) (w.adicCompletion E)) :
    locGL E a w h * ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) =
      ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) * locGL E a w h := by
  refine glAf_ext fun v => ?_
  simp only [map_mul, map_inv]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL, pLoc_locGL, inv_mul_cancel, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, pLoc_locGL_of_ne hv, inv_one, one_mul, one_mul, mul_one]

theorem op_eq_locRep_comp (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a) :
    ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V),
      (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  cases o with
  | fin k =>
    set kw := GeneralLinearGroup.map (pLoc E w) k
    set k' := (locGL E a w kw)⁻¹ * k
    refine ⟨kw, π.op (.fin k'), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k') (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
        locGL_comm_away]
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k) φ.1 = rt E a (finGL E a (locGL E a w kw)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
  | cpt k =>
    refine ⟨1, π.op (.cpt k), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (infGL E a (Unitary.toUnits k)) (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (infGL E a (Unitary.toUnits k)) φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, infGL_comm]
    · rw [map_one]; rfl
  | lie X =>
    refine ⟨1, π.op (.lie X), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change lie E a X (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (lie E a X φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, lie_rt_fin]
    · rw [map_one]; rfl

theorem exists_locRep_comp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E))
    (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T :=
  fun _ _ _ _ _ π w o => op_eq_locRep_comp π w o

end GlobalTheory.LocFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperatorStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localTranslation_comp_commuting_operator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  first | exact @GlobalTheory.LocFactor.exists_locRep_comp | exact GlobalTheory.LocFactor.exists_locRep_comp | (intros; apply GlobalTheory.LocFactor.exists_locRep_comp <;> assumption)
end
end

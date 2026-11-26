module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published GlobalTheory.LFun

namespace GlobalTheory.SpehPair

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N a d : ℕ}

theorem isUnitary_of_isNormalised {π : CuspSub E a} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
  have hs : ∀ (b : ℕ) (t : ℝ), splitCentre E b t =
      Matrix.GeneralLinearGroup.scalar (Fin b) (infId E (expU fun _ => (t : ℂ))) := fun b t =>
    (cornerGL_scalar (sInf E) _)
  have h1 : ∀ t : ℝ, ((ω.1 (infId E (expU fun _ => (t : ℂ))) : ℂˣ) : ℂ) = 1 := fun t => by
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h0 (Subtype.ext (funext hc))
    have h2 := hω.apply hφ (infId E (expU fun _ => (t : ℂ))) g
    rw [← hs, h φ hφ] at h2
    exact mul_right_cancel₀ hg (h2.symm.trans (one_mul _).symm)
  have h3 : ((CuspSub.triv E (le_refl 1)).twist ω).HasCentral ω :=
    CuspSub.hasCentral_iff.2 (CG.hasCentChar_ofChar ω)
  have h4 : IsNormalised ((CuspSub.triv E (le_refl 1)).twist ω) := fun φ hφ t g => by
    rw [hs, h3.apply hφ, h1, one_mul]
  exact hω.isUnitary_iff.2 (h3.isUnitary_iff.1 (Model.isUnitary_of_isNormalised h4))

theorem eventually_spherical {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ, IsLocCompGL V w σ →
      GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := N)) := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  filter_upwards [LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨f, hf0, hfV, hf⟩ := hσ
  let F : σ.V →ₗ[ℂ] V := f.codRestrict V hfV
  have hF : ∀ g v, F (σ.ρ g v) = DiscLocEx.locRepD hV.stable w g (F v) := fun g v => Subtype.ext (hf g v)
  have hF0 : F ≠ 0 := fun e => hf0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v))
  have hi : LinearMap.ker F = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hF, hv, map_zero]) |>.resolve_right fun e => hF0 (LinearMap.ker_eq_top.1 e)
  have hfix : (⟨φ, hφ⟩ : V) ∈ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w (n := N)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
      obtain ⟨g, rfl⟩ := hk
      exact hw g)
  have h1 : LinearMap.range F ⊓ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w (n := N)) ≠ ⊥ := fun e =>
    hF0 (LinearMap.range_eq_bot.1 (DiscLocEx.eq_bot_of_fixedD hV w GlobalTheory.SatInd.isCompact_KGL
      (fun e => h0 (congrArg Subtype.val e)) hfix _ (by rintro g _ ⟨v, rfl⟩; exact ⟨_, hF g v⟩) e))
  obtain ⟨_, ⟨⟨v, rfl⟩, hv⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 h1
  exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => LinearMap.ker_eq_bot.1 hi (by
    rw [hF, GlobalTheory.LGrp.mem_fixed.1 hv k hk]), fun e => hv0 (by rw [e, map_zero])⟩

theorem exists_sat_twist (hd : 1 ≤ d) {π : CuspSub E a} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} {σ' : SmIrr (GL (Fin N) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ)
    {T : Multiset ℂˣ} (hT : HasSatGL w σ'.ρ T) (ν : ℝ → HChar E) (hν : ∀ s, (ν s).IsAbsPow s) :
    ∃ B : Fin d → Multiset ℂˣ, (∀ i, ((CG.mk π).twist (ν (-spehExp d i))).HasSat w (B i)) ∧ ∑ i, B i = T := by
  obtain ⟨S, hS, e⟩ := GlobalTheory.SatInd.exists_sat_of_isSpeh hd σ.smooth σ.irred h hT
  refine ⟨_, fun i => GlobalTheory.SphGal.hasSatGL_twist E a π _ w S ((hν _).1 w)
    (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hS), ?_⟩
  refine Multiset.map_injective Units.val_injective (Eq.trans ?_ e)
  refine (map_sum (Multiset.mapAddMonoidHom _) _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Units.val_mul, (hν _).2.1 w, spehExp]
  congr 2
  push_cast
  ring

end GlobalTheory.SpehPair

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

section Twist

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

theorem coe_scalar (u : kˣ) : ((GeneralLinearGroup.scalar (Fin a) u : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
    (u : k) • (1 : Matrix (Fin a) (Fin a) k) := by
  ext i j
  by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.one_apply, h]

def twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := GeneralLinearGroup.scalar (Fin a) (c g) * r g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul]
    have e : GeneralLinearGroup.scalar (Fin a) (c h) * r g = r g * GeneralLinearGroup.scalar (Fin a) (c h) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [mul_assoc]
    rw [← mul_assoc (GeneralLinearGroup.scalar (Fin a) (c h)), e, mul_assoc]

theorem coe_twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) (g : Γ) :
    (twistBy c r g : Matrix (Fin a) (Fin a) k) = (c g : k) • (r g : Matrix (Fin a) (Fin a) k) := by
  change ((GeneralLinearGroup.scalar (Fin a) (c g) * r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = _
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]

end Twist

section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem isPolarized_twist {π : CuspSub E a} (hc : π.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) :
    ∃ ψ, IsPolarized (π.twist ν) ψ := by
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.PolChar.exists_compNorm_eq hν
  refine ⟨_, IsConjDualBy.isPolarized (m := 0) (χ := ψ) ?_ ?_⟩
  · rw [h1]; exact GlobalTheory.T.isConjugateDualTwistBy_twist_of_conjSelfDual hc ν
  · simpa using h2

theorem expo_mul (χ χ' : HChar E) (τ : E →+* ℂ) : expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv (χ : HChar E) (τ : E →+* ℂ) : expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isSSRep_twistBy {Γ K : Type} [Group Γ] [Field K] {n : ℕ} (c : Γ →* Kˣ) {ρ : Γ →* GL (Fin n) K} (hs : IsSSRep ρ) :
    IsSSRep (twistBy c ρ) := by
  have key : ∀ W, IsInv (twistBy c ρ) W ↔ IsInv ρ W := fun W => forall_congr' fun g => forall₂_congr fun v _ => by
    rw [coe_twistBy, Matrix.smul_mulVec, W.smul_mem_iff (c g).ne_zero]
  exact fun W hW => (hs W ((key W).1 hW)).imp fun W' h' => ⟨(key W').2 h'.1, h'.2⟩

theorem conj_of_frob (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {r r' : G E Ω →* GL (Fin a) (Qbar l)} (hc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) (hs : IsSSRep r) (hs' : IsSSRep r')
    (h : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (B : ValuationSubring Ω) (g : G E Ω),
      IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
      (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  have htr : ∀ g, ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
    intro g
    refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 h))
      (hc.matrix_trace) (hc'.matrix_trace) ?_) g
    rintro σ ⟨w, hw, B, hB, hσ⟩
    have e := not_not.1 hw B σ hB hσ
    show Matrix.trace _ = Matrix.trace _
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.trace]
    · haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]
  exact GlobalTheory.TraceConj.conj_of_trace_eq _ _ a r r' hs hs' htr

theorem potCrys_twistBy {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ) (r : ↥Gw →* GL (Fin a) (Om l))
    (hr : IsPotCrysAt P Bw r) (hc : IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp c)) :
    IsPotCrysAt P Bw (twistBy c r) := by
  obtain ⟨L₁, r₁, m₁, hp₁⟩ := hr
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  obtain ⟨K', hK, hcr⟩ := (local_ext P Bw l₁ r₁).2.2.1.2 hp₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    rw [MonoidHom.comp_apply, coe_scalar]
    simp
  have hM : IsModel Bw (twistBy c r) L (twistBy d r₁') := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        (r g : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((twistBy d r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((twistBy c r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [coe_twistBy, coe_twistBy, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, e]
    exact congrArg₂ (· * ·) (hcd g) rfl
  refine ⟨L, _, hM, K', hK, ?_⟩
  let θ : ↥(GK K') →* (↥L.1)ˣ := (d.comp Bw.e.symm.toMonoidHom).comp (Subgroup.inclusion (GK_le hK))
  have repE_apply : ∀ {m} (r' : ↥Gw →* GL (Fin m) ↥L.1) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥L.1),
      Bw.repE L r' g x = ((r' (Bw.e.symm g) : GL (Fin m) ↥L.1) : Matrix (Fin m) (Fin m) ↥L.1).mulVec x :=
    fun _ _ _ => by simp [LocBridge.repE, Matrix.toLinAlgEquiv'_apply]
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T K' L _ _ θ (fun g x => ?_) ?_).1 hcr
  · change Bw.repE L (twistBy d r₁') _ x = _ • Bw.repE L r₁' _ x
    rw [repE_apply, repE_apply, coe_twistBy, Matrix.smul_mulVec]
    rfl
  · have h1 := GlobalTheory.Per.TiedRestrict.isCrys_restrict hK (Bw.repE L c₂') T hq
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K') (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) h1
    change (Bw.repE L c₂' _ x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm (Subgroup.inclusion (GK_le hK) g)))

end G

theorem exists_halfChar (D : D7) : haveI := host_isCMField D.host; ∃ ξ : HChar D.host.E, (∀ v, ξ.UnrAt v) ∧
    (CG.ofChar ξ).IsCsd ∧ (CG.ofChar ξ⁻¹).IsCsd ∧ ∀ τ, ∃ n : ℤ, expo ξ τ = n + 1 / 2 := by
  have := host_isCMField D.host
  obtain ⟨ξ₀, h⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host
  let ξ : HChar D.host.E := ξ₀
  have hneg : (-1 : ℂˣ)⁻¹ = -1 := inv_eq_of_mul_eq_one_left (by simp)
  refine ⟨ξ, h.unr, isCsd_ofChar_of_res _ _ (Or.inr h.res), isCsd_ofChar_of_res _ _ (Or.inr ⟨fun v k => ?_, fun w k => ?_⟩), fun τ => ?_⟩
  · have e1 : (ξ.resFin v) k = etaFin (↥D.host.F) v k := h.res.1 v k
    have e2 : (ξ⁻¹.resFin v) k = ((ξ.resFin v) k)⁻¹ := by
      simp only [HChar.resFin, MonoidHom.finsetProd_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaFin
    split_ifs
    · rw [← inv_zpow, hneg]
    · exact inv_one
  · have e1 : (ξ.resInf w) k = etaInf (↥D.host.F) w k := h.res.2 w k
    have e2 : (ξ⁻¹.resInf w) k = ((ξ.resInf w) k)⁻¹ := by
      simp only [HChar.resInf, MonoidHom.finsetProd_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaInf
    split_ifs
    · exact hneg
    · exact inv_one
  · have hI : Function.Injective fun i => InfinitePlace.mk (embPsi D.host i) := fun i j e => by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact GlobalTheory.HalfIntChars.embPsi_inj D.host e
      · exact (GlobalTheory.HalfIntChars.embPsi_ne_conj D.host j i (e.symm.trans (RingHom.ext fun x => rfl))).elim
    obtain ⟨ρ, b, rfl⟩ := GlobalTheory.JumpDictionaryFoundation.exists_embOver D τ
    have h3 := (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ξ).2.2 _ _ _ hI h.inf (D.eTau ρ)
    cases b
    · exact ⟨0, by rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ false = embPsi D.host (D.eTau ρ) from rfl, h3.1]; simp⟩
    · refine ⟨-1, ?_⟩
      rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ true = ComplexEmbedding.conjugate (embPsi D.host (D.eTau ρ)) from
        RingHom.ext (GlobalTheory.JumpDictionaryFoundation.embOver_true_apply D ρ), h3.2]
      norm_num

end GlobalTheory.TripleLocal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
  GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.DiscClosure

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}


variable (E N) in
def autSub : Submodule ℂ (Sm E N) where
  carrier := {φ | IsAutForm φ}
  zero_mem' := isAutForm_const (Submodule.zero_mem _)
  add_mem' := fun {φ ψ} h h' => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add 1 h h'
  smul_mem' := fun c φ h => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add c h (isAutForm_const (Submodule.zero_mem _))


variable (μ : Measure (GA E N)) in
def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E N) where
  carrier := {φ | MemL2Quotient (latticeGL E N) μ φ.1}
  zero_mem' := ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ hγ g => by
    change φ.1 (γ * g) + ψ.1 (γ * g) = φ.1 g + ψ.1 g
    rw [h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩
  smul_mem' := fun c φ h => ⟨fun γ hγ g => by
    change c * φ.1 (γ * g) = c * φ.1 g
    rw [h.1 γ hγ g], h.2.const_smul c⟩

def stabSub (φ : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k φ = φ}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) φ = φ
    have ha' : finRep E N a φ = φ := ha
    have hb' : finRep E N b φ = φ := hb
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change finRep E N 1 φ = φ
    rw [map_one]; rfl
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ φ = φ
    have ha' : finRep E N a φ = φ := ha
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

end GlobalTheory.DiscClosure

namespace GlobalTheory.DiscClosure

open GlobalTheory.PRep GlobalTheory.CuspRep.LocEx GlobalTheory.DiscLocEx

end GlobalTheory.DiscClosure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AVGood

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL (k := k)} (h : Toral x) : Good x := by
  obtain ⟨s, hs, h1⟩ := h
  exact ⟨s, hs, fun y hy => Or.inl (h1 y hy)⟩

theorem fixed_ne_bot_of_mem_support {x : IrrGL (k := k)} (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥)
    {s : Multiset (IrrGL (k := k))} (hs : HasSupport x.rep s) {y : IrrGL (k := k)} (hy : y ∈ s) :
    fixed y.rep (KOne k (Fin y.1)) ≠ ⊥ := by
  obtain ⟨h, z, rfl, -, -, e, he⟩ := hs
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hx
  obtain ⟨w, hw, hw0⟩ := DepthZero.fixed_of_isSubquotient e (fun a => (z a).rep) he ⟨v, hv, hv0⟩ a
  exact (Submodule.ne_bot_iff _).2 ⟨w, hw, hw0⟩

theorem good_of_fixed_KOne (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hk : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) (x : IrrGL (k := k))
    (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥) : Good x := by
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ x
  exact ⟨s, hs, fun y hy => Or.inr ⟨hk, y, 1, isSmoothChar_one, fixed_ne_bot_of_mem_support hx hs hy,
    (IrrGL.tw_one y _).symm⟩⟩

theorem good_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (x : IrrGL (k := k)) (hx : IsSpherical x.rep) :
    Good x :=
  (GlobalTheory.SphSupport.toral_and_good_of_isSpherical hBZ k x hx).2

end Local

def TameAtG (D : D7) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ (i : D.nd.Loc) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.w = D.naut.plGw k v →
    NG.IsCompAt (tup (D.nd.mu i) j) s ξ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1

end GlobalTheory.AVGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise Formalism.UG

namespace GlobalTheory.DefiniteDense

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infPt (y : UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) : UA E n :=
  ⟨infGL E n y.1, infGL_mem_UA y.1 (by
    have h : cT (starRingEnd (Cinf E)) (y.1 : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * y.1 = 1 := y.2
    rw [mul_one] at h
    exact h)⟩

theorem continuous_infPt : Continuous (infPt (E := E) (n := n)) :=
  (GlobalTheory.DefU.continuous_infGL.comp continuous_subtype_val).subtype_mk _

theorem mem_closure_rat_fin (x : UA E n) (hx : x ∈ infU E n) :
    x ∈ closure ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
  have hne : ∃ z, (IsCMField.complexConj E : E →+* E) z ≠ z := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hd := GlobalTheory.RealApprox.dense_unitary (GlobalTheory.CuspRep.InfType.diagInf E) (IsCMField.complexConj E : E →+* E)
    (starRingEnd (Cinf E)) (fun z => (pInf_complexConj z).symm) (fun z => IsCMField.complexConj_apply_apply E z) hne
    (fun z => star_star z) continuous_star GlobalTheory.CuspRep.InfType.denseRange_diagInf Units.isOpen
    (fun z hz => by obtain ⟨u, rfl⟩ := hz; exact NormedRing.inverse_continuousAt u)
    (1 : Matrix (Fin n) (Fin n) E)
    (by rw [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]) (by simp)
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at hd
  have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) := fun a => (infEq E).symm_apply_apply _
  have hM : GeneralLinearGroup.map (pInf E) x.1 ∈ UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
    have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
    rw [mul_one] at h0
    have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
        (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
      ext i j
      simp [Formalism.UG.cT, hp]
    change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
      (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
    rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hxe : infPt ⟨_, hM⟩ = x := by
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans hx.symm
  rw [← hxe]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPt ⟨_, hd ⟨_, hM⟩, rfl⟩)
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.1 hh
  have hγ0 : cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * γ = 1 := hγ
  rw [mul_one] at hγ0
  have hr : ratGL E n γ ∈ UA E n := by
    have e : cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
        (cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
      ext i j
      simp [Formalism.UG.cT, conjAd_algebraMap]
    change cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) * 1 *
      (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1
    rw [e, mul_one, ← Matrix.map_mul, hγ0, Matrix.map_one _ (map_zero _) (map_one _)]
  let r : UA E n := ⟨ratGL E n γ, hr⟩
  have hrU : r ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩
  have hk : r⁻¹ * infPt h ∈ finU (E := E) (n := n) := by
    have e1 : GeneralLinearGroup.map (pInf E) (ratGL E n γ) = h.1 := by
      rw [← hγh]
      exact Units.ext rfl
    change GeneralLinearGroup.map (pInf E) ((ratGL E n γ)⁻¹ * infGL E n h.1) = 1
    rw [map_mul, map_inv, e1, pInf_infGL, inv_mul_cancel]
  exact ⟨r, hrU, r⁻¹ * infPt h, hk, mul_inv_cancel_left r _⟩

theorem eq_zero_of_finU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (φ : UA L n → ℂ),
    IsAutFormU φ → (∀ y ∈ finU (E := L) (n := n), φ y = 0) → φ = 0 := by
  intro L _ _ _ n φ hφ h0
  have hS : ((ratU L n : Set (UA L n)) * (finU (E := L) (n := n) : Set (UA L n))) ⊆ {g | φ g = 0} := by
    rintro _ ⟨γ, hγ, k, hk, rfl⟩
    change φ (γ * k) = 0
    rw [hφ.left γ hγ k]
    exact h0 k hk
  have hZ : IsClosed {g : UA L n | φ g = 0} := isClosed_eq hφ.cont continuous_const
  funext g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU L n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA L n → UA L n) := continuous_mul_const k
  have hxk : x * k ∈ closure ((ratU L n : Set (UA L n)) * (finU (E := L) (n := n) : Set (UA L n))) := by
    refine closure_mono ?_ (image_closure_subset_closure_image hc ⟨x, mem_closure_rat_fin x hx, rfl⟩)
    rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
    exact ⟨γ, hγ, k' * k, (finU (E := L) (n := n)).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩
  exact hZ.closure_subset_iff.2 hS hxk

end GlobalTheory.DefiniteDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryAutForm_eq_zero_of_finitePoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (φ : UA L n → ℂ), IsAutFormU φ → (∀ y ∈ finU (E := L) (n := n), φ y = 0) → φ = 0 := by
  first | exact @GlobalTheory.DefiniteDense.eq_zero_of_finU | exact GlobalTheory.DefiniteDense.eq_zero_of_finU | (intros; apply GlobalTheory.DefiniteDense.eq_zero_of_finU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqBotOrEqTopOfInvariant
namespace GlobalTheory.InvariantSupremum

theorem eq_bot_or_eq_top_of_invariant {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (P : Submodule ℂ W)
    (hP : ∀ g : G, ∀ w ∈ P, σ g w ∈ P) : P = ⊥ ∨ P = ⊤ := by
  let Q : Subrepresentation σ :=
    { toSubmodule := P
      apply_mem_toSubmodule := by
        intro g v hv
        exact hP g v hv }
  rcases @IsSimpleOrder.eq_bot_or_eq_top _ _ _ hσ Q with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem fixed_mem_of_mem_iSup_range {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ι : Type} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (f : ι → W →ₗ[ℂ] V)
    (hf : ∀ (i : ι) (g : G) (u : W), f i (σ g u) = ρ g (f i u)) (K : Set G)
    (Z : Submodule ℂ V) (hZ : ∀ (i : ι) (v : W), (∀ k ∈ K, σ k v = v) → f i v ∈ Z)
    (_hfix : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V) (hφ : ∀ k ∈ K, ρ k φ = φ)
    (hmem : φ ∈ ⨆ i : ι, LinearMap.range (f i)) : φ ∈ Z := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  clear hmem

  have inv : ∀ (t : Finset ι) (g : G), ∀ z ∈ ⨆ i ∈ t, LinearMap.range (f i),
      ρ g z ∈ ⨆ i ∈ t, LinearMap.range (f i) := by
    intro t g z hz
    have hle : (⨆ i ∈ t, LinearMap.range (f i)) ≤
        (⨆ i ∈ t, LinearMap.range (f i)).comap (ρ g) := by
      refine iSup₂_le fun i hi => ?_
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_comap, ← hf i g w]
      exact (le_iSup₂ (f := fun i (_ : i ∈ t) => LinearMap.range (f i)) i hi)
        (LinearMap.mem_range_self _ _)
    exact hle hz
  induction s using Finset.induction_on generalizing φ with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hs
    rw [hs]
    exact Z.zero_mem
  | @insert j s hj ih =>
    rw [Finset.iSup_insert, Submodule.mem_sup] at hs
    obtain ⟨y, ⟨u, rfl⟩, z, hz, rfl⟩ := hs

    rcases eq_bot_or_eq_top_of_invariant σ hσ ((⨆ i ∈ s, LinearMap.range (f i)).comap (f j)) (by
        intro g w hw
        rw [Submodule.mem_comap] at hw ⊢
        rw [hf]
        exact inv s g _ hw) with hN | hN
    ·
      have hu : ∀ k ∈ K, σ k u = u := by
        intro k hk
        have e : ρ k (f j u) - f j u = z - ρ k z := by
          rw [sub_eq_sub_iff_add_eq_add, ← map_add (f := _), hφ k hk, add_comm]
        have h1 : σ k u - u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [Submodule.mem_comap, map_sub, hf, e]
          exact Submodule.sub_mem _ hz (inv s k z hz)
        rw [hN, Submodule.mem_bot, sub_eq_zero] at h1
        exact h1
      have hzfix : ∀ k ∈ K, ρ k z = z := by
        intro k hk
        have h2 := hφ k hk
        rw [map_add (f := _), ← hf, hu k hk] at h2
        exact add_left_cancel h2
      exact Z.add_mem (hZ j u hu) (ih z hzfix hz)
    ·
      have hu : f j u ∈ ⨆ i ∈ s, LinearMap.range (f i) := by
        have h3 : u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [hN]
          trivial
        exact h3
      exact ih _ hφ (Submodule.add_mem _ hu hz)

end GlobalTheory.InvariantSupremum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertHeckeEigen

open Formalism.UG GlobalTheory.PRep

section Abstract

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def quotMap (p : G →* H) (K : Subgroup H) : G ⧸ K.comap p → H ⧸ K :=
  Quotient.map' p fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact hab

theorem quotMap_mk (p : G →* H) (K : Subgroup H) (a : G) :
    quotMap p K (a : G ⧸ K.comap p) = (p a : H ⧸ K) := rfl

theorem quotMap_bijective (p : G →* H) (hp : Function.Surjective p) (K : Subgroup H) :
    Function.Bijective (quotMap p K) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [quotMap_mk, quotMap_mk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  · intro d
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨a, rfl⟩ := hp y
    exact ⟨a, rfl⟩

theorem heckeVec_comp_surj (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (ρ : Representation ℂ H V) {v : V} (hv : v ∈ fixed ρ K) :
    GlobalTheory.LFun.heckeVec (ρ.comp p) (K.comap p) (fun x => h (p x)) v = GlobalTheory.LFun.heckeVec ρ K h v := by
  let e := Equiv.ofBijective _ (quotMap_bijective p hp K)
  rw [GlobalTheory.LFun.heckeVec_eq_of_section hh hv (fun d => p (e.symm d).out) fun d => ?_]
  · rw [← finsum_comp_equiv e (f := fun d => h (p (e.symm d).out) • ρ (p (e.symm d).out) v)]
    simp only [Equiv.symm_apply_apply]
    rfl
  · rw [← quotMap_mk, QuotientGroup.out_eq']
    exact e.apply_symm_apply d

theorem finite_support_comp (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (hf : {d : H ⧸ K | h d.out ≠ 0}.Finite) :
    {c : G ⧸ K.comap p | h (p c.out) ≠ 0}.Finite := by
  refine (hf.preimage (quotMap_bijective p hp K).1.injOn).subset fun c hc => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hc ⊢
  have hk : (quotMap p K c).out⁻¹ * p c.out ∈ K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← quotMap_mk, QuotientGroup.out_eq']
  have e1 := hh 1 ⟨_, hk⟩ (quotMap p K c).out
  simp only [OneMemClass.coe_one, one_mul, mul_inv_cancel_left] at e1
  rwa [e1] at hc

theorem heckeVec_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (S : Finset (G ⧸ K))
    (hS : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ S) (x : V) :
    GlobalTheory.LFun.heckeVec ρ K h x = ∑ c ∈ S, h c.out • ρ c.out x := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => hS c fun h0 => hc ?_
  simp [h0]

theorem mem_of_mem_iSup {ι : Type} (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hσ : σ.IsIrreducible)
    (f : ι → W →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (Z : Submodule ℂ V)
    (hZ : ∀ i v, (∀ k ∈ K, σ k v = v) → f i v ∈ Z) (hZK : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V)
    (hK : ∀ k ∈ K, ρ k φ = φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : φ ∈ Z := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7; revert G V W h_3 h_4 h_5 h_6 h_7 ι ρ σ hσ f hf K Z hZ hZK φ hK hφ; exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range)
  | exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | (apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range ..)

end Abstract

end GlobalTheory.InertHeckeEigen


open GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in
theorem GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), Formalism.UG.IsUnramInv ϖ s q → ∀ p : locU n w →* Formalism.UG.GU s n, Function.Surjective p → ∀ σ : SmIrr (Formalism.UG.GU s n), IsCompAlong U (locU n w) p σ.ρ → ∀ α0 : Fin (n / 2) → ℂˣ, GlobalTheory.LFun.HasSatU ϖ q σ.ρ α0 → ∀ φ ∈ U, (∀ x : locU n w, p x ∈ Formalism.UG.KU s n → RU L n x.val φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU s n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU s n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU ϖ q h (fun i => (α0 i : ℂ)) • φ := by
  intro L _ _ _ n U hU w s ϖ q hq p hp σ hcomp α0 hsat φ hφ hfix h hh
  have hfin : {c : locU n w ⧸ (KU s n).comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hq n) hh.2)
  have hS : ∀ c : locU n w ⧸ (KU s n).comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let lam := SatU ϖ q h (fun i => (α0 i : ℂ))
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ (KU s n).comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl

  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.ρ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype (σ.ρ.comp p) (σ.ρ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) → σ.V →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.ρ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this

  have hZ : ∀ i v, (∀ k ∈ ((KU s n).comap p : Set (locU n w)), (σ.ρ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ.ρ (KU s n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ.ρ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [((hsat.2 v hvK hv0).2.2 h hh)] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.ρ.comp p) c.out v) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ ((KU s n).comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.ρ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_parameters_unramified_unitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), Formalism.UG.IsUnramInv ϖ s q → ∀ p : locU n w →* Formalism.UG.GU s n, Function.Surjective p → ∀ σ : SmIrr (Formalism.UG.GU s n), IsCompAlong U (locU n w) p σ.ρ → ∀ α0 : Fin (n / 2) → ℂˣ, GlobalTheory.LFun.HasSatU ϖ q σ.ρ α0 → ∀ φ ∈ U, (∀ x : locU n w, p x ∈ Formalism.UG.KU s n → RU L n x.val φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU s n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU s n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU ϖ q h (fun i => (α0 i : ℂ)) • φ := by
  first | exact @GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed | exact GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed | (intros; apply GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUn
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSatakeGiven

theorem continuous_of_valuation_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

theorem exists_hasSatAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  intro L _ _ _ n U hU w hun hns s ϖ q hs hI hph
  have hsph : (GlobalTheory.DefU.AU.mk ⟨U, hU⟩).Sph w := (GlobalTheory.DefU.AU.sph_mk _ w).2 hph
  obtain ⟨α0, hα⟩ := (GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert L n _ w hun hns).1 hsph
  rw [GlobalTheory.DefU.AU.isSat_mk] at hα
  obtain ⟨s', ϖ', q', hs', hI', hsat⟩ := hα
  have hss : s' = s := by
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap L w).equalizer (continuous_of_valuation_eq s' hI'.2.1)
      (continuous_of_valuation_eq s hI.2.1) (funext fun k => ?_)
    simp only [Function.comp_apply, hs', hs]
  subst hss
  have hqq : q' = q := Nat.pow_left_injective (n := 2) (by norm_num) (hI'.2.2.2.2.2.2.symm.trans hI.2.2.2.2.2.2)
  subst hqq
  obtain ⟨b, hb, hbJ, p, hp, σ, hc, hS⟩ := hsat
  exact ⟨α0, b, hb, hbJ, p, hp, σ, hc, hS.1, fun x hx h0 => (hS.2 x hx h0).of_unif hI' hI⟩

end GlobalTheory.InertSatakeGiven

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUnStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  first | exact @GlobalTheory.InertSatakeGiven.exists_hasSatAt | exact GlobalTheory.InertSatakeGiven.exists_hasSatAt | (intros; apply GlobalTheory.InertSatakeGiven.exists_hasSatAt <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DetSubMemOfConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedSpaceLeSupEigenspaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedAtSplit

open Filter Topology IsDedekindDomain

theorem exists_ne_zero_norm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_, ?_⟩
  · intro h0
    have := v.valuedAdicCompletion_eq_valuation' π
    rw [h0, map_zero, hπ] at this
    exact WithZero.coe_ne_zero this.symm
  · rw [Valued.toNormedField.norm_lt_one_iff, v.valuedAdicCompletion_eq_valuation', hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem valued_lt_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) < 1) : Valued.v z < 1 := by
  rw [← Valued.toNormedField.norm_lt_one_iff] at hz ⊢
  have h1 : ∀ y : v.adicCompletion F, ‖y‖ < 1 → ‖c y‖ < 1 := fun y hy => by
    have h2 := (hc.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.2 hy)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ?_
    simpa [Function.comp_def, map_pow] using h2
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ne_zero_norm_lt_one v
  by_contra h
  push_neg at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    norm_num at h
  have hcz0 : 0 < ‖c z‖ := norm_pos_iff.2 ((map_ne_zero c).2 hz0)
  have hcϖ : 0 < ‖c ϖ‖ := norm_pos_iff.2 ((map_ne_zero c).2 hϖ0)
  have key : ∀ N : ℕ, ‖c ϖ‖ < ‖c z‖ ^ N := by
    intro N
    have hzN : 1 ≤ ‖z‖ ^ N := one_le_pow₀ h
    have hq : ‖ϖ / z ^ N‖ < 1 := by
      rw [norm_div, norm_pow, div_lt_one (by positivity)]
      exact lt_of_lt_of_le hϖ1 hzN
    have := h1 _ hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (by positivity)] at this
    exact this
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (c z)) hz
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hcϖ)).exists
  exact lt_asymm hN (key N)

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

open IsDedekindDomain ValuativeRel

theorem mem_KOne_iff' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (κ : GL (Fin n) (w.adicCompletion E)) :
    κ ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n) ↔
      ∀ a b, Valued.v (((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) a b) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [GlobalTheory.StepData.mem_KOne]
  exact forall_congr' fun a => forall_congr' fun b => he.lt_one_iff_lt_one

theorem mem_KOne_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (A : GL (Fin n) (v.adicCompletion F))
    (h : Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) :
    A ∈ GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n) := by
  refine (mem_KOne_iff' A).2 fun a b => valued_lt_one_of_map c hc _ ?_
  have := (mem_KOne_iff' _).1 h a b
  convert this using 2
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.GeneralLinearGroup.map_apply]
  split_ifs <;> simp

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

theorem fixed_ne_bot_of_fixed_vector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → s.loc n κ ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ hloc f hf hf0 hfix
  classical
  obtain ⟨c, _, hc, hci, _⟩ := id hloc
  have hspan := GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent L n π s τ hloc c hc hci hf
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun {x y} hx hy v hv => by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
      one_mem' := fun v _ => by simp
      inv_mem' := fun {x} hx v hv => by
        have h1 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
        have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
        simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
        exact h2 }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map c.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h
    rw [e]
    ext i j
    simp
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr φ hφ
  let ρ' : Representation ℂ H (GAf L n → ℂ) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [iSup_subtype'] at hspan
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.1 hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    LinearMap.intertwiningMap_of_isIntertwiningMap σ' ρ' j.1.1 fun g v => j.1.2.2 g.1 g.2 v
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)).comap φ
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk =>
    hfix k.1 k.2 (mem_KOne_of_map c hc _ hk)
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hy0⟩
  obtain ⟨x, rfl⟩ := hφ h
  exact GlobalTheory.Parabolic.mem_fixed.1 hy x hh

end GlobalTheory.FixedAtSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Lift

def sgnGL (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : GL (Fin n) S := Units.map (Int.castRingHom _).toMonoidHom ε

theorem sgnGL_val (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : (sgnGL n S ε).1 = (ε : ℤ) • 1 := (zsmul_one _).symm

theorem sgnGL_comm {n : ℕ} {S : Type} [CommRing S] (ε : ℤˣ) (x : GL (Fin n) S) : x * sgnGL n S ε = sgnGL n S ε * x :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, sgnGL_val, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])

theorem bc_sgnGL {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) :
    Formalism.UG.bc f (sgnGL n S ε) = sgnGL n S' ε :=
  Units.ext (map_intCast (f.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) S') (ε : ℤ))

theorem map_sgn {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) (i j : Fin n) :
    (sgnGL n S' ε).1 i j = f ((sgnGL n S ε).1 i j) := by
  rw [← bc_sgnGL f]; rfl

theorem frGL_sgn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (ε : ℤˣ) : frGL β (sgnGL n _ ε) = sgnGL n _ ε := by
  have h : intGL F E n (sgnGL n _ ε) = sgnGL n _ ε := bc_sgnGL (Formalism.L2.Herm.intAf F E).subtype ε
  rw [frGL, MonoidHom.comp_apply, h, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sgnGL_comm, mul_inv_cancel_right]

theorem exists_matrix_sign {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P x = sgnGL n _ ε) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - (sgnGL n _ ε).1) = M • N :=
  GlobalTheory.LevelUnique.exists_matrix_hat hfr T hJ hx ⟨sgnGL n _ ε, rfl⟩
    (fun P hP => by rw [h P hP, redFn_frGL, bc_sgnGL]) hb hK
    (fun i j => by
      rw [frGL_sgn]
      exact map_sgn (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom ε i j)

theorem eq_sgn_of_submatrix {n r : ℕ} (hr : n = r) (h : r ≤ n) {S : Type} [CommRing S] {x : GL (Fin n) S} {ε : ℤˣ}
    (e : x.1.submatrix (Fin.castLE h) (Fin.castLE h) = (sgnGL r S ε).1) : x = sgnGL n S ε := by
  subst hr
  exact Units.ext e

theorem sign_calc {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {x z w₂ w₃ : Fin n → R} {M : ℕ} {ε : ℤˣ}
    (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - (sgnGL n R ε).1 *ᵥ z = M • w₃) : x - (ε : ℤ) • z = M • (w₂ + w₃) := by
  rw [smul_add, ← e₂, ← e₃, sub_add_sub_cancel, sgnGL_val, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {D : D7}

theorem finVec_sub_zsmul (V : HSp D) (x y : Fin V.rank → D.host.E) (e : ℤ) :
    finVec V (x - e • y) = finVec V x - e • finVec V y := by
  funext j
  exact (map_sub (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) (x j) (e • y j)).trans
    (congrArg (fun t => finVec V x j - t) (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) e (y j)))

theorem hatV_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) : GlobalTheory.Ker.hatV Λ = Formalism.L2.Pj.latHat V := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  rw [hl]; rfl

theorem mulVec_mem {V : HSp D} {k : GA D V} (hk : GlobalTheory.Member.FinCong V 1 k) :
    ∀ z ∈ Formalism.L2.Pj.latHat V, (finHom V k).1 *ᵥ z ∈ Formalism.L2.Pj.latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [one_nsmul] at e
  rw [sub_eq_iff_eq_add.1 e]
  exact add_mem hy hz

theorem isMov_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {k : GA D V} (hk : Lev.finE V k ∈ St β) : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) Λ Λ := by
  have hk' : Lev.finE V k⁻¹ ∈ St β := by rw [map_inv]; exact inv_mem hk
  have h1 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk)
  have h2 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk')
  intro u
  rw [hatV_eq hβ]
  change _ ↔ ∃ u₀ ∈ _, u = (finHom V k).1 *ᵥ u₀
  constructor
  · intro hu
    exact ⟨_, h2 u hu, by rw [← GlobalTheory.Member.LatMove.fin_mul, mul_inv_cancel, GlobalTheory.Member.LatMove.fin_one]⟩
  · rintro ⟨u₀, h0, rfl⟩
    exact h1 u₀ h0

theorem cong_on_half {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w) :
    ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      K *ᵥ finVec V (ι a) - K' *ᵥ finVec V (ι a) = M • w := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  intro a ha
  refine Submodule.smul_induction_on ha (fun b hb a _ => ?_) ?_
  · obtain ⟨w, hw, e⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
    have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
      rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
    exact ⟨w, hw, by rw [e₀, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, e]⟩
  · rintro x y ⟨w, hw, e⟩ ⟨w', hw', e'⟩
    have e₀ : finVec V (ι (x + y)) = finVec V (ι x) + finVec V (ι y) := by
      rw [map_add (f := _)]; funext i; exact TensorProduct.tmul_add _ _ _
    refine ⟨w + w', add_mem hw hw', ?_⟩
    rw [e₀, Matrix.mulVec_add, Matrix.mulVec_add, smul_add, ← e, ← e']
    abel

theorem mark_calc {R : Type} [CommRing R] {n : ℕ} {Hm K K' : Matrix (Fin n) (Fin n) R} {m x z w₁ w₂ w₃ : Fin n → R} {M : ℕ}
    (e₁ : m - Hm *ᵥ x = M • w₁) (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - K' *ᵥ z = M • w₃) :
    m - Hm *ᵥ (K' *ᵥ z) = M • (w₁ + Hm *ᵥ (w₂ + w₃)) := by
  rw [smul_add, ← Matrix.mulVec_smul, smul_add, ← e₁, ← e₂, ← e₃, sub_add_sub_cancel, Matrix.mulVec_sub, sub_add_sub_cancel]

theorem exists_cong_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = sgnGL _ _ ε) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z -
        (sgnGL V.rank (Af D.host.F ⊗[D.host.F] D.host.E) ε).1 *ᵥ z) = M • w := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := (hatV_eq hβ).symm
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_sign hfr T hJ hk ε h hb (K := (finHom V k).1) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k) (ε : ℤˣ) (hg : ∀ P, g P = sgnGL _ _ ε) :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = sgnGL _ _ ε := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = g ⟨P, hP⟩ := congrFun hk.2.2 ⟨P, hP⟩
  have e' := congrArg Units.val (e.trans (hg ⟨P, hP⟩))
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP))] at e'
  exact eq_sgn_of_submatrix hr L.hr e'

theorem exists_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a : La}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1) (e : finVec V (ι a) = M • w) :
    ∃ b, a = M • b := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm a⟩ (h5 ▸ hw) e
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  refine ⟨c, hι.1 ?_⟩
  rw [map_nsmul]
  exact congrArg Subtype.val ev

theorem sign_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a a' : La} {e : ℤ}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1)
    (h : finVec V (ι a') - e • finVec V (ι a) = M • w) : ∃ b, a' = e • a + M • b := by
  obtain ⟨b, hb⟩ := exists_div (a := a' - e • a) hι hM hw (by rw [map_sub, map_zsmul, finVec_sub_zsmul, h])
  exact ⟨b, by rw [← hb, add_sub_cancel]⟩

theorem mu_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) {k : GA D W}
    {x : (AE D)ˣ} (hx : IsDetRoot W k x) : castDict hV mu k = ((χ x : Circle) : ℂ) := by
  subst hV
  exact h.2 k x hx

theorem mem_iff_prod_le {E : Type} [Field E] [NumberField E] (T : Finset (Pl E)) (P : Pl E) :
    P ∈ T ↔ ∏ Q ∈ T, Q.asIdeal ≤ P.asIdeal := by
  rw [P.isPrime.prod_le]
  refine ⟨fun h => ⟨P, h, le_rfl⟩, ?_⟩
  rintro ⟨Q, hQ, h⟩
  rwa [← HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)]

end GlobalTheory.OneMapRef.Lift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelSubgroupBoundedOpenHyperspecial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelSubgroupBoundedOpenHyperspecial
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.OpenLev
open Classical
variable {D : D7} {n : ℕ}

theorem cong_entry {N : ℕ} {κ : Formalism.AUTREP.GAf D.host.E n} (hκ : NG.Cong D.host.E n N κ) (i j : Fin n) :
    ∃ w ∈ GlobalTheory.StdFrameExist.SI D, (km D n κ).val i j - (1 : Matrix (Fin n) (Fin n) (EAf D)) i j = (N : EAf D) * w := by
  obtain ⟨w, hw, e⟩ := hκ.2 i j
  refine ⟨w, (GlobalTheory.StdFrameExist.mem_ALint_iff w).1 hw, ?_⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) (EAf D)) i j = (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h2 : (N : EAf D) = (N : ReciprocityTheory.Aut.AL D.host.E) := by
    induction N with
    | zero => simp
    | succ k ih => simp
  rw [h1, h2]
  exact e

set_option maxHeartbeats 2000000 in
theorem redFn_eq_one_of_cong {N : ℕ} {PP : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    {κ : Formalism.AUTREP.GAf D.host.E n} (hκ : NG.Cong D.host.E n N κ) :
    redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
  obtain ⟨y, hy⟩ := ((GlobalTheory.T.stdMaximalCompact_reduction_properties D n).2.1 κ).2 hκ.1
  rw [← hy, redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : ((y.val i j : Herm.intAf D.host.F D.host.E) : EAf D) = (km D n κ).val i j := by
    rw [← hy]
    simp [frGL, intGL, Formalism.UG.bc]
  obtain ⟨w, hw', e⟩ := cong_entry hκ i j
  have h1 : (((1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j : Herm.intAf D.host.F D.host.E) : EAf D) =
      (1 : Matrix (Fin n) (Fin n) (EAf D)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have key : y.val i j - (1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j =
      (N : Herm.intAf D.host.F D.host.E) * ⟨w, hw'⟩ := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [hyij, h1]
    exact e
  have hN' : (N : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hN
    simpa using this
  have k2 := congrArg (resS D.host.F PP) key
  rw [map_sub, map_mul, map_natCast, hN', zero_mul, sub_eq_zero] at k2
  have h3 : resS D.host.F PP ((1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (kP PP)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  simp only [Formalism.UG.bc]
  show resS D.host.F PP (y.val i j) = _
  rw [k2, h3]
  rfl

theorem mem_stdJ_of {Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n} {κ : Formalism.AUTREP.GAf D.host.E n}
    (hU : km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E))
    (hS : km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)))
    (hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) : κ ∈ stdJ Ld := by
  show km D n κ ∈ Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld
  refine Kg_le_lev (T := Ld.Pg ∪ Ld.Q) Finset.subset_union_left Finset.subset_union_right ?_
  exact ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hS, hr PP hP⟩⟩

theorem stdX_eq_one_of {Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n} {κ : Formalism.AUTREP.GAf D.host.E n} (h : κ ∈ stdJ Ld)
    (hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) : stdX Ld ⟨κ, h⟩ = 1 := by
  show levFn (1 : GL (Fin n) (EAf D)) Ld (km D n κ) = 1
  have hT : rTup (1 : GL (Fin n) (EAf D)) Ld (km D n κ) = 1 := by
    funext PP
    show upperLeftBlock Ld.hr (redFn (1 : GL (Fin n) (EAf D)) PP.1 (km D n κ)) = 1
    rw [hr PP.1 (Finset.mem_union_left _ PP.2)]
    exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [hT, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [hr PP (Finset.mem_union_right _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hr PP (Finset.mem_union_left _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_nat_mem (T : Finset (Pl D.host.E)) :
    ∃ N : ℕ, 0 < N ∧ ∀ PP ∈ T, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  refine ⟨∏ PP ∈ T, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero fun h0 =>
    PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0), fun PP hP => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem PP.asIdeal)

theorem stdJ_open : ∀ (D : D7) (n : ℕ) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n), stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n ∧
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E n N κ → ∃ h : κ ∈ stdJ Ld, stdX Ld ⟨κ, h⟩ = 1) ∧
    ∀ B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))),
      (∀ PP, PP ∈ Ld.Pg ∨ PP ∈ Ld.Q → ∀ v, NG.OverPl PP v → v ∈ B) → NG.HypOutside (stdJ Ld) (stdX Ld) B := by
  intro D n Ld
  have R := GlobalTheory.T.stdMaximalCompact_reduction_properties D n
  have hle : stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
    (R.2.1 κ).1 (parLev_St (lev_le_parLev (show km D n κ ∈ Formalism.L2.DIV.lev D.sp.cm
      (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld from hκ)))
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨N, hN, hmem⟩ := exists_nat_mem (D := D) (Ld.Pg ∪ Ld.Q)
    refine ⟨N, hN, fun κ hκ => ?_⟩
    have hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 :=
      fun PP hP => redFn_eq_one_of_cong (hmem PP hP) hκ
    have h := mem_stdJ_of (R.1 κ) ((R.2.1 κ).2 hκ.1) hr
    exact ⟨h, stdX_eq_one_of h hr⟩
  · intro B hB κ hκ
    have hr : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n →
        ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
      intro hU PP hP
      have hov : NG.OverPl PP (PP.under (𝓞 (maximalRealSubfield D.host.E))) := by
        simp [NG.OverPl, HeightOneSpectrum.under_asIdeal, Ideal.under_def]
      refine R.2.2.1 κ hU Bᶜ _ PP hκ hov ?_
      exact fun hc => hc <| hB PP (Finset.mem_union.1 hP) _ hov
    exact ⟨⟨fun h => hle h, fun hU => mem_stdJ_of (R.1 κ) ((R.2.1 κ).2 hU) (hr hU)⟩,
      fun h => stdX_eq_one_of h (hr (hle h))⟩

end GlobalTheory.MtIn.OpenLev

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelSubgroupBoundedOpenHyperspecialStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdFrameLevelSubgroup_bounded_open_hyperspecial : ∀ (D : D7) (n : ℕ) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n), stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n ∧ (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E n N κ → ∃ h : κ ∈ stdJ Ld, stdX Ld ⟨κ, h⟩ = 1) ∧ ∀ B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), (∀ PP, PP ∈ Ld.Pg ∨ PP ∈ Ld.Q → ∀ v, NG.OverPl PP v → v ∈ B) → NG.HypOutside (stdJ Ld) (stdX Ld) B := by
  first | exact @GlobalTheory.MtIn.OpenLev.stdJ_open | exact GlobalTheory.MtIn.OpenLev.stdJ_open | (intros; apply GlobalTheory.MtIn.OpenLev.stdJ_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitCOfCXiAt
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.OneMapTuples.unitC_of_cXiAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n r : ℕ) (d : DeltaDat Xo c n) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∀ (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → d.IsLev → d.l₂.A = 1 → ∀ (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (N : ℕ), 0 < N → (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1) → ∀ (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U₂.X k).Ψ r) (c0 : ℂ), c0 ^ N = 1 → GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0 → GlobalTheory.Dict.UnitC d := by
  intro D H Dw V l Xo c n r d hr io hι hpq x₀ hx₀ hd hA xi N hN hxN U dict c0 hc0 hv A y
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := hd
  have hc0' : c0 ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc0; exact zero_ne_one hc0
  have hσ : GoodEmb d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) := rfl
  have val₀ : ∀ h : GA D V, ∃ hx : (dict h).2 ∈ (U.X (dict h).1).dom,
      toC (evR d.Xo₂ d.c₂ d.cδ (U.un _ ⟨_, hx⟩)) ^ N = 1 := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    obtain ⟨hx, ex⟩ := GlobalTheory.ShortMove.rdU_eq U d.cδ _ _ (hv ▸ mul_ne_zero hc0' (Units.ne_zero _))
    refine ⟨hx, ?_⟩
    rw [ex.symm.trans hv, mul_pow, hc0, ← Units.val_pow_eq_pow_val, hxN, Units.val_one, one_mul]
  choose hdom val₀ using val₀
  have hx : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)
  have hroot : ∀ z : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      evR d.Xo₂ d.c₂ d.cδ z ^ N = 1 := fun z => by
    obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U dict io e₀ F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx hdom z
    rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hsec hh]
    exact val₀ h
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS _ H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    _ d.cδ hsec.1 N hroot
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ N h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS _ _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hN.ne'

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmulEntry
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RedAdjCong

theorem conj_smul_entry {E R : Type} [CommRing E] [CommRing R] (φ : E →+* R) {m n : ℕ} (t : R) (d : E)
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (G : Matrix (Fin m) (Fin m) E)
    (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin m) (Fin n) E) (i : Fin m) (j : Fin n) :
    t * (A * (G * (d • M) * H).map φ * B) i j = φ d * (t * (A * (G * M * H).map φ * B) i j) := by
  have h2 : ∀ N : Matrix (Fin m) (Fin n) E, (d • N).map φ = φ d • N.map φ := by
    intro N
    ext b a
    simp
  rw [Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    mul_left_comm]

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)

theorem adj_add (X Y : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => X b + Y b) i j = uMat S T βS βT e X i j + uMat S T βS βT e Y i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((X b + Y b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = (Matrix.of fun b a => D.sp.cm.sig (X b a)) + (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add (eToEAf D)), Matrix.mul_add, Matrix.add_mul,
    Matrix.add_apply, mul_add]

theorem adj_smul (c : D.host.E) (X : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => c • X b) i j = eToEAf D (D.sp.cm.sig c) * uMat S T βS βT e X i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((c • X b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (X b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h]
  exact conj_smul_entry (eToEAf D) _ _ _ _ _ _ _ i j

end GlobalTheory.RedAdjCong

namespace GlobalTheory


open GlobalTheory.RedAdjCong in
theorem redM_adj_congr : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E), (∀ a ∈ J, ∃ a' ∈ PP.asIdeal, (a' : D.host.E) = star (a : D.host.E)) → ∀ x x' : Fin S.rank → La, (∀ b, x b - x' b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) := by
  intro D S T βS βT e La _ _ ι hint J PP hJ x x' hx
  ext i j
  let f : (Fin S.rank → La) →+ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    AddMonoidHom.mk' (fun y => ⟨uMat S T βS βT e (fun b => ι (y b)) i j, hint y i j⟩) (by
      intro y z
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (y b + z b)) i j = _ + _
      simp only [map_add (f := _)]
      exact adj_add S T βS βT e _ _ i j)
  let g : (Fin S.rank → La) →+ kP PP := (resS D.host.F PP).toAddMonoidHom.comp f
  have hg : ∀ y, redM PP (uMat S T βS βT e fun b => ι (y b)) i j = g y := by
    intro y
    unfold redM
    rw [dite_eq_left (hint y i j)]
    rfl
  have hs : ∀ a ∈ J, ∀ y : Fin S.rank → La, g (a • y) = 0 := by
    intro a ha y
    obtain ⟨a', ha', hc⟩ := hJ a ha
    have h1 : f (a • y) = oToS D.host.F D.host.E a' * f y := by
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (a • y b)) i j = eToEAf D (a' : D.host.E) * uMat S T βS βT e (fun b => ι (y b)) i j
      rw [hc]
      simp only [map_smul]
      exact adj_smul S T βS βT e (a : D.host.E) (fun b => ι (y b)) i j
    show resS D.host.F PP (f (a • y)) = 0
    rw [h1, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', zero_mul]
  have h0 : ∀ (b : Fin S.rank) (l : La), l ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) → g (Pi.single b l) = 0 := by
    intro b l hl
    refine Submodule.smul_induction_on hl ?_ ?_
    · intro a ha m _
      rw [Pi.single_smul']
      exact hs a ha _
    · intro u v hu hv
      rw [Pi.single_add, map_add (f := _), hu, hv, add_zero]
  have h3 : g (x - x') = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single (x - x'), map_sum]
    exact Finset.sum_eq_zero fun b _ => h0 b _ (hx b)
  rw [hg, hg]
  rw [map_sub, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBasisFreeModulePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem charpoly_eq_prod_of_iSup_eigenspace {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (s : Finset K)
    (h : ⨆ r ∈ s, f.eigenspace r = ⊤) :
    ∃ m : Multiset K, f.charpoly = (m.map fun a => X - C a).prod := by
  classical
  let E : s → Submodule K V := fun r => f.eigenspace (r : K)
  have hind : iSupIndep E := (Module.End.eigenspaces_iSupIndep f).comp Subtype.val_injective
  have htop : iSup E = ⊤ := by
    rw [← h, iSup_subtype]
  have hint : DirectSum.IsInternal E :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top E).mpr ⟨hind, htop⟩
  let bE : ∀ r : s, Module.Basis (Module.Free.ChooseBasisIndex K (E r)) K (E r) :=
    fun r => Module.Free.chooseBasis K (E r)
  let bb := hint.collectedBasis bE
  have hdiag : LinearMap.toMatrix bb bb f = Matrix.diagonal (fun x => ((x.1 : s) : K)) := by
    ext x y
    rw [LinearMap.toMatrix_apply]
    have hy : (bb y : V) = (bE y.1 y.2 : V) := by
      rw [hint.collectedBasis_coe]
    have hev : f (bE y.1 y.2 : V) = ((y.1 : s) : K) • (bE y.1 y.2 : V) :=
      Module.End.mem_eigenspace_iff.mp (bE y.1 y.2).2
    rw [hy, hev, ← hy, map_smul, bb.repr_self, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hxy), if_neg hxy, smul_zero]
  refine ⟨Finset.univ.val.map (fun x : (Σ r : s, Module.Free.ChooseBasisIndex K (E r)) => ((x.1 : s) : K)), ?_⟩
  rw [← LinearMap.charpoly_toMatrix f bb, hdiag, Matrix.charpoly_diagonal, Multiset.map_map,
    Finset.prod_eq_multiset_prod]
  rfl

theorem charpoly_restrict_map_eq_prod {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) [Module.Free O B] [Module.Finite O B] (f : Module.End (FractionRing O) V)
    (hf : ∀ x ∈ B, f x ∈ B) (s : Finset (FractionRing O))
    (hs : ∀ x ∈ B, x ∈ ⨆ r ∈ s, f.eigenspace r) :
    ∃ m : Multiset (FractionRing O), (LinearMap.charpoly ((f.restrictScalars O).restrict hf)).map
      (algebraMap O (FractionRing O)) = (m.map fun a => X - C a).prod := by
  classical
  let b := Module.Free.chooseBasis O B
  let v : Module.Free.ChooseBasisIndex O B → V := fun i => (b i : V)
  have hliO : LinearIndependent O v := b.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hli : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO
  let V' := Submodule.span (FractionRing O) (Set.range v)
  have hBV : ∀ x ∈ B, x ∈ V' := by
    intro x hx
    have h1 : (⟨x, hx⟩ : B) ∈ Submodule.span O (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := B.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O (FractionRing O) _ h2
  have hV' : ∀ x ∈ V', f x ∈ V' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => f x ∈ V') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      exact hBV _ (hf _ (b i).2)
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact V'.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact V'.smul_mem a hx
  let f' := f.restrict hV'
  let bK : Module.Basis (Module.Free.ChooseBasisIndex O B) (FractionRing O) V' := Module.Basis.span hli
  haveI : FiniteDimensional (FractionRing O) V' := Module.Finite.of_basis bK
  set g := (f.restrictScalars O).restrict hf with hgdef
  have hmat : LinearMap.toMatrix bK bK f' = (LinearMap.toMatrix b b g).map (algebraMap O (FractionRing O)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have hg : (g (b j) : V) = ∑ i, b.repr (g (b j)) i • v i := by
      calc (g (b j) : V) = ((∑ i, b.repr (g (b j)) i • b i : B) : V) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (g (b j)) i • v i := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    have hf' : f' (bK j) = ∑ i, algebraMap O (FractionRing O) (b.repr (g (b j)) i) • bK i := by
      have hbK : ∀ i, (bK i : V) = v i := fun i => by rw [Module.Basis.span_apply]
      apply Subtype.ext
      simp only [f', LinearMap.restrict_apply, Submodule.coe_sum, Submodule.coe_smul]
      simp_rw [hbK]
      rw [show f (v j) = (g (b j) : V) from rfl, hg]
      simp [algebraMap_smul]
    rw [hf', bK.repr_sum_self]
  have hcp : (LinearMap.charpoly g).map (algebraMap O (FractionRing O)) = f'.charpoly := by
    rw [← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map, ← hmat, LinearMap.charpoly_toMatrix]
  rw [hcp]
  apply charpoly_eq_prod_of_iSup_eigenspace f' s
  have hle : V' ≤ LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) := by
    rw [GlobalTheory.JointDiag.ker_prod, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hs _ (b i).2
  rw [← GlobalTheory.JointDiag.ker_prod, LinearMap.ker_eq_top]
  ext y
  rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, GlobalTheory.JointDiag.aeval_restrict_coe]
  exact hle y.2

end GlobalTheory.HeightCounting.FormsStep

namespace GlobalTheory.HeightCounting.FormsStep

end GlobalTheory.HeightCounting.FormsStep
end

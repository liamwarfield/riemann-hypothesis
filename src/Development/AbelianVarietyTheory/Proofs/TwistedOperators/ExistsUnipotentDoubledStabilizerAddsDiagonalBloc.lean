module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGra
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacUnip

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

def uni (Z : Matrix n n A) : Matrix (n ⊕ n) (n ⊕ n) A := Matrix.fromBlocks (1 + Z) (-Z) Z (1 - Z)

theorem uni_mul_uni_neg (Z : Matrix n n A) : uni Z * uni (-Z) = 1 := by
  rw [uni, uni, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> noncomm_ring

def uniGL (Z : Matrix n n A) : GL (n ⊕ n) A :=
  ⟨uni Z, uni (-Z), uni_mul_uni_neg Z, by simpa using uni_mul_uni_neg (-Z)⟩

theorem uni_unitary (c : A →ₐ[R] A) (J Z : Matrix n n A) (h : Zᵀ * J + J * Z.map c = 0) :
    (uni Z)ᵀ * dbl J * (uni Z).map c = dbl J := by
  have h1 : (1 + Z).map c = 1 + Z.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h2 : (1 - Z).map c = 1 - Z.map c := by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : (-Z).map c = - Z.map c := by
    ext i j; simp
  have h4 : J * Z.map c = - (Zᵀ * J) := eq_neg_of_add_eq_zero_right h
  rw [uni, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, h1, h2, h3, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_neg]
  generalize Z.map c = Zc at *
  generalize Zᵀ = Zt at *
  congr 1
  · calc _ = J + (Zt * J + J * Zc) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = -J + (Zt * J + J * Zc) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem uni_mul_diagCols (Z : Matrix n n A) : uni Z * (diagCols n : Matrix (n ⊕ n) n A) = diagCols n := by
  rw [uni, diagCols, Matrix.fromBlocks_mul_fromRows]
  congr 1 <;> simp

theorem smul_uni_sub_one (u : R) (Z : Matrix n n A) (h : u • Z = 0) : u • (uni Z - 1) = 0 := by
  have h' : ∀ i j, u • Z i j = 0 := fun i j => congrFun (congrFun h i) j
  ext (i | i) (j | j) <;> simp [uni, Matrix.one_apply, h']

theorem uni_mulVec_inl (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_sub]
  abel

theorem uni_mulVec_inr (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inr = z ∘ Sum.inr + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inr, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_sub]
  abel

theorem blocks_uni_mul (Z : Matrix n n A) (g : Matrix (n ⊕ n) (n ⊕ n) A) :
    (uni Z * g).toBlocks₁₁ + (uni Z * g).toBlocks₁₂ + (uni Z * g).toBlocks₂₁ + (uni Z * g).toBlocks₂₂ =
      g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂ +
        (Z + Z) * (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g, uni, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  noncomm_ring

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_invOf_two_mem {v : Pl (F := F)} (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h0 : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [h0, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [map_inv₀, h2]

theorem uni_mulVec_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ GlobalTheory.DblVac.latD W v, uni Z *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [uni_mulVec_inl]; exact add_mem hz.1 (hZ _ (sub_mem hz.1 hz.2))
  · rw [uni_mulVec_inr]; exact add_mem hz.2 (hZ _ (sub_mem hz.1 hz.2))

theorem mul_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {p g : GlobalTheory.DblVac.UD σ W}
    (hp : p ∈ GlobalTheory.DblVac.KD σ W v) (hg : g ∈ GlobalTheory.DblVac.KD σ W v) : p * g ∈ GlobalTheory.DblVac.KD σ W v := by
  have hm : ∀ a b : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * b) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD b :=
    fun _ _ => rfl
  refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have e : GlobalTheory.DblVac.matD (p * g) - 1 =
        (GlobalTheory.DblVac.matD p - 1) * GlobalTheory.DblVac.matD g + (GlobalTheory.DblVac.matD g - 1) := by
      rw [hm]; noncomm_ring
    rw [e, smul_add, ← Matrix.smul_mul, hp.1 u hu, hg.1 u hu, Matrix.zero_mul, add_zero]
  · rw [hm, ← Matrix.mulVec_mulVec]
    exact (hp.2 _ (hg.2 z hz).1).1
  · rw [mul_inv_rev, hm, ← Matrix.mulVec_mulVec]
    exact (hg.2 _ (hp.2 z hz).2).2

theorem exists_unip : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (AE F E),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  intro F E _ _ _ _ _ σ d W v h2 Y hAt hL hY
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin d) (Fin d) (AE F E), Z = ⅟(2 : AF F) • Y := ⟨_, rfl⟩
  have hZZ : Z + Z = Y := by
    rw [← two_smul (AF F) Z, hZ, smul_smul, mul_invOf_self, one_smul]
  have hZc : Z.map (cA σ) = ⅟(2 : AF F) • Y.map (cA σ) := by
    rw [hZ]; ext i j; simp
  have hZu : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 := by
    rw [hZc, hZ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]
  have hZL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [hZ, Matrix.smul_mulVec]
    exact GlobalTheory.LatAlmostAll.smul_mem_latAt W v (evFin_invOf_two_mem h2) (hL z hz)
  have hZL' : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (-Z) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [Matrix.neg_mulVec]
    exact neg_mem (hZL z hz)
  let p : GlobalTheory.DblVac.UD σ W := ⟨uniGL Z, uni_unitary (cA σ) (incM F W.J) Z hZu⟩
  have hp : p ∈ GlobalTheory.DblVac.KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨uni_mulVec_mem W v Z hZL z hz, uni_mulVec_mem W v (-Z) hZL' z hz⟩⟩
    refine smul_uni_sub_one u Z ?_
    rw [hZ, smul_comm, hAt u hu, smul_zero]
  refine ⟨p, hp, ⟨1, ?_⟩, fun g hg => ⟨mul_mem_KD hp hg, ?_⟩⟩
  · exact (uni_mul_diagCols Z).trans (Matrix.mul_one _).symm
  · have e : GlobalTheory.DblVac.matD (p * g) = uni Z * GlobalTheory.DblVac.matD g := rfl
    rw [GlobalTheory.DblVac.diagonalBlockOfMatrix, GlobalTheory.DblVac.diagonalBlockOfMatrix, e, blocks_uni_mul, smul_add, hZZ, Matrix.mul_smul]

end GlobalTheory.DblVacUnip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBlocStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  first | exact @GlobalTheory.DblVacUnip.exists_unip | exact GlobalTheory.DblVacUnip.exists_unip | (intros; apply GlobalTheory.DblVacUnip.exists_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter
section -- merged from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.GenInhabited
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc.FamilyModel

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ConjWeil

variable {D : D7}

theorem cjOm_apply {S T : HSp D} (om : Om (negSp S) T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    cjOm om p f = cj id (om (negGA S p.1, p.2) (cj id f)) := rfl

theorem negGA_mem_GQ (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _)

theorem weil_cjOm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om (negSp S) T) (hw : IsWeilDatumO ψ (negSp S) T χS χT om) :
    IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (cjOm om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f) := fun f => (I.1 f).2.symm
  have thS' : ∀ f : WO S T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO S T → ℂ),
      heisO ψ S T w f = cj id (heisO ψ (negSp S) T w (cj id f)) := fun w f => by
    rw [(I.2 w f).2, cj_id_cj_id]
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [cjOm_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [cjOm_apply, cjOm_apply, hzS w₀ f, cj_id_cj_id]
    erw [hw.om_heis _ _ _ _ ((thS f).1 hf)]
    rw [hzS _ (cj id _), cj_id_cj_id, actO_negS, MulEquiv.symm_apply_apply]
  · intro γ hγ γ' hγ' f hf
    rw [cjOm_apply]
    show starRingEnd ℂ (om (negGA S γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [cjOm_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (negGA S p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [cjOm_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he (negGA S g) h
      (by unfold SuppAt; rw [mt_negGA]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (negGA S g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        have e1 := hzS u (cj id f')
        rw [cj_id_cj_id] at e1
        rw [← e1, hℓ u hu (cj id f') ((thS' f').1 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← cjOm_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem vac_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) :
    VacG ψ (negSp S) T Γ f ↔ VacG ψ S T Γ (star f) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T
  have e0 : star f = cj id f := rfl
  have th : IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hz : ∀ w : WO S T, heisO ψ (negSp S) T w f = f ↔ heisO ψ S T w (cj id f) = cj id f := fun w => by
    have := (I.2 w (cj id f)).2
    rw [cj_id_cj_id] at this
    rw [this]
    exact ⟨fun h => by have := congrArg (cj id) h; rwa [cj_id_cj_id] at this, fun h => by rw [h, cj_id_cj_id]⟩
  rw [e0]
  unfold VacG IsLatVac
  simp only [th, hz]

theorem part_succ {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ u) (i : ℕ)
    (hi : i < D.R.m) : part W M ρ Φ u (i + 1) hi = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, hi⟩) (part W M ρ Φ u i hi.le) := rfl

theorem part_congr {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ ρ' Φ' u)
    (i : ℕ) (hi : i ≤ D.R.m) (h : ∀ j : Fin D.R.m, j.1 < i → ρ j = ρ' j ∧ Φ j = Φ' j) :
    part W M ρ Φ u i hi = part W M ρ' Φ' u i hi := by
  unfold part
  congr 2
  funext j
  have := h (Fin.castLE hi j) j.2
  unfold GridData.Weil.datum
  rw [this.1, this.2]

theorem conjRead : ConjRead := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have r1 : (G.pS (.chi i 0)).rank = rankV D (i + 1) 0 := (node_isV G hL (X := .grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).rank
  have r0 : (G.pT (.chi i 0)).rank = rankV D i 0 := (node_isV G hL (X := .grid i 0) ⟨hi.le, Nat.zero_le _⟩).rank
  have e1 := even_rankV D (i + 1) 0
  have e0 := even_rankV D i 0
  refine ⟨weil_cjOm _ _ _ _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩), ?_, fun ho => ?_, fun he => ?_, fun f => ?_,
    fun v f Ψ => ?_, fun ρ Φ u => ?_, fun ρ Φ ρ' Φ' u h => part_congr W M ρ Φ ρ' Φ' u i hi.le h, (hM.row i hi.le).haar_fund⟩
  · have := weil_cjOm _ _ _ _ _ _ (W.om_is (.core i) hi)
    rwa [(G.chr_core hi).1, (G.chr_core hi).2] at this
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e1]; simpa [Nat.odd_add_one] using ho)),
      if_neg (Nat.not_odd_iff_even.2 (e0.2 (by simpa using ho)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e0]; simpa using he)),
      if_neg (Nat.not_odd_iff_even.2 (e1.2 (by simpa [Nat.odd_add_one] using he)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · exact vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) f
  · funext g
    rw [liftT_apply, Pi.star_apply, dn, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.core i) (negGA _ h, g) z 0)) (cj_id_cj_id f).symm
  · funext g
    rw [liftS_apply, Pi.star_apply, part_succ, liftA_apply, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.chi i 0) (negGA _ g, h) z 0)) (cj_id_cj_id _).symm

end GlobalTheory.Asc.FamilyModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem conjRead_holds : ConjRead := GlobalTheory.Asc.FamilyModel.conjRead

end GlobalTheory.Asc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridConjugation_weilData_inverseCharacter : ConjRead := by
  first | exact @GlobalTheory.Asc.conjRead_holds | exact GlobalTheory.Asc.conjRead_holds | (intros; apply GlobalTheory.Asc.conjRead_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientLipschitzAtRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientLipschitzAtRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PackLoc.lipAt : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (K lam q : ℝ) (c : ℂ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, ∀ (s : ℝ) u,
    GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • (A * X * A⁻¹)) * GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, A * X * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ)), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
        K * |s| * GlobalTheory.SepReal.hsn X) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ,
    (Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < lam → lam * K ≤ Real.exp q * ‖c‖ →
  ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤
      Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹) := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ A K lam q c hB hA hL hK hH hlam hlk X hX s
  set X' := A * X * A⁻¹ with hX'
  have hX'L := hL X hX
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ := fun x =>
    ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X') * x)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ‖ with hF
  have hfun : (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) =
      fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := by
    funext u
    rw [hA X hX s u, hB u]
  obtain ⟨hint, hbd⟩ := hK X' hX'L s
  obtain ⟨hiff, heq⟩ := hH F
  have hsnEq : GlobalTheory.SepReal.hsn X' = hsn X' := rfl
  have hsn0 : 0 ≤ hsn X' := Real.sqrt_nonneg _
  rw [hfun]
  refine ⟨hiff.2 hint, ?_⟩
  rw [heq, smul_eq_mul]
  have h1 : lam * ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      lam * (K * |s| * hsn X') := by
    rw [← hsnEq]
    exact mul_le_mul_of_nonneg_left hbd hlam.le
  have h2 : lam * (K * |s| * hsn X') ≤ Real.exp q * ‖c‖ * |s| * hsn X' := by
    have hm : 0 ≤ |s| * hsn X' := mul_nonneg (abs_nonneg s) hsn0
    calc lam * (K * |s| * hsn X') = (lam * K) * (|s| * hsn X') := by ring
      _ ≤ (Real.exp q * ‖c‖) * (|s| * hsn X') := mul_le_mul_of_nonneg_right hlk hm
      _ = Real.exp q * ‖c‖ * |s| * hsn X' := by ring
  exact h1.trans h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientLipschitzAtRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_lipschitz_at_real_place : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (K lam q : ℝ) (c : ℂ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, ∀ (s : ℝ) u,
    GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • (A * X * A⁻¹)) * GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, A * X * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ)), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
        K * |s| * GlobalTheory.SepReal.hsn X) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ,
    (Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < lam → lam * K ≤ Real.exp q * ‖c‖ →
  ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤
      Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹) := by
  first | exact @GlobalTheory.PackLoc.lipAt | exact GlobalTheory.PackLoc.lipAt | (intros; apply GlobalTheory.PackLoc.lipAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedMatrixCoefficientInAdaptedFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedMatrixCoefficientInAdaptedFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

lemma inUJ_mul' {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Formalism.MainNotions.S.UJset ε) (hb : b ∈ Formalism.MainNotions.S.UJset ε) : a * b ∈ Formalism.MainNotions.S.UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem mco_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  intro D V S M τ B g v₀ hB hBg hg
  set F := M.fr τ with hFdef
  set J := Formalism.REAL.Jm (M.ε τ) with hJdef
  set G := gramAt D V τ with hGdef
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp (M.fr_unit τ)
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hFg : Fᴴ * J * F = G := M.fr_gram τ
  have hg' : gᴴ * J * g = J := hg
  have hBH : (B⁻¹)ᴴ * Bᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv B hBd, conjTranspose_one]
  have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv F hFd, conjTranspose_one]
  have hBinv : (B⁻¹)ᴴ * G * B⁻¹ = J := by
    rw [← hBg]
    calc (B⁻¹)ᴴ * (Bᴴ * J * B) * B⁻¹ = ((B⁻¹)ᴴ * Bᴴ) * J * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hBH, Matrix.mul_nonsing_inv B hBd]; simp
  have hFinv : (F⁻¹)ᴴ * G * F⁻¹ = J := by
    rw [← hFg]
    calc (F⁻¹)ᴴ * (Fᴴ * J * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * J * (F * F⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hFH, Matrix.mul_nonsing_inv F hFd]; simp
  refine ⟨?_, ?_⟩
  · show (B⁻¹ * g * F)ᴴ * G * (B⁻¹ * g * F) = G
    rw [conjTranspose_mul, conjTranspose_mul]
    calc Fᴴ * (gᴴ * (B⁻¹)ᴴ) * G * (B⁻¹ * g * F) = Fᴴ * (gᴴ * ((B⁻¹)ᴴ * G * B⁻¹) * g) * F := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hBinv, hg', hFg]
  · intro x hx
    have hx' : xᴴ * G * x = G := hx
    obtain ⟨⟨_, hmul⟩, hiso, _⟩ := (M.ds τ).2.2.1
    have hk : F * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * B⁻¹)ᴴ * J * (F * B⁻¹) = J
      rw [conjTranspose_mul]
      calc (B⁻¹)ᴴ * Fᴴ * J * (F * B⁻¹) = (B⁻¹)ᴴ * (Fᴴ * J * F) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hBinv]
    have hy : B * x * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (B * x * B⁻¹)ᴴ * J * (B * x * B⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (B⁻¹)ᴴ * (xᴴ * Bᴴ) * J * (B * x * B⁻¹) = (B⁻¹)ᴴ * (xᴴ * (Bᴴ * J * B) * x) * B⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hBg, hx', hBinv]
    have hz : F * x * F⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * x * F⁻¹)ᴴ * J * (F * x * F⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (F⁻¹)ᴴ * (xᴴ * Fᴴ) * J * (F * x * F⁻¹) = (F⁻¹)ᴴ * (xᴴ * (Fᴴ * J * F) * x) * F⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hx', hFinv]
    have e1 : F * (B⁻¹ * g * F) * F⁻¹ = F * B⁻¹ * g := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv F hFd, Matrix.mul_one]
    have e2 : F * x * F⁻¹ * (F * B⁻¹ * g) = F * B⁻¹ * (B * x * B⁻¹ * g) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left F _ hFd,
        Matrix.nonsing_inv_mul_cancel_left B _ hBd]
    have hkg := inUJ_mul' hk hg
    have hyg := inUJ_mul' hy hg
    unfold mco DSModel.rep
    rw [← hFdef, e1, ← ContinuousLinearMap.comp_apply, ← hmul _ hz _ hkg, e2,
      hmul _ hk _ hyg, hmul _ hk _ hg, hmul _ hy _ hg]
    simp only [ContinuousLinearMap.comp_apply]
    let L : M.H τ →ₗᵢ[ℂ] M.H τ := ⟨(M.σ τ (F * B⁻¹)).toLinearMap, hiso _ hk⟩
    exact L.inner_map_map _ _

end GlobalTheory.PackLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedMatrixCoefficientInAdaptedFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  first | exact @GlobalTheory.PackLoc.mco_frame | exact GlobalTheory.PackLoc.mco_frame | (intros; apply GlobalTheory.PackLoc.mco_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjSmoothVectorConjugateModelMemSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjSmoothVectorConjugateModelMemSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSmooth

open GlobalTheory.ConjDS

theorem conj_list_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    A * l.prod * A⁻¹ = (l.map fun x => A * x * A⁻¹).prod := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  induction l with
  | nil => simp [h1]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc A * (x * l.prod) * A⁻¹ = A * x * (A⁻¹ * A) * l.prod * A⁻¹ := by rw [h2]; noncomm_ring
      _ = A * x * A⁻¹ * (A * l.prod * A⁻¹) := by noncomm_ring

theorem cj_mem_sm : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  intro D Y S M τ w hw
  apply Submodule.subset_span
  intro k Xs hXs
  set A := (conjModel M).fr τ with hAdef
  have hA : IsUnit A := (conjModel M).fr_unit τ
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet

  have hrep : ∀ g, M.rep τ g (cj (M.H τ) w) = cj (M.H τ) ((conjModel M).σ τ (A * g * A⁻¹) w) := by
    intro g
    have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
      rw [inv_submatrix_equiv]
      have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
          rv (M.fr τ * g * (M.fr τ)⁻¹) := by
        ext i j
        simp [rv, Matrix.mul_apply]
      rw [this, rv_rv]
    show M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj (M.H τ) w) = M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj (M.H τ) w)
    rw [e]

  have hX' : ∀ i, A * Xs i * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((conjModel M).ε τ)) := by
    intro i
    have hg : Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A = gramAt D Y τ := (conjModel M).fr_gram τ
    have hi : (Xs i)ᴴ * gramAt D Y τ + gramAt D Y τ * Xs i = 0 := hXs i
    have h3 : (A⁻¹)ᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) = 0
    rw [← hg] at hi
    have : (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) =
        (A⁻¹)ᴴ * ((Xs i)ᴴ * (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) + (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) * Xs i) * A⁻¹ := by
      simp only [Matrix.conjTranspose_mul]
      calc _ = (A⁻¹)ᴴ * (Xs i)ᴴ * Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + 1 * Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) := by
              rw [Matrix.one_mul]; noncomm_ring
        _ = _ := by rw [← h3]; simp only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul]
    rw [this, hi, Matrix.mul_zero, Matrix.zero_mul]
  have hprod : ∀ t : Fin k → ℝ, A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * A⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * A⁻¹))).prod := by
    intro t
    rw [conj_list_prod hA, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp]
    rw [← Matrix.exp_conj A _ hA, Matrix.mul_smul, Matrix.smul_mul]
  have hc := hw k (fun i => A * Xs i * A⁻¹) hX'
  let L : Cj (M.H τ) →L[ℝ] M.H τ :=
    { toFun := cj (M.H τ)
      map_add' := map_add (cj (M.H τ))
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
        rfl
      cont := (cj (M.H τ)).continuous }
  have hL := L.contDiff.comp hc
  convert hL using 1
  funext t
  rw [hrep, hprod]
  rfl

end GlobalTheory.ConjSmooth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjSmoothVectorConjugateModelMemSmoothStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_smooth_vector_conjugate_model_mem_smooth : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  first | exact @GlobalTheory.ConjSmooth.cj_mem_sm | exact GlobalTheory.ConjSmooth.cj_mem_sm | (intros; apply GlobalTheory.ConjSmooth.cj_mem_sm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelFrameMatrixFactsAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelFrameMatrixFactsAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLocFacts

variable {n : ℕ}

theorem conj_mem_lie {F J G X : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hX : Xᴴ * G + G * X = 0) : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = 0 := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have e : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = (F⁻¹)ᴴ * (Xᴴ * G + G * X) * F⁻¹ := by
    rw [← hG]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    congr 1
    · rw [h1, Matrix.mul_one]
    · rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul]
  rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem ofFr_mem_UH {F J G g : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hg : gᴴ * J * g = J) : F⁻¹ * g * F ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
  rw [← hG]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul, ← Matrix.mul_assoc F F⁻¹, h1, Matrix.one_mul,
    ← Matrix.mul_assoc J g F, ← Matrix.mul_assoc gᴴ (J * g) F, ← Matrix.mul_assoc gᴴ J g, hg]

theorem rev_conj (F g : Matrix (Fin n) (Fin n) ℂ) :
    F.submatrix Fin.revPerm (Equiv.refl _) * g * (F.submatrix Fin.revPerm (Equiv.refl _))⁻¹ =
      GlobalTheory.ConjDS.rv (F * g * F⁻¹) := by
  rw [Matrix.inv_submatrix_equiv]
  ext i j
  simp [GlobalTheory.ConjDS.rv, Matrix.mul_apply]

theorem frame_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  intro D θ hθ Y S M τ
  have hF : IsUnit (M.fr τ) := M.fr_unit τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hF
  have hA : ∀ g, (GlobalTheory.ConjDS.conjModel M).fr τ * g * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (M.fr τ * g * (M.fr τ)⁻¹) := fun g => rev_conj (M.fr τ) g
  have hcan : ∀ U : Matrix (Fin Y.rank) (Fin Y.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * U * M.fr τ) * (M.fr τ)⁻¹ = U := by
    intro U
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  refine ⟨fun u => ⟨?_, ?_, ?_⟩, fun X hX => ⟨?_, fun s => ?_⟩⟩
  · exact ofFr_mem_UH hF (M.fr_gram τ) u.2
  · show _ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * _ = _
    rw [hA, hcan]
  · show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * (M.fr τ)⁻¹) = _
    rw [hcan]
  · exact conj_mem_lie ((GlobalTheory.ConjDS.conjModel M).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M).fr_gram τ) hX
  · have hmem : NormedSpace.exp (s • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) :=
      GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit Y τ) hX s
    have hc : cmp θ τ (oneP θ Y τ X s) = NormedSpace.exp (s • X) :=
      (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hmem).2.1
    rw [hc]
    refine ⟨hmem, ?_⟩
    rw [← Matrix.exp_conj _ _ ((GlobalTheory.ConjDS.conjModel M).fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.PackLocFacts

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelFrameMatrixFactsAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_model_frame_matrix_facts_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  first | exact @GlobalTheory.PackLocFacts.frame_facts | exact GlobalTheory.PackLocFacts.frame_facts | (intros; apply GlobalTheory.PackLocFacts.frame_facts <;> assumption)
end
end

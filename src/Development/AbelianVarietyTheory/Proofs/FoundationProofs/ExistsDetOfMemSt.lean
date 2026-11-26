module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistTrivialOnRational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDetOfMemSt
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_baseChange_lift {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (γ : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M))) (f : M →ₗ[R] M)
    (hf : ∀ v, (I • (⊤ : Submodule R M)).mkQ (f v) = γ ((I • (⊤ : Submodule R M)).mkQ v)) :
    LinearMap.det (LinearMap.baseChange (R ⧸ I) f) =
      ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective) : (R ⧸ I)ˣ) : R ⧸ I) := by
  let e := (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective
  rw [LinearEquiv.coe_det, ← LinearMap.det_conj _ e]
  congr 1
  refine LinearMap.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change TensorProduct.quotTensorEquivQuotSMul M I (LinearMap.baseChange (R ⧸ I) f
    ((TensorProduct.quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk a))) = γ _
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearMap.baseChange_tmul,
    ← TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearEquiv.apply_symm_apply]
  exact hf a

section General

open GlobalTheory.AdLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def swapF : RA F E →+* E ⊗[F] Formalism.L2.Herm.Af F :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom

theorem exists_res_eq_zero {I : Ideal (𝓞 E)} {PP : Pl E} (hI : I ≤ PP.asIdeal) {x : RA F E}
    (hx : x ∈ hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ t : Formalism.L2.Herm.intAf F E, t.1 = swapF F E x ∧ resS F PP t = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    refine ⟨oToS F E b * ⟨(1 : E) ⊗ₜ a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩, ?_, ?_⟩
    · change ((b : E) ⊗ₜ 1) * ((1 : E) ⊗ₜ a) = (b : E) ⊗ₜ a
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · rw [map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 (hI hb), zero_mul]
  | zero => exact ⟨0, (RingHom.map_zero _).symm, RingHom.map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hs'⟩ := hx
    obtain ⟨t, ht, ht'⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add (f := _), ← hs, ← ht]; rfl, by rw [RingHom.map_add (f := _), hs', ht', add_zero]⟩
  | neg x _ hx =>
    obtain ⟨s, hs, hs'⟩ := hx
    exact ⟨-s, by rw [RingHom.map_neg, ← hs]; rfl, by rw [RingHom.map_neg, hs', neg_zero]⟩

theorem det_eq_one_of_lift {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (Pg : Finset (Pl E)) (I J : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hIJ : I ⊔ J = ⊤)
    (hPg : I = ∏ PP ∈ Pg, PP.asIdeal) {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (ι : M →ₗ[𝓞 E] (Fin n → E))
    (hinj : Function.Injective ι) (hr : LinearMap.range ι = L)
    (γ : (M ⧸ I • (⊤ : Submodule (𝓞 E) M)) ≃ₗ[𝓞 E] (M ⧸ I • (⊤ : Submodule (𝓞 E) M))) (f : M →ₗ[𝓞 E] M)
    (hf : ∀ v, (I • (⊤ : Submodule (𝓞 E) M)).mkQ (f v) = γ ((I • (⊤ : Submodule (𝓞 E) M)).mkQ v))
    (k : Matrix (Fin n) (Fin n) (RA F E)) (s : Formalism.L2.Herm.intAf F E) (hs : swapF F E k.det = s.1)
    (hdet : ∀ PP ∈ Pg, resS F PP s = 1) {N : ℕ} (hN : (N : 𝓞 E) ∈ I)
    (h : ∀ a ∈ J • (⊤ : Submodule (𝓞 E) M), ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (ι (f a)) - k.mulVec (fv F (ι a)) = N • w) :
    LinearMap.det (LinearMap.baseChange (𝓞 E ⧸ I) f) = 1 := by
  have h1 : (1 : 𝓞 E) ∈ I ⊔ J := by rw [hIJ]; trivial
  obtain ⟨m, hm, c, hc, hmc⟩ := Submodule.mem_sup.1 h1
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ I)
    Ideal.Quotient.mk_surjective) : (𝓞 E ⧸ I)ˣ) : 𝓞 E ⧸ I)
  let ρ : 𝓞 E →+* RA F E :=
    (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom.comp (algebraMap (𝓞 E) E)
  have hfv : ∀ (b : 𝓞 E) a, fv F (ι (b • a)) = ρ b • fv F (ι a) := fun b a => by
    funext i
    rw [map_smul]
    change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((b : E) * ι a i) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ι a i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have key := GlobalTheory.LevDet.det_sub_mem_completedIdeal_of_level F L hfg hsp I hI ι hinj hr γ f hf (ρ c • k) (fun a => by
      obtain ⟨w, hw, e⟩ := h (c • a) (Submodule.smul_mem_smul hc trivial)
      have hfa : fv F (ι (f a)) ∈ hat F (L : Set (Fin n → E)) :=
        AddSubgroup.subset_closure ⟨1, fun v => one_mem _, _, hr ▸ LinearMap.mem_range_self ι _, rfl⟩
      rw [map_smul, hfv, hfv, Matrix.mulVec_smul, ← Nat.cast_smul_eq_nsmul (RA F E), ← map_natCast ρ] at e
      have e' : (ρ c • k) *ᵥ fv F (ι a) - fv F (ι (f a)) = -(ρ m • fv F (ι (f a))) - ρ (N : 𝓞 E) • w := by
        have : ρ m = 1 - ρ c := by rw [← map_one ρ, ← hmc, map_add (f := _), add_sub_cancel_right]
        rw [← e, this, Matrix.smul_mulVec, sub_smul, one_smul]
        abel
      rw [e']
      exact sub_mem (neg_mem (AddSubgroup.subset_closure ⟨m, hm, _, hfa, rfl⟩))
        (AddSubgroup.subset_closure ⟨_, hN, w, hw, rfl⟩)) u hu
  rw [det_baseChange_lift I γ _ hf, ← hu, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hPg,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime fun a _ b _ hab => HeightOneSpectrum.isCoprime_of_ne _ _ hab]
  refine Ideal.mem_iInf.2 fun PP => Ideal.mem_iInf.2 fun hP => ?_
  have hle : I ≤ PP.asIdeal := hPg ▸ Ideal.prod_le_inf.trans (Finset.inf_le hP)
  obtain ⟨t, ht, ht0⟩ := exists_res_eq_zero hle key
  have hρ : ∀ b, swapF F E (ρ b) = (oToS F E b).1 := fun _ => rfl
  have e : t = oToS F E c ^ n * s - oToS F E u := by
    apply Subtype.ext
    rw [ht, Matrix.det_smul, RingHom.map_sub, RingHom.map_mul, RingHom.map_pow, hρ, hs, Fintype.card_fin]
    rfl
  have h4 : Ideal.Quotient.mk PP.asIdeal c = 1 := by
    rw [← map_one (Ideal.Quotient.mk PP.asIdeal), ← hmc, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 (hle hm), zero_add]
  rw [e, RingHom.map_sub, RingHom.map_mul, RingHom.map_pow, resS_oToS, resS_oToS, hdet PP hP, h4, one_pow, one_mul,
    sub_eq_zero] at ht0
  rw [← Ideal.Quotient.eq, ← ht0, map_one]

theorem exists_det_of_mem_St {n : ℕ} (k : Matrix (Fin n) (Fin n) (RA F E)) {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hk : x.1 = (swapF F E).mapMatrix k) (hx : x ∈ St β) : ∃ s : Formalism.L2.Herm.intAf F E, swapF F E k.det = s.1 ∧
      ∀ PP, resS F PP s = ((redFn β PP x : GL _ _) : Matrix (Fin n) (Fin n) (kP PP)).det := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y.1.det, ?_, fun PP => ?_⟩
  · have e2 : (y.1.det).1 = (intGL F E _ y).1.det := RingHom.map_det (Formalism.L2.Herm.intAf F E).subtype _
    rw [RingHom.map_det, ← hk, e2]
    exact Matrix.det_units_conj β _
  · rw [redFn_frGL]
    exact RingHom.map_det _ _

end General

variable {D : D7}

theorem detOne_of_lift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (γ : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l)
    (κ : GA D V) (β : GL (Fin V.rank) (EAf D)) (hκ : finE V κ ∈ St β) (Pg : Finset (Pl D.host.E))
    (hPg : l.Mb = ∏ PP ∈ Pg, PP.asIdeal)
    (hdet : ∀ PP ∈ Pg, ((redFn β PP (finE V κ) : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)).det = 1)
    (h : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      finVec V (ι (liftLa γ a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = l.M • w) : DetOne γ := by
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hI : l.Mb ≠ ⊥ := fun h0 => by
    have h1 := (natCast_mem_half l).1
    rw [h0, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    have := l.three_le
    omega
  rw [hhat] at h
  obtain ⟨s, hs, hs'⟩ := exists_det_of_mem_St (F := D.host.F) (finHom V κ).1 rfl hκ
  exact det_eq_one_of_lift (latG V 1) hfg hsp Pg l.Mb (Mfr l) hI l.coprime hPg ι hι.1 hι.2 γ _ (liftLa_spec γ)
    (finHom V κ).1 s hs (fun PP hP => (hs' PP).trans (hdet PP hP)) (natCast_mem_half l).1 h

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem latEmb_iotaW {T : Full D} (hT : LawsFull T) (ι : Fin D.R.m) : LatEmb (Wc D ι) (iotaW T.J ι) := by
  obtain ⟨hr, _, _, _, _, _, _, hL, -⟩ := hT.j.adPin _ (inR_succ ι) T.σ₀ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (_ : V = Wc D ι) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((ι : ℕ) + 1)) →
      LatEmb (Wc D ι) (iotaW T.J ι) := by
    rintro _ rfl _ h
    exact h
  exact key _ (hT.p.spaceW _ (inR_succ ι) _ T.toCore.good_σ₀) hr hL

theorem detOne_of_levelPin {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} (hT : LawsFull T)
    {ι : Fin D.R.m} {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    (hℓ : LevelPin R ι ℓ) (hPg : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal) {g : G}
    (hg : ∀ PP : R.Pg, ((R.eG g PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) : DetOne (ℓ g) := by
  obtain ⟨κ, ⟨-, hκ, hr⟩, h⟩ := hℓ g
  refine detOne_of_lift (Wc D ι) _ (latEmb_iotaW hT ι) _ κ (R.βW ι) (parLev_St hκ) R.Pg hPg (fun PP hP => ?_) h
  have e : upperLeftBlock (r_le_rank_Wc ι) (redFn (R.βW ι) PP (finE (Wc D ι) κ)) = R.eG g ⟨PP, hP⟩ := congrFun hr ⟨PP, hP⟩
  have hb : redFn (R.βW ι) PP (finE (Wc D ι) κ) ∈ blockTri (blk2 D.R.r) := fun i j hij => by
    have hi : i.val < D.R.r := (rank_Wc ι) ▸ i.2
    have hj : j.val < D.R.r := (rank_Wc ι) ▸ j.2
    simp [blk2, hi, hj] at hij
  rw [← hg ⟨PP, hP⟩, ← e, upper_block_val_submatrix _ hb]
  exact (Matrix.det_submatrix_equiv_self (finCongr (rank_Wc ι).symm) _).symm

end GlobalTheory.TraceLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormVal

def Bd (p : ℕ) [Fact p.Prime] (r : ℝ) (x : ℂ) : Prop :=
  x ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam x‖ ≤ r

variable {p : ℕ} [Fact p.Prime]

lemma lamC_of_mem (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) : lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC
  rw [dite_eq_left h]

lemma Bd.zero {r : ℝ} (hr : 0 ≤ r) : Bd p r 0 := by
  refine ⟨zero_mem _, fun lam => ?_⟩
  rw [lamC_of_mem lam (zero_mem _)]
  have : (⟨0, zero_mem _⟩ : Qbar) = 0 := rfl
  rw [this, map_zero, norm_zero]
  exact hr

lemma Bd.add {r : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p r y) : Bd p r (x + y) := by
  refine ⟨add_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (add_mem hx.1 hy.1)]
  have : (⟨x + y, add_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

lemma Bd.mul {r s : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p s y) : Bd p (r * s) (x * y) := by
  refine ⟨mul_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (mul_mem hx.1 hy.1)]
  have : (⟨x * y, mul_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ := rfl
  rw [this, map_mul, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

lemma Bd.mono {r s : ℝ} {x : ℂ} (hx : Bd p r x) (h : r ≤ s) : Bd p s x :=
  ⟨hx.1, fun lam => (hx.2 lam).trans h⟩

lemma conj_mem {x : ℂ} (hx : x ∈ Qbar) : (starRingEnd ℂ) x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at hx ⊢
  exact hx.algHom ((starRingEnd ℂ).toRatAlgHom)

noncomputable def conjQ : Qbar →+* Qbar :=
  ((starRingEnd ℂ).comp (algebraMap Qbar ℂ)).codRestrict Qbar (fun x => conj_mem x.2)

lemma Bd.conj {r : ℝ} {x : ℂ} (hx : Bd p r x) : Bd p r ((starRingEnd ℂ) x) := by
  refine ⟨conj_mem hx.1, fun lam => ?_⟩
  have h1 := hx.2 (lam.comp conjQ)
  rw [lamC_of_mem _ hx.1] at h1
  rw [lamC_of_mem lam (conj_mem hx.1)]
  exact h1

lemma Bd.inv_nat {n M : ℕ} (hM : M ≠ 0) (h : n ∣ M) :
    Bd p ((p : ℝ) ^ (padicValNat p M : ℝ)) ((n : ℂ)⁻¹) := by
  have hn : n ≠ 0 := fun h0 => hM (by simpa [h0] using h)
  have hm : (n : ℂ)⁻¹ ∈ Qbar := inv_mem (natCast_mem _ n)
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have : (⟨(n : ℂ)⁻¹, hm⟩ : Qbar) = (n : Qbar)⁻¹ := by
    apply Subtype.ext
    simp
  rw [this, map_inv₀, map_natCast, norm_inv]
  have h2 : ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) n, norm_algebraMap']
  have hn' : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
  rw [h2, Padic.norm_eq_zpow_neg_valuation hn', Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast, Real.rpow_natCast]
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  apply pow_le_pow_right₀ hp
  rw [← (by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hM]
  simpa only [_root_.Nat.padicValNat_def] using
    (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)).trans h

lemma order_dvd {f r N : ℕ} (h : r ≤ 2 * N) :
    8 ^ (2 * f * r) * (2 * (2 * f * r)).factorial ∣ 8 ^ (4 * f * N) * (8 * f * N).factorial := by
  have h1 : f * r ≤ f * (2 * N) := Nat.mul_le_mul_left _ h
  apply mul_dvd_mul
  · apply pow_dvd_pow
    nlinarith
  · apply Nat.factorial_dvd_factorial
    nlinarith

theorem norm_mem_and_le : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (N : ℕ) (B : ℝ), P.Small N B → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((P.norm : ℝ) : ℂ) ∈ Qbar ∧ ‖lamC lam ((P.norm : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ (3 * ((padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ))) := by
  intro D hI S dl hL δ t0 Q hC hT hQ P N B hS p _ lam
  set M : ℕ := 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial with hMdef
  have hM : M ≠ 0 := by positivity
  set c : ℝ := dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ) with hc
  set v : ℝ := (padicValNat p M : ℝ) with hv
  set w : ℝ := (padicValNat p Q : ℝ) with hw
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  have hv0 : 0 ≤ v := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by
    have := hL.2.1 p
    have h2 : (0 : ℝ) ≤ (if p = D.host.d then 1 / 4 else 0) := by split_ifs <;> norm_num
    rw [hc]
    linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * c + ((P.a * P.d : ℕ) : ℝ) * w with he
  have he0 : 0 ≤ e := by positivity
  have ha : P.a ≤ 2 * N := P.a_le.trans hS.1
  have heE : e ≤ 4 * fF D * N * B * c + 4 * (N : ℝ) ^ 2 * w := by
    have hcard := (GlobalTheory.T.derivationDenominators_and_hostField_sizes D hI.g1).2.2.2.2.1
    have h1 : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ fF D * (2 * B) := by
      rw [Nat.cast_sum, ← hcard]
      have := Finset.sum_le_card_nsmul Finset.univ (fun τ => (P.n τ : ℝ)) (2 * B)
        (fun τ _ => hS.2 τ)
      simpa using this
    have haR : (P.a : ℝ) ≤ 2 * N := by exact_mod_cast ha
    have hdR : (P.d : ℝ) ≤ 2 * N := by exact_mod_cast hS.1
    have h2 : ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) ≤ 4 * fF D * N * B := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * ((∑ τ, P.n τ : ℕ) : ℝ) ≤ (2 * N) * (fF D * (2 * B)) :=
            mul_le_mul haR h1 (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    have h3 : ((P.a * P.d : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * (P.d : ℝ) ≤ (2 * N) * (2 * N) :=
            mul_le_mul haR hdR (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    exact add_le_add (mul_le_mul_of_nonneg_right h2 hc0) (mul_le_mul_of_nonneg_right h3 hw0)
  obtain ⟨hterm, hsq, -⟩ := GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q hC hT P hQ.1
  have hgam : ∀ (r : ℕ), r ≤ 2 * N → ∀ (J : Subgroup (GA D r)), J ≤ intG D r → ∀ g,
      Bd p ((p : ℝ) ^ v) ((gam D J g : ℂ)⁻¹) := fun r hr J hJ g =>
    Bd.inv_nat hM ((GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D r J hJ g).2.1.trans (order_dvd hr))
  have hcoord : ∀ (h k' : GA D P.d), k' ∈ intG D P.d →
      TrivAt D p ((h * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T,
      Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e) (P.coord h T) := by
    intro h k' hk' htr T
    unfold Pair.coord
    refine finsum_induction (Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e)) (Bd.zero (by positivity))
      (fun x y => Bd.add) (fun x => ?_)
    refine Bd.mul (hgam _ ha _ le_rfl _) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.a p Fact.out x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact ⟨(GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam _ h k' hk' h3 htr T).1,
      fun lam' => (GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam' _ h k' hk' h3 htr T).2⟩
  have hsqb : ∀ h : GA D P.d,
      Bd p (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)) ((P.sq h : ℝ) : ℂ) := by
    intro h
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.d p Fact.out h
    rw [← hsq γ (Subgroup.subset_closure ⟨γ', h1⟩) 1 (one_mem _) h, mul_one]
    unfold Pair.sq
    rw [Complex.ofReal_sum]
    refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
    have hb := hcoord (γ * h) k (Subgroup.subset_closure h2) h3 T
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    exact hb.mul hb.conj
  have hfin : Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)))
      ((P.norm : ℝ) : ℂ) := by
    unfold Pair.norm
    refine finsum_induction (fun x : ℝ => Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) *
      ((p : ℝ) ^ v * (p : ℝ) ^ e))) (x : ℂ)) ?_ (fun x y hx hy => ?_) (fun x => ?_)
    · rw [Complex.ofReal_zero]
      exact Bd.zero (by positivity)
    · rw [Complex.ofReal_add]
      exact hx.add hy
    · rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
      exact (hgam _ hS.1 _ P.J_le _).mul (hsqb _)
  refine ⟨hfin.1, (hfin.2 lam).trans ?_⟩
  rw [← Real.rpow_add hp0, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  linarith

end GlobalTheory.NormVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBoundStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaPairNorm_padicValuation_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (N : ℕ) (B : ℝ), P.Small N B → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((P.norm : ℝ) : ℂ) ∈ Qbar ∧ ‖lamC lam ((P.norm : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ (3 * ((padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ))) := by
  first | exact @GlobalTheory.NormVal.norm_mem_and_le | exact GlobalTheory.NormVal.norm_mem_and_le | (intros; apply GlobalTheory.NormVal.norm_mem_and_le <;> assumption)
end
end

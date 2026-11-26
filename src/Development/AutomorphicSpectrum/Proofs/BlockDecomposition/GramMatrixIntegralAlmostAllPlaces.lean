module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlaces
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

private theorem tensorBasis_repr_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (c : R) (e : E) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m = c * algebraMap F R (b.repr e m) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.smul_def]

private theorem eq_sum_repr_tmul_basis {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (z : R ⊗[F] E) :
    z = ∑ k, ((Algebra.TensorProduct.basis R b).repr z k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem tensorBasis_repr_sum_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) {ι : Type} (s : Finset ι)
    (f : ι → R ⊗[F] E) (h : ∀ x ∈ s, ∀ m, (Algebra.TensorProduct.basis R b).repr (f x) m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (∑ x ∈ s, f x) m ∈ O := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact O.sum_mem fun x hx => h x hx m

private theorem tensorBasis_repr_tmul_mem_of_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (c : R) (e : E) (hc : c ∈ O)
    (he : ∀ m, algebraMap F R (b.repr e m) ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m ∈ O := by
  rw [tensorBasis_repr_tmul]
  exact O.mul_mem hc (he m)

private theorem tensorBasis_repr_mul_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R)
    (hb : ∀ k l m, algebraMap F R (b.repr (b k * b l) m) ∈ O) (z w : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O)
    (hw : ∀ m, (Algebra.TensorProduct.basis R b).repr w m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by
  rw [eq_sum_repr_tmul_basis b z, eq_sum_repr_tmul_basis b w, Finset.sum_mul_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun l _ m'' => ?_) m') m
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (O.mul_mem (hz k) (hw l)) (hb k l) m''

private theorem tensorBasis_repr_sigR_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (σ : E →ₐ[F] E)
    (hs : ∀ k m, algebraMap F R (b.repr (σ (b k)) m) ∈ O) (z : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ z) m ∈ O := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_repr_tmul_basis b z, map_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => ?_) m
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (hz k) (hs k) m'

theorem hermOf_sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ),
    2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn d b T hT
  have intF : ∀ t : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) t ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    intro t
    filter_upwards [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b t] with v hv
    have h0 := hv 0 (fun a i k => by simp)
    simpa [qR, hR, Formalism.UG.hform] using h0
  have hdiag := Filter.eventually_all.2 fun i : Fin n =>
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b ((1 / 2) * Algebra.trace F E (T i i))
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun m => intF _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k m,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => intF _
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ p q m,
      algebraMap F (Fv F v) (b.repr (J p q) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun m => intF _
  have h4 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j m,
      algebraMap F (Fv F v) (b.repr (T i j) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun m => intF _
  filter_upwards [hdiag, h1, h2, h3, h4] with v hd hb hs hJv hTv
  intro X hX
  clear intF hdiag h1 h2 h3 h4
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  unfold latH gramH
  refine ⟨fun i => ?_, fun i j _ k => ?_⟩
  · have hX' := hd i (fun _ => X i) (fun _ a k => hX i a k)
    convert hX' using 1
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, qR, Matrix.map_apply, map_sub, mul_sub]
    congr 1
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, map_mul]
  · let O : Subring (Fv F v) := (HeightOneSpectrum.adicCompletionIntegers F v).toSubring
    have gX : ∀ a p m, (Algebra.TensorProduct.basis (Fv F v) b).repr (X a p) m ∈ O := fun a p m => hX a p m
    have gI : ∀ e : E, (∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ O) →
        ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) e) m ∈ O := by
      intro e he m
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [tensorBasis_repr_tmul, one_mul]
      exact he m
    have gH : ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (hR (Fv F v) σ J (X i) (X j)) m ∈ O := by
      intro m
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply]
      exact tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun p _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun q _ m'' =>
        tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (fun m3 => tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (tensorBasis_repr_sigR_mem_of_repr_mem b O σ hs _ (gX i p))
          (gI _ (hJv p q)) m3) (gX j q) m'') m') m
    have gT := gI (T i j) (hTv i j)
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, Matrix.map_apply, map_sub,
      Finsupp.coe_sub, Pi.sub_apply]
    exact O.sub_mem (gT k) (gH k)

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlacesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_integral_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.hermOf_sub_gramH_mem_latH | exact GlobalTheory.CompanionTheory.SiegelND.Coef.hermOf_sub_gramH_mem_latH | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.hermOf_sub_gramH_mem_latH <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexEqCard
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeAct

theorem hint_mul_const {H : Type} [Group H] (K : Subgroup H) (v : H → ℂ) (c : ℂ) :
    hint K (fun z => v z * c) = hint K v * c := by
  by_cases hc : c = 0
  · subst hc
    simp [hint]
  have hS : rStab (fun z => v z * c) = rStab v := by
    ext k
    constructor
    · intro hk z
      exact mul_right_cancel₀ hc (hk z)
    · intro hk z
      show v (z * k) * c = v z * c
      rw [hk z]
  unfold hint
  rw [hS, mul_assoc]
  congr 1
  have e := smul_finsum c (fun q : H ⧸ rStab v ⊓ K => v q.out)
  simp only [smul_eq_mul] at e
  rw [mul_comm, e]
  exact finsum_congr fun q => mul_comm _ _

theorem relIndex_eq_card {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') : K'.relIndex K = X.card := by
  let φ : {x // x ∈ X} → K ⧸ K'.subgroupOf K := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ K'.subgroupOf K)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxy)
      exact Subtype.ext ((hX y.1 (hXK _ y.2)).unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  show Nat.card (K ⧸ K'.subgroupOf K) = _
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem finsum_left {G : Type} [Group G] (K' : Subgroup G) (φ : G → ℂ) (hφ : ∀ g, ∀ k ∈ K', φ (g * k) = φ g) (x : G) :
    ∑ᶠ q : G ⧸ K', φ (x * q.out) = ∑ᶠ q : G ⧸ K', φ q.out := by
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (G ⧸ K')))
  refine finsum_congr fun q => ?_
  have e : (MulAction.toPerm x : Equiv.Perm (G ⧸ K')) q = ((x * q.out : G) : G ⧸ K') := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [e]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (x * q.out)
  show φ (x * q.out) = φ ((x * q.out : G) : G ⧸ K').out
  rw [hs, hφ _ _ s.2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ind_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GLw a w × GLw b w) W)
    (u : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom))
    (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (g : GLw n w) :
    u.1.1 (blk h w m Y * g) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) • ρ m (u.1.1 g) := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ = GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) (GlobalTheory.LeviFubini.levH_blk h w m Y)
    simpa [GlobalTheory.LeviFubini.levH] using this
  have := GlobalTheory.SmGL.parInd_law _ _ u ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ g
  rw [hl] at this
  rw [GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf E a b w m]
  simpa using this

theorem hk_ind_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W), ∀ (f : GLw n w → ℂ), IsHk K' f → ∀ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X, ∀ lw : W →ₗ[ℂ] ℂ, lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m => phi3 h w f x y m * lw (ρ m (u.1.1 y)) := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX W _ _ ρ f hf u hu x hx lw
  have hfr : ∀ g, ∀ k ∈ K', f (g * k) = f g := fun g k hk => by
    simpa using hf.2.2.2 1 K'.one_mem k hk g
  have hur : ∀ g, ∀ k ∈ K', u.1.1 (g * k) = u.1.1 g := fun g k hk => by
    have h1 : GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ k u = u := (hu ⟨k, hk⟩).trans (one_smul ℂ u)
    exact congrArg (fun v : GlobalTheory.SmGL.IndSp _ _ => v.1.1 g) h1

  set φ : GLw n w → ℂ := fun g => f (x⁻¹ * g) * lw (u.1.1 g) with hφdef
  have hφr : ∀ g, ∀ k ∈ K', φ (g * k) = φ g := fun g k hk => by
    simp only [hφdef]
    rw [← mul_assoc, hfr _ k hk, hur g k hk]
  have hφc : HasCompactSupport φ := by
    have h1 : HasCompactSupport fun g => f (x⁻¹ * g) := hf.2.2.1.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
    exact h1.mul_right
  have hcard : K'.relIndex (GlobalTheory.LFun.KGL w (n := n)) = X.card := relIndex_eq_card _ K' X hXK hX
  have hX0 : X.card ≠ 0 := by
    obtain ⟨z, ⟨hz, -⟩, -⟩ := hX 1 (GlobalTheory.LFun.KGL w (n := n)).one_mem
    exact (Finset.card_pos.2 ⟨z, hz⟩).ne'
  have hX0' : (X.card : ℂ) ≠ 0 := by exact_mod_cast hX0

  let Ψ : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] ℂ :=
    { toFun := fun v => lw (v.1.1 x)
      map_add' := fun v v' => map_add lw _ _
      map_smul' := fun c v => map_smul lw c _ }
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen f hf.2.2.1
  have e1 : lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ᶠ q : GLw n w ⧸ K', φ (x * q.out) := by
    show Ψ (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u) = _
    unfold hk
    refine (Ψ.toAddMonoidHom.map_finsum (hfin.subset fun q hq h0 => hq (by
      have h0' : f q.out = 0 := h0
      show f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u = 0
      rw [h0', zero_smul]))).trans ?_
    refine finsum_congr fun q => ?_
    show Ψ (f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u) = _
    rw [map_smul]
    simp only [hφdef, inv_mul_cancel_left]
    rfl
  have e2 := GlobalTheory.CompanionTheory.HintSmaller.hint_eq_of_le (GlobalTheory.LFun.KGL w (n := n)) K' φ hle (fun k hk g => hφr g k hk)
    (by rw [hcard]; exact hX0) (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen φ hφc)
  have e3 := GlobalTheory.T.hecke_coset_sum_compact E n a b h w K' hopen hle hnorm X hXK hX φ hφr hφc
  rw [hcard] at e2
  have e4 : ∑ᶠ q : GLw n w ⧸ K', φ q.out =
      ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m =>
        hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
    have := e2.symm.trans e3
    exact mul_left_cancel₀ (inv_ne_zero hX0') this
  rw [e1, finsum_left K' φ hφr x, e4]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  funext m
  have e5 : (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      φ (blk h w m (Multiplicative.toAdd Y) * y)) = fun Y =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y) *
        (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * lw (ρ m (u.1.1 y))) := by
    funext Y
    simp only [hφdef]
    rw [ind_blk h w ρ u m _ y, map_smul, smul_eq_mul, mul_assoc]
  rw [e5, hint_mul_const]
  unfold phi3
  ring

end GlobalTheory.CompanionTheory.HeckeAct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecomposition
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM

def splitVec (F : Type) [Field F] [NumberField F] (ι : Type) :
    (ι → AF F) ≃ₜ+ (ι → Ainf F) × (ι → Af F) where
  toFun y := (fun i => (y i).1, fun i => (y i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => continuous_fst.comp (continuous_apply i)
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk ?_ ?_
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd

theorem map_split_eq_smul_prod : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)),
    m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) =
        c • μ₁.prod μ₂ := by
  intro F _ _ ι _ m μ₁ μ₂ hm h₁ h₂
  haveI : SecondCountableTopology (Af F) := Formalism.IndefR.Eqv.G5.af_secondCountable
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) :=
    inferInstanceAs (SecondCountableTopology (Ainf F × Af F))
  have hH : (m.map (splitVec F ι)).IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map m (splitVec F ι)
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (m.map (splitVec F ι)) (μ₁.prod μ₂)
  refine ⟨(Measure.addHaarScalarFactor (m.map (splitVec F ι)) (μ₁.prod μ₂) : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast hc.ne'
  · have h := Measure.isAddLeftInvariant_eq_smul (m.map (splitVec F ι)) (μ₁.prod μ₂)
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecompositionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_haar_product_decomposition : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)), m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFinite
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord

section Coords

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def tupCrd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ (Fin n × Fin M × Fin d → R) where
  toFun X p := (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2
  invFun Y a i := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm_apply_apply (X a i)
  right_inv Y := by
    funext p
    obtain ⟨a, i, k⟩ := p
    exact congrFun ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).apply_symm_apply fun k => Y (a, i, k)) k
  map_add' X Y := by
    funext p
    simp
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2.2).comp ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).continuous.comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1)))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.continuous.comp
      (continuous_pi fun k => continuous_apply (a, i, k))

theorem tupCrd_apply (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) (X : Fin n → Fin M → R ⊗[F] E)
    (p : Fin n × Fin M × Fin d) :
    tupCrd R b n M X p = (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2 := rfl

end Coords

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem tupCrd_projInf {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    tupCrd (Ainf F) b n M (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projInf X) = fun p => (tupCrd (AF F) b n M X p).1 := by
  funext p
  rw [tupCrd_apply, tupCrd_apply]
  exact repr_map (fstA F) b (X p.1 p.2.1) p.2.2

theorem tupCrd_projFin {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    tupCrd (Af F) b n M (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projFin X) = fun p => (tupCrd (AF F) b n M X p).2 := by
  funext p
  rw [tupCrd_apply, tupCrd_apply]
  exact repr_map (sndA F) b (X p.1 p.2.1) p.2.2

def splitHomeo (F : Type) [Field F] [NumberField F] (ι : Type) :
    (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun y := (fun i => (y i).1, fun i => (y i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv y := rfl
  right_inv p := rfl
  continuous_toFun :=
    (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun :=
    continuous_pi fun i => ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)

end Split

theorem map_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure →
  ∃ (μ₁ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (μ₂ : Measure (Fin n → Fin M → Af F ⊗[F] E)) (c : ℝ≥0∞),
    μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ SFinite μ₁ ∧ SFinite μ₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    dx.map (fun X => (projInf X, projFin X)) = c • μ₁.prod μ₂ := by
  intro F E _ _ _ _ _ σ hCM M n dx hdx
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasis F E
  obtain ⟨tA, -, sA, -, -, -, -, hBA, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  obtain ⟨tI, -, sI, -, -, -, -, hBI, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  obtain ⟨tF, -, sF, -, -, -, -, hBF, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  haveI := hBA n M
  haveI := hBI n M
  haveI := hBF n M
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let ι := Fin n × Fin M × Fin (Module.finrank F E)
  let e := tupCrd (AF F) b n M
  let eI := tupCrd (Ainf F) b n M
  let eF := tupCrd (Af F) b n M
  let eA : (Fin n → Fin M → AF F ⊗[F] E) ≃+ (ι → AF F) := e
  have hm : (dx.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map dx eA e.continuous e.symm.continuous
  let m₁ : Measure (ι → Ainf F) := Measure.addHaar
  let m₂ : Measure (ι → Af F) := Measure.addHaar
  haveI : m₁.IsAddHaarMeasure := by dsimp only [m₁]; infer_instance
  haveI : m₂.IsAddHaarMeasure := by dsimp only [m₂]; infer_instance
  haveI : SFinite m₁ := by dsimp only [m₁]; infer_instance
  haveI : SFinite m₂ := by dsimp only [m₂]; infer_instance
  obtain ⟨c, -, hcT, hc⟩ := GlobalTheory.T.adele_haar_product_decomposition F ι (dx.map e) m₁ m₂ hm inferInstance inferInstance
  let S := splitHomeo F ι
  let H : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ
      (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) :=
    e.toHomeomorph.trans (S.trans (eI.symm.toHomeomorph.prodCongr eF.symm.toHomeomorph))
  have hH : (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) = H := by
    funext X
    refine Prod.ext ?_ ?_
    · show _ = eI.symm (fun i => (e X i).1)
      rw [show (fun i => (e X i).1) = eI (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projInf X) from (tupCrd_projInf b X).symm]
      exact (eI.symm_apply_apply _).symm
    · show _ = eF.symm (fun i => (e X i).2)
      rw [show (fun i => (e X i).2) = eF (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projFin X) from (tupCrd_projFin b X).symm]
      exact (eF.symm_apply_apply _).symm
  have hc' : (dx.map e).map S = c • m₁.prod m₂ := hc
  have he : Measurable e := e.continuous.measurable
  have hPI : Measurable eI.symm := eI.symm.continuous.measurable
  have hPF : Measurable eF.symm := eF.symm.continuous.measurable
  refine ⟨m₁.map eI.symm, m₂.map eF.symm, c, ?_, ?_, inferInstance, inferInstance, hcT, ?_, ?_⟩
  · let eIA : (ι → Ainf F) ≃+ (Fin n → Fin M → Ainf F ⊗[F] E) := eI.symm
    exact AddEquiv.isAddHaarMeasure_map m₁ eIA eI.symm.continuous eI.continuous
  · let eFA : (ι → Af F) ≃+ (Fin n → Fin M → Af F ⊗[F] E) := eF.symm
    exact AddEquiv.isAddHaarMeasure_map m₂ eFA eF.symm.continuous eF.continuous
  · rw [hH]
    exact H.measurableEmbedding
  · rw [hH, Measure.map_prod_map m₁ m₂ hPI hPF, ← Measure.map_smul, ← hc',
      Measure.map_map (hPI.prodMap hPF) S.continuous.measurable,
      Measure.map_map ((hPI.prodMap hPF).comp S.continuous.measurable) he]
    rfl
    exact (hPI.prodMap hPF).aemeasurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFiniteStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_splits_as_arch_times_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure →
  ∃ (μ₁ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (μ₂ : Measure (Fin n → Fin M → Af F ⊗[F] E)) (c : ℝ≥0∞),
    μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ SFinite μ₁ ∧ SFinite μ₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    dx.map (fun X => (projInf X, projFin X)) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | exact GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBound
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCount

theorem exists_cone_lower (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ l : ℝ, 0 < l ∧ ∀ t ∈ cone r c, ∀ i, l ≤ t i := by
  set c' : ℝ := min c 1 with hc'
  have h0 : 0 < c' := lt_min hc one_pos
  have h1 : c' ≤ 1 := min_le_right _ _
  have h2 : c' ≤ c := min_le_left _ _
  have key : ∀ t ∈ cone r c, ∀ (m : ℕ) (i : Fin r), i.val + m + 1 = r → c' ^ (m + 1) ≤ t i := by
    intro t ht m
    induction m with
    | zero =>
      intro i hi
      simpa using h2.trans (ht.2.2 i (by omega))
    | succ m ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have a1 := ih ⟨i.val + 1, hj⟩ (by simp only; omega)
      have a2 := ht.2.1 i ⟨i.val + 1, hj⟩ rfl
      have a3 : 0 < t ⟨i.val + 1, hj⟩ := ht.1 _
      calc c' ^ (m + 1 + 1) = c' * c' ^ (m + 1) := by ring
        _ ≤ c' * t ⟨i.val + 1, hj⟩ := by gcongr
        _ ≤ c * t ⟨i.val + 1, hj⟩ := by gcongr
        _ ≤ t i := a2
  refine ⟨c' ^ r, by positivity, fun t ht i => ?_⟩
  have hi := i.2
  obtain ⟨m, hm⟩ : ∃ m, i.val + m + 1 = r := ⟨r - i.val - 1, by omega⟩
  exact (pow_le_pow_of_le_one h0.le h1 (by omega)).trans (key t ht m i hm)

theorem le_prod_max {r : ℕ} (t : Fin r → ℝ) (i : Fin r) : max (t i) 1 ≤ ∏ k, max (t k) 1 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by positivity) (Finset.one_le_prod₀ fun v _ => le_max_right _ _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem eq_of_act (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (u v : Fin r → ℂ)
    (hX : M * X.map τ = X.map τ * diagonal u) (hY : M * Y.map τ = Y.map τ * diagonal v)
    (hZ : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      M *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) :
    M = X.map τ * diagonal u * (Formalism.UG.cT (σ : E →+* E) Y * J).map τ +
      Y.map τ * diagonal v * (Formalism.UG.cT (σ : E →+* E) X * J).map τ +
      (1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)).map τ := by
  set Ax := Formalism.UG.cT (σ : E →+* E) X * J with hAx
  set Ay := Formalism.UG.cT (σ : E →+* E) Y * J with hAy
  have xx : Ax * X = 0 := hW.xx
  have xy : Ax * Y = 1 := hW.xy
  have yy : Ay * Y = 0 := hW.yy
  have yx : Ay * X = 1 := by
    have e := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    have cc : ∀ Z : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z :=
      fun Z => Matrix.ext fun i j => sigma_sigma h _
    have hJ' : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ', Formalism.UG.cT_one, ← Matrix.mul_assoc] at e
  set P := 1 - X * Ay - Y * Ax with hP
  have hxP : Ax * P = 0 := by
    simp only [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, xx, xy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hyP : Ay * P = 0 := by
    simp only [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, yx, yy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hMP : M * P.map τ = P.map τ := by
    ext i j
    have e := hZ (fun a => P a j) (funext fun k => congrFun (congrFun hxP k) j) (funext fun k => congrFun (congrFun hyP k) j)
    exact congrFun e i
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = X.map τ * Ay.map τ + Y.map τ * Ax.map τ + P.map τ := by
    have : (1 : Matrix (Fin n) (Fin n) E) = X * Ay + Y * Ax + P := by simp [hP]
    have e := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map τ) this
    simpa [Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_one] using e
  calc M = M * 1 := (Matrix.mul_one _).symm
    _ = _ := by
      rw [h1, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, hY, hMP]

theorem exists_entry_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Matrix (Fin n) (Fin n) ℂ) (u v : Fin r → ℂ) (S : ℝ), 1 ≤ S → (∀ k, ‖u k‖ ≤ S) →
      (∀ k, ‖v k‖ ≤ S) → M * X.map τ = X.map τ * diagonal u → M * Y.map τ = Y.map τ * diagonal v →
      (∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        M *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) → ∀ i j, ‖M i j‖ ≤ c * S := by
  set A := X.map τ
  set A' := Y.map τ
  set B := (Formalism.UG.cT (σ : E →+* E) Y * J).map τ
  set B' := (Formalism.UG.cT (σ : E →+* E) X * J).map τ
  set Q := (1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)).map τ
  let f : Fin n → Fin n → ℝ := fun i j => ∑ k, ‖A i k‖ * ‖B k j‖ + ∑ k, ‖A' i k‖ * ‖B' k j‖ + ‖Q i j‖
  have hf : ∀ i j, 0 ≤ f i j := fun i j => by positivity
  refine ⟨∑ i, ∑ j, f i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hf i j,
    fun M u v S hS hu hv hX hY hZ i j => ?_⟩
  have hd : ∀ (P : Matrix (Fin n) (Fin r) ℂ) (R : Matrix (Fin r) (Fin n) ℂ) (d : Fin r → ℂ), (∀ k, ‖d k‖ ≤ S) →
      ‖(P * diagonal d * R) i j‖ ≤ (∑ k, ‖P i k‖ * ‖R k j‖) * S := fun P R d hd => by
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Matrix.mul_diagonal, norm_mul, norm_mul]
    have := hd k
    calc ‖P i k‖ * ‖d k‖ * ‖R k j‖ ≤ ‖P i k‖ * S * ‖R k j‖ := by gcongr
      _ = _ := by ring
  have e := eq_of_act h hJ hW τ M u v hX hY hZ
  have h1 : ‖M i j‖ ≤ f i j * S := by
    rw [e, Matrix.add_apply, Matrix.add_apply]
    refine (norm_add₃_le).trans ?_
    have := hd A B u hu
    have := hd A' B' v hv
    have hq : ‖Q i j‖ ≤ ‖Q i j‖ * S := le_mul_of_one_le_right (norm_nonneg _) hS
    simp only [f, add_mul]
    linarith
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hf i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (fun j _ => hf i j) (Finset.mem_univ j)

theorem exists_torus_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) {w : InfinitePlace F} (τ : EmbOver E w) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J) (S : ℝ), (∀ k, 0 < t k) → 1 ≤ S → (∀ k, t k ≤ S) →
      (∀ k, (t k)⁻¹ ≤ S) → IsTorusElt σ J X Y t a → ∀ i j,
        ‖archMat σ J τ (projArch σ J w a) i j‖ ≤ c * S ∧ ‖archMat σ J τ (projArch σ J w a⁻¹) i j‖ ≤ c * S := by
  obtain ⟨c, hc, hb⟩ := exists_entry_bound h hJ hW τ.1
  refine ⟨c, hc, fun t a S ht hS h1 h2 ha i j => ?_⟩
  obtain ⟨hX, hY, hZ⟩ := ha.2 w τ
  set M := archMat σ J τ (projArch σ J w a) with hM
  set M' := archMat σ J τ (projArch σ J w a⁻¹) with hM'
  have hMM : M' * M = 1 := by
    rw [hM, hM', ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hn : ∀ k, ‖(t k : ℂ)‖ ≤ S := fun k => by
    rw [Complex.norm_real, Real.norm_of_nonneg (ht k).le]; exact h1 k
  have hn' : ∀ k, ‖(t k : ℂ)⁻¹‖ ≤ S := fun k => by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (ht k).le]; exact h2 k
  have hD : diagonal (fun i => (t i : ℂ)) * diagonal (fun i => (t i : ℂ)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun k => mul_inv_cancel₀ (by exact_mod_cast (ht k).ne'))
  have hD' : diagonal (fun i => (t i : ℂ)⁻¹) * diagonal (fun i => (t i : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun k => inv_mul_cancel₀ (by exact_mod_cast (ht k).ne'))
  have hX' : M' * X.map τ.1 = X.map τ.1 * diagonal (fun i => (t i : ℂ)⁻¹) := by
    calc M' * X.map τ.1 = M' * (X.map τ.1 * (diagonal (fun i => (t i : ℂ)) * diagonal (fun i => (t i : ℂ)⁻¹))) := by
          rw [hD, Matrix.mul_one]
      _ = (M' * M) * X.map τ.1 * diagonal (fun i => (t i : ℂ)⁻¹) := by
          rw [Matrix.mul_assoc M', hX]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hMM, Matrix.one_mul]
  have hY' : M' * Y.map τ.1 = Y.map τ.1 * diagonal (fun i => (t i : ℂ)) := by
    calc M' * Y.map τ.1 = M' * (Y.map τ.1 * (diagonal (fun i => (t i : ℂ)⁻¹) * diagonal (fun i => (t i : ℂ)))) := by
          rw [hD', Matrix.mul_one]
      _ = (M' * M) * Y.map τ.1 * diagonal (fun i => (t i : ℂ)) := by
          rw [Matrix.mul_assoc M', hY]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hMM, Matrix.one_mul]
  have hZ' : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      M' *ᵥ (fun i => τ.1 (z i)) = fun i => τ.1 (z i) := fun z z1 z2 => by
    conv_lhs => rw [← hZ z z1 z2]
    rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  exact ⟨hb M _ _ S hS hn hn' hX hY hZ i j, hb M' _ _ S hS hn' hn hX' hY' hZ' i j⟩

theorem torus_count : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ C : Set (GA D V), IsCompact C →
    ∃ (A : ℕ) (B : ℝ), ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a →
      {δ : GF V | a⁻¹ * rat V δ * a ∈ C}.Finite ∧
      (({δ : GF V | a⁻¹ * rat V δ * a ∈ C}.ncard : ℕ) : ℝ) ≤ B * (∏ i, max (t i) 1) ^ A := by
  intro D V r X Y hW c hc C hC
  obtain ⟨hcm, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  let θ : Formalism.IndefR.Datum.InfFam D := fun ρ => infProj (embOverOf D ρ)
  have hθ : IsInfFam θ := isInfFam_infProj D
  obtain ⟨N, hN⟩ := GlobalTheory.RatCount.ncard_rational_le D θ V hθ C hC
  obtain ⟨C₀, hC₀⟩ := hN 1
  obtain ⟨l, hl, hlow⟩ := exists_cone_lower r hc
  choose cb hcb0 hcb using fun ρ => exists_torus_bound hcm (hJ V) hW (embOverOf D ρ)
  set K : ℝ := ∑ ρ, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (cb ρ + cb ρ) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun ρ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (hcb0 ρ) (hcb0 ρ)
  set L : ℝ := max 1 l⁻¹ with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  refine ⟨N, |C₀| * (K * L) ^ N, fun t ht a ha => ?_⟩
  set T : ℝ := ∏ i, max (t i) 1 with hT
  have hT1 : 1 ≤ T := Finset.one_le_prod₀ fun v _ => le_max_right _ _
  have hS1 : 1 ≤ L * T := one_le_mul_of_one_le_of_one_le hL1 hT1
  have hs1 : ∀ k, t k ≤ L * T := fun k =>
    ((le_max_left _ _).trans (le_prod_max t k)).trans (le_mul_of_one_le_left (by linarith) hL1)
  have hs2 : ∀ k, (t k)⁻¹ ≤ L * T := fun k =>
    ((inv_anti₀ hl (hlow t ht k)).trans (le_max_right _ _)).trans (le_mul_of_one_le_right (by linarith) hT1)
  have hnorm : Formalism.L2.Theta.normInf θ V a ≤ K * (L * T) := by
    unfold Formalism.L2.Theta.normInf
    rw [hK, Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hb := hcb ρ t a (L * T) ht.1 hS1 hs1 hs2 ha i j
    have e : ∀ g : GA D V, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) g =
        archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) g) := fun g =>
      infMat_infProj V.gram hcm (embOverOf D ρ) g
    rw [e, e, add_mul]
    exact add_le_add hb.1 hb.2
  have h0 := GlobalTheory.RatCount.normInf_nonneg θ V a
  have hsub : rat V '' {δ : GF V | a⁻¹ * rat V δ * a ∈ C} ⊆
      {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ C, γ * a = 1 * a * o} := by
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨?_, _, hδ, by group⟩
    exact (range_ratEmb D.sp.cm.sig V.gram).le ⟨δ, rfl⟩
  obtain ⟨hf, hcard⟩ := hC₀ a ha.1 a
  have hinj : Function.Injective (rat V) := ratEmb_injective _ _
  refine ⟨Set.Finite.of_finite_image (hf.subset hsub) hinj.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  calc _ ≤ (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ C, γ * a = 1 * a * o}.ncard : ℕ) : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hf
    _ ≤ _ := by simpa using hcard
    _ ≤ |C₀| * Formalism.L2.Theta.normInf θ V a ^ N := by gcongr; exact le_abs_self _
    _ ≤ |C₀| * (K * (L * T)) ^ N := by gcongr
    _ = _ := by rw [mul_assoc, mul_pow, mul_pow]; ring

end GlobalTheory.CompanionTheory.TorusCount

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBoundStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_points_in_siegel_set_bound : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ C : Set (GA D V), IsCompact C →
    ∃ (A : ℕ) (B : ℝ), ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a →
      {δ : GF V | a⁻¹ * rat V δ * a ∈ C}.Finite ∧
      (({δ : GF V | a⁻¹ * rat V δ * a ∈ C}.ncard : ℕ) : ℝ) ≤ B * (∏ i, max (t i) 1) ^ A := by
  first | exact @GlobalTheory.CompanionTheory.TorusCount.torus_count | exact GlobalTheory.CompanionTheory.TorusCount.torus_count | (intros; apply GlobalTheory.CompanionTheory.TorusCount.torus_count <;> assumption)
end
end

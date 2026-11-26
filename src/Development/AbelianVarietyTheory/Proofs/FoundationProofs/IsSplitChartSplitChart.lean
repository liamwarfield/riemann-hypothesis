module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
noncomputable section

namespace GlobalTheory.LFun.SplitTie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.LFun.SplitChart
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

section Transport

def glEquiv {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (ψ : A ≃+* B) : GL (Fin n) A ≃* GL (Fin n) B :=
  Units.mapEquiv ψ.mapMatrix.toMulEquiv

variable {ψ : Fv F v ≃+* w.adicCompletion E}

theorem mem_KGL_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (x : GL (Fin n) (Fv F v)) :
    x ∈ KGL v (n := n) ↔ glEquiv n ψ x ∈ KGL w (n := n) := (bc_mem_KGL_iff h3).symm

theorem Tj_comp (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (ϖ : Fv F v) (j : ℕ) :
    Tj ℂ n (Ov E w) (ψ ϖ) j ∘ glEquiv n ψ = Tj ℂ n (Ov F v) ϖ j := by
  have hd : diagJ n (ψ ϖ) j = ψ.mapMatrix (diagJ n ϖ j) := by
    rw [RingEquiv.mapMatrix_apply, diagJ, diagJ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  have hv : ∀ x : GL (Fin n) (Fv F v), (glEquiv n ψ x).1 = ψ.mapMatrix x.1 := fun _ => rfl
  refine (funext fun g => (Set.indicator_comp_right (g := 1) (glEquiv n ψ)).symm).trans (congrArg (Set.indicator · 1) ?_)
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, (glEquiv n ψ).surjective.exists, ← mem_KGL_iff h3, hd, hv, ← map_mul,
    EmbeddingLike.apply_eq_iff_eq]

theorem isSatVecGL_comp_symm (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (hq : qV E w = qV F v)
    (ρ : Representation ℂ (GL (Fin n) (Fv F v)) V) (x : V) (B : Multiset ℂˣ) :
    IsSatVecGL w (ρ.comp (glEquiv n ψ).symm.toMonoidHom) x B ↔ IsSatVecGL v ρ x B := by
  unfold IsSatVecGL
  rw [mem_fixed_comp_symm (glEquiv n ψ) (mem_KGL_iff h3), hq, ψ.surjective.forall]
  refine and_congr_right fun _ => and_congr_right fun hx => and_congr_right fun _ => forall_congr' fun ϖ => ?_
  have hu : IsUnifV E w (ψ ϖ) ↔ IsUnifV F v ϖ := by unfold IsUnifV; rw [h3]
  rw [hu]
  refine forall_congr' fun hϖ => forall₂_congr fun j _ => ?_
  rw [heckeVec_comp_symm (glEquiv n ψ) (mem_KGL_iff h3) (Tj_mem_hecke (hu.2 hϖ) j).1 hx, Tj_comp h3]

end Transport

variable [Algebra F E] {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}

section Compl

variable (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)

theorem complMap_bijective : Function.Bijective (complMap hw) := by
  obtain ⟨ψ, h1, -⟩ := exists_equiv_complMap τ hw
  exact (funext h1 : ⇑ψ = complMap hw) ▸ ψ.bijective

theorem valued_complMap (a : Fv F v) : Valued.v (complMap hw a) = Valued.v a := by
  obtain ⟨ψ, h1, -, h3, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h3]

theorem complMap_apply_emb (x : E) : complMap hw (τ x) = algebraMap E _ x := by
  obtain ⟨ψ, h1, h2, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h2]

def complEquiv : Fv F v ≃+* (splitPrime τ).adicCompletion E :=
  RingEquiv.ofBijective (complMap hw) (complMap_bijective τ hw)

theorem complEquiv_apply (a : Fv F v) : complEquiv τ hw a = complMap hw a := rfl

theorem toCompl_eq_complMap (y : Fv F v ⊗[F] E) : toCompl hw y = complMap hw (splitProj τ y) :=
  toCompl_eq (ψ := complEquiv τ hw) (fun _ => rfl) (complMap_apply_emb τ hw) y

theorem qV_splitPrime : qV E (splitPrime τ) = qV F v := absNorm_splitPrime τ

end Compl

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)
  (β : GL (Fin n) (Fv F v))

variable {τ β}

variable (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β)
include hL hβ

end GlobalTheory.LFun.SplitTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

theorem eq_one_of_forall_norm_pow_sub_one_le {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

theorem nonarchimedeanGroup_of_isCompact_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H] {K : Subgroup H} (hc : IsCompact (K : Set H)) (ho : IsOpen (K : Set H)) :
    NonarchimedeanGroup H :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : NonarchimedeanGroup K := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  NonarchimedeanGroup.nonarchimedean_of_emb K.subtype ho.isOpenEmbedding_subtypeVal

section General

variable {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ}

variable [TopologicalSpace G] [ContinuousMul G]

end General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

section Groups

variable {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem totallyDisconnectedSpace_GLoc (v : HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (GLoc σ J v) := by
  haveI : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
    exact e.symm.totallyDisconnectedSpace
  haveI : TotallyDisconnectedSpace (Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin m → Fin m → Fv F v ⊗[F] E))
  exact ⟨isTotallyDisconnected_of_image (f := fun g => (matHom _ σ J g).1)
    (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).continuousOn
    (Units.val_injective.comp (matHom_injective _ σ J)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem totallyDisconnectedSpace_GFin : TotallyDisconnectedSpace (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GLoc σ J
  ⟨isTotallyDisconnected_of_image (f := fun g v => projFinLoc σ J v g)
    (continuous_pi fun v => continuous_projFinLoc σ J v).continuousOn
    (fun _ _ e => GFin_ext σ J (congrFun e)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem nonarchimedeanGroup_GLoc (v : HeightOneSpectrum (𝓞 F)) : NonarchimedeanGroup (GLoc σ J v) :=
  haveI := totallyDisconnectedSpace_GLoc σ J v
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_stabLoc σ J (stdLattice E m) v)
    (isOpen_stabLoc σ J (stdLattice E m) v)

theorem nonarchimedeanGroup_GFin : NonarchimedeanGroup (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GFin σ J
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_levelOffFin σ J (stdLattice E m) ∅)
    (isOpen_levelOffFin_empty σ J (stdLattice E m))

variable {σ J}

end Groups

variable {σ} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L]

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Record

end GlobalTheory.Doubling

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev Ser : Type := (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) → GA D (Wc D i) → ℂ

def kernA (t : T0) (h : GA D (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i where
  toFun w v := singleSeries R i (R.ωP i t) (R.vP i t) h ((R.cV i).ρ h⁻¹ w) v
  map_add' w w' := by
    funext v g
    simp [singleSeries, Datum.thetaKO]
  map_smul' c w := by
    funext v g
    simp [singleSeries, Datum.thetaKO]

def kern (t : T0) (h : Bridge.Gf (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i :=
  kernA R i t (MonoidHom.mem_range.1 h.2).choose

def DatumType (t : T0) : Prop :=
  ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ →
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' →
    R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t

def GoodLiftOnto (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) : Prop :=
  ∀ θ, OnTies.IsClassSum R i t U ψ ph θ →
    (R.FW i).Wgood U ψ (fun g => (idemOf A.X).coeff g) ≤
      LinearMap.range ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ θ)

end GlobalTheory.TraceIncl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem hecke_induction {p : (G → ℂ) → Prop} (h0 : p 0)
    (hadd : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, p f → p f' → p (f + f'))
    (hind : ∀ (r : ℂ) (g : G), p (r • dosetInd ℂ K g)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : p f := by
  classical
  obtain ⟨e, he⟩ := Final.HeckeBasis G K ℂ
  suffices ∀ a, p (e.symm a) by simpa using this (e ⟨f, hf⟩)
  intro a
  induction a using Finsupp.induction_linear with
  | zero => simpa using h0
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ (e.symm a).2 _ (e.symm b).2 ha hb
  | single c r =>
    obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk K K g = c := Quotient.exists_rep c
    convert hind r g
    funext x
    rw [← he, e.apply_symm_apply, Finsupp.single_apply, Pi.smul_apply, dosetInd, Set.indicator_apply]
    have : DoubleCoset.mk K K g = DoubleCoset.mk K K x ↔ x ∈ DoubleCoset.doubleCoset g (K : Set G) K := by
      rw [DoubleCoset.eq, DoubleCoset.mem_doubleCoset]; rfl
    by_cases hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) K
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx]

theorem heckeVec_add (hK : IsCommensurated K) (ρ : Representation ℂ G V) {f f' : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (hf' : f' ∈ Hecke ℂ K) (x : V) : heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  simp only [heckeVec, Pi.add_apply, add_smul]
  exact finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)

theorem heckeVec_smul (hK : IsCommensurated K) (ρ : Representation ℂ G V) (r : ℂ) {f : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (x : V) : heckeVec ρ K (r • f) x = r • heckeVec ρ K f x := by
  simp only [heckeVec, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact (smul_finsum' r (finite_heckeVec hK hf ρ x)).symm

theorem dosetInd_comp (e : G ≃* H) {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') (t : H) :
    dosetInd ℂ K' t ∘ e = dosetInd ℂ K (e.symm t) := by
  funext g
  have : e g ∈ DoubleCoset.doubleCoset t (K' : Set H) K' ↔ g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨e.symm a, (hK _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), e.injective (by simpa using h)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨e a, (hK _).1 ha, e b, (hK _).1 hb, by simp⟩
  by_cases hg : g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K
  · simp [dosetInd, hg, this.2 hg]
  · simp [dosetInd, hg, mt this.1 hg]

theorem dosetInd_mul {a b : G} (ha : a ∈ K) (hb : b ∈ K) (t : G) : dosetInd ℂ K (a * t * b) = dosetInd ℂ K t := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, rfl⟩)]

end Generic

section Unitary

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
  {σ : w.adicCompletion E →+* w.adicCompletion E} {n q : ℕ} {ϖ : w.adicCompletion E}
  {V : Type} [AddCommGroup V] [Module ℂ V]

open GlobalTheory.InertThetaCompare in
theorem cartanU (hU : IsUnramInv ϖ σ q) (g : GU σ n) : ∃ (d : Fin n → ℤ) (t : GU σ n), Antitone d ∧
    t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  have hϖ : IsUnifV E w ϖ := hU.2.2.2.1
  obtain ⟨d, hd, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp E w n ϖ (mem_Ov_of_isUnifV hϖ) hϖ g.1
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  have hh' : h ∈ GLint (Fin n) (Ov E w) := hh
  have hd' : ∀ i : Fin n, (List.ofFn d).getD i.1 0 = d i := fun i => by simp [List.getD_eq_getElem?_getD]
  have hG : Good n (List.ofFn d) := good_of_unitary hU (π := ϖ) hϖ (by simp)
    (List.pairwise_ofFn.2 fun i j hij => hd hij.le)
    (GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eh) g.2)
    ⟨h * k₁, mul_mem hh' h₁, k₂ * h⁻¹, mul_mem h₂ (inv_mem hh'), by
      simp only [Units.val_mul, e, hd', inv_inv, Matrix.mul_assoc]; rfl⟩
  obtain ⟨t, ht, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => ϖ ^ (List.ofFn d).getD i.1 0) fun i => by
    rw [map_zpow₀, hU.2.2.1, hG.rev, ← zpow_add₀ (unif_ne_zero hU), add_neg_cancel, zpow_zero]
  simp only [hd'] at ht
  exact ⟨d, t, hd, ht, dc_GU hU (a := k₁) (b := k₂) h₁ h₂ (Units.ext (by simp only [Units.val_mul, ht]; exact e))⟩

theorem isSatVecU_of_diag (hU : IsUnramInv ϖ σ q) {ρ : Representation ℂ (GU σ n) V} {x : V} {α : Fin (n / 2) → ℂˣ}
    (h0 : x ≠ 0) (hx : x ∈ fixed ρ (KU σ n))
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      heckeVec ρ (KU σ n) (dosetInd ℂ (KU σ n) t) x = SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) • x) :
    IsSatVecU ϖ q ρ x α := by
  obtain ⟨y, hy⟩ := (hasSatU_psFunU hU α).exists_vec
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hm := Final.DosetIndMem _ (KU σ n) ℂ
  refine ⟨h0, hx, fun f hf => ?_⟩
  refine hecke_induction (K := KU σ n)
    (p := fun f => heckeVec ρ (KU σ n) f x = SatU ϖ q f (fun i => (α i : ℂ)) • x) ?_ ?_ ?_ hf
  · simp [heckeVec, SatU]
  · intro f hf f' hf' h1 h2
    have := hy.2.2 _ (add_mem hf hf')
    rw [heckeVec_add hK _ hf hf', hy.2.2 _ hf, hy.2.2 _ hf', ← add_smul] at this
    rw [heckeVec_add hK _ hf hf', h1, h2, ← add_smul, smul_left_injective ℂ hy.1 this]
  · intro r g
    obtain ⟨d, t, hd, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
    rw [dosetInd_mul h₁ h₂]
    have := hy.2.2 _ (Submodule.smul_mem _ r (hm t))
    rw [heckeVec_smul hK _ r (hm t), hy.2.2 _ (hm t), smul_smul] at this
    rw [heckeVec_smul hK _ r (hm t), h d t hd ht, smul_smul, smul_left_injective ℂ hy.1 this]

end Unitary

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

def IsEigenSys (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (c : List ℤ → ℂ) : Prop :=
  ∀ (a : GL (Fin n) (w.adicCompletion E)) (g : GLoc σ J v) (d : Fin n → ℤ) (u : Fin n → w.adicCompletion E),
    IsFrameAt w L a → Antitone d → (∀ i, Valued.v (u i) = WithZero.exp (-d i)) →
    (a⁻¹ * locMat σ J h g * a).1 = Matrix.diagonal u →
    heckeVec ρ (stabLoc σ J L v) (dosetInd ℂ (stabLoc σ J L v) g) x = c (List.ofFn d) • x

variable {σ J L} {h : w.under (𝓞 F) = v} {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {c : List ℤ → ℂ}
  {B : Multiset ℂˣ}

theorem IsEigenSys.split (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)} (he : IsSplitChart σ J L h e) {ϖ : w.adicCompletion E}
    (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) x =
      c (List.replicate j 1 ++ List.replicate (n - j) 0) • x := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let t : GL (Fin n) (w.adicCompletion E) := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (by
    rw [diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0])
  have ht : Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (KGL w (n := n)) t := by
    rw [Tj, dosetInd]
    congr 1
    ext g
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, Units.ext e⟩,
      fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, congrArg Units.val e⟩⟩
  obtain ⟨⟨a, ha, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Tj_mem_hecke hϖ j).1 hx, ht, dosetInd_comp e e2,
    hc a (e.symm t) (fun i => if i.1 < j then 1 else 0) (fun i => if i.1 < j then ϖ else 1) ha
      (fun i k hik => ?_) (fun i => ?_) (by rw [← e1, e.apply_symm_apply]; rfl)]
  · congr 2
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    by_cases hi : i < j <;> simp [hi, List.getElem_append]
  · have : i.1 ≤ k.1 := hik
    dsimp only
    split_ifs <;> omega
  · split_ifs
    · exact hϖ
    · simp

theorem IsEigenSys.inert (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {τ : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU τ n} (he : IsInertChart σ J L h τ e)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {d : Fin n → ℤ} {t : GU τ n} (hd : Antitone d)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KU τ n) (dosetInd ℂ (KU τ n) t) x = c (List.ofFn d) • x := by
  obtain ⟨-, ⟨a, ha, -, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Final.DosetIndMem _ _ ℂ t).1 hx, dosetInd_comp e e2,
    hc a (e.symm t) d _ ha hd (fun i => ?_) (by rw [← e1, e.apply_symm_apply, ht])]
  rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
  simp

theorem IsEigenSys.isSysParam (hc : IsEigenSys σ J L h ρ x c) (hB : IsParamVec σ J L h ρ x B) :
    IsSysParam σ n h c B := by
  have hx := hB.mem_fixed
  rcases hB with ⟨hv, e, he, hB⟩ | ⟨hw, τ, ϖ, e, α, hU, he, hB, rfl⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    exact Or.inl ⟨hv, hB.2.2.1, fun j hj =>
      smul_left_injective ℂ hB.1 ((hc.split hx he hϖ hj).symm.trans (hB.2.2.2 ϖ hϖ j hj))⟩
  · exact Or.inr ⟨hw, τ, ϖ, α, hU, he.1, rfl, fun d t hd ht => smul_left_injective ℂ hB.1
      ((hc.inert hx he hU.2.2.2.1 hd ht).symm.trans (hB.2.2 _ (Final.DosetIndMem _ _ ℂ t)))⟩

theorem IsEigenSys.isParamVec (hc : IsEigenSys σ J L h ρ x c) (h0 : x ≠ 0) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    (hs : IsSplit (E := E) v → ∃ e, IsSplitChart σ J L h e)
    (hi : IsInertAt F E v w → ∀ τ, IsConjAt σ h τ → ∃ e, IsInertChart σ J L h τ e)
    (hB : IsSysParam σ n h c B) : IsParamVec σ J L h ρ x B := by
  rcases hB with ⟨hv, h1, h2⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, h2⟩
  · obtain ⟨e, he⟩ := hs hv
    exact Or.inl ⟨hv, e, he, h0, (mem_fixed_comp_symm e he.2).2 hx, h1, fun ϖ hϖ j hj => by
      rw [hc.split hx he hϖ hj, h2 j hj]⟩
  · obtain ⟨e, he⟩ := hi hw τ hτ
    exact Or.inr ⟨hw, τ, ϖ, e, α, hU, he, isSatVecU_of_diag hU h0 ((mem_fixed_comp_symm e he.2.2).2 hx)
      fun d t hd ht => by rw [hc.inert hx he hU.2.2.2.1 hd ht, h2 d t hd ht], rfl⟩

end Place

end GlobalTheory.LFun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem exists_siegelH_proj_eq (x : ∀ v : HeightOneSpectrum (𝓞 F), siegelH (Fv F v) σ Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ∃ p : siegelH (AF F) σ Q,
      (∀ v ∈ S, proj σ Q v p = x v) ∧ (∀ v ∉ S, proj σ Q v p = 1) ∧ ∀ w, projArch σ Q w p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [proj_emb_self, h2 _ hu, mul_one]
      · rw [proj_emb_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embP, proj_emb_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embP, projArch_emb, h3, mul_one]

theorem exists_siegelH_projArch_eq (x : ∀ w : InfinitePlace F, siegelH w.Completion σ Q)
    (S : Finset (InfinitePlace F)) : ∃ p : siegelH (AF F) σ Q,
      (∀ w ∈ S, projArch σ Q w p = x w) ∧ (∀ w ∉ S, projArch σ Q w p = 1) ∧ ∀ v, proj σ Q v p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embArchP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [projArch_embArch_self, h2 _ hu, mul_one]
      · rw [projArch_embArch_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embArchP, projArch_embArch_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP, proj_embArch, h3, mul_one]

variable {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}

theorem HasIwasawa.adelic (hf : ∀ v : HeightOneSpectrum (𝓞 F), HasIwasawa σ Q (KFin σ Q L v))
    (hi : ∀ w : InfinitePlace F, HasIwasawa σ Q (KArch σ Q w (bc (compInf F E w) a))) :
    HasIwasawa σ Q (KAd σ Q L a) := fun g => by
  choose x k hk hx using fun v => hf v (proj σ Q v g)
  choose y l hl hy using fun w => hi w (projArch σ Q w g)
  have hS := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ Q (sumLat finSumFinEquiv L L) g)
  obtain ⟨p, h1, h2, h3⟩ := exists_siegelH_proj_eq x hS.toFinset
  obtain ⟨q, h4, -, h5⟩ := exists_siegelH_projArch_eq y Finset.univ
  refine ⟨p * q, (↑(p * q) : GAd σ Q)⁻¹ * g, mem_KAd.2 ⟨fun v => ?_, fun w => ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h5, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [h1 v hv, hx v, inv_mul_cancel_left]
      exact hk v
    · rw [h2 v hv, inv_one, one_mul]
      exact not_not.1 fun h => hv (hS.mem_toFinset.2 h)
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h3, one_mul, h4 w (Finset.mem_univ w), hy w, inv_mul_cancel_left]
    exact hl w

end GlobalTheory.Doubling

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.UnramDoubleCoset

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
  {ϖ : L} {σ : L →+* L} {q n : ℕ}

def intConj (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  (σ.comp (intL L).subtype).codRestrict (intL L) fun x => by
    show Valued.v (σ x) ≤ 1
    rw [hσ]; exact x.2

open scoped Valued in
theorem exists_dvd_norm_sub_X (hU : IsUnramInv ϖ σ q) (f : Polynomial (intL L)) (hf : f.Monic)
    (hfc : f.map (intConj hU.2.1) = f) (h0 : IsUnit (f.coeff 0)) :
    ∃ p : Polynomial (intL L), f ∣ p * p.map (intConj hU.2.1) - Polynomial.X := by
  haveI := P.fSatake_nontriv hU
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  obtain ⟨hσσ, hσ, h3, h4, ⟨x, hx1, hx2⟩, hq, hcard⟩ := hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  haveI : IsDiscreteValuationRing A := (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    refine NormIntegers.isAdicComplete_of_fg (C := L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let c : A →+* A := intConj hσ
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal A, c x ∈ IsLocalRing.maximalIdeal A := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X A _ c hc hI hω f hf hfc h0

theorem exists_antiJ_frame (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ h ∈ GLint (Fin n) (intL L), cT σ h.1 * 1 * h.1 = antiJ L n := by
  let c := intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hBι : B.map ι = antiJ L n := by
    refine Matrix.ext fun i j => ?_
    show ι (if i.val + j.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite ι, map_one, map_zero]
  have hB : cT c B = B := by
    refine Matrix.ext fun i j => ?_
    show c (if j.val + i.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite c, map_one, map_zero, add_comm j.val]
  have hBB : B * B = 1 := Matrix.map_injective (f := ι) Subtype.val_injective (by
    show (B * B).map ι = (1 : Matrix _ _ _).map ι
    rw [Matrix.map_mul, hBι, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.map_one _ (map_zero ι) (map_one ι)])
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (exists_dvd_norm_sub_X hU) hB
    (IsUnit.of_mul_eq_one _ hBB)
  have h1 : (B * cT c (Polynomial.aeval B p)) * Polynomial.aeval B p = 1 := by rw [Matrix.mul_assoc, hp, hBB]
  refine ⟨bc ι ⟨Polynomial.aeval B p, _, mul_eq_one_comm.1 h1, h1⟩, ⟨_, rfl⟩, ?_⟩
  show cT σ ((Polynomial.aeval B p).map ι) * 1 * (Polynomial.aeval B p).map ι = _
  rw [Matrix.mul_one, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp, hBι]

theorem doubleCoset_one (hU : IsUnramInv ϖ σ q) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L), ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L),
    ∀ h ∈ GLint (Fin n) (intL L), ∀ k ∈ GLint (Fin n) (intL L), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g' = k₁ * g * k₂ := by
  rintro g hg g' hg' _ ⟨h, rfl⟩ _ ⟨k, rfl⟩ e
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M, hM⟩, e'⟩ :=
    GlobalTheory.UnitaryDoubleCoset.exists_unitary_factors (intL L).subtype (c := intConj hU.2.1) (σ := σ) (fun _ => rfl)
      (fun x => Subtype.ext (hU.1 x)) (exists_dvd_norm_sub_X hU) hg hg' h k e
  refine ⟨k₁, hk₁, k₂, ⟨hk₂, ?_⟩, e'⟩
  refine GlobalTheory.UnitarySwap.mem_GLint_of_unitary (J := 1) hU.2.1 (one_mem _) hk₂ fun i j => ?_
  rw [hM]
  exact (M i j).2

open GlobalTheory.InertDoubleCoset in
theorem doubleCoset_GU_of_GL : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  intro L _ _ _ ϖ σ q n hU g g' a b ha hb e
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := doubleCoset_one hU _
    (conj_mem_UJ σ (inv_frame σ eh) g.2) _ (conj_mem_UJ σ (inv_frame σ eh) g'.2) (h * a * h⁻¹)
    (mul_mem (mul_mem hh ha) (inv_mem hh)) (h * b * h⁻¹) (mul_mem (mul_mem hh hb) (inv_mem hh)) (by rw [e]; group)
  have m : ∀ k ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k' ∈ KU σ n, (k' : GL (Fin n) L) = h⁻¹ * k * h := fun k hk =>
    ⟨⟨_, conj_mem_UJ σ eh hk.1⟩, ⟨conj_mem_UJ σ eh hk.1,
      mul_mem (s := GLint (Fin n) (intL L)) (mul_mem (inv_mem hh) hk.2) hh⟩, rfl⟩
  obtain ⟨l₁, m₁, e₁⟩ := m k₁ h₁
  obtain ⟨l₂, m₂, e₂⟩ := m k₂ h₂
  refine ⟨l₁, m₁, l₂, m₂, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, e₁, e₂]
  calc (g' : GL (Fin n) L) = h⁻¹ * (h⁻¹⁻¹ * g' * h⁻¹) * h := by group
    _ = _ := by rw [e']; group

end GlobalTheory.UnramDoubleCoset

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCosetStatement
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | exact GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | (intros; apply GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def halfInf (F : Type) [Field F] [NumberField F] : (AF F)ˣ where
  val := (algebraMap F (Ainf F) 2⁻¹, 1)
  inv := (algebraMap F (Ainf F) 2, 1)
  val_inv := Prod.ext (by
    change algebraMap F (Ainf F) 2⁻¹ * algebraMap F (Ainf F) 2 = 1
    rw [← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]) (mul_one _)
  inv_val := Prod.ext (by
    change algebraMap F (Ainf F) 2 * algebraMap F (Ainf F) 2⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]) (mul_one _)

def halfE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : (AF F ⊗[F] E)ˣ :=
  Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom (halfInf F)

theorem _root_.GlobalTheory.Eis.Conv.sigR_halfE {F E : Type} [Field F] [NumberField F] [Field E]
    [Algebra F E] (σ : E →ₐ[F] E) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ (_root_.GlobalTheory.Eis.Conv.halfE F E).1 =
      (_root_.GlobalTheory.Eis.Conv.halfE F E).1 := by
  simp [_root_.GlobalTheory.Eis.Conv.halfE, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

end GlobalTheory.Eis.Conv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitary
noncomputable section

open Formalism.UG Formalism.IndefR.Mult GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.InertThetaCompare

namespace GlobalTheory.LFun.UnitaryDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem exists_cartan (hU : IsUnramInv ϖ σ q) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ GLint (Fin n) (intL L), ∃ k₂ ∈ GLint (Fin n) (intL L),
      (g : Matrix (Fin n) (Fin n) L) = (k₁ : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin n) (Fin n) L) := by
  have hnt := P.fSatake_nontriv hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  obtain ⟨c, hc0, hg, -⟩ := P.glint_exists_denom (n := Fin n) A g
  refine P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ (unif_ne_zero hU) (fun x hx => ?_) g c hc0 hg
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  rw [hϖ, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log hx']

theorem good_of_mem (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h1 : d.length = n) (h2 : d.Pairwise fun a b => b ≤ a)
    {g : GL (Fin n) L} (hg : g ∈ GU σ n) {k₁ k₂ : GL (Fin n) L} (h₁ : k₁ ∈ GLint (Fin n) (intL L))
    (h₂ : k₂ ∈ GLint (Fin n) (intL L))
    (e : g.1 = k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) : Good n d := by
  have hπ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨π', hπ', a, ha, b, hb, e'⟩ := GlobalTheory.DualDivU.hasDiv_dualLab _ σ n d _ hU.2.1 h1 hg
    ⟨ϖ, hπ, k₁, h₁, k₂, h₂, e⟩
  have l1 : (dualLab d).length = n := by simpa [dualLab] using h1
  have l2 : (dualLab d).Pairwise fun a b => b ≤ a := by
    rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact h2.imp fun h => neg_le_neg h
  rw [e] at e'
  have ent := fun {x} (hx : x ∈ GLint (Fin n) (intL L)) => GlobalTheory.DualDivU.entry_mem _ hx
  refine ⟨h1, h2, eq_of_getD l1 h1 (congrFun (eq_of_tails fun k => le_antisymm ?_ ?_))⟩
  · refine tail_le hπ' hπ (anti_getD l1 l2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem h₁) ha)) (ent (mul_mem hb (inv_mem h₂))) ?_ k
    calc _ = (k₁⁻¹).1 * (k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) * (k₂⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e']; simp only [Units.val_mul, Matrix.mul_assoc]
  · refine tail_le hπ hπ' (anti_getD h1 h2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem ha) h₁)) (ent (mul_mem h₂ (inv_mem hb))) ?_ k
    calc _ = (a⁻¹).1 * (a.1 * Matrix.diagonal (fun i : Fin n => π' ^ (dualLab d).getD i.1 0) * b.1) * (b⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← e']; simp only [Units.val_mul, Matrix.mul_assoc]

theorem exists_good_div : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧
      ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L),
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) *
          Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  intro L _ _ ϖ σ q n hU g
  obtain ⟨a, ha, k₁, h₁, k₂, h₂, e⟩ := exists_cartan hU (g : GL (Fin n) L)
  have hd : ∀ i : Fin n, (List.ofFn a).getD i.1 0 = a i := fun i => by simp [List.getD_eq_getElem?_getD]
  have e' : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ (List.ofFn a).getD i.1 0) * k₂.1 := by
    simp only [hd]; exact e
  exact ⟨List.ofFn a, good_of_mem hU List.length_ofFn
    (List.pairwise_ofFn.2 fun i j hij => ha hij.le) g.2 h₁ h₂ e', k₁, h₁, k₂, h₂, e'⟩

end GlobalTheory.LFun.UnitaryDiv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitaryStatement
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_elementaryDivisors_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧ ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L), ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  first | exact @GlobalTheory.LFun.UnitaryDiv.exists_good_div | exact GlobalTheory.LFun.UnitaryDiv.exists_good_div | (intros; apply GlobalTheory.LFun.UnitaryDiv.exists_good_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectors
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.HeckeScalar

open GlobalTheory.LFun.SatCompare GlobalTheory.LocGL

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {K : Subgroup G}

theorem heckeVec_dosetInd_eq_idem (hπ : GlobalTheory.LGrp.IsIrrSmooth π) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (g : G) {z : V} (hz : z ∈ fixed π K) :
    ∃ N : ℂ, N ≠ 0 ∧ heckeVec π K (dosetInd ℂ K g) z = N • idem hπ.1 hc (π g z) := by
  classical
  have hm := Final.DosetIndMem G K ℂ g
  have hfin := Formalism.UG.P.finite_support_cosets hK hm.2
  have hS : ∀ c : G ⧸ K, c ∈ hfin.toFinset ↔ c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c => by
    simp [dosetInd]
  refine ⟨hfin.toFinset.card, ?_, ?_⟩
  · refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (hS _).2 ?_⟩)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← idem_of_mem hπ.1 hc (heckeVec_mem_fixed hK hm hz), heckeVec,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
      · refine Finset.sum_congr rfl fun c hcS => ?_
        have h1 := (hS c).1 hcS
        obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h1
        rw [dosetInd, Set.indicator_of_mem h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
          GlobalTheory.LGrp.mem_fixed.1 hz b hb]
        simpa using idem_apply_mem hπ.1 hc ha (π g z)
      · intro c hc'
        refine Finset.mem_coe.2 ((hS c).2 ?_)
        by_contra h0
        exact hc' (by simp [dosetInd, h0])

theorem exists_scalar : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K →
    (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π →
    FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  intro G V _ _ _ _ _ π K hc hK hcomm hπ hfd h hh
  by_cases hb : fixed π K = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have := heckeVec_mem_fixed hK hh hx
    rw [hb] at this
    simpa using this
  haveI : Nontrivial (fixed π K) := Submodule.nontrivial_iff_ne_bot.2 hb
  let A : Module.End ℂ (fixed π K) := (heckeLin hK hh π).restrict fun x hx => heckeVec_mem_fixed hK hh hx
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  obtain ⟨⟨x₀, hx₀⟩, hv⟩ := hcA.exists_hasEigenvector
  have h0 : x₀ ≠ 0 := fun e => hv.2 (Subtype.ext e)
  have he : heckeVec π K h x₀ = c • x₀ := congrArg Subtype.val hv.apply_eq_smul
  have key : ∀ g, heckeLin hK hh π (idem hπ.1 hc (π g x₀)) = c • idem hπ.1 hc (π g x₀) := fun g => by
    obtain ⟨N, hN, e⟩ := heckeVec_dosetInd_eq_idem hπ hc hK g hx₀
    have hm := Final.DosetIndMem G K ℂ g
    refine smul_right_injective V hN ?_
    show N • _ = N • _
    rw [← map_smul, smul_comm N c, ← e, heckeLin_apply, ← heckeVec_conv hK hh hm hx₀, hcomm _ hh _ hm,
      heckeVec_conv hK hm hh hx₀, he]
    exact (heckeLin hK hm π).map_smul c x₀
  refine ⟨c, fun x hx => ?_⟩
  have all : ∀ w : MonoidAlgebra ℂ G, heckeLin hK hh π (idem hπ.1 hc (orbitMap π x₀ w)) =
      c • idem hπ.1 hc (orbitMap π x₀ w) := fun w => by
    induction w using MonoidAlgebra.induction_on with
    | of g =>
      have : orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀ := by
        show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _
        simp
      rw [this]; exact key g
    | add a b ha hb =>
      have : orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b := map_add _ _ _
      rw [this, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | smul r a ha =>
      have : orbitMap π x₀ (r • a) = r • orbitMap π x₀ a := map_smul _ _ _
      rw [this, map_smul, map_smul, ha, smul_comm]
  obtain ⟨w, rfl⟩ := orbitMap_surjective hπ.2 h0 x
  have := all w
  rwa [idem_of_mem hπ.1 hc hx] at this

end GlobalTheory.LFun.HeckeScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectorsStatement
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π → FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  first | exact @GlobalTheory.LFun.HeckeScalar.exists_scalar | exact GlobalTheory.LFun.HeckeScalar.exists_scalar | (intros; apply GlobalTheory.LFun.HeckeScalar.exists_scalar <;> assumption)
end
end

module

public import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
public import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
public import Formalism.MonomialMeanResidues.ZerosPerVariable
public import Formalism.LocalToGlobal.Columns.Record

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.BrpStarLatLattice
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HN Formalism.HermitianLatticesTheory

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def stdHL (N : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := N

theorem brp_hStd_basis (i j : Fin n) :
    hStd K n (Pi.basisFun K (Fin n) i) (Pi.basisFun K (Fin n) j) = if i = j then 1 else 0 := by
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, Pi.basisFun_apply, Pi.single_apply]
  split_ifs with h
  · subst h; simp
  · rw [Finset.sum_eq_zero]; intro k _; split_ifs <;> simp_all

theorem brp_hStd_pos (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (hStd K n (Pi.basisFun K (Fin n) i) (Pi.basisFun K (Fin n) j))).PosDef := by
  convert Matrix.PosDef.one (n := Fin n) (R := ℂ) using 1
  ext i j
  rw [Matrix.of_apply, brp_hStd_basis, Matrix.one_apply]
  split_ifs <;> simp

theorem brp_formAt_std (v : InfinitePlace K) (x y : Fin n → K) :
    formAt (Pi.basisFun K (Fin n)) (hStd K n) v x y = ∑ i, starRingEnd ℂ (v.embedding (x i)) * v.embedding (y i) := by
  unfold formAt
  simp only [Pi.basisFun_repr, brp_hStd_basis]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem brp_normAt_std (v : InfinitePlace K) (x : Fin n → K) :
    normAt (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v x =
      Real.sqrt (formAt (Pi.basisFun K (Fin n)) (hStd K n) v x x).re := by
  rw [brp_formAt_std]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  congr 1
  simp only [inv_one, Matrix.one_mulVec, Complex.re_sum, Pi.basisFun_repr]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem brp_latK_mu (N : Submodule (𝓞 K) (Fin n → K)) (hN : N.FG) : (latK K N).mu = (stdHL K N).mu := by
  have hs := formH_spec (Pi.basisFun K (Fin n)) (hStd K n) (brp_hStd_pos K) N
  have h := frame_free K (Fin n → K) (Fin n) (Fin n) (Pi.basisFun K (Fin n)) (latK K N).X (Pi.basisFun K (Fin n))
    (fun _ => 1) hs.1 (fun _ => by simp) (fun v x => by rw [hs.2.2, brp_normAt_std]) N hN
  exact h.2.1

end Std

section Dual

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

end Dual

section Star

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

def brpCO : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)

theorem brp_star_smul (c : 𝓞 K) (x : Fin n → K) : star (c • x) = brpCO K c • star x := by
  funext i
  show star (c • x i) = brpCO K c • star (x i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul']
  congr 1

def starLat (N : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) where
  carrier := {x | star x ∈ N}
  add_mem' := by
    intro x y hx hy
    show star (x + y) ∈ N
    rw [star_add]
    exact N.add_mem hx hy
  zero_mem' := by
    show star (0 : Fin n → K) ∈ N
    rw [star_zero]
    exact N.zero_mem
  smul_mem' := by
    intro c x hx
    show star (c • x) ∈ N
    rw [brp_star_smul]
    exact N.smul_mem _ hx

theorem mem_starLat (N : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) : x ∈ starLat K N ↔ star x ∈ N := Iff.rfl

theorem brp_star_mem_span (S : Set (Fin n → K)) (y : Fin n → K) (hy : y ∈ Submodule.span (𝓞 K) S) :
    star y ∈ Submodule.span (𝓞 K) (star '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [brp_star_smul]; exact Submodule.smul_mem _ _ hx

theorem brp_starLat_span (S : Set (Fin n → K)) :
    starLat K (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 K) (star '' S) := by
  ext x
  rw [mem_starLat]
  constructor
  · intro h
    have := brp_star_mem_span K S (star x) h
    rwa [star_star] at this
  · intro h
    have hS : star '' (star '' S) = S := by
      rw [Set.image_image]; simp
    have := brp_star_mem_span K (star '' S) x h
    rwa [hS] at this

end Star

section StarMu

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

theorem brp_star_smulK (a : K) (x : Fin n → K) : star (a • x) = star a • star x := by
  funext i
  show star (a * x i) = star a * star (x i)
  rw [star_mul', mul_comm]

theorem brp_star_mem_spanK (S : Set (Fin n → K)) (y : Fin n → K) (hy : y ∈ Submodule.span K S) :
    star y ∈ Submodule.span K (star '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [brp_star_smulK]; exact Submodule.smul_mem _ _ hx

theorem brp_star_span_top (S : Set (Fin n → K)) (h : Submodule.span K S = ⊤) : Submodule.span K (star '' S) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have := brp_star_mem_spanK K S (star x) (h ▸ Submodule.mem_top)
  rwa [star_star] at this

theorem brp_starLat_lattice (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (starLat K N) := by
  classical
  obtain ⟨S, hS⟩ := hN.fg
  apply Submodule.IsLattice.of_fg
  refine ⟨S.image star, ?_⟩
  rw [Finset.coe_image, ← brp_starLat_span, hS]

variable [_root_.NumberField.IsTotallyComplex K]

end StarMu

section ESide

variable (E : Type) [Field E] [NumberField E] [StarRing E] {n : ℕ}

variable [_root_.NumberField.IsTotallyComplex E]

end ESide

section Tau

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [_root_.NumberField.IsTotallyComplex E] [Field K] [NumberField K] [StarRing K]
  [_root_.NumberField.IsTotallyComplex K] {n : ℕ}

theorem brp_mu_degT {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (h0 : L ≠ ⊥) (hr : 0 < rkK L) :
    muDef b X L = 2 * Formalism.HermiteSiegelSlopes.degT b X L / (rkK L : ℝ) := by
  rw [T2.mu_eq_log_ht b X hX L hL h0]
  unfold Formalism.HermiteSiegelSlopes.degT
  have h1 : (0 : ℝ) < (nPl K : ℝ) := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have h2 : (0 : ℝ) < (rkK L : ℝ) := by exact_mod_cast hr
  field_simp

end Tau

section EE

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end EE

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TiedGlPl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E)
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))

theorem glk_val_lt (x : v.adicCompletionIntegers F) (h : IsLocalRing.residue (v.adicCompletionIntegers F) x = 0) :
    Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  have hle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 x.2
  refine lt_of_le_of_ne hle fun h1 => h ?_
  have hx0 : (x : v.adicCompletion F) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  let y : v.adicCompletionIntegers F := ⟨(x : v.adicCompletion F)⁻¹,
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by rw [map_inv₀, h1, inv_one])⟩
  have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
  exact ⟨⟨x, y, hxy, (mul_comm _ _).trans hxy⟩, rfl⟩

theorem gloRho_oToS (a : 𝓞 E) : gloRho v spl halg (oToS F E a) = IsLocalRing.residue (v.adicCompletionIntegers F)
    ⟨gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a)), by
      have := gloPhi_int v spl halg _ (afsplit_prV_int v _ (oToS F E a).2)
      rwa [show ((oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) from rfl, afsplit_prV_inclE] at this⟩ := by
  rw [gloRho_apply]
  congr 1


include hc in
theorem glk_ker (w : Pl E) (hov : IsOver v w) (ϖ : 𝓞 E) (h2 : cO E ϖ ∉ w.asIdeal)
    (hval : Valued.v (gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E ϖ))) < 1) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (by rw [map_zero]; exact zero_mem _)
  have hϖ : gloRho v spl halg (oToS F E ϖ) = 0 := by
    rw [gloRho_oToS]
    exact glo_res_zero v _ hval
  let Q : Pl E :=
    { asIdeal := RingHom.ker ((gloRho v spl halg).comp (oToS F E))
      isPrime := RingHom.ker_isPrime _
      ne_bot := fun hb => hϖ0 (by
        have : ϖ ∈ RingHom.ker ((gloRho v spl halg).comp (oToS F E)) := hϖ
        rwa [hb, Ideal.mem_bot] at this) }
  have hQ : IsOver v Q := by
    show v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    ext r
    rw [Ideal.mem_comap]
    show r ∈ v.asIdeal ↔ gloRho v spl halg (oToS F E (algebraMap (𝓞 F) (𝓞 E) r)) = 0
    rw [gloRho_algMap]
    constructor
    · intro hr
      refine glo_res_zero v _ ?_
      show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1
      rw [csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
    · intro hr
      have := glk_val_lt v _ hr
      change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 at this
      rw [csApprox_val_int] at this
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).1 this
  rcases rll_over_cases hc hov hQ with h | h
  · intro a ha
    have : a ∈ Q.asIdeal := by rw [h]; exact ha
    exact this
  · exfalso
    have : ϖ ∈ Q.asIdeal := hϖ
    rw [h, mem_conjP] at this
    exact h2 this

end Ker

section Pl

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

structure GSplit where
  sp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
    X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F
  sp_sig : ∀ i v h x, sp i v h (sigR hc.sig (v.adicCompletion X.F) x) = swapR _ (sp i v h x)
  sp_alg : ∀ i v h (a : v.adicCompletion X.F), sp i v h ((1 : X.E) ⊗ₜ[X.F] a) = (a, a)
  sp_pi : ∀ i v h, Valued.v (sp i v h (inclE (F := X.F) (v.adicCompletion X.F) (hc.sig (Pr.piG i : X.E)))).1 < 1


variable {hc}



end Pl

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.WordFin
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColBase where
  R : Ranks
  host : Host R
  sp : Spaces R host.F host.E
  what₂ : ColRows R
  eTau : what₂.Tau ≃ (R.Psi)
  [wordFin : Fintype what₂.Word]
  u₀ : what₂.Word
  hcW : what₂.Word → what₂.Tau → HCParam R
  [nfLL : NumberField what₂.LL]
  [starLL : StarRing what₂.LL]
  embE : host.E →+* what₂.LL

  cond : ℕ

  piG : Fin 2 → 𝓞 host.E

  T : what₂.Word → ℕ

  piT : what₂.Word → 𝓞 host.E

  tops : Finset what₂.Tau

attribute [instance] ColBase.wordFin ColBase.nfLL ColBase.starLL

namespace ColBase

variable (B : ColBase)

@[reducible] def X : Fields where
  F := B.host.F
  E := B.host.E
  K := B.what₂.LL
  starE := B.host.cmStar
  Tau := B.what₂.Tau
  deTau := Classical.decEq _
  emb := fun τ => B.embE.comp (B.host.sigmaOf (B.eTau τ : B.R.GG) : B.host.E →+* B.host.E)

@[reducible] def Pr : Primes B.X where
  cond := B.cond
  g := B.host.g
  piG := B.piG
  Word := B.what₂.Word
  deWord := Classical.decEq _
  T := B.T
  piT := B.piT

@[reducible] def W : Wts B.X B.what₂.Word B.R where
  row := fun τ => RowPar.of (B.hcW B.u₀ τ)
  hc := B.hcW
  tops := B.tops

@[reducible] def σ₀ : B.X.K →+* ℂ := B.what₂.embLL

end ColBase

structure ColDat extends ColBase where

  Ch : Chars toColBase.X toColBase.Pr R.m

  lev : ∀ j, LevFam toColBase.X.E toColBase.X.K (R.N j) toColBase.Pr.vGs := colLevS Ch

  lev0 : lev 0 = colLev Ch 0 := by
    exact colLevS_of_lt _ (Nat.lt_of_lt_of_le (by norm_num) (Ranks.two_le_m _))

  levP : LevFam toColBase.X.E toColBase.X.K (R.N R.m - 1) toColBase.Pr.vGs := (rowTyG Ch (rPsharp Ch)).inv

  Ps : CharT toColBase.X toColBase.Pr

  num : AtTNum

  plEq : what₂.places.Pl ≃ HeightOneSpectrum (𝓞 what₂.LL)
  hX : toColBase.X.Ok
  hPr : toColBase.Pr.Ok
  hPs : Ps.Ok

  star_cx : ∀ x : what₂.LL, what₂.embLL (star x) = starRingEnd ℂ (what₂.embLL x)

structure ColArgs (d : ColDat) where

  G : ChainGlob (Pr := d.Pr) d.W d.σ₀

  A : ∀ u : d.what₂.Word, ChainArg (Pr := d.Pr) d.W d.lev G u

  th : ∀ u : d.what₂.Word, ThArg (Pr := d.Pr) d.W d.lev u
  free : ∀ u : d.what₂.Word, (stepGSD (Pr := d.Pr) d.W d.lev u 0).Free
  rowOk : (rowGSD (Pr := d.Pr) d.W d.levP).Ok
  piT_off : ∀ (u : d.what₂.Word) (w : d.Pr.vGs), d.Pr.piT u ∉ w.1.asIdeal
  levExt : LevExt (Pr := d.Pr) d.lev (Finset.Subset.refl _) d.levP

namespace ColDat

variable (d : ColDat) (a : ColArgs d)

theorem f_eq : d.X.f = d.R.f := d.what₂.card_Tau

@[reducible] def chain (u : d.what₂.Word) : ColumnChain d.R d.what₂.Tau (d.hcW u) :=
  recChain (Pr := d.Pr) (W := d.W) (Λ := d.lev) d.hX d.σ₀ a.G u (a.A u)

@[reducible] def atT (u : d.what₂.Word) : ColumnsAtT d.R (d.chain a u) :=
  recAtT (Pr := d.Pr) (W := d.W) (Λ := d.lev) d.hX d.hPr d.f_eq d.σ₀ d.star_cx u a.G (a.A u) d.Ps d.hPs (a.free u) d.num

@[reducible] def per (u : d.what₂.Word) : PeriodMap d.R (d.chain a u) :=
  recPer (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hX d.σ₀ d.star_cx u a.G (a.A u) a.rowOk

@[reducible] def forms (u : d.what₂.Word) :
    MemberForms d.what₂.LL d.what₂.embLL d.what₂.places d.what₂.Tau (d.hcW u) (d.chain a u) (d.atT a u) (d.per a u) :=
  recFormsX (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hX d.hPr d.f_eq d.σ₀ d.star_cx u a.G (a.A u) d.Ps d.hPs
    (a.free u) d.num d.what₂.places d.plEq a.rowOk (a.piT_off u) a.levExt (a.th u)

def crd (i : ℕ) (hi : i ≤ d.R.m) : (d.sp.X i).V ≃ₗ[d.host.E] (Fin (d.R.N i) → d.host.E) :=
  (d.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft d.host.E d.host.E (finCongr (d.sp.X_rank i hi)).symm)

def repr (u : d.what₂.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : DecoSet (E := d.X.E) (n := d.R.N i) (ST := d.Pr.vT u) (SG := d.Pr.vGs) :=
  (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c


open Classical in
def clsLat (u : d.what₂.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : Submodule (𝓞 d.host.E) (d.sp.X i).V :=
  if hi : i ≤ d.R.m then
    (d.repr u i c).1.L.map (((d.crd i hi).symm : (Fin (d.R.N i) → d.host.E) →ₗ[d.host.E] (d.sp.X i).V).restrictScalars (𝓞 d.host.E))
  else (d.sp.X i).L0

@[reducible] def colRec : ColRec where
  R := d.R
  host := d.host
  sp := d.sp
  what₂ := d.what₂
  eTau := d.eTau
  u₀ := d.u₀
  hcW := d.hcW
  mem := fun u => ⟨d.chain a u, d.atT a u, d.per a u⟩
  embE := d.embE
  cOf := fun u => (d.piT d.u₀ : d.host.E) / (d.piT u : d.host.E)
  clsLat := fun u i c => d.clsLat u i c
  fm := fun u => d.forms a u

end ColDat

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.GFamEv
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev Pt (F : GFam K) : Type := Σ b, F.D b

def cls (F : GFam K) (p : F.Pt) : F.Cl := ⟨p.1, (F.mem p.1).cls p.2⟩

structure Ev (F : GFam K) (σ : K →+* ℂ) where

  Y : Type

  ev : F.V →ₛₗ[σ] (Y → ℂ)
  li : LinearIndependent ℂ fun i => ev (F.bV i)

  ip : (Y → ℂ) →ₗ⋆[ℂ] (Y → ℂ) →ₗ[ℂ] ℂ
  ip_ev : ∀ x y, ip (ev x) (ev y) = σ (F.pair x y)

  tr : ∀ b, F.G b →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ))
  tr_ev : ∀ b g x, tr b g (ev x) = ev (F.ρ b g x)

namespace Ev

variable {F : GFam K} {σ : K →+* ℂ} (E : F.Ev σ)


end Ev

end GFam

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

end GSD.Ev

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {β : Type} [Fintype β] [DecidableEq β]

end Round

end Formalism.L2.Col
end
end

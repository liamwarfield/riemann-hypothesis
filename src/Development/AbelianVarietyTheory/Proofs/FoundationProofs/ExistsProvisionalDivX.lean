module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigIdxFiniteTypesCOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PointGlobalSectionsNeBot
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped NNReal

namespace GlobalTheory.PointGeometry

variable (F : Type) [Field F] [NumberField F]

structure AdelicLine where

  inf : InfinitePlace F → ℝ

  fin : HeightOneSpectrum (𝓞 F) → ℝ
  fin_finite : (Function.mulSupport fin).Finite

variable {F}


open Classical in
def AdelicLine.of (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  if h : (Function.mulSupport b).Finite then ⟨a, b, h⟩ else ⟨a, 1, by simp⟩

@[simp] theorem AdelicLine.of_inf (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) :
    (AdelicLine.of a b).inf = a := by
  unfold AdelicLine.of; split_ifs <;> rfl

theorem AdelicLine.of_fin (a : InfinitePlace F → ℝ) {b : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : (Function.mulSupport b).Finite) : (AdelicLine.of a b).fin = b := by
  unfold AdelicLine.of; rw [dite_eq_left h]

def AdelicLine.deg (L : AdelicLine F) : ℝ :=
  -((∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log (L.inf v)) + ∑ᶠ w, Real.log (L.fin w)) /
    (Module.finrank ℚ F : ℝ)

def AdelicLine.twist (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  AdelicLine.of (fun v => Real.exp (-ci v) * L.inf v) (fun w => Real.exp (-cf w) * L.fin w)

theorem AdelicLine.twist_fin (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (h : (Function.support cf).Finite) :
    (L.twist ci cf).fin = fun w => Real.exp (-cf w) * L.fin w := by
  refine AdelicLine.of_fin _ ((h.union L.fin_finite).subset fun w hw => ?_)
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, Function.mem_mulSupport, not_or, not_not] at hn
  exact hw (by simp [hn.1, hn.2])

variable [StarRing F]

def latticeNorm (W : HLat F) (ι : W.V →ₗ[F] F) (w : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (⨆ x : W.L, FinitePlace.mk w (ι x))⁻¹

def frameSq (W : HLat F) (ι : W.V →ₗ[F] F) (v : InfinitePlace F) : ℝ≥0 :=
  ∑ k : W.ι, ‖∑ i, (W.X v) i k • v.embedding (ι (W.b i))‖₊ ^ 2

def ofLattice (W : HLat F) (ι : W.V →ₗ[F] F) : AdelicLine F :=
  AdelicLine.of (fun v => (Real.sqrt (frameSq W ι v))⁻¹) (latticeNorm W ι)

variable (F)

def pointGeo : DV.Geo F where
  Var := Unit
  dim _ := 0
  Fn _ := F
  Dv _ := PUnit
  Eff _ _ := True
  eff_zero _ := trivial
  eff_add _ _ _ _ _ := trivial
  H0 _ _ := ⊤
  degreeZeroCohomology_finiteDimensional _ _ := inferInstance
  mul_mem_riemannRochSpace_add _ _ _ _ _ _ _ := Submodule.mem_top
  riemannRoch_mono _ _ _ _ := le_rfl
  KY _ := 0
  Cl _ := Set Unit
  properCl _ Z := Z ≠ Set.univ
  subCl _ Z Z' := Z ⊆ Z'
  supp _ _ := ∅
  inter _ _ := 1
  nef _ _ := True
  big _ _ := True
  bpf _ _ V := ∃ f ∈ V, f ≠ 0
  phiBir _ _ V := ∃ f ∈ V, f ≠ 0
  phiNoContr _ _ _ _ := True
  vanishOn _ _ f Z := Z.Nonempty → f = 0
  hdim _ i _ := if i = 0 then 1 else 0
  pts _ _ := Unit
  ptsMeas _ _ := ⊤
  vol _ _ := @MeasureTheory.Measure.dirac Unit ⊤ ()
  FnC _ _ := ℂ
  cx _ σ := σ
  cx_smul _ σ a f := by simp
  Met _ _ _ := ℝ≥0
  mAdd _ _ _ _ h h' := h * h'
  mPow _ _ _ k h := h ^ k
  fsMet _ _ _ _ _ e := ∑ k, ‖e k‖₊ ^ 2
  pn _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  pnK _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  mSmooth _ _ _ h := h ≠ 0
  mPsh _ _ _ _ _ := True
  redZero _ _ _ _ S := S = Set.univ
  agreeOn _ _ _ f g S := S.Nonempty → f = g
  resNorm _ _ _ h _ _ _ g _ := ‖g‖ ^ 2 / (h : ℝ)
  Adl _ := AdelicLine F
  ofW _ _ W ι := ofLattice W ι
  twist _ L ci cf := L.twist ci cf
  arTop _ L := L.deg
  arVol _ L := max L.deg 0
  nefA _ L := 0 ≤ L.deg
  supInf _ L v τ f := v f * L.inf v ^ τ
  supFin _ L w τ f := FinitePlace.mk w f * L.fin w ^ τ
  cutGood _ bd _ _ _ _ _ _ _ := bd = ∅
  cutHt _ L _ _ _ _ _ _ _ := L.deg
  cutOrd _ _ _ _ _ _ _ _ _ _ := 0
  resFull _ _ _ _ _ _ _ _ M ι _ :=
    (M.L.map (ι.restrictScalars (𝓞 F))).FG ∧ M.L.map (ι.restrictScalars (𝓞 F)) ≠ ⊥
  resDeg _ _ _ _ _ _ _ _ M ι L := (AdelicLine.of L.inf (latticeNorm M ι)).deg
  supInf_ofW _ _ W ι v τ f := by
    rw [ciSup_unique]
    change v f * (ofLattice W ι).inf v ^ τ =
      Real.sqrt (‖v.embedding f‖ ^ 2 / ((frameSq W ι v ^ τ : ℝ≥0) : ℝ))
    rw [ofLattice, AdelicLine.of_inf, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      InfinitePlace.norm_embedding_eq, inv_pow, div_eq_mul_inv]
    congr 2
    rw [NNReal.coe_pow, eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
      ← mul_pow, Real.mul_self_sqrt (NNReal.coe_nonneg _)]
  supInf_twist _ L ci cf _ v τ f := by
    rw [AdelicLine.twist, AdelicLine.of_inf, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  supFin_twist _ L ci cf h w τ f := by
    rw [AdelicLine.twist_fin L ci h, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  regOn _ _ _ _ _ := True

theorem point_global_sections_ne_bot (Y : (pointGeo F).Var) : (pointGeo F).H0 Y 0 ≠ ⊥ :=
  (top_ne_bot : (⊤ : Submodule F F) ≠ ⊥)

theorem exists_geo : ∀ (F : Type) [Field F] [NumberField F] [StarRing F],
    ∃ G : DV.Geo F, ∃ Y : G.Var, G.H0 Y 0 ≠ ⊥ :=
  fun F _ _ _ => ⟨pointGeo F, (), point_global_sections_ne_bot F _⟩

end GlobalTheory.PointGeometry
end
end

open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory.ProvisionalDivX

section Form

variable {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
  (c : Module.Basis (Fin n) ℂ W)

end Form

structure MjForm (D : D7) (j : ℕ) where

  H : HLat D.what₂.LL

  jm : H.V →ₛₗ[D.what₂.embLL] D.what₂.Mj j
  good : H.Good
  basis : LinearIndependent ℂ (fun i => jm (H.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jm (H.b i))) = ⊤
  lat : 1 ≤ j → j ≤ D.R.m → ∀ x, x ∈ H.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
    jm x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v
  sub : 1 ≤ j → j ≤ D.R.m → ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range jm
  metric : ∀ x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord H.b H.X
    (InfinitePlace.mk D.what₂.embLL) x) = ‖jm x‖

theorem resChar_eq_iff (D : D7) {p : ℕ} (hp : p.Prime) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ (p : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  constructor
  · intro h; rw [← h]; exact resChar_mem D w
  · intro hmem
    by_contra hne
    have hcop : Nat.Coprime (D.what₂.places.resChar w) p :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).mpr hne
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (p : 𝓞 D.what₂.LL) :=
      hcop.cast
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem D w)) (Ideal.mul_mem_left _ _ hmem)

def placeEquiv (D : D7) (p : ℕ) [hp : Fact p.Prime] :
    Formalism.L2.Geo.PlL D p ≃ {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (resChar_eq_iff D hp.out)).symm

theorem wtL_eq_ramIdx_mul (D : D7) (p : ℕ) [hp : Fact p.Prime] (la : Formalism.L2.Geo.PlL D p) :
    Formalism.L2.Geo.wtL D p la = (D.what₂.places.ramIdx (placeEquiv D p la).1 : ℝ) *
      (padicValNat p (Ideal.absNorm (D.plEq (placeEquiv D p la).1).asIdeal) : ℝ) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
  have he : D.plEq (placeEquiv D p la).1 = la.1 := D.plEq.apply_symm_apply _
  have := liesOver_of_mem p hp.out la.1 la.2
  have hN := Ideal.pow_inertiaDeg p la.1.asIdeal
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  have hval : padicValNat p (p ^ la.1.asIdeal.inertiaDeg ℤ) = la.1.asIdeal.inertiaDeg ℤ := by
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  rw [D.ram_eq, he, Formalism.L2.Geo.wtL, ← hN, hval]
  push_cast
  rw [Real.log_pow]
  field_simp

def smallShim (D : D7) (r : ℕ) : DV.ShimX D.what₂.Tau :=
  provisionalShimX D.what₂.Tau (max r 2) 1 ∅ le_rfl (by omega) (by simp)

end GlobalTheory.ProvisionalDivX

namespace GlobalTheory

open ProvisionalDivX

def provisionalDivX (D : D7) (G : DV.Geo D.what₂.LL) (Y : G.Var)
    (jc : ∀ (p : ℕ) [Fact p.Prime], DV.KW p →+* ℂ)
    (M : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ),
      DV.Mdl D p (max r 2) (DV.rkOf (DV.PsiOf D (jc p)) (max r 2) 1))
    (F : ∀ j, MjForm D j) : DivX D :=
  letI := D.host.cmStar
  { geo := G
    Lev := Unit
    levPr := fun _ => ∅
    shv := fun S _ => smallShim D S.rank
    shv_N := fun _ _ h => max_eq_left h
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => Formalism.L2.Geo.PlL D p
    plpFin := fun p _ => Formalism.L2.Geo.finPl D p
    plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
    wtP := fun p _ => Formalism.L2.Geo.wtL D p
    divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
    divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
    plP := fun p _ => placeEquiv D p
    divisorWeight_def := fun p _ => wtL_eq_ramIdx_mul D p
    jC := fun p _ _ => jc p
    Mp := fun _ _ _ _ _ => Unit
    md := fun S _ p _ _ _ => M p S.rank
    vdd := fun _ _ => 0
    vdd_unram := fun _ _ _ => rfl
    phiFr_unram := fun _ _ _ _ _ _ => rfl
    vdd_nonneg := fun _ _ => le_rfl
    CurveM := fun _ _ _ _ _ _ => Empty
    degM := fun _ _ _ _ _ _ _ _ => 0
    htMdl := fun _ _ _ _ _ => ()
    htCurve := fun _ _ p _ =>
      { toFun := fun c => Empty.elim c
        invFun := fun c => c.2
        left_inv := fun c => Empty.elim c
        right_inv := fun c => Empty.elim c.2 }
    htCurve_deg := fun _ _ _ _ c => Empty.elim c
    MjH := fun j => (F j).H
    MjH_good := fun j => (F j).good
    jM := fun j => (F j).jm
    jM_basis := fun j => (F j).basis
    jM_lat := fun j => (F j).lat
    MjLat_sub := fun j => (F j).sub
    jM_metric := fun j _ _ => (F j).metric
    Qp := fun _ => ∅
    degreeZero_partial_set_empty := rfl
    Qp_muAt := fun _ => Finset.notMem_empty _
    Qp_g := fun _ _ _ => Finset.notMem_empty _
    QPl := fun _ => Empty
    qv := fun _ v => v.elim
    qv_gt := fun _ v => v.elim
    qv_char := fun _ _ v => v.elim
    nu := fun _ v => v.elim
    nu_ne := fun _ v => v.elim
    nu_abs := fun _ v => v.elim
    ZQ := fun _ v => v.elim
    quotientLocalValueFirst := fun _ v => v.elim
    typeDim := fun _ v => v.elim
    Comp := fun _ => Unit
    degHH := fun _ _ _ => 0
    Yv := fun _ _ => Y
    Ybd := fun _ _ => G.supp Y 0
    Lw := fun _ _ => 0
    iMj := fun _ _ => 0
    iMj_mem := fun _ _ _ => Submodule.zero_mem _
    logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
    logLam_base := fun _ _ => rfl
    kapR := fun _ => kapSharp D
    kapR_pos := fun _ => RowSide.kapOf_pos _ _
    kapR_conj := fun _ => rfl
    Surf := Empty
    surfCh2 := fun s => s.elim
    surfDegOm := fun s => s.elim
    SurfFp := Empty
    surfFpCh2 := fun s => s.elim }

end GlobalTheory

end

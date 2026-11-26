module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CuspDim.IsoPow

variable {Z : Scheme.{0}} {B : LB Z}

theorem res_res {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(Z, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  change (Z.presheaf.map (homOfLE h).op ≫ Z.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

theorem pow_le (n : ℕ) (j : PUnit → B.ι) : (lbPow B n).U j ≤ B.U (j PUnit.unit) :=
  LB.wchart_le B (fun _ => 𝟙 Z) j PUnit.unit

theorem res_pow_g (n : ℕ) (j j' : PUnit → B.ι) {W : Z.Opens} (h : W ≤ (lbPow B n).U j ⊓ (lbPow B n).U j') :
    res h ((lbPow B n).g j j') =
      res (h.trans (inf_le_inf (pow_le n j) (pow_le n j'))) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
  have e : (lbPow B n).g j j' =
      res (inf_le_inf (pow_le n j) (pow_le n j')) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) :=
    Fintype.prod_unique fun a : PUnit.{1} => res (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => 𝟙 Z) j a))
      (inf_le_right.trans (LB.wchart_le B (fun _ => 𝟙 Z) j' a))) (pullU (𝟙 Z) _ (B.g (j a) (j' a))) ^ (n : ℤ)
  rw [e, zpow_natCast, map_pow, res_res]



theorem ev_res_pow {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} {U W : Z.Opens} {y : CxPts q σ} (h : W ≤ U)
    (hy : y ∈ ptsIn q σ W) (u : Γ(Z, U)ˣ) (n : ℕ) :
    ev q σ W (res h u ^ n).val y = ev q σ U u.val y ^ (n : ℤ) := by
  rw [zpow_natCast, ← ev_res h hy, ev_eq hy, ev_eq hy, Units.val_pow_eq_pow_val, map_pow]
  rfl

end GlobalTheory.CuspDim.IsoPow
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PowRep

open GlobalTheory.CuspDim.IsoPow
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem h_powLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : Geo.HermLine ι) (r : ℕ)
    (z : (Σ k, ι k) → ℂ) : (powLine A r).h z = A.h z ^ r := by
  induction r with
  | zero => simp [powLine, constLine]
  | succ r ih => simp [powLine, Geo.HermLine.tensor, ih, pow_succ]

theorem frame_pow {Z : Scheme.{0}} (B : LB Z) (r : ℕ) (V : Z.Opens) (u : ∀ i, Γ(Z, B.U i ⊓ V)ˣ)
    (h : ∀ i j, Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ V ≤ B.U j ⊓ V) (u j) =
        Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ B.U j) (B.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ V) (u i))
    (j j' : PUnit.{1} → B.ι) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j' ⊓ V)
        (Semi.res (inf_le_inf_right V (pow_le r j')) (u (j' PUnit.unit)) ^ r) =
      Semi.res (inf_le_left : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ (lbPow B r).U j')
          ((lbPow B r).g j j') *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ V)
          (Semi.res (inf_le_inf_right V (pow_le r j)) (u (j PUnit.unit)) ^ r) := by
  have hW : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤
      B.U (j PUnit.unit) ⊓ B.U (j' PUnit.unit) ⊓ V :=
    inf_le_inf_right V (inf_le_inf (pow_le r j) (pow_le r j'))
  have e := congrArg (fun t => Semi.res hW t ^ r) (h (j PUnit.unit) (j' PUnit.unit))
  simp only [map_mul, mul_pow, GlobalTheory.CuspDim.IsoPow.res_res] at e
  rw [res_pow_g]
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  exact e

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    Semi.res h' (blockUnit i j h) = blockUnit i j (h'.trans h) :=
  GlobalTheory.CuspDim.IsoPow.res_res _ _ _

theorem ev_res_pow {p : (MP ℤ m n) ⟶ Sp ℤ} {W U : (MP ℤ m n).Opens} (h : W ≤ U) (v : Γ(MP ℤ m n, U)ˣ) (r : ℕ)
    {y : CxPts p σ₀} (hy : y ∈ ptsIn p σ₀ W) :
    CxPts.ev p σ₀ W ((Semi.res h v ^ r : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      CxPts.ev p σ₀ U (v : Γ(MP ℤ m n, U)) y ^ r := by
  rw [Units.val_pow_eq_pow_val, CxPts.ev_eq hy, map_pow, ← CxPts.ev_eq hy]
  exact congrArg (· ^ r) (CxPts.ev_res h hy _)

theorem chart_pow {B : LB (MP ℤ m n)} (A : Geo.HermLine (Bk n)) (r : ℕ) (j : PUnit.{1} → B.ι) (c c' : ∀ k, Bk n k)
    (v : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c')ˣ)
    (h : Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c) v =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c') v' *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤
              prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c)
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v ^ r) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c')
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v' ^ r) *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤
            prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ (powLine A r).a k := by
  have hW : (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') :=
    inf_le_inf_right _ (pow_le r j)
  have e := congrArg (fun t => Semi.res hW t ^ r) h
  simp only [map_mul, mul_pow, map_prod, map_zpow, res_blockUnit, GlobalTheory.CuspDim.IsoPow.res_res] at e
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  refine e.trans (congrArg _ ?_)
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]
  exact congrArg (fun t => (t ^ A.a k) ^ r) (res_blockUnit _ _ _ _)

theorem isHermRep_pow (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) (r : ℕ)
    (hM : IsHermRep M A) : IsHermRep (M.pow r) (powLine A r) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨fun (j : PUnit.{1} → M.B.ι) c =>
    Semi.res (inf_le_inf_right _ (pow_le (B := M.B) r j)) (u (j PUnit.unit) c) ^ r, ?_, ?_, ?_⟩
  · intro j j' c
    exact frame_pow M.B r (mchart c) (fun i => u i c) (fun i j => h₁ i j c) j j'
  · intro j c c'
    exact chart_pow A r j c c' _ _ (h₂ (j PUnit.unit) c c')
  · intro (j : PUnit.{1} → M.B.ι) c y z hz hy
    have hy' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U (j PUnit.unit) ⊓ mchart c) :=
      CxPts.ptsIn_mono (inf_le_inf_right _ (pow_le (B := M.B) r j)) hy
    have e := h₃ (j PUnit.unit) c y z hz hy'
    have eφ : ((M.pow r).φ σ₀).φ j y = r * (M.φ σ₀).φ (j PUnit.unit) y := by
      exact ((M.φ σ₀).zpow_φ r j y).trans (by simp)
    have ev := ev_res_pow (p := mpStr ℤ m n) (inf_le_inf_right (mchart c) (pow_le (B := M.B) r j))
      (u (j PUnit.unit) c) r hy
    beta_reduce
    rw [h_powLine, e, eφ, show CxPts.ev (mpStr ℤ m n) σ₀ ((M.pow r).B.U j ⊓ mchart c) _ y = _ from ev, norm_pow, mul_pow, mul_pow, ← Finset.prod_pow,
      ← Real.exp_nat_mul, mul_div_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]

end GlobalTheory.CompanionTheory.MPDict.PowRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem lintegral_close {R : Type} [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) {S N : Set R}
    (hS : MeasurableSet S) (hfin : ν S ≠ ⊤) (hN : ν N = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ s ∈ S, s ∉ N → G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ) :
    |(∫⁻ s in S, G s ∂ν).toReal - (ν S).toReal| ≤ δ * (ν S).toReal := by
  have hae : ∀ᵐ s ∂(ν.restrict S), G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ := by
    rw [ae_restrict_iff' hS]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with s hs hsS
    exact h s hsS hs
  have hup : ∫⁻ s in S, G s ∂ν ≤ ENNReal.ofReal (1 + δ) * ν S := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).2])
  have hlo : ENNReal.ofReal (1 - δ) * ν S ≤ ∫⁻ s in S, G s ∂ν := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).1])
  have hfinU : ENNReal.ofReal (1 + δ) * ν S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hup' : (∫⁻ s in S, G s ∂ν).toReal ≤ (1 + δ) * (ν S).toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (1 - δ) * (ν S).toReal ≤ (∫⁻ s in S, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [abs_le]
  constructor <;> nlinarith

theorem density_close {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hM : 3 ≤ M) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lv : Measure (Fv F v)) (hlv : IsStdV v lv)
    (mv : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hmv : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M) (coordHerm (Fv F v) σ b lv 1) mv)
    {x δ : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 →
      |(mv (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ δ)
    (hav : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U →
      |(coordW (Fv F v) b lv 1 M (latV b v ∩ {X | algebraMap F (Fv F v) (1 / 2) *
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal -
        x * (lv V).toReal| ≤ ε * (lv V).toReal) :
    |x - 1| ≤ δ := by
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW 1 M
  obtain ⟨n1, n2⟩ := GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hσ M J hJ (by omega) v
    (coordW (Fv F v) b lv 1 M) lv (hW 1 M) hlv.1
  have hmv' : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M)
      (lv.map (hermScal (Fv F v) σ)) mv := by
    rw [(GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hσ (Fv F v) d b).2.2 lv hlv.1]
    exact hmv
  have FF := GlobalTheory.CompanionTheory.SW.isFibreFamily_length F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) _ lv
    (hW 1 M) hlv.1 n1 n2 mv hmv'
  have hqc : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0) :=
    GlobalTheory.CompanionTheory.SW.LenFib.continuous_qR (Fv F v) hσ J
  obtain ⟨hLc, hLo, -, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have hLm : MeasurableSet (latV (M := M) (n := 1) b v) := hLo.measurableSet

  let φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ := (latV b v).indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hLo.frontier_eq, hLc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hLc fun X hX => ?_
    exact Set.indicator_of_notMem hX _
  obtain ⟨hI, -⟩ := FF.2.2 φ hφc hφs (Set.subset_univ _)
  have hfinG : ∀ s : Fv F v, s ≠ 0 → mv (hermScal (Fv F v) σ s) (latV b v) ≠ ⊤ := by
    intro s hs
    have h := hI s (isUnit_iff_ne_zero.2 hs)
    rw [integrable_indicator_iff hLm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨U, hU, hUV⟩ := hav ε hε
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  set S : Set (Fv F v) := interior U ∩ (v.adicCompletionIntegers F : Set (Fv F v)) with hSdef
  have hSo : IsOpen S := isOpen_interior.inter hOo
  have h0S : (0 : Fv F v) ∈ S := ⟨mem_interior_iff_mem_nhds.2 hU, zero_mem _⟩
  have hSfin : lv S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [hlv.2]
    exact ENNReal.one_ne_top
  have hSpos : 0 < (lv S).toReal :=
    ENNReal.toReal_pos (hSo.measure_ne_zero lv ⟨0, h0S⟩) hSfin
  have h1 := hUV S hSo.measurableSet (Set.inter_subset_left.trans interior_subset)
  have h2 := lintegral_close lv (fun s => mv (hermScal (Fv F v) σ s) (latV b v)) hSo.measurableSet hSfin
    n1 hδ (fun s hs hs0 => ⟨hfinG s (not_not.1 hs0).ne_zero, hB s hs.2 (not_not.1 hs0).ne_zero⟩)
  rw [← GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.fibre_mass_eq _ lv _ hqc.measurable _ _ FF hLm hSo.measurableSet] at h2
  have h3 : |x - 1| * (lv S).toReal ≤ (δ + ε) * (lv S).toReal := by
    have e : (x - 1) * (lv S).toReal = (x * (lv S).toReal -
        (coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal) +
        ((coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        (lv S).toReal) := by ring
    rw [← abs_of_pos hSpos, ← abs_mul, abs_of_pos hSpos, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm]
    have h1' : |(coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        x * (lv S).toReal| ≤ ε * (lv S).toReal := h1
    linarith
  exact le_of_mul_le_mul_right h3 hSpos

end GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal - 1| := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b lam hlam m hm
  have hL := fun v => GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have avg := fun v => GlobalTheory.T.local_volume_rank_one_isotropic F E σ hσ M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v)
    (latV b v) (hL v).1 (hL v).2.1
  refine ⟨fun v => (avg v).1, ?_⟩
  refine Summable.of_norm_bounded_eventually
    (g := fun v : HeightOneSpectrum (𝓞 F) => 2 * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
    ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left 2) ?_
  filter_upwards [GlobalTheory.T.rank_one_local_density_almost_all F E σ hσ M J hJ hM d b] with v hv
  obtain ⟨m', hm'⟩ := GlobalTheory.CompanionTheory.SW.GoodMass.exists_family hσ hJ b v (lam v) (hlam v) 1
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := GlobalTheory.CompanionTheory.SW.GoodMass.absNorm_one_le v
  have hd := GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.density_close hσ hJ hM b v (lam v) (hlam v) m' hm'
    (x := (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal)
    (δ := 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1)) (by positivity)
    (hv (lam v) (hlam v) m' hm') (avg v).2
  rw [Real.norm_eq_abs, abs_abs]
  refine hd.trans ?_
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ hq (by omega))
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_volume_rank_one_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal - 1| := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModule
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModule
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi

theorem exists_bound_inf {F : Type} [Field F] [NumberField F] (C : Set (Ainf F)) (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ C, ∏ w : InfinitePlace F, ‖y w‖ ^ w.mult ≤ B := by
  have hc : Continuous fun y : Ainf F => ∏ w : InfinitePlace F, ‖y w‖ ^ w.mult :=
    continuous_finsetProd _ fun w _ => ((continuous_apply w).norm).pow _
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem exists_bound_fin {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (C : Set (Fv F v)) (hC : IsCompact C) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ C, ‖y‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hC.image continuous_norm).bddAbove
  exact ⟨max B 1, le_max_right _ _, fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem md_le_of_bounds {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : ℝ) (c : HeightOneSpectrum (𝓞 F) → ℝ) (hc : ∀ v ∈ S, 1 ≤ c v) (b : (AF F)ˣ)
    (hinf : ∏ w : InfinitePlace F, ‖(b : AF F).1 w‖ ^ w.mult ≤ B)
    (hS : ∀ v ∈ S, ‖(b : AF F).2 v‖ ≤ c v)
    (hout : ∀ v, v ∉ S → (b : AF F).2 v ∈ v.adicCompletionIntegers F) :
    md b ≤ B * ∏ v ∈ S, c v := by
  have hfin := IdeleGroup.finite_mulSupport_norm (K := F) b
  set T : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset ∪ S with hT
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ‖(b : AF F).2 v‖) ⊆ (T : Set _) := by
    intro v hv
    simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hv
  have hfp : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(b : AF F).2 v‖ ≤ ∏ v ∈ S, c v := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc ∏ v ∈ T, ‖(b : AF F).2 v‖ ≤ ∏ v ∈ T, (if v ∈ S then c v else 1) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
          by_cases hv : v ∈ S
          · simpa [hv] using hS v hv
          · simpa [hv] using (Valued.toNormedField.norm_le_one_iff).2
              ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 (hout v hv))
      _ = ∏ v ∈ S, (if v ∈ S then c v else 1) := by
          refine (Finset.prod_subset Finset.subset_union_right fun v _ hv => ?_).symm
          simp [hv]
      _ = ∏ v ∈ S, c v := Finset.prod_congr rfl fun v hv => by simp [hv]
  have hcS : 0 ≤ ∏ v ∈ S, c v := Finset.prod_nonneg fun v hv => zero_le_one.trans (hc v hv)
  have hB0 : 0 ≤ ∏ w : InfinitePlace F, ‖(b : AF F).1 w‖ ^ w.mult :=
    Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  have hfp0 : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(b : AF F).2 v‖ :=
    finprod_nonneg fun _ => norm_nonneg _
  rw [md, IdeleGroup.ideleModule_eq]
  exact mul_le_mul hinf hfp hfp0 (hB0.trans hinf)

theorem th_pure_vanish : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), HasCompactSupport G → (∀ v ∈ S, HasCompactSupport (g v)) →
    ∃ R : ℝ, ∀ a : (AF F)ˣ, R < md a → th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = 0 := by
  intro F _ _ S G g hG hg
  obtain ⟨B, -, hB⟩ := exists_bound_inf (F := F) (tsupport G) hG
  have hfin : ∀ v ∈ S, ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ tsupport (g v), ‖y‖ ≤ B :=
    fun v hv => exists_bound_fin v _ (hg v hv)
  choose! c hc1 hc using hfin
  refine ⟨B * ∏ v ∈ S, c v, fun a ha => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * a) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (by simp [th, hall])
  rw [pure_rv_zero_apply] at ht
  split_ifs at ht with hint
  · have hprod : G ((pr t * a : (AF F)ˣ) : AF F).1 * ∏ v ∈ S, g v (((pr t * a : (AF F)ˣ) : AF F).2 v) ≠ 0 :=
      fun h => ht (by rw [h]; simp)
    have hGne := left_ne_zero_of_mul hprod
    have hgne := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hprod)
    have hle := md_le_of_bounds S B c hc1 (pr t * a)
      (hB _ (subset_tsupport _ (Function.mem_support.2 hGne)))
      (fun v hv => hc v hv _ (subset_tsupport _ (Function.mem_support.2 (hgne v hv)))) hint
    rw [md_mul, md_pr, one_mul] at hle
    exact absurd ha (not_lt.2 hle)
  · exact ht rfl

end GlobalTheory.CompanionTheory.BasePsi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModuleStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_vanishes_large_module : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), HasCompactSupport G → (∀ v ∈ S, HasCompactSupport (g v)) →
    ∃ R : ℝ, ∀ a : (AF F)ˣ, R < md a → th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | exact GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | (intros; apply GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish <;> assumption)
end
end

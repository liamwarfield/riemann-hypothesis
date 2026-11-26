module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedCuspidalHolomorphicLeSpanAlgebraicCuspSec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddAllOfThetaSumOnCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormRationalDescentToBase
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormRationalDescentToBase
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CoverDescRat


set_option maxHeartbeats 1000000 in
theorem mu_mul_level_of_tie (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hJ : LawsJ T) (hlev : R.toLevCh.Is A.μ0) (hT : TieIn T R κ v₀) (j : Fin D.R.m) :
    ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, T.mu ((j : ℕ) + 1) T.σ₀ (g * k) = T.mu ((j : ℕ) + 1) T.σ₀ g := by
  intro k hk g
  have hj := inR j
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨τ, hτ⟩ := GlobalTheory.MuLevel.exists_ext (L := D.what₂.LL) T.σ₀
  obtain ⟨hf, hk'⟩ := (hJ.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := hJ.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨y, hy, hu, hc⟩ := GlobalTheory.MuLevel.exists_root_of_level _ _ hodd k hf hk'
  have hm := R.C.isMu0 j
  have h1 : R.mu0 ((j : ℕ) + 1) y = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hlev.mu0 j) hm.tame _
      (fun P hP => hm.unr P fun a ha => hP ?_) y hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  have hg : GoodEmb T.Q.c (τ.comp (algebraMap T.Q.c.F D.what₂.LL)) := hτ ▸ hσ
  obtain ⟨z, hz1, hz2⟩ := (hT.chiR j τ hg).2.2.2.1 y hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL z = 1 :=
    D.what₂.embLL.injective (by rw [← hz1, h1, map_one, Circle.coe_one])
  have hχ : T.chiW ((j : ℕ) + 1) T.σ₀ y = 1 := by
    rw [hτ] at hz2
    apply Subtype.ext
    rw [hz2, h2, map_one, Circle.coe_one]
  have hMV := hJ.muVal _ hj _ hσ
  obtain ⟨x, hx⟩ := hMV.1 g
  have hxy : IsDetRoot _ (g * k) (x * y) := (GlobalTheory.Member.isDetRoot_laws D _).2.2.2 g k x y hx hy
  rw [hMV.2 _ _ hxy, hMV.2 g x hx, map_mul, hχ, mul_one]


set_option maxHeartbeats 1000000 in
theorem cover_desc_rat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ φ ∈ C.ratForms (wtA (κ i)) (κ i).n, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) ∧ φ = ∑ a, C.σ₂ (x a) • ψ a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hJ hlev _ _ _ _ hT i _ hV _ l _ C hC hP φ hφ hinv
  have hn : 0 < (κ i).n := by
    obtain ⟨t⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
    rw [(hT.kap i t).2.2]
    unfold Ranks.nV
    have := D.R.t_odd.pos
    omega
  exact GlobalTheory.CoverFormDesc.cover_form_desc D T hJ ((i : ℕ) + 1) (inR i) T.σ₀ T.toCore.good_σ₀ C hC.1 (wtA (κ i)) (κ i).n (dom_wtA (κ i)) hP
    (GlobalTheory.T.boundedCuspidalHolomorphic_le_span_algebraicCuspSections D T hJ ((i : ℕ) + 1) (inR i) T.σ₀ T.toCore.good_σ₀ (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs hT.kap i) hn)
    (mu_mul_level_of_tie D G Pl0 T0 A T R κ v₀ hJ hlev hT i) φ hφ hinv

end GlobalTheory.CoverDescRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormRationalDescentToBaseStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverForm_rational_descent_to_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ φ ∈ C.ratForms (wtA (κ i)) (κ i).n, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) ∧ φ = ∑ a, C.σ₂ (x a) • ψ a := by
  first | exact @GlobalTheory.CoverDescRat.cover_desc_rat | exact GlobalTheory.CoverDescRat.cover_desc_rat | (intros; apply GlobalTheory.CoverDescRat.cover_desc_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlaces
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ScaleInt

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_avoid {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) (hq : q.IsPrime)
    (s : Finset (HeightOneSpectrum (𝓞 K))) (hs : ∀ p ∈ s, p.asIdeal ≠ q) (N : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ t : 𝓞 K, t ∉ q ∧ ∀ p ∈ s, t ∈ p.asIdeal ^ N p := by
  have hle : ¬ (s.prod fun p => p.asIdeal ^ N p) ≤ q := by
    rw [hq.prod_le]
    rintro ⟨p, hp, hpq⟩
    rcases Nat.eq_zero_or_pos (N p) with h0 | hpos
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hpq
      exact hq.ne_top hpq
    · have h1 : p.asIdeal ≤ q := hq.le_of_pow_le hpq
      exact hs p hp (p.isMaximal.eq_of_le hq.ne_top h1)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.1 hle
  exact ⟨t, htq, fun p hp => (Ideal.prod_le_inf.trans (Finset.inf_le hp)) ht⟩

theorem le_vLa_of_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K} (n : ℕ)
    (ht : t ∈ p.asIdeal ^ n) (ht0 : t ≠ 0) : (n : ℤ) ≤ vLa p (t : K) := by
  have h := (p.intValuation_le_pow_iff_mem t n).2 ht
  have hne : p.intValuation t ≠ 0 := HeightOneSpectrum.intValuation_ne_zero p t ht0
  have e : p.valuation K (t : K) = p.intValuation t := p.valuation_of_algebraMap t
  unfold vLa
  rw [e]
  have := (WithZero.log_le_log hne (by simp)).2 h
  simp at this
  omega

theorem vLa_eq_zero_of_not_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K}
    (ht : t ∉ p.asIdeal) : vLa p (t : K) = 0 := by
  unfold vLa
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem p).mpr ht, WithZero.log_one, neg_zero]

end GlobalTheory.ScaleInt

namespace GlobalTheory.ScaleInt


set_option maxHeartbeats 800000 in
theorem smul_mem_baseInt : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos →
    ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite →
    ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q},
      ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  intro D T hT i κ hκ q hq P hP ψ hψ
  obtain ⟨f, ⟨hfs, hfh, hfv⟩, rfl⟩ := hψ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hcusp : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtA κ) κ.n := GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hT _ hj κ hκ f hfs hfh
  have hbd : ∀ p : HeightOneSpectrum (𝓞 T.Q.c.F), ∃ κ' : T.Q.c.F, κ' ≠ 0 ∧
      GlobalTheory.GoodPts.BddAll (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p κ' f := by
    intro p
    obtain ⟨pr, hpr, hmem⟩ := exists_prime_mem p
    exact GlobalTheory.CuspBound.exists_bddAll_cusp _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hT.unf _ hj) p pr hpr hmem
      (goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne pr hpr) _ _ f
      (dom_wtA κ) hcusp
  choose κ' hκ0 hκb using hbd
  obtain ⟨t, htq, htm⟩ := exists_avoid q hq (hP.toFinset.filter fun p => p.asIdeal ≠ q)
    (fun p hp => (Finset.mem_filter.1 hp).2) (fun p => (vLa p (κ' p)).toNat)
  have ht0 : t ≠ 0 := fun h => htq (h ▸ q.zero_mem)
  have htK : (t : T.Q.c.F) ≠ 0 := by exact_mod_cast ht0
  refine ⟨t, htq, (t : T.Q.c.F) • f, ⟨(sec _ _ _ _).smul_mem _ hfs, ?_, ?_⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hfh
  · intro la hla v hv
    have hV := isVal_valSet la v hv
    rw [hV.smul _ _ htK]
    by_cases hlq : la.asIdeal = q
    · have h0 : vAdd la (t : T.Q.c.F) = 0 := vLa_eq_zero_of_not_mem la (hlq ▸ htq)
      rw [h0]
      simpa using hfv la hlq v hv
    · have hmem : la ∈ hP.toFinset.filter fun p => p.asIdeal ≠ q :=
        Finset.mem_filter.2 ⟨hP.mem_toFinset.2 hla, hlq⟩
      have hge : (vLa la (κ' la) : ℤ) ≤ vAdd la (t : T.Q.c.F) :=
        (Int.self_le_toNat _).trans (le_vLa_of_mem la _ (htm la hmem) ht0)
      obtain ⟨y, rfl⟩ := hv
      have hb := (GlobalTheory.GoodPtsModel.bddAll_iff_vAtV (hκ0 la) f).1 (hκb la) y
      exact hb.trans (add_le_add (by exact_mod_cast hge) le_rfl)
  · simp only [CoreJ.phiJ, map_smulₛₗ, LinearMap.map_smul, smul_comm ((lieFac _ _ _ : ℝ) : ℂ)]
    rfl

end GlobalTheory.ScaleInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlacesStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos → ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite → ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q}, ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  first | exact @GlobalTheory.ScaleInt.smul_mem_baseInt | exact GlobalTheory.ScaleInt.smul_mem_baseInt | (intros; apply GlobalTheory.ScaleInt.smul_mem_baseInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPartitionOneIntegralAtPlaces
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_partition_one_integral_at_places (L : Type) [Field L] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : S.Nonempty) (Y : S → Finset L)
    (hY : ∀ la, ∀ y ∈ Y la, la.1.valuation L y ≤ 1) :
    ∃ e : S → L, ∑ la, e la = 1 ∧
      ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, la'.valuation L (e la * y) ≤ 1 := by
  classical
  have hb : ∀ (_la : S) (y : L) (la' : HeightOneSpectrum (𝓞 L)),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) * la'.valuation L y ≤ 1 := by
    intro _ y la'
    by_cases hy : la'.valuation L y = 0
    · exact ⟨0, by simp [hy]⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = la'.valuation L y := ⟨_, WithZero.exp_log hy⟩
      refine ⟨m.toNat, ?_⟩
      rw [← hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  choose n hn using hb
  let N : ℕ := ∑ la : S, ∑ y ∈ Y la, ∑ la' ∈ S, n la y la'
  have hN : ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, n la y la' ≤ N := by
    intro la y hy la' hla'
    calc n la y la' ≤ ∑ la'' ∈ S, n la y la'' :=
          Finset.single_le_sum (f := fun la'' => n la y la'') (fun _ _ => Nat.zero_le _) hla'
      _ ≤ ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'' :=
          Finset.single_le_sum (f := fun y' => ∑ la'' ∈ S, n la y' la'') (fun _ _ => Nat.zero_le _) hy
      _ ≤ N := Finset.single_le_sum (f := fun la => ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ la)
  let J : S → Ideal (𝓞 L) := fun la => ∏ la' ∈ S.erase la.1, la'.asIdeal ^ N
  have htop : ⨆ la ∈ (Finset.univ : Finset S), J la = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hJM : ∀ la : S, J la ≤ M := fun la =>
      le_trans (le_iSup₂_of_le (f := fun la (_ : la ∈ (Finset.univ : Finset S)) => J la)
        la (Finset.mem_univ _) le_rfl) hle
    obtain ⟨la0, hla0⟩ := hS
    obtain ⟨la1, hla1, h1⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la0, hla0⟩)
    have hle1 : la1.asIdeal ≤ M := hM.isPrime.le_of_pow_le h1
    have heq : la1.asIdeal = M := la1.isMaximal.eq_of_le hM.ne_top hle1
    have hla1S : la1 ∈ S := Finset.mem_of_mem_erase hla1
    obtain ⟨la2, hla2, h2⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la1, hla1S⟩)
    have hle2 : la2.asIdeal ≤ la1.asIdeal := heq ▸ hM.isPrime.le_of_pow_le h2
    have h22 : la2.asIdeal = la1.asIdeal := la2.isMaximal.eq_of_le la1.isPrime.ne_top hle2
    exact (Finset.ne_of_mem_erase hla2) (HeightOneSpectrum.ext h22)
  have h1 : (1 : 𝓞 L) ∈ ⨆ la ∈ (Finset.univ : Finset S), J la := htop ▸ Submodule.mem_top
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 h1
  refine ⟨fun la => ((μ la : 𝓞 L) : L), ?_, ?_⟩
  · have := congrArg (fun x : 𝓞 L => (x : L)) hμ
    simpa using this
  · intro la y hy la' hla'
    rw [map_mul]
    by_cases h : la' = la.1
    · subst h
      calc la.1.valuation L ((μ la : 𝓞 L) : L) * la.1.valuation L y ≤ 1 * 1 :=
            mul_le_mul' (HeightOneSpectrum.valuation_le_one _ _) (hY la y hy)
        _ = 1 := one_mul 1
    · have hmem : (μ la : 𝓞 L) ∈ la'.asIdeal ^ N := by
        have hm : (μ la : 𝓞 L) ∈ J la := (μ la).2
        have hs : la' ∈ S.erase la.1 := Finset.mem_erase.2 ⟨h, hla'⟩
        have : J la ≤ la'.asIdeal ^ N := by
          show ∏ la'' ∈ S.erase la.1, la''.asIdeal ^ N ≤ _
          rw [← Finset.mul_prod_erase _ _ hs]
          exact le_trans Ideal.mul_le_inf inf_le_left
        exact this hm
      have hv : la'.valuation L ((μ la : 𝓞 L) : L) ≤ WithZero.exp (-(N : ℤ)) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          Ideal.dvd_span_singleton]
        exact hmem
      calc la'.valuation L ((μ la : 𝓞 L) : L) * la'.valuation L y
          ≤ WithZero.exp (-(N : ℤ)) * la'.valuation L y := mul_le_mul' hv le_rfl
        _ ≤ WithZero.exp (-(n la y la' : ℤ)) * la'.valuation L y := by
            refine mul_le_mul' ?_ le_rfl
            rw [WithZero.exp_le_exp]
            have := hN la y hy la' hla'
            omega
        _ ≤ 1 := hn la y la'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrime
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescGlue

open GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries

theorem finite_of_overPrime {L : Type} [Field L] [NumberField L] (l : ℕ) (hl : l.Prime)
    (S : Set (HeightOneSpectrum (𝓞 L))) (h : OverPrime l S) : S.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun la hla => ?_
  show la.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact h la hla

theorem finite_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : S.Finite) : (below φ S).Finite := by
  have e : below φ S = ⋃ la ∈ S, {p : HeightOneSpectrum (𝓞 K) |
      p.asIdeal = la.asIdeal.comap (RingOfIntegers.mapRingHom φ)} := by
    ext p; simp [below]
  rw [e]
  exact hS.biUnion fun la _ => Set.Subsingleton.finite fun p1 h1 p2 h2 =>
    HeightOneSpectrum.ext (h1.trans h2.symm)


set_option maxHeartbeats 800000 in
theorem glue : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.OverPrime l S → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc S → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → (∀ la ∈ S, ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a) → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ S (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc S)) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT h1 h2 h3 h4 h5 h6 i hVS hV hFP l hl C hC hPin S hS hUn φ hφmem hKf
    m x ψ hψ hφ hloc
  classical
  have hσ : ∀ t : T.Q.c.F, C.σ₂ (C.inc t) = T.σ₀ t := fun t => by
    rw [← RingHom.comp_apply, hC.1.2.2.1]
  have hfin : S.Finite := finite_of_overPrime l hl S hS
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst hS0
    refine ⟨m, fun a => C.σ₂ (x a), ψ, fun a => ⟨x a, rfl, fun la h => absurd h (Set.notMem_empty la)⟩,
      fun a => ?_, hφ⟩
    obtain ⟨f, ⟨hf1, hf2⟩, hf⟩ := hψ a
    exact ⟨f, ⟨hf1, hf2, fun p hp => by
      obtain ⟨la, hla, _⟩ := hp
      exact absurd hla (Set.notMem_empty la)⟩, hf⟩
  set S' := hfin.toFinset with hS'
  have hmem : ∀ la : S', la.1 ∈ S := fun la => hfin.mem_toFinset.1 la.2
  choose m' x' ψ' hx' hψ' hφ' using fun la : S' => hloc la.1 (hmem la)
  choose a' ha' hav using fun (la : S') (a : Fin (m' la)) => hx' la a
  have hset : ∀ la : S', below C.inc {la.1} =
      {p | p.asIdeal = la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc)} := fun la => by
    ext p; simp [below]
  choose t ht htψ using fun (la : S') (a : Fin (m' la)) =>
    GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places D T hT i (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs h6.kap i)
      (la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc))
      (Ideal.IsPrime.comap _ (hK := la.1.isPrime)) (below C.inc S) (finite_below C.inc hfin) (ψ' la a)
      (hset la ▸ hψ' la a)
  have hte : ∀ (la : S') (a : Fin (m' la)), la.1.valuation _ (C.inc (t la a : T.Q.c.F)) = 1 := fun la a => by
    have e : C.inc (t la a : T.Q.c.F) = ((RingOfIntegers.mapRingHom C.inc (t la a) : 𝓞 C.d.c₂.F) : C.d.c₂.F) := rfl
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem la.1).mpr fun h => ht la a (Ideal.mem_comap.2 h)
  have ht0 : ∀ (la : S') (a : Fin (m' la)), T.σ₀ (t la a : T.Q.c.F) ≠ 0 := fun la a => by
    refine (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.mpr ?_)
    rintro h0
    exact ht la a (h0 ▸ Ideal.zero_mem _)
  let Y : S' → Finset C.d.c₂.F := fun la => Finset.univ.image fun a => a' la a / C.inc (t la a : T.Q.c.F)
  have hY : ∀ la, ∀ y ∈ Y la, la.1.valuation _ y ≤ 1 := by
    intro la y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    rw [map_div₀, hte, div_one]
    exact hav la a la.1 (Set.mem_singleton _)
  have hne : S'.Nonempty := by
    obtain ⟨la, h⟩ := hSne
    exact ⟨la, hfin.mem_toFinset.2 h⟩
  obtain ⟨e, he1, he⟩ := GlobalTheory.exists_partition_one_integral_at_places _ S' hne Y hY
  let ι := Σ la : S', Fin (m' la)
  let ε := Fintype.equivFin ι
  let X : ι → ℂ := fun s => C.σ₂ (e s.1 * (a' s.1 s.2 / C.inc (t s.1 s.2 : T.Q.c.F)))
  let Ψ : ι → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ) := fun s => T.σ₀ (t s.1 s.2 : T.Q.c.F) • ψ' s.1 s.2
  have key : ∀ s : ι, X s • Ψ s = C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := by
    intro s
    simp only [X, Ψ, smul_smul, map_mul, map_div₀, hσ, ha']
    congr 1
    field_simp [ht0 s.1 s.2]
  refine ⟨Fintype.card ι, fun k => X (ε.symm k), fun k => Ψ (ε.symm k), fun k => ⟨_, rfl, fun la'' h'' =>
    he _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)) la'' (hfin.mem_toFinset.2 h'')⟩,
    fun k => htψ _ _, ?_⟩
  symm
  calc ∑ k, X (ε.symm k) • Ψ (ε.symm k) = ∑ s : ι, X s • Ψ s := Equiv.sum_comp ε.symm (fun s => X s • Ψ s)
    _ = ∑ s : ι, C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := Finset.sum_congr rfl fun s _ => key s
    _ = ∑ la : S', ∑ a : Fin (m' la), C.σ₂ (e la) • (x' la a • ψ' la a) := Fintype.sum_sigma _
    _ = ∑ la : S', C.σ₂ (e la) • φ := Finset.sum_congr rfl fun la _ => by rw [← Finset.smul_sum, ← hφ' la]
    _ = φ := by rw [← Finset.sum_smul, ← map_sum, he1, map_one, one_smul]

end GlobalTheory.DescGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrimeStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_integral_decompositions_over_rationalPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.OverPrime l S → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc S → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → (∀ la ∈ S, ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a) → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ S (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc S)) ∧ φ = ∑ a, x' a • ψ' a := by
  first | exact @GlobalTheory.DescGlue.glue | exact GlobalTheory.DescGlue.glue | (intros; apply GlobalTheory.DescGlue.glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAtPlaceOfIntegralCoverReading
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAtPlaceOfIntegralCoverReading
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLocInt

theorem rd_sum {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (s : Fin m → C.d.c₂.F) (g : Fin m → Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (∑ b, s b • g b) = ∑ b, C.σ₂ (s b) • C.rd a (g b) := by
  unfold Cover.rd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smulₛₗ, map_smul, smul_comm]

theorem rd_sub {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (g h : Rul C.d.Xo₂ C.d.c₂) : C.rd a (g - h) = C.rd a g - C.rd a h := by
  unfold Cover.rd
  rw [map_sub, map_sub, smul_sub]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem bddAll_of_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (la' : HeightOneSpectrum (𝓞 C.c'.F)), (∀ y : C.c'.F, la'.valuation C.c'.F y = la.valuation C.d.c₂.F (C.d.eF y)) → ∀ (m : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → (∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b)) ∈ C.intForms a n {la} → GlobalTheory.GoodPts.BddAll (T.Q.Xo j) C.c' la' 1 (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
  intro D T hL j hj σ hσ C hU a n hdom hPin la la' hval m x f hf hmem
  obtain ⟨g₂, ⟨hcs, hint⟩, hrd⟩ := hmem
  have hex : ∀ b, ∃ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull (f b) f₂ := fun b =>
    GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n (f b) (hf b)
  choose f₂ hf₂ using hex
  have hpin : ∀ b, C.rd a (f₂ b) = T.phiJ j σ a (f b) := fun b => hPin.2 (f b) (hf b) (f₂ b) (hf₂ b).1 (hf₂ b).2
  have hG : g₂ = ∑ b, C.d.eF (x b) • f₂ b := by
    by_contra hne
    have h0 : g₂ - ∑ b, C.d.eF (x b) • f₂ b ≠ 0 := sub_ne_zero.2 hne
    have hsec : g₂ - ∑ b, C.d.eF (x b) • f₂ b ∈ sec C.d.Xo₂ C.d.c₂ a n :=
      sub_mem hcs.1 (sum_mem fun b _ => Submodule.smul_mem _ _ (hf₂ b).1)
    have hli : LinearIndependent C.d.c₂.F ![g₂ - ∑ b, C.d.eF (x b) • f₂ b] :=
      linearIndependent_unique_iff.2 h0
    have hli2 := GlobalTheory.T.coverSections_linearIndependent_adelicReadings D T hL j hj σ hσ C hU hPin.1 a n hdom 1 ![g₂ - ∑ b, C.d.eF (x b) • f₂ b]
      (fun i => by fin_cases i; exact hsec) hli
    have hz : C.rd a (g₂ - ∑ b, C.d.eF (x b) • f₂ b) = 0 := by
      rw [rd_sub, rd_sum, hrd]
      simp only [hpin, sub_self]
    exact hli2.ne_zero 0 (by simpa using hz)
  intro Tv io e ho y hy
  obtain ⟨T', iT, e', y', io₂, y₂, hext, hfin', hio₂, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 Tv io y hy
  have ho₂ : OverLa la T'.V io₂ (e' * e) := by
    refine ⟨Nat.mul_pos hext.1 ho.1, fun z => ?_⟩
    have h1 := hio₂ (C.d.eF.symm z)
    rw [C.d.eF.apply_symm_apply] at h1
    have h2 : vLa la z = vLa la' (C.d.eF.symm z) := by
      simp only [vLa, hval, C.d.eF.apply_symm_apply]
    rw [h1, hext.2.1, ho.2, h2]
    push_cast
    ring
  have hB := (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ C.d.Xo₂ C.d.c₂ la g₂).2 (hint la (Set.mem_singleton la)) T' io₂ (e' * e) ho₂
    y₂ hfin'
  rw [map_one, one_mul] at hB
  have laws := GlobalTheory.firstFiveLaws.1
  letI a1 : Algebra C.c'.F T'.Fr := (iT.comp io).toAlgebra
  letI a2 : Algebra C.d.c₂.F T'.Fr := io₂.toAlgebra
  letI a0 : Algebra T.Q.c.F T'.Fr := ((iT.comp io).comp (incF T.Q.c C.c' C.hle)).toAlgebra
  have hAO : AlgOver T.Q.c C.c' C.hle T'.Fr := fun _ => rfl
  have hcomp : ∀ z : C.c'.F, algebraMap C.d.c₂.F T'.Fr (C.d.eF z) = algebraMap C.c'.F T'.Fr z := hio₂
  have e1 : ∀ b, evI y₂ (f₂ b) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    (hf₂ b).2 T'.Fr hAO hcomp y₂.1 y'.1 hover
  have e2 : ∀ b, evI y' (GlobalTheory.FieldBC.rulBC C.hle (f b)) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf b).1 hAO y'.1
  have e3 : evI y₂ g₂ = evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
    rw [hG, GlobalTheory.GalSup.evI_sum, GlobalTheory.GalSup.evI_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [e1, e2, hio₂]
    rfl
  have hgs : (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈ sec (T.Q.Xo j) C.c' a n :=
    sum_mem fun b _ => Submodule.smul_mem _ _ (GlobalTheory.FieldBCModel.rulBC_mem_sec C.hle (hf b))
  obtain ⟨φ, hφ, hm⟩ := hext.2.2
  letI a3 : Algebra C.c'.F Tv.Fr := io.toAlgebra
  have e4 : evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) =
      iT (evI y (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b))) := by
    have := GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange _ _ _ _ (T.Q.Xo j) C.c').2.2.1 _ hgs.1 φ y.1 y.2.1 y'.1 hm
    exact this.trans (congrArg (fun r : Tv.Fr →+* T'.Fr => r (evR (T.Q.Xo j) C.c' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) y.1)) hφ)
  rw [map_one, one_mul, ← GlobalTheory.CoverBound.inV_map_iff iT hext.1 hext.2.1, ← e4, ← e3]
  exact hB

end GlobalTheory.CoverLocInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAtPlaceOfIntegralCoverReadingStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_at_place_of_integral_cover_reading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (la' : HeightOneSpectrum (𝓞 C.c'.F)), (∀ y : C.c'.F, la'.valuation C.c'.F y = la.valuation C.d.c₂.F (C.d.eF y)) → ∀ (m : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → (∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b)) ∈ C.intForms a n {la} → GlobalTheory.GoodPts.BddAll (T.Q.Xo j) C.c' la' 1 (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
  first | exact @GlobalTheory.CoverLocInt.bddAll_of_mem_intForms | exact GlobalTheory.CoverLocInt.bddAll_of_mem_intForms | (intros; apply GlobalTheory.CoverLocInt.bddAll_of_mem_intForms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrime
open NumberField IsDedekindDomain

namespace GlobalTheory.InertiaEigenvalues.UnramPlace

theorem exists_place_below : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  intro K L _ _ _ _ φ l _ la hl hun
  letI : Algebra K L := φ.toAlgebra
  have hmap : RingOfIntegers.mapRingHom φ = algebraMap (𝓞 K) (𝓞 L) := by
    ext x; rfl
  refine ⟨la.under (𝓞 K), ?_, ?_, ?_⟩
  · ext q
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
    rw [hmap]
    exact ⟨fun h => HeightOneSpectrum.ext h, fun h => h ▸ rfl⟩
  · show ((l : ℕ) : 𝓞 K) ∈ la.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
    rw [Ideal.mem_comap, map_natCast]
    exact hl
  · intro x
    have hu := hun la rfl
    rw [hmap] at hu
    have : la.asIdeal.LiesOver (la.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have he : (la.under (𝓞 K)).asIdeal.ramificationIdx' la.asIdeal = 1 := by
      refine Ideal.ramificationIdx'_spec ?_ ?_
      · rw [pow_one]; exact Ideal.map_comap_le
      · exact hu
    have h := HeightOneSpectrum.valuation_liesOver L (la.under (𝓞 K)) la x
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (la.under (𝓞 K)).ne_bot, he, pow_one] at h
    exact h.symm

end GlobalTheory.InertiaEigenvalues.UnramPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrimeStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_place_below_of_unramified_place_over_prime : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  first | exact @GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below | exact GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below | (intros; apply GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquivStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquiv
open NumberField IsDedekindDomain

namespace GlobalTheory.PlaceTransport

theorem eq_of_forall_le_exp_neg {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  have key : ∀ n : ℕ, (m ≤ -(n : ℤ) ↔ k ≤ -(n : ℤ)) := fun n => by
    simpa only [WithZero.exp_le_exp] using h n
  have hkm : k ≤ m := by
    have := (key (-m).toNat).1 (by omega)
    omega
  have hmk : m ≤ k := by
    have := (key (-k).toNat).2 (by omega)
    omega
  rw [le_antisymm hmk hkm]

theorem intValuation_comap_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (f : R ≃+* S) (w : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap (f : R →+* S) f.surjective w).intValuation x = w.intValuation (f x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hfx : f x ≠ 0 := by simpa using hx
  refine eq_of_forall_le_exp_neg (HeightOneSpectrum.intValuation_ne_zero _ x hx)
    (w.intValuation_ne_zero _ hfx) (HeightOneSpectrum.intValuation_le_one _ x)
    (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  change x ∈ (w.asIdeal.comap (f : R →+* S)) ^ n ↔ f x ∈ w.asIdeal ^ n
  have hJ : ∀ J : Ideal S, J.comap (f : R →+* S) = J.map (f.symm : S →+* R) := fun J =>
    (Ideal.map_comap_of_equiv f.symm).symm
  rw [hJ, ← Ideal.map_pow, ← hJ, Ideal.mem_comap]
  rfl

theorem exists_place_valuation_comp_equiv :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
      (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K),
        ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  intro K L _ _ _ _ e la
  set g : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  refine ⟨HeightOneSpectrum.comap (g : 𝓞 K →+* 𝓞 L) g.surjective la, fun y => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hcast : ∀ c : 𝓞 K, e (algebraMap (𝓞 K) K c) = algebraMap (𝓞 L) L (g c) := fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hcast, hcast, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap_equiv, intValuation_comap_equiv]

end GlobalTheory.PlaceTransport
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlace_valuation_comp_ringEquiv : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K), ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  first | exact @GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv | exact GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv | (intros; apply GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCover
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverBCRead

theorem evR_sum_eq {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ)
    (hσ : C.σ₂.comp C.inc = σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {m m' : ℕ} (x : Fin m → C.c'.F)
    (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j)
    (hf : ∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n)
    (hBC : IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs)
    (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) :
    (∑ b, C.σ₂ (C.d.eF (x b)) * toC (evR (T.Q.Xo j) T.Q.c (f b) y)) =
      ∑ i, C.σ₂ (C.d.eF (as i)) * toC (evR (T.Q.Xo j) T.Q.c (fs i) y) := by
  letI : Algebra C.c'.F (CAt σ) := (C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)).toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle (CAt σ) := by
    intro c0
    show C.σ₂ (C.d.eF (incF T.Q.c C.c' C.hle c0)) = σ c0
    exact RingHom.congr_fun hσ c0
  have h1 := hBC (CAt σ) hA (FrPt.ext C.hle hA y)
  rw [Formalism.L2.Pj.evR_sum_smul] at h1
  simp only [GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf _).1 hA, FrPt.res_ext] at h1
  exact h1

theorem phiJ_sum_eq_of_isBC : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  intro D T j σ C hσ a n m m' x f as fs hf hBC
  have key : (∑ b, C.σ₂ (C.d.eF (x b)) • rdU (T.U j σ) (f b) : FDSec (T.U j σ).X) =
      ∑ i, C.σ₂ (C.d.eF (as i)) • rdU (T.U j σ) (fs i) := by
    funext k z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : z ∈ ((T.U j σ).X k).dom
    · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
      exact evR_sum_eq T j σ C hσ a n x f as fs hf hBC ((T.U j σ).un k ⟨z, h⟩)
    · simp [rdU, dif_neg h]
  let L : FDSec (T.U j σ).X →ₗ[ℂ] (GA D (T.V j σ) → ℂ) := (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))
  have e : ∀ g : T.R j, T.phiJ j σ a g = L (rdU (T.U j σ) g) := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, ← map_smul, ← map_sum, key]

end GlobalTheory.CoverBCRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCoverStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_adelicReading_eq_of_two_baseChange_decomps_on_cover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  first | exact @GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | exact GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | (intros; apply GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlace
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.DescLoc

theorem holSub0_of_cusp : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ T.cuspA j a n, rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) a n) := by
  intro D T j a n f hf
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ a n ⟨f, hf⟩

theorem desc_loc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVstd hV hFP l hl C hC hPin la hla hUn φ hφ hKf m x ψ hψ hsum
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hU := hC.1
  choose f hf hfψ using hψ
  have hfc : ∀ b, f b ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := fun b =>
    GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hL _ hj (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs hTie.kap i) (f b) (hf b).1 (hf b).2
  obtain ⟨p, hbelow, hlp, hval⟩ := GlobalTheory.T.exists_unique_place_below_of_unramified_place_over_prime _ _ C.inc l hl la hla hUn
  obtain ⟨la', hla'⟩ := GlobalTheory.T.exists_finitePlace_valuation_comp_ringEquiv _ _ C.d.eF.toRingEquiv la
  let x' : Fin m → C.c'.F := fun b => C.d.eF.symm (x b)
  have hx' : ∀ b, C.d.eF (x' b) = x b := fun b => C.d.eF.apply_symm_apply (x b)
  have hφ' : (∑ b, C.σ₂ (C.d.eF (x' b)) • T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (f b)) ∈
      C.intForms (wtA (κ i)) (κ i).n {la} := by
    simp only [hx', hfψ]
    rw [← hsum]
    exact hφ
  have hint := GlobalTheory.T.bounded_at_place_of_integral_cover_reading D T hL _ hj T.σ₀ T.good_σ₀ C hU (wtA (κ i)) (κ i).n (dom_wtA (κ i)) hPin la la'
    (fun y => hla' y) m x' f (fun b => (hf b).1) hφ'
  have hmem : (∑ b, x' b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈
      cusp (T.Q.Xo ((i : ℕ) + 1)) C.c' (unfBC C.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
      ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ C.hle _ (T.U ((i : ℕ) + 1)) _ _ (f b) (hf b).1).2.2 (hfc b))
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hvLa : ∀ y : T.Q.c.F, vLa la' (incF T.Q.c C.c' C.hle y) = vLa p y := fun y => by
    unfold vLa
    rw [hla', ← hval]
    rfl
  obtain ⟨m', as, fs, has, hfs, hBC⟩ := GlobalTheory.T.cuspForm_integral_lattice_unramified_descent _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hL.unf _ hj) p l hl hlp hgood
    C.c' C.hle la' hvLa (GlobalTheory.SecFieldChange.cuspBC_holds C.hle _) (wtA (κ i)) (κ i).n (dom_wtA (κ i))
    (hL.cuspFD _ hj _ _ (dom_wtA (κ i))) _ hmem hint
  refine ⟨m', fun k => C.σ₂ (C.d.eF (as k)), fun k => T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (fs k), ?_, ?_, ?_⟩
  · intro k
    refine ⟨C.d.eF (as k), rfl, fun q hq => ?_⟩
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (hla' (as k)).symm.trans_le (has k)
  · intro k
    rw [hbelow]
    refine ⟨fs k, ⟨(cusp_le_sec _ _ _ _ _ (hfs k).1), holSub0_of_cusp D T _ _ _ (fs k) (hfs k).1, ?_⟩, rfl⟩
    intro q hq v hv
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ _ _ _ (fs k)).1 (hfs k).2 v hv
  · rw [hsum]
    have e := GlobalTheory.T.sum_adelicReading_eq_of_two_baseChange_decomps_on_cover D T _ T.σ₀ C hU.2.2.1 (wtA (κ i)) (κ i).n m m' x' f as fs (fun b => (hf b).1) hBC
    simp only [hx', hfψ] at e
    exact e

end GlobalTheory.DescLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlaceStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_descent_integral_forms_one_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  first | exact @GlobalTheory.DescLoc.desc_loc | exact GlobalTheory.DescLoc.desc_loc | (intros; apply GlobalTheory.DescLoc.desc_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCover
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescIntRoad

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem descIntAt_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.DescIntAt T i (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin S hO hU φ hφ hk
  obtain ⟨m, x, ψ, hψ, e⟩ := GlobalTheory.T.coverForm_rational_descent_to_base D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin φ
    (C.intForms_subset _ _ S hφ) hk
  refine GlobalTheory.T.glue_integral_decompositions_over_rationalPrime D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin S hO hU φ hφ hk m x ψ hψ e
    fun la hla => ?_
  have hsub : C.intForms (wtA (κ i)) (κ i).n S ⊆ C.intForms (wtA (κ i)) (κ i).n {la} :=
    Set.image_mono fun _ hf => ⟨hf.1, fun la' h => hf.2 la' (by rw [Set.mem_singleton_iff.1 h]; exact hla)⟩
  exact GlobalTheory.T.unramified_descent_integral_forms_one_place D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin la (hO la hla)
    (fun la' h => hU la' (by rw [Set.mem_singleton_iff.1 h]; exact hla)) φ (hsub hφ) hk m x ψ hψ e

end GlobalTheory.DescIntRoad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCoverStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_descent_integral_forms_tower_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.DescIntAt T i (κ i) := by
  first | exact @GlobalTheory.DescIntRoad.descIntAt_of_laws | exact GlobalTheory.DescIntRoad.descIntAt_of_laws | (intros; apply GlobalTheory.DescIntRoad.descIntAt_of_laws <;> assumption)
end

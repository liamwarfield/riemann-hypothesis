module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiDimensional
theorem UpperTheory.Reformulated.B.MultiDimensional.multi_dim :
    ∀ {P : Type} [inst : Fintype P] (g : P → ℤ → ENNReal), ∑' (x : P → ℤ), ∏ p : P, g p (x p) ≤ ∏ p : P, ∑' (n : ℤ), g p n := by
  intro P _ g
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ x ∈ s, ∏ p : P, g p (x p)
      ≤ ∑ x ∈ Fintype.piFinset (fun p => s.image (fun y : P → ℤ => y p)), ∏ p : P, g p (x p) := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        exact Fintype.mem_piFinset.2 fun p => Finset.mem_image_of_mem _ hx
    _ = ∏ p : P, ∑ n ∈ s.image (fun y : P → ℤ => y p), g p n :=
        (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ p : P, ∑' (n : ℤ), g p n :=
        Finset.prod_le_prod' fun p _ => ENNReal.sum_le_tsum _
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicDenominator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicDenominator
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.AdelicDenom

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} := by
  have h := RestrictedProduct.isOpen_forall_mem (ι := HeightOneSpectrum (𝓞 F))
    (R := fun v => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

theorem natCast_integral (F : Type) [Field F] [NumberField F] (M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (M : Af F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
  GlobalTheory.IntegralFinAdele.natCast_apply F M v ▸
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v (M : 𝓞 F)

theorem exists_common_denominator (F : Type) [Field F] [NumberField F] (K : Set (Af F))
    (hK : IsCompact K) :
    ∃ M : ℕ, 0 < M ∧ ∀ a ∈ K, ∀ v,
      ((M : Af F) * a) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  let U : {M : ℕ // 0 < M} → Set (Af F) := fun M =>
    (fun a => (M.1 : Af F) * a) ⁻¹'
      {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  have hU : ∀ M, IsOpen (U M) := fun M =>
    (isOpen_integral F).preimage (continuous_const_mul _)
  have hcov : K ⊆ ⋃ M, U M := fun a _ => by
    obtain ⟨M, hM, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a
    exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  refine ⟨∏ m ∈ t, m.1, Finset.prod_pos fun m _ => m.2, fun a ha v => ?_⟩
  obtain ⟨m, hm, ham⟩ := Set.mem_iUnion₂.1 (ht ha)
  obtain ⟨c, hc⟩ : m.1 ∣ ∏ m ∈ t, m.1 := Finset.dvd_prod_of_mem (fun m => m.1) hm
  have h : ((∏ m ∈ t, m.1 : ℕ) : Af F) * a = (c : Af F) * ((m.1 : Af F) * a) := by
    rw [hc, Nat.cast_mul]; ring
  rw [h, GlobalTheory.IntegralFinAdele.mul_apply']
  exact mul_mem (natCast_integral F c v) (ham v)

theorem exists_denominator_of_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (C : Set (Af F ⊗[F] E)), IsCompact C →
    ∃ d : ℕ, 0 < d ∧ ∀ x : E, (1 : Af F) ⊗ₜ[F] x ∈ C → ∃ y : 𝓞 E, (d : E) * x = y := by
  intro F E _ _ _ _ _ C hC
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let ε := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (Af F) ε
  have hcont : ∀ k, Continuous (b.coord k) := fun k =>
    IsModuleTopology.continuous_of_linearMap (b.coord k)
  have hK : IsCompact (⋃ k, (b.coord k) '' C) :=
    isCompact_iUnion fun k => hC.image (hcont k)
  obtain ⟨M, hM, hMK⟩ := exists_common_denominator F _ hK

  have : Algebra.IsAlgebraic ℤ E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).2 inferInstance
  have hm : ∀ k, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * ε k) := fun k => by
    obtain ⟨m, y, hm, hmy⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E)
      (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (ε k))
    refine ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
    rw [← nsmul_eq_mul, hmy]
    exact RingOfIntegers.isIntegral_coe y
  choose m hm0 hmi using hm
  refine ⟨M * ∏ k, m k, Nat.mul_pos hM (Finset.prod_pos fun k _ => hm0 k), fun x hx => ?_⟩

  have hcoord : ∀ k, IsIntegral ℤ ((M : F) * ε.repr x k) := fun k => by
    have hmem : b.coord k ((1 : Af F) ⊗ₜ[F] x) ∈ ⋃ k, (b.coord k) '' C :=
      Set.mem_iUnion.2 ⟨k, Set.mem_image_of_mem _ hx⟩
    have hrepr : b.coord k ((1 : Af F) ⊗ₜ[F] x) = algebraMap F (Af F) (ε.repr x k) := by
      simp [b, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
    have h := hMK _ hmem
    rw [hrepr, ← map_natCast (algebraMap F (Af F)) M, ← map_mul] at h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h
    rw [hy]
    exact RingOfIntegers.isIntegral_coe y

  have hP : ∀ k, IsIntegral ℤ (((∏ j, m j : ℕ) : E) * ε k) := fun k => by
    obtain ⟨c, hc⟩ : m k ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ k)
    have : ((∏ j, m j : ℕ) : E) * ε k = (c : E) * ((m k : E) * ε k) := by
      rw [hc, Nat.cast_mul]; ring
    rw [this]
    exact (isIntegral_natCast c : IsIntegral ℤ (c : E)).mul (hmi k)
  have hdx : ((M * ∏ k, m k : ℕ) : E) * x =
      ∑ k, algebraMap F E ((M : F) * ε.repr x k) * (((∏ j, m j : ℕ) : E) * ε k) := by
    conv_lhs => rw [← ε.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  have hint : IsIntegral ℤ (((M * ∏ k, m k : ℕ) : E) * x) := by
    rw [hdx]
    exact IsIntegral.sum _ fun k _ => (hcoord k).algebraMap.mul (hP k)
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  exact ⟨y, hy.symm⟩

end GlobalTheory.CompanionTheory.AdelicDenom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicDenominatorStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adelic_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (C : Set (Af F ⊗[F] E)), IsCompact C → ∃ d : ℕ, 0 < d ∧ ∀ x : E, (1 : Af F) ⊗ₜ[F] x ∈ C → ∃ y : 𝓞 E, (d : E) * x = y := by
  first | exact @GlobalTheory.CompanionTheory.AdelicDenom.exists_denominator_of_isCompact | exact GlobalTheory.CompanionTheory.AdelicDenom.exists_denominator_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AdelicDenom.exists_denominator_of_isCompact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InversePointTorusScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InversePointTorusScaling
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCoord

variable {K : Type} [CommRing K] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) K} {Rx Ry : Matrix (Fin r) (Fin n) K}

theorem left_proj (h1 : Rx * X = 0) (h3 : Rx * Y = 1) : Rx * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, h3, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem left_proj' (h2 : Ry * Y = 0) (h4 : Ry * X = 1) : Ry * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h2, h4, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem lin (h1 : Rx * X = 0) (h2 : Ry * Y = 0) (h3 : Rx * Y = 1) (h4 : Ry * X = 1)
    {A B : Matrix (Fin n) (Fin n) K} (hAB : A * B = 1) {T S : Matrix (Fin r) (Fin r) K} (hTS : T * S = 1)
    (hST : S * T = 1) (hX : B * X = X * T) (hY : B * Y = Y * S) (ξ : Matrix (Fin n) (Fin 1) K)
    (hq : B * ((1 - X * Ry - Y * Rx) * ξ) = (1 - X * Ry - Y * Rx) * ξ) :
    Ry * (A * ξ) = S * (Ry * ξ) ∧ Rx * (A * ξ) = T * (Rx * ξ) ∧
      (1 - X * Ry - Y * Rx) * (A * ξ) = (1 - X * Ry - Y * Rx) * ξ := by
  have hRxQ := left_proj (Ry := Ry) h1 h3
  have hRyQ := left_proj' (Rx := Rx) h2 h4
  have e : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K),
      (1 - X * Ry - Y * Rx) * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  generalize hQ : 1 - X * Ry - Y * Rx = Q at hq hRxQ hRyQ ⊢
  have eQ : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K), Q * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    rw [← hQ]; exact e M
  have hAX : A * X = X * S := by
    have h : A * (B * X) = X := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hX, ← Matrix.mul_assoc] at h
    calc A * X = A * X * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = (A * X * T) * S := by simp only [Matrix.mul_assoc]
      _ = X * S := by rw [h]
  have hAY : A * Y = Y * T := by
    have h : A * (B * Y) = Y := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hY, ← Matrix.mul_assoc] at h
    calc A * Y = A * Y * (S * T) := by rw [hST, Matrix.mul_one]
      _ = (A * Y * S) * T := by simp only [Matrix.mul_assoc]
      _ = Y * T := by rw [h]
  have hAQ : A * (Q * ξ) = Q * ξ := by
    conv_lhs => rw [← hq]
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have hQX : Q * X = 0 := by rw [eQ, h1, h4]; simp
  have hQY : Q * Y = 0 := by rw [eQ, h2, h3]; simp
  have hQQ : Q * Q = Q := by rw [eQ, hRxQ, hRyQ]; simp
  have hdec : ξ = X * (Ry * ξ) + Y * (Rx * ξ) + Q * ξ := by rw [eQ]; abel
  have hu : A * ξ = X * (S * (Ry * ξ)) + Y * (T * (Rx * ξ)) + Q * ξ := by
    conv_lhs => rw [hdec]
    rw [Matrix.mul_add, Matrix.mul_add, hAQ, ← Matrix.mul_assoc A X, ← Matrix.mul_assoc A Y, hAX, hAY,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Ry X, ← Matrix.mul_assoc Ry Y, ← Matrix.mul_assoc Ry Q, h4, h2,
      hRyQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Rx X, ← Matrix.mul_assoc Rx Y, ← Matrix.mul_assoc Rx Q, h3, h1,
      hRxQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Q X, ← Matrix.mul_assoc Q Y, ← Matrix.mul_assoc Q Q, hQX, hQY,
      hQQ]
    simp

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  have h := congrArg Units.val (map_mul (Formalism.L2.Theta.matHom V) a⁻¹ a)
  rw [inv_mul_cancel, map_one] at h
  exact h.symm

theorem map_mt_eq_archMat {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (ρ : D.what₂.Tau) (a : GA D V) :
    (Formalism.L2.Theta.mt V a).map (fun x => θ ρ (infPart D x)) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) a) := by
  have e := eq_infProj hθ (embOverOf D ρ) rfl
  have h := infMat_infProj (J := V.gram) (isCMExt_host D) (embOverOf D ρ) a
  rw [← e] at h
  refine Eq.trans ?_ (h.trans (GlobalTheory.Orb.archMat_eq_archEquiv V.gram (isCMExt_host D) _ _).symm)
  ext i j
  rfl

theorem torus_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ (ξ : Matrix (Fin V.rank) (Fin 1) D.host.E), (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∧ ∀ ρ, (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => ((t i : ℂ))⁻¹) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ξ).map (tauE D ρ)) ∧ (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => (t i : ℂ)) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ξ).map (tauE D ρ)) ∧ (((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ).map (tauE D ρ)) := by
  intro D θ hθ V r Xf Yf hW t ht a ha ξ
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  refine ⟨?_, fun ρ => ?_⟩
  · have h1 : (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 :=
      GlobalTheory.CompanionTheory.SiegelArch.map_matHom_fin V.gram (inv_mem ha.1)
    change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map (finPart D) = _
    rw [Matrix.map_mul, h1, Matrix.one_mul, Matrix.map_map]
    ext i j
    exact GlobalTheory.LatVac.finPart_incA _
  · have hhτ : ∀ x, θ ρ (infPart D (incA D x)) = tauE D ρ x := fun x => (hθ ρ).1 x
    let φ : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hAB : (Formalism.L2.Theta.mt V a⁻¹).map φ * (Formalism.L2.Theta.mt V a).map φ = 1 := by
      rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hB : (Formalism.L2.Theta.mt V a).map φ = _ := map_mt_eq_archMat hθ V ρ a
    have hcomp : compAt θ ρ (invPt V a ξ) = (Formalism.L2.Theta.mt V a⁻¹).map φ * ξ.map (tauE D ρ) := by
      change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map φ = _
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hhτ _
    obtain ⟨hX, hY, hZ⟩ := ha.2 (placeOf D ρ) (embOverOf D ρ)
    rw [← hB] at hX hY hZ
    simp only [embOverOf_val] at hX hY hZ
    obtain ⟨-, -, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)
    have hxx := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).1
    have hyy := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).2.1
    have hJc : (V.gram.map (tauE D ρ))ᴴ = V.gram.map (tauE D ρ) := by
      ext i j
      rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]
    have hyx := GlobalTheory.CentreFin.dual_swap hJc hxy
    have hR : ∀ C : Matrix (Fin V.rank) (Fin r) D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (tauE D ρ) =
          (C.map (tauE D ρ))ᴴ * V.gram.map (tauE D ρ) := fun C => by
      rw [Matrix.map_mul, GlobalTheory.CentreFin.map_cT_emb hcm]
    have h1 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hxx
    have h2 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hyy
    have h3 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hxy
    have h4 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hyx
    have h4E : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * Xf = 1 := by
      refine Matrix.map_injective (tauE D ρ).injective ?_
      beta_reduce
      rw [Matrix.map_mul, h4, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQm : (1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ) =
        1 - Xf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ) -
          Yf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ) := by
      change (tauE D ρ).mapMatrix _ = _
      rw [map_sub, map_sub, map_one]
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul]
    have hxq := left_proj (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.xx hW.xy
    have hyq := left_proj' (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.yy h4E
    have hq := hZ (fun i => ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ :
            Matrix (Fin V.rank) (Fin 1) D.host.E) i 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hxq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hyq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
    have hq' := by
      refine lin h1 h2 h3 h4 hAB (T := diagonal fun i => (t i : ℂ)) (S := diagonal fun i => (t i : ℂ)⁻¹) ?_ ?_ hX hY
        (ξ.map (tauE D ρ)) ?_
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact mul_inv_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact inv_mul_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [← hQm, ← Matrix.map_mul]
        ext i j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        exact congrFun hq i
    obtain ⟨c1, c2, c3⟩ := hq'
    have m : ∀ {a : ℕ} (M : Matrix (Fin a) (Fin V.rank) D.host.E),
        (M * ξ).map (tauE D ρ) = M.map (tauE D ρ) * ξ.map (tauE D ρ) := fun M => Matrix.map_mul
    rw [hcomp, m, m, m, hQm]
    exact ⟨c1, c2, c3⟩

end GlobalTheory.CompanionTheory.TorusCoord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InversePointTorusScalingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_point_torus_scaling : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ (ξ : Matrix (Fin V.rank) (Fin 1) D.host.E), (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∧ ∀ ρ, (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => ((t i : ℂ))⁻¹) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ξ).map (tauE D ρ)) ∧ (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => (t i : ℂ)) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ξ).map (tauE D ρ)) ∧ (((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ).map (tauE D ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCoord.torus_coords | exact GlobalTheory.CompanionTheory.TorusCoord.torus_coords | (intros; apply GlobalTheory.CompanionTheory.TorusCoord.torus_coords <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumDecayBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumDecayBound
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Count

theorem one_dim_step (b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    ((1 + (x + 1) / b) ^ 2)⁻¹ ≤ b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) := by
  have h1 : 0 < b + x := by linarith
  have h2 : 0 < b + x + 1 := by linarith
  have e1 : (1 + (x + 1) / b) = (b + x + 1) / b := by field_simp; ring
  have e2 : b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) = b ^ 2 / ((b + x) * (b + x + 1)) := by
    field_simp; ring
  rw [e1, e2, div_pow, inv_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem one_dim_partial (b : ℝ) (hb : 0 < b) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹ ≤ b - b ^ 2 / (b + N) := by
  induction N with
  | zero =>
    have : b ^ 2 / (b + ((0 : ℕ) : ℝ)) = b := by
      simp only [Nat.cast_zero, add_zero]; field_simp
    rw [Finset.range_zero, Finset.sum_empty, this, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := one_dim_step b N hb (Nat.cast_nonneg N)
    push_cast
    have e : b + ((N : ℝ) + 1) = b + N + 1 := by ring
    rw [e]
    linarith

theorem one_dim_nat (b : ℝ) (hb : 0 < b) :
    ∑' k : ℕ, ENNReal.ofReal (((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹) ≤ ENNReal.ofReal b := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := one_dim_partial b hb N
  have h3 : 0 ≤ b ^ 2 / (b + N) := by positivity
  linarith

theorem one_dim (b : ℝ) (hb : 0 < b) :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 + 2 * b) := by
  set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) with hf
  have hsplit : HasSum f ((∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    HasSum.of_nat_of_neg_add_one ENNReal.summable.hasSum ENNReal.summable.hasSum
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have hpos : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have h0 : f ((0 : ℕ) : ℤ) = 1 := by simp [hf]
  have hN := one_dim_nat b hb
  have hz : ∑' n : ℕ, f n ≤ 1 + ENNReal.ofReal b := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ', h0, add_comm]
      gcongr
      calc ∑ k ∈ Finset.range N, f ((k + 1 : ℕ) : ℤ)
          ≤ ∑' k : ℕ, f ((k + 1 : ℕ) : ℤ) := ENNReal.sum_le_tsum _
        _ ≤ ENNReal.ofReal b := by rw [tsum_congr hpos]; exact hN
  rw [hsplit.tsum_eq, tsum_congr hneg]
  calc _ ≤ 1 + ENNReal.ofReal b + ENNReal.ofReal b := add_le_add hz hN
    _ = ENNReal.ofReal (1 + 2 * b) := by
      rw [two_mul, ← add_assoc, ENNReal.ofReal_add (by positivity) hb.le,
        ENNReal.ofReal_add (by norm_num) hb.le, ENNReal.ofReal_one]

theorem multi_dim {P : Type} [Fintype P] (g : P → ℤ → ℝ≥0∞) :
    ∑' x : P → ℤ, ∏ p, g p (x p) ≤ ∏ p, ∑' n, g p n :=
  _root_.UpperTheory.Reformulated.B.MultiDimensional.multi_dim g

theorem tsum_le_prod_of_injOn {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ)
    (hb : ∀ p, 0 < b p) (h : S → ℝ≥0∞) (hinj : Set.InjOn m {ξ | h ξ ≠ 0})
    (hh : ∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) :
    ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  set g : P → ℤ → ℝ≥0∞ := fun p n => ENNReal.ofReal (((1 + |(n : ℝ)| / b p) ^ 2)⁻¹) with hg
  have hsupp : ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ :=
    (tsum_subtype_eq_of_support_subset (f := h) (s := {ξ | h ξ ≠ 0})
      (fun _ hx => hx)).symm
  have hinj' : Function.Injective (fun ξ : {ξ | h ξ ≠ 0} => m ξ) :=
    fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
  calc ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ := hsupp
    _ ≤ ∑' ξ : {ξ | h ξ ≠ 0}, (fun x : P → ℤ => ∏ p, g p (x p)) (m ξ) :=
        ENNReal.tsum_le_tsum fun ξ => hh ξ
    _ ≤ ∑' x : P → ℤ, ∏ p, g p (x p) :=
        (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective hinj' _); exact _root_.le_rfl)
    _ ≤ ∏ p, ∑' n, g p n := multi_dim g
    _ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) :=
        Finset.prod_le_prod' fun p _ => one_dim (b p) (hb p)

end GlobalTheory.CompanionTheory.Count
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumDecayBoundStatement
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_decay_bound : ∀ {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ), (∀ p, 0 < b p) → ∀ (h : S → ℝ≥0∞), Set.InjOn m {ξ | h ξ ≠ 0} → (∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) → ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  first | exact @GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | exact GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | (intros; apply GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerCoordinatesBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerCoordinatesBound
open NumberField

namespace GlobalTheory.CompanionTheory.NumberFieldCoord

theorem abs_repr_le_of_forall_norm_embedding_le :
    ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)),
      Function.Surjective (fun i => InfinitePlace.mk (τ i)) →
      ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) →
        ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  intro E _ _ I _ τ hτ
  classical
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis E).equivFun.toLinearMap
    with hLc
  refine ⟨‖Lc‖ + 1, by positivity, fun e R hR k => ?_⟩
  have hR0 : 0 ≤ R := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    obtain ⟨i, -⟩ := hτ w
    exact (norm_nonneg _).trans (hR i)
  have hw : ∀ w : InfinitePlace E, w (e : E) ≤ R := by
    intro w
    obtain ⟨i, rfl⟩ := hτ w
    simpa only [InfinitePlace.apply] using hR i
  have hn : ‖mixedEmbedding E (e : E)‖ ≤ R := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_of_isReal w.2] at h
      simpa [mixedEmbedding] using h
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_eq] at h
      simpa [mixedEmbedding] using h
  have hval : Lc (mixedEmbedding E (e : E)) k = (((RingOfIntegers.basis E).repr e k : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis E).equivFun (mixedEmbedding E (e : E)) k = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply E e k
    rw [show (e : E) = algebraMap (𝓞 E) E e from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  calc ‖Lc (mixedEmbedding E (e : E)) k‖ ≤ ‖Lc (mixedEmbedding E (e : E))‖ := norm_le_pi_norm _ k
    _ ≤ ‖Lc‖ * ‖mixedEmbedding E (e : E)‖ := Lc.le_opNorm _
    _ ≤ ‖Lc‖ * R := by gcongr
    _ ≤ (‖Lc‖ + 1) * R := by nlinarith

end GlobalTheory.CompanionTheory.NumberFieldCoord
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerCoordinatesBoundStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_coordinates_bound : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)), Function.Surjective (fun i => InfinitePlace.mk (τ i)) → ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) → ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  first | exact @GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | exact GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | (intros; apply GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSet
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilCount
open NumberField IsDedekindDomain Matrix

theorem lattice_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (hτ : Function.Surjective fun i => InfinitePlace.mk (τ i))
    {n : ℕ} {ι : Type} [Fintype ι] (R : Matrix ι (Fin n) E) (R' : Matrix (Fin n) ι E) (hR : R' * R = 1)
    (L : Set (Matrix (Fin n) (Fin 1) (Af F ⊗[F] E))) (hL : IsCompact L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : ι → ℝ), (∀ i, 0 < s i) → ∀ (U : Matrix (Fin n) (Fin 1) E → ℝ), (∀ ξ, 0 ≤ U ξ) →
      (∀ ξ, ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L → ∀ ρ i, ‖τ ρ ((R * ξ) i 0)‖ ≤ s i * U ξ) →
      ∀ N, 2 * (Fintype.card ι * Module.finrank ℚ E) ≤ N →
      ∑' ξ : Matrix (Fin n) (Fin 1) E, ENNReal.ofReal (((1 + U ξ) ^ N)⁻¹ *
          Set.indicator L (fun _ => (1 : ℝ)) (ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x))) ≤
        ENNReal.ofReal (∏ i, (1 + K * s i) ^ Module.finrank ℚ E) := by
  classical
  have hev : ∀ j : Fin n, Continuous fun M : Matrix (Fin n) (Fin 1) (Af F ⊗[F] E) => M j 0 := fun j =>
    (continuous_apply 0).comp (continuous_apply j)
  have hC : IsCompact ((⋃ j, (fun M : Matrix (Fin n) (Fin 1) (Af F ⊗[F] E) => M j 0) '' L) ∪
      Set.range fun p : ι × Fin n => (1 : Af F) ⊗ₜ[F] R p.1 p.2) :=
    (isCompact_iUnion fun j => hL.image (hev j)).union (Set.finite_range _).isCompact
  obtain ⟨d, hd, hden⟩ := GlobalTheory.T.compact_adelic_denominator F E _ hC
  obtain ⟨K₀, hK₀, hco⟩ := GlobalTheory.T.integer_coordinates_bound τ hτ
  have hint : ∀ ξ : Matrix (Fin n) (Fin 1) E, ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L → ∀ i,
      ∃ y : 𝓞 E, ((d * d : ℕ) : E) * (R * ξ) i 0 = y := by
    intro ξ hξ i
    choose y₁ hy₁ using fun j => hden (R i j) (Or.inr ⟨(i, j), rfl⟩)
    choose y₂ hy₂ using fun j => hden (ξ j 0) (Or.inl (Set.mem_iUnion.2 ⟨j, _, hξ, rfl⟩))
    refine ⟨∑ j, y₁ j * y₂ j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, Finset.mul_sum, RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ← hy₁ j, ← hy₂ j]
    push_cast
    ring
  have hdd : (0 : ℝ) < ((d * d : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hd
  have hddE : ((d * d : ℕ) : E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hd hd).ne'
  set D₀ : ℝ := ((d * d : ℕ) : ℝ) with hD₀
  refine ⟨2 * (K₀ * D₀), by positivity, fun s hs U hU hb N hN => ?_⟩
  let e : Matrix (Fin n) (Fin 1) E → ι → 𝓞 E := fun ξ i =>
    if h : ∃ y : 𝓞 E, ((d * d : ℕ) : E) * (R * ξ) i 0 = y then h.choose else 0
  have he : ∀ ξ : Matrix (Fin n) (Fin 1) E, ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L → ∀ i,
      ((e ξ i : 𝓞 E) : E) = ((d * d : ℕ) : E) * (R * ξ) i 0 := fun ξ hξ i => by
    have h := hint ξ hξ i
    simp only [e, dif_pos h]
    exact h.choose_spec.symm
  let κ := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let m : Matrix (Fin n) (Fin 1) E → ι × κ → ℤ := fun ξ p => (RingOfIntegers.basis E).repr (e ξ p.1) p.2
  let b : ι × κ → ℝ := fun p => K₀ * D₀ * s p.1
  have hbp : ∀ p, 0 < b p := fun p => mul_pos (by positivity) (hs p.1)
  let h : Matrix (Fin n) (Fin 1) E → ℝ≥0∞ := fun ξ => ENNReal.ofReal (((1 + U ξ) ^ N)⁻¹ *
    Set.indicator L (fun _ => (1 : ℝ)) (ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x)))
  have hsupp : ∀ ξ, h ξ ≠ 0 → ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L := fun ξ h0 => by
    by_contra hn
    exact h0 (by simp [h, Set.indicator_of_notMem hn])
  have hinj : Set.InjOn m {ξ | h ξ ≠ 0} := by
    intro ξ hξ ξ' hξ' hm
    have hξ1 := hsupp ξ hξ
    have hξ2 := hsupp ξ' hξ'
    have h1 : ∀ i, e ξ i = e ξ' i := fun i =>
      (RingOfIntegers.basis E).ext_elem fun k => congrFun hm (i, k)
    have h2 : R * ξ = R * ξ' := by
      ext i j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have := congrArg (fun y : 𝓞 E => (y : E)) (h1 i)
      simp only [he ξ hξ1 i, he ξ' hξ2 i] at this
      exact mul_left_cancel₀ hddE this
    calc ξ = R' * (R * ξ) := by rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
      _ = R' * (R * ξ') := by rw [h2]
      _ = ξ' := by rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
  have hh : ∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹) := by
    intro ξ
    by_cases hξ : ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L
    · rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => by positivity]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Set.indicator_of_mem hξ, mul_one]
      have h1 : ∀ p, ((1 + U ξ) ^ 2)⁻¹ ≤ ((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹ := fun p => by
        have hUp := hU ξ
        have h2 : |(m ξ p : ℝ)| ≤ K₀ * (D₀ * (s p.1 * U ξ)) := by
          refine hco (e ξ p.1) _ (fun ρ => ?_) p.2
          rw [he ξ hξ p.1, map_mul, norm_mul, map_natCast, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (hb ξ hξ ρ p.1) hdd.le
        have h3 : |(m ξ p : ℝ)| / b p ≤ U ξ := by
          rw [div_le_iff₀ (hbp p)]
          calc |(m ξ p : ℝ)| ≤ K₀ * (D₀ * (s p.1 * U ξ)) := h2
            _ = U ξ * b p := by simp only [b]; ring
        have h4 : 0 ≤ |(m ξ p : ℝ)| / b p := div_nonneg (abs_nonneg _) (hbp p).le
        refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
      have hcard : Fintype.card (ι × κ) = Fintype.card ι * Module.finrank ℚ E := by
        rw [Fintype.card_prod, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
      have h5 : ((1 + U ξ) ^ N)⁻¹ ≤ ∏ _p : ι × κ, ((1 + U ξ) ^ 2)⁻¹ := by
        have hUp := hU ξ
        rw [Finset.prod_const, Finset.card_univ, hcard, inv_pow, ← pow_mul]
        refine inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) ?_)
        exact hN
      exact h5.trans (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun p _ => h1 p)
    · simp [h, Set.indicator_of_notMem hξ]
  refine (GlobalTheory.T.lattice_sum_decay_bound m b hbp h hinj hh).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => by have := hbp p; positivity]
  congr 1
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hc : ∀ y : κ, 1 + 2 * b (i, y) = 1 + 2 * (K₀ * D₀) * s i := fun y => by simp only [b]; ring
  simp only [hc, Finset.prod_const, Finset.card_univ]
  rw [← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]

theorem count_main : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ {c : ℝ}, 0 < c → ∀ (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) ((invPt V a ξ).map (finPart D))) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) := by
  intro D θ hθ V r Xf Yf hW c hc L hL
  have hCM := GlobalTheory.AdelicU.isCMExt_host D
  have hf2 : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ D.host.F := by
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, hCM.2.2.1, mul_comm]
  set Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram with hRx
  set Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram with hRy
  set Q := 1 - Xf * Ry - Yf * Rx with hQ
  let R : Matrix (Fin r ⊕ Fin r ⊕ Fin V.rank) (Fin V.rank) D.host.E := Matrix.fromRows Ry (Matrix.fromRows Rx Q)
  let R' : Matrix (Fin V.rank) (Fin r ⊕ Fin r ⊕ Fin V.rank) D.host.E := Matrix.fromCols Xf (Matrix.fromCols Yf 1)
  have hR : R' * R = 1 := by
    simp only [R, R', Matrix.fromCols_mul_fromRows, hQ, Matrix.one_mul]
    abel
  obtain ⟨K, hK, hsum⟩ := lattice_sum (F := D.host.F) (tauE D) (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 R R' hR L hL
  set Cn : ℝ := 1 + ∑ ρ, ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ with hCn
  have hCn1 : 1 ≤ Cn := by
    have : 0 ≤ ∑ ρ, ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ := by positivity
    linarith
  have hCn0 : 0 < Cn := by linarith
  have hrow : ∀ ρ i, ∑ j, ‖tauE D ρ (R i j)‖ ≤ Cn := fun ρ i => by
    have h1 : ∑ j, ‖tauE D ρ (R i j)‖ ≤ ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖tauE D ρ (R i j)‖) (fun _ _ => by positivity) (Finset.mem_univ i)
    have h2 : ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ ≤ ∑ ρ, ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ :=
      Finset.single_le_sum (f := fun ρ => ∑ i, ∑ j, ‖tauE D ρ (R i j)‖) (fun _ _ => by positivity) (Finset.mem_univ ρ)
    linarith
  refine ⟨2 * (Fintype.card (Fin r ⊕ Fin r ⊕ Fin V.rank) * Module.finrank ℚ D.host.E), fun N hN => ?_⟩
  set c₀ : ℝ := min 1 c ^ r with hc₀
  have hc₀p : 0 < c₀ := pow_pos (lt_min one_pos hc) _
  set A₁ : ℝ := c₀⁻¹ + K * Cn with hA₁
  set A₂ : ℝ := 1 + K * Cn * c₀⁻¹ with hA₂
  set A₃ : ℝ := 1 + K * Cn with hA₃
  have hA₁p : 0 < A₁ := by positivity
  have hA₂p : 0 < A₂ := by positivity
  have hA₃p : 0 < A₃ := by positivity
  set f := Module.finrank ℚ D.host.E with hf
  refine ⟨(∏ _i : Fin r, A₁ ^ f) * (∏ _i : Fin r, A₂ ^ f) * ∏ _j : Fin V.rank, A₃ ^ f, fun t ht a ha => ?_⟩
  have ht0 : ∀ i, 0 < t i := ht.1
  have htc : ∀ i, c₀ ≤ t i := GlobalTheory.SiegelHt.cone_low hc ht
  let U : Matrix (Fin V.rank) (Fin 1) D.host.E → ℝ := fun ξ => ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖
  let s : Fin r ⊕ Fin r ⊕ Fin V.rank → ℝ := Sum.elim (fun i => Cn * t i) (Sum.elim (fun i => Cn * (t i)⁻¹) fun _ => Cn)
  have hs : ∀ i, 0 < s i := by
    rintro (i | i | i)
    · exact mul_pos hCn0 (ht0 i)
    · exact mul_pos hCn0 (inv_pos.2 (ht0 i))
    · exact hCn0
  have hU : ∀ ξ, 0 ≤ U ξ := fun ξ => norm_nonneg _
  have hcoord := GlobalTheory.T.inverse_point_torus_scaling D θ hθ V Xf Yf hW t ht0 a ha
  have hent : ∀ ξ ρ j, ‖compAt θ ρ (invPt V a ξ) j 0‖ ≤ U ξ := fun ξ ρ j =>
    (norm_le_pi_norm (fun i => compAt θ ρ (invPt V a ξ) i 0) j).trans
      (norm_le_pi_norm (fun τ i => compAt θ τ (invPt V a ξ) i 0) ρ)
  have hmul : ∀ ξ ρ i, ‖((R.map (tauE D ρ)) * compAt θ ρ (invPt V a ξ)) i 0‖ ≤ Cn * U ξ := fun ξ ρ i => by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖(R.map (tauE D ρ)) i j * compAt θ ρ (invPt V a ξ) j 0‖
        ≤ ∑ j, ‖tauE D ρ (R i j)‖ * U ξ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul, Matrix.map_apply]
          exact mul_le_mul_of_nonneg_left (hent ξ ρ j) (norm_nonneg _)
      _ = (∑ j, ‖tauE D ρ (R i j)‖) * U ξ := (Finset.sum_mul _ _ _).symm
      _ ≤ Cn * U ξ := mul_le_mul_of_nonneg_right (hrow ρ i) (hU ξ)
  have hb : ∀ ξ, ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∈ L → ∀ ρ i, ‖tauE D ρ ((R * ξ) i 0)‖ ≤ s i * U ξ := by
    intro ξ _ ρ i
    obtain ⟨-, h⟩ := hcoord ξ
    obtain ⟨h1, h2, h3⟩ := h ρ
    rcases i with i | i | i
    · have e := congrFun (congrFun h1 i) 0
      have e2 : (R.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) (Sum.inl i) 0 = (Ry.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) i 0 := rfl
      have e3 : (R * ξ) (Sum.inl i) 0 = (Ry * ξ) i 0 := rfl
      have h4 := hmul ξ ρ (Sum.inl i)
      rw [e2, e, Matrix.diagonal_mul, Matrix.map_apply, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (ht0 i).le] at h4
      rw [e3]
      show _ ≤ Cn * t i * U ξ
      have := ht0 i
      rw [inv_mul_le_iff₀ this] at h4
      linarith
    · have e := congrFun (congrFun h2 i) 0
      have e2 : (R.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) (Sum.inr (Sum.inl i)) 0 = (Rx.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) i 0 := rfl
      have e3 : (R * ξ) (Sum.inr (Sum.inl i)) 0 = (Rx * ξ) i 0 := rfl
      have h4 := hmul ξ ρ (Sum.inr (Sum.inl i))
      rw [e2, e, Matrix.diagonal_mul, Matrix.map_apply, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (ht0 i).le] at h4
      rw [e3]
      show _ ≤ Cn * (t i)⁻¹ * U ξ
      have := ht0 i
      rw [mul_comm Cn, mul_assoc, inv_mul_eq_div, le_div_iff₀ this, mul_comm]
      exact h4
    · have e := congrFun (congrFun h3 i) 0
      have e2 : (R.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) (Sum.inr (Sum.inr i)) 0 = (Q.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) i 0 := rfl
      have e3 : (R * ξ) (Sum.inr (Sum.inr i)) 0 = (Q * ξ) i 0 := rfl
      have h4 := hmul ξ ρ (Sum.inr (Sum.inr i))
      rw [e2, e, Matrix.map_apply] at h4
      rw [e3]
      exact h4
  have main := hsum s hs U hU hb N hN
  have hsame : ∀ ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) := fun ξ => (hcoord ξ).1
  simp only [hsame]
  refine main.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← hf2, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [s, Sum.elim_inl, Sum.elim_inr]
  have h1 : ∀ i, (1 + K * (Cn * t i)) ^ f ≤ A₁ ^ f * t i ^ f := fun i => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by have := ht0 i; positivity) ?_ _
    have : 1 ≤ c₀⁻¹ * t i := by
      rw [inv_mul_eq_div, one_le_div hc₀p]; exact htc i
    rw [hA₁]; nlinarith
  have h2 : ∀ i, (1 + K * (Cn * (t i)⁻¹)) ^ f ≤ A₂ ^ f := fun i => by
    refine pow_le_pow_left₀ (by have := ht0 i; positivity) ?_ _
    have : (t i)⁻¹ ≤ c₀⁻¹ := inv_anti₀ hc₀p (htc i)
    have hKC : 0 < K * Cn := by positivity
    rw [hA₂]; nlinarith
  calc (∏ i, (1 + K * (Cn * t i)) ^ f) * ((∏ i, (1 + K * (Cn * (t i)⁻¹)) ^ f) * ∏ _j : Fin V.rank, (1 + K * Cn) ^ f)
      ≤ (∏ i, A₁ ^ f * t i ^ f) * ((∏ _i : Fin r, A₂ ^ f) * ∏ _j : Fin V.rank, A₃ ^ f) := by
        refine mul_le_mul (Finset.prod_le_prod₀ (fun i _ => by have := ht0 i; positivity) fun i _ => h1 i) ?_ (by
          refine mul_nonneg (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity) (Finset.prod_nonneg fun i _ => by positivity)) (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity)
        refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun i _ => by have := ht0 i; positivity) fun i _ => h2 i) (Finset.prod_nonneg fun i _ => by positivity)
    _ = (∏ _i : Fin r, A₁ ^ f) * (∏ _i : Fin r, A₂ ^ f) * (∏ _j : Fin V.rank, A₃ ^ f) * ∏ i, t i ^ f := by
        rw [Finset.prod_mul_distrib]; ring

end GlobalTheory.CompanionTheory.WeilCount

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSetStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_rapid_decay_siegel_set : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ {c : ℝ}, 0 < c → ∀ (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) ((invPt V a ξ).map (finPart D))) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilCount.count_main | exact GlobalTheory.CompanionTheory.WeilCount.count_main | (intros; apply GlobalTheory.CompanionTheory.WeilCount.count_main <;> assumption)
end

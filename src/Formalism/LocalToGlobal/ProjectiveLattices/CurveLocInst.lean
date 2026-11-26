module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import Formalism.LocalToGlobal.ProjectiveLattices.FnDefB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveCountB
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor MvPolynomial

namespace CurveCount

variable {K : Type*} [Field K] {N : ℕ}

def homog (a : Fin N) (Q : MvPolynomial (Fin N) K) : MvPolynomial (Fin N) K :=
  ∑ m ∈ Q.support, monomial (m + Finsupp.single a (Q.totalDegree - m.degree)) (Q.coeff m)

theorem homog_isHomogeneous (a : Fin N) (Q : MvPolynomial (Fin N) K) :
    (homog a Q).IsHomogeneous Q.totalDegree := by
  classical
  refine IsHomogeneous.sum _ _ _ fun m hm => isHomogeneous_monomial _ ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [map_add (f := _), Finsupp.degree_single]
  omega

theorem aeval_homog {L : Type*} [Field L] [Algebra K L] (a : Fin N) (Q : MvPolynomial (Fin N) K) (y : Fin N → L)
    (hy : y a ≠ 0) : aeval y (homog a Q) = y a ^ Q.totalDegree * aeval (fun i => y i / y a) Q := by
  classical
  have hQ : aeval (fun i => y i / y a) Q =
      ∑ m ∈ Q.support, aeval (fun i => y i / y a) (monomial m (Q.coeff m)) := by
    conv_lhs => rw [Q.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hQ, homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (by simp)]
  simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hd : m.degree = ∑ i ∈ m.support, m i := rfl
  rw [← hd]
  have e : y a ^ Q.totalDegree = y a ^ (Q.totalDegree - m.degree) * y a ^ m.degree := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [e]
  field_simp

theorem adjoin_ratio_eq {L : Type*} [Field L] [Algebra K L] (v : Fin N → L) {a b : Fin N} (ha : v a ≠ 0)
    (hb : v b ≠ 0) :
    IntermediateField.adjoin K (Set.range fun i => v i / v a) = IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
  have key : ∀ a b : Fin N, v a ≠ 0 → v b ≠ 0 →
      IntermediateField.adjoin K (Set.range fun i => v i / v a) ≤ IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
    intro a b ha hb
    rw [IntermediateField.adjoin_le_iff, Set.range_subset_iff]
    intro i
    have e : v i / v a = (v i / v b) / (v a / v b) := by field_simp
    rw [SetLike.mem_coe, e]
    exact IntermediateField.div_mem _ (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      (IntermediateField.subset_adjoin K _ ⟨a, rfl⟩)
  exact le_antisymm (key a b ha hb) (key b a hb ha)

end CurveCount

namespace CurveLoc

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem tv_indep :
    AlgebraicIndependent (X.Kl la) (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) := by
  have h0 := MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)
  have hinj1 : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have hinj2 : Function.Injective (@algebraMap (Op X la N) (Kp X la N) _ _ _) := IsFractionRing.injective _ _
  let g : Pol X la N →ₐ[X.Ol la] Kp X la N :=
    (IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)).comp
      (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N))
  have h1 : AlgebraicIndependent (X.Ol la)
      (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) :=
    h0.map' (f := g) (hinj2.comp hinj1)
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic (X.Kl la) (nonZeroDivisors (X.Ol la))
  exact h1.extendScalars (X.Kl la)

theorem sfr_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    sfr X la w i = ∑ k, algebraMap (Kp X la N) ↥(Frac0 X la w)
      (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) * xw X la N w k := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_sfr, Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def]
  rfl

theorem sfr_zero : sfr X la w 0 = 1 := by
  apply Subtype.ext
  rw [coe_sfr, frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem countQAt_of (v : Fin N → Ω) (hv : ∀ i, gF (X.inc wL (w i)) = v i)
    (htr : ∃ a₀, v a₀ ≠ 0 ∧
      Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a₀)) ≤ WeightFamilies.dimY D j) :
    CountQAt X la N w gF := by
  classical
  intro 𝔮 h𝔮 hJ hK Pw k hPw hne hmem
  have : 𝔮.IsPrime := h𝔮
  have hvf : (fun i => gF (X.inc wL (w i))) = v := funext hv
  rw [hvf] at hne
  let Fr := ↥(Frac0 X la w)
  let κ := FractionRing (Fr ⧸ 𝔮)
  let ρ : Fr →+* κ := (algebraMap (Fr ⧸ 𝔮) κ).comp (Ideal.Quotient.mk 𝔮)
  have hρ : ∀ f, ρ f = 0 ↔ f ∈ 𝔮 := fun f => by
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρK : Kp X la N →+* κ := ρ.comp (algebraMap (Kp X la N) Fr)
  let algKl : Algebra (X.Kl la) κ := (ρK.comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  let algK : Algebra B.KO κ :=
    ((ρK.comp (algebraMap (X.Kl la) (Kp X la N))).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  let _ := algKl
  let _ := algK
  have : IsScalarTower B.KO (X.Kl la) κ :=
    @IsScalarTower.of_algebraMap_eq B.KO (X.Kl la) κ _ _ _ _ algKl algK (fun _ => rfl)
  let x : Fin N → κ := fun i => ρ (xw X la N w i)
  let t : Fin (WeightFamilies.dimY D j + 1) × Fin N → κ :=
    fun p => ρK (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))
  have ht : AlgebraicIndependent B.KO t := by
    let g : Kp X la N →ₐ[X.Kl la] κ := { ρK with commutes' := fun _ => rfl }
    have h1 := (tv_indep X la N).map' (f := g) ρK.injective
    exact h1.restrictScalars (algebraMap B.KO (X.Kl la)).injective
  have hρpol : ∀ Q : MvPolynomial (Fin N) B.KO, ρ (polX X la N w Q) = aeval x Q := fun Q => by
    rw [polX, MvPolynomial.eval₂_comp_left, aeval_def]
    rfl
  have hlin : ∀ i : Fin (WeightFamilies.dimY D j), ∑ k, t (i.succ, k) * x k = 0 := by
    intro i
    have h := congrArg ρ (sfr_eq X la N w i.succ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_mul] at h
    rw [← (hρ _).mpr (hJ (sfr_succ_mem_Jid X la w i)), h]
    rfl
  have hlin0 : ∑ k, t (0, k) * x k = 1 := by
    have h := congrArg ρ (sfr_eq X la N w 0)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, sfr_zero, map_one] at h
    simp only [map_mul] at h
    rw [h]
    rfl
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hlin0.symm ▸ one_ne_zero : ∑ k, t (0, k) * x k ≠ 0)
  have hxa : x a ≠ 0 := right_ne_zero_of_mul ha
  have hva : v a ≠ 0 := by
    intro h0
    apply hxa
    refine (hρ _).mpr (hK ?_)
    rw [RingHom.mem_ker, phiZ_xw, hv, h0, map_zero, zero_mul]
  obtain ⟨a₀, ha₀, htr₀⟩ := htr
  have htra : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a)) ≤ WeightFamilies.dimY D j := by
    rw [CurveCount.adjoin_ratio_eq v hva ha₀]
    exact htr₀
  have htrans : ∀ Q : MvPolynomial (Fin N) B.KO, aeval (fun i => v i / v a) Q = 0 →
      aeval (fun i => x i / x a) Q = 0 := by
    intro Q hQ
    have hH := CurveCount.homog_isHomogeneous a Q
    have hv0 : aeval v (CurveCount.homog a Q) = 0 := by rw [CurveCount.aeval_homog a Q v hva, hQ, mul_zero]
    have hq : polX X la N w (CurveCount.homog a Q) ∈ 𝔮 := hK (by
      rw [RingHom.mem_ker, phiZ_polX X la N w gF hH, hvf, hv0, map_zero, mul_zero])
    have hx0 : aeval x (CurveCount.homog a Q) = 0 := by rw [← hρpol]; exact (hρ _).mpr hq
    rw [CurveCount.aeval_homog a Q x hxa] at hx0
    exact (mul_eq_zero.mp hx0).resolve_left (pow_ne_zero _ hxa)
  exact CurveCount.countCore v x a hva hxa htra htrans t ht hlin hlin0 Pw hPw hne
    (by rw [← hρpol]; exact (hρ _).mpr hmem)

end CurveLoc

end Formalism.L2.Pj
end
end

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem formsEvR_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    formsEvR j hG hT Z ((recPlus h j hj).inc u F) = evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j) :=
  formsEvR_single j hG hT Z _ _

theorem birAt_of_ev {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (X : PJ D B P j) (N : ℕ) {wL : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (ev : ∀ u : WeightFamilies.Wt D j, B.Cusp j u → Ω) (hev : ∀ u F, gF (X.inc u F) = ev u F)
    (hB : ∀ a : Ω, ∃ (k : ℕ) (g : B.Cusp j (wsmul k wL)) (Pw : MvPolynomial (Fin N) B.KO), Pw.IsHomogeneous k ∧
      MvPolynomial.aeval (fun i => ev wL (w i)) Pw ≠ 0 ∧
      a * MvPolynomial.aeval (fun i => ev wL (w i)) Pw = ev (wsmul k wL) g) :
    CurveLoc.BirAt X N w gF := by
  intro a
  obtain ⟨k, g, Pw, hP, hne, he⟩ := hB a
  refine ⟨k, g, Pw, hP, ?_, ?_⟩
  · simp only [hev]
    exact hne
  · simp only [hev]
    exact he

theorem birAt_of {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BIRSt h j hj hG G)
    (Z : Comp (T.Q.Xo j) T.Q.c) : CurveLoc.BirAt (recPlus h j hj) G.N G.w (formsEvR j hG hT Z) :=
  birAt_of_ev j (recPlus h j hj) G.N G.w (formsEvR j hG hT Z)
    (fun u F => evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j))
    (fun u F => formsEvR_inc h j hj hG hT Z u F) (hB Z)

theorem split_of (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (Z : Comp (T.Q.Xo j) T.Q.c) (k : Fin G.N) :
    ∃ g : (recB h.toLawsCore).Cusp j wL,
      formsEvR j hG hT Z ((recPlus h j hj).inc wL g) = formsEvR j hG hT Z ((recPlus h j hj).inc wL (G.w k)) ∧
      ∀ Z', Z' ≠ Z → formsEvR j hG hT Z' ((recPlus h j hj).inc wL g) = 0 := by
  obtain ⟨g', h1, h2⟩ := hC Z wL (G.w k)
  exact ⟨g', by rw [formsEvR_inc, formsEvR_inc, h1], fun Z' hZ' => by rw [formsEvR_inc, h2 Z' hZ']⟩

def CountQAtSt : Prop :=
  ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)),
    CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      CurveLoc.CountQAt (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)

theorem hone_of (hC : CompSplitSt h j hG) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
        ∀ Z Z', RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z') ≤ Q → Z = Z' := by
  intro ka wL wF G S g0 la _ Q hQ _ Z Z' hZ hZ'
  exact CurveLoc.one_of_split (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun Z k => split_of h j hj hG hT hC G Z k) Q hQ Z Z' hZ hZ'

theorem countQAtSt_holds : CountQAtSt h j hj hG hT := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨k₀, hk₀, htr⟩ := hH.2.1.2 Z
  exact CurveLoc.countQAt_of (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun i => formsEvR_inc h j hj hG hT Z wL (G.w i)) ⟨k₀, hk₀, le_of_eq htr⟩

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FnDefC
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem relab_rt_iff (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
  have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    rw [hval, ← hσ0]
    exact congrArg σ (Subtype.ext hx)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
        rw [← map_neg]
        exact congrArg σ (Subtype.ext hx)
      rw [← hval, h, hσ0] at h1
      exact h0 (by linear_combination h1 / 2)
    · exfalso
      exact h0 (by linear_combination (h.symm.trans hx) / 2)

variable {σ : c.F →+* ℂ}



open Classical in
def nCol (U : Unf Xo c σ r) (n : ℕ) (k : U.Comp) (j : Fin r) : ℝ :=
  if (U.X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℝ) else -((n / 2 : ℕ) : ℝ)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.GenSpecCut
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def SepXSt : Prop := IsSeparated Xo.s

variable {Xo c}


end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.TieGenR
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def RatAt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) (P : Om Z →+* ℂ) : Prop :=
  ∀ (u : WeightFamilies.Wt D j) (F G' : (recB h.toLawsCore).Cusp j u), Even u.n →
    valC hG (wtA u) u.n G'.1 Z ≠ 0 →
    rdR h j F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F.1 Z)
      (valC hG (wtA u) u.n G'.1 Z)) * rdR h j G' (κ Z) x


end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.TieGenRg
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ratio_single {Z : Comp Xo c} (G : WTZ E) (r s : Om Z) (hs : s ≠ 0) :
    ratio (Ω := Om Z) (AddMonoidAlgebra.single G r : AC Z) (AddMonoidAlgebra.single G s) = r / s := by
  have hex : ∃ a : Om Z, (AddMonoidAlgebra.single G r : AC Z) = a • AddMonoidAlgebra.single G s :=
    ⟨r / s, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ r hs]⟩
  unfold ratio
  rw [dite_eq_left hex]
  have e := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at e
  have e2 : r = hex.choose * s := by
    simpa [AddMonoidAlgebra.coeff_single] using congrArg (fun q : AC Z => q.coeff G) e
  rw [eq_div_iff hs]
  exact e2.symm

variable {D : D7} {T : Top D} {j : ℕ}
  {d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)}
  {Z : Comp (T.Q.Xo j) T.Q.c} {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r}


end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ZeroWeightAlgebraicPart
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def evCH (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c) :
    T.R j →+* Om Z where
  toFun f := evC hG Z f
  map_one' := evalAt_one (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) _
    (h.allTest j hj (Om Z) _)
  map_mul' f g := evalAt_mul (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f g _
  map_zero' := evalAt_zero (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) _
  map_add' f g := evalAt_add (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f g _

theorem rdU_one_of (h : LawsP T) {j : ℕ} (hj : InR D j) (k : (T.U j T.σ₀).Comp)
    {y : Frame ((T.U j T.σ₀).X k).Ψ D.R.r} (hy : y ∈ ((T.U j T.σ₀).X k).dom) : rdU (T.U j T.σ₀) 1 k y = 1 := by
  haveI : IsReduced (CAt T.σ₀) := inferInstanceAs (IsReduced ℂ)
  unfold rdU
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
  show toC (evalAt (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) 1
    ((T.U j T.σ₀).un k ⟨y, hy⟩)) = 1
  rw [evalAt_one (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) _
    (h.allTest j hj _ _)]
  rfl


open Classical in
def frAt {j : ℕ} {k : (T.U j T.σ₀).Comp} (x₀ x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) :
    Frame ((T.U j T.σ₀).X k).Ψ D.R.r :=
  if x ∈ ((T.U j T.σ₀).X k).dom then x else x₀

theorem frAt_mem {j : ℕ} {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) (x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) :
    frAt x₀ x ∈ ((T.U j T.σ₀).X k).dom := by
  unfold frAt
  split_ifs with hx
  · exact hx
  · exact hx0

def evFr (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) : T.R j →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) where
  toFun f x := rdU (T.U j T.σ₀) f k (frAt x₀ x)
  map_one' := funext fun x => rdU_one_of h hj k (frAt_mem hx0 x)
  map_mul' f g := funext fun x => by
    show rdU (T.U j T.σ₀) (f * g) k (frAt x₀ x) = rdU (T.U j T.σ₀) f k (frAt x₀ x) * rdU (T.U j T.σ₀) g k (frAt x₀ x)
    rw [rdU_mul]; rfl
  map_zero' := funext fun x => by simp
  map_add' f g := funext fun x => by simp

def augF {j : ℕ} (k : (T.U j T.σ₀).Comp) :
    AddMonoidAlgebra (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (WTZ D.host.E) →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id _) 1 (fun _ _ => Commute.all _ _)

def thR (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) :
    AddMonoidAlgebra (T.R j) (WTZ D.host.E) →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  (augF k).comp (AddMonoidAlgebra.mapRingHom (WTZ D.host.E) (evFr h hj hx0))

def secZ (T : Top D) (j : ℕ) (G : WTZ D.host.E) : Submodule T.Q.c.F (T.R j) :=
  ⨆ u : {u : WeightFamilies.Wt D j // wtZ (wtA u) u.n = G}, sec (T.Q.Xo j) T.Q.c (wtA u.1) u.1.n

theorem secZ_mul {j : ℕ} {G G' : WTZ D.host.E} {f g : T.R j} (hf : f ∈ secZ T j G) (hg : g ∈ secZ T j G') :
    f * g ∈ secZ T j (G + G') := by
  refine Submodule.iSup_induction _ (motive := fun f => f * g ∈ secZ T j (G + G')) hf (fun p f hf => ?_)
    (by rw [zero_mul]; exact zero_mem _) (fun f1 f2 h1 h2 => by rw [add_mul]; exact add_mem h1 h2)
  refine Submodule.iSup_induction _ (motive := fun g => f * g ∈ secZ T j (G + G')) hg (fun q g hg => ?_)
    (by rw [mul_zero]; exact zero_mem _) (fun g1 g2 h1 h2 => by rw [mul_add]; exact add_mem h1 h2)
  have hs := sec_mul (T.Q.Xo j) T.Q.c _ _ _ _ hf hg
  rw [← wtA_wadd] at hs
  refine Submodule.mem_iSup_of_mem ⟨WeightAlgebra.wadd p.1 q.1, ?_⟩ hs
  show wtZ (wtA (WeightAlgebra.wadd p.1 q.1)) (p.1.n + q.1.n) = G + G'
  rw [wtA_wadd, wtZ_add, p.2, q.2]

def w00 (D : D7) (j : ℕ) : WeightFamilies.Wt D j := WeightAlgebra.wscalar D j 0 ⟨0, rfl⟩

theorem zero_weight_algebraic_part {j : ℕ} : wtA (w00 D j) = 0 := by
  funext x
  simp [wtA, w00, WeightAlgebra.wscalar, ext0]

theorem one_mem_sec {j : ℕ} : (1 : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA (w00 D j)) (w00 D j).n := by
  rw [zero_weight_algebraic_part]
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1; rw [map_one]
  · show (1 : p.R) = wchar (ex (T.Q.Dw j) 0 0) t * 1
    have : ex (T.Q.Dw j) 0 0 = 0 := by funext i; cases i <;> rfl
    simp [wchar, this]

theorem zero_weight_exponent_zero {j : ℕ} : wtZ (wtA (w00 D j)) (w00 D j).n = 0 := by
  rw [zero_weight_algebraic_part]
  rfl

def secSub (T : Top D) (j : ℕ) : Subring (AddMonoidAlgebra (T.R j) (WTZ D.host.E)) where
  carrier := {b | ∀ G, b.coeff G ∈ secZ T j G}
  one_mem' G := by
    classical
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with hG0
    · subst hG0
      exact Submodule.mem_iSup_of_mem ⟨w00 D j, zero_weight_exponent_zero⟩ one_mem_sec
    · exact zero_mem _
  mul_mem' {a b} ha hb G := by
    classical
    rw [AddMonoidAlgebra.coeff_mul]
    refine Submodule.finsuppSum_mem _ _ _ _ fun m1 _ => Submodule.finsuppSum_mem _ _ _ _ fun m2 _ => ?_
    split_ifs with hm
    · subst hm; exact secZ_mul (ha m1) (hb m2)
    · exact zero_mem _
  zero_mem' G := by simp
  add_mem' {a b} ha hb G := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact add_mem (ha G) (hb G)
  neg_mem' {a} ha G := by
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]; exact neg_mem (ha G)

section Kappa
variable (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (Z : Comp (T.Q.Xo j) T.Q.c)


variable {x₀ : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r} (hx0 : x₀ ∈ ((T.U j T.σ₀).X (κ Z)).dom)


end Kappa

section Rd
variable (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (Z : Comp (T.Q.Xo j) T.Q.c)
  {x₀ : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r} (hx0 : x₀ ∈ ((T.U j T.σ₀).X (κ Z)).dom)



end Rd

end Formalism.L2.Pj
end
end

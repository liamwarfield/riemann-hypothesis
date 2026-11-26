module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.SecJet

section Alg

variable (R : Type) [CommRing R]

def sqIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) R) ^ 2)

abbrev EpsAlg (k : ℕ) : Type := MvPolynomial (Fin k) R ⧸ sqIdeal R k

def eps {k : ℕ} (a : Fin k) : EpsAlg R k := Ideal.Quotient.mk _ (MvPolynomial.X a)

theorem eps_mul_self {k : ℕ} (a : Fin k) : eps R a * eps R a = 0 := by
  rw [eps, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span ⟨a, rfl⟩

def epsIncl {k : ℕ} (a : Fin k) : DualNumber R →ₐ[R] EpsAlg R k :=
  DualNumber.lift ⟨(Algebra.ofId R (EpsAlg R k), eps R a), eps_mul_self R a,
    fun _ => Commute.all _ _⟩

end Alg

end GlobalTheory.SecJet

namespace GlobalTheory.SecJet

section Geo

variable (R : Type) [CommRing R]

abbrev epsT (k : ℕ) : Over (Sp R) := Over.mk (spMap (algebraMap R (EpsAlg R k)))

theorem spMap_comp_eq {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    spMap (f : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def epsIn {k : ℕ} (a : Fin k) : epsT R k ⟶ epsR R :=
  Over.homMk (spMap ((epsIncl R a : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k))
    (spMap_comp_eq R (epsIncl R a))

def epsScaleA (c : R) : DualNumber R →ₐ[R] DualNumber R :=
  { epsScaleR c with commutes' := fun r => by simp [epsScaleR] }

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (spMap_comp_eq R (epsScaleA R c))

variable {R}

def tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) : epsR R ⟶ G :=
  (List.ofFn fun i => epsScale R (c i) ≫ v i).prod

theorem isLieComb_tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) :
    IsLieComb c v (tanComb c v) :=
  ⟨_, fun _ => rfl, rfl⟩

end Geo


open Classical in
def rigVal {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA]
    {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {N : ℕ} (w : LB.Iso (MM.L.pull φ) (lbPow P.L N))
    (i₀ : (lbPow P.L N).ι) : K :=
  if h : ∃ p : PUnit → MM.L.ι,
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) then
    valR (X := P.A.left) (eSec P.A) _ (w.s (i₀, h.choose)).val *
      valR (X := Sp (𝓞 K)) (spMap (algebraMap (𝓞 K) K)) _ (MM.rig.s h.choose).val
  else 0

end GlobalTheory.SecJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

namespace GlobalTheory.Discrepancy.DivOver

theorem sum_ord_sub_one_le_formOrd_dOn : ∀ {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [LocallyOfFiniteType p] {n : ℕ}, topologicalKrullDim X = n → ∀ (E : DivOver p) {U : X.Opens} {y : X}
    (hy : y ∈ U), E.Through y → ∀ (z : Fin n → Γ(X, U)), formOf U (gen_mem hy) (dOn p z) ≠ 0 →
    ∀ {J : Type} [Fintype J] (e : J → Fin n), Function.Injective e → ∀ (u : J → X.functionFieldˣ),
    (∀ j, (u j : X.functionField) = fnOf U (gen_mem hy) (z (e j))) →
    ∑ j, E.ord (u j) - 1 ≤ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn p z)) := by
  intro k _ _ X _ p _ n hn E U y hy hE z hz0 J _ e he u hu
  classical
  letI := (Cartier.constFn p).toAlgebra
  letI := E.const.toAlgebra
  haveI : IsScalarTower k E.ring X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let x : Fin n → X.functionField := fun i => fnOf U (gen_mem hy) (z i)
  have hxV : ∀ i, x i ∈ E.ring := fun i => hE _ (regAt_fnOf hy _ (z i))
  have hη : formOf U (gen_mem hy) (dOn p z) = dWedge k x := by
    change TopForm.formMap n _ _ (dForm _ z) = _
    rw [formMap_dForm]
    rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht0 : algebraMap E.ring X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective E.ring X.functionField)).mpr ht.ne_zero
  let S : Finset (Fin n) := Finset.univ.map ⟨e, he⟩
  have hxe : ∀ j, x (e j) = (u j : X.functionField) := fun j => (hu j).symm
  have hxS : ∀ i ∈ S, x i ≠ 0 := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    change x (e j) ≠ 0
    rw [hxe j]
    exact (u j).ne_zero
  obtain ⟨γ, hγ⟩ := GlobalTheory.smul_dlogWedge_mem_regForms k t ht0 S x
    (fun i hi => exists_eq_unit_mul_zpow ht (hxS i hi)) (fun i _ => ⟨⟨x i, hxV i⟩, rfl⟩)
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨a, rfl⟩ := hω.2 γ
  have hbr : ∀ θ, GlobalTheory.formMap k E.ring X.functionField n θ = E.toRat n θ := fun _ => rfl
  have hP : (∏ i ∈ S, x i) = ∏ j, (u j : X.functionField) := by
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun j _ => hxe j
  have hPne : (∏ i ∈ S, x i) ≠ 0 := Finset.prod_ne_zero_iff.2 hxS
  have h2 : dWedge k x = (∏ i ∈ S, x i) • dlogWedge k S x := by
    rw [GlobalTheory.dlogWedge_eq_smul, smul_smul, mul_inv_cancel₀ hPne, one_smul]
  have h3 : (algebraMap E.ring X.functionField t) • dlogWedge k S x =
      (algebraMap E.ring X.functionField a) • E.toRat n ω := by
    calc (algebraMap E.ring X.functionField t) • dlogWedge k S x = t • dlogWedge k S x :=
          algebraMap_smul _ t _
      _ = GlobalTheory.formMap k E.ring X.functionField n (a • ω) := hγ.symm
      _ = a • E.toRat n ω := by rw [map_smul, hbr]
      _ = (algebraMap E.ring X.functionField a) • E.toRat n ω := (algebraMap_smul _ a _).symm
  have key : formOf U (gen_mem hy) (dOn p z) =
      ((∏ i ∈ S, x i) * (algebraMap E.ring X.functionField t)⁻¹ *
        algebraMap E.ring X.functionField a) • E.toRat n ω := by
    rw [hη, h2, mul_assoc, mul_smul, mul_smul, ← h3, inv_smul_smul₀ ht0]
  have ha0 : algebraMap E.ring X.functionField a ≠ 0 := by
    intro h
    apply hz0
    rw [key, h, mul_zero, zero_smul]
  let f : X.functionFieldˣ := (∏ j, u j) * (Units.mk0 _ ht0)⁻¹ * Units.mk0 _ ha0
  have hf : formOf U (gen_mem hy) (dOn p z) = (f : X.functionField) • E.toRat n ω := by
    rw [key, hP]
    simp [f]
  have hsum : ∀ s : Finset J, E.ord (∏ j ∈ s, u j) = ∑ j ∈ s, E.ord (u j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, E.ord_mul, ih]
  have hordt : E.ord (Units.mk0 _ ht0) = 1 :=
    (congrArg WithZero.log (Ring.ordFrac_irreducible (K := X.functionField) ht)).trans
      (WithZero.log_exp 1)
  have horda : 0 ≤ E.ord (Units.mk0 _ ha0) := (E.ord_nonneg_iff _).2 a.2
  change (∑ j, E.ord (u j) - 1) ≤ E.formOrd (formOf U (gen_mem hy) (dOn p z))
  rw [IsFormOrd.formOrd_eq hz0 ⟨ω, hω, f, hf, rfl⟩]
  simp only [f, E.ord_mul, E.ord_inv, hsum, hordt]
  omega

end GlobalTheory.Discrepancy.DivOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_ord_sub_one_le_ord_wedgeDifferentials : ∀ {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [LocallyOfFiniteType p] {n : ℕ}, topologicalKrullDim X = n → ∀ (E : DivOver p) {U : X.Opens} {y : X}
    (hy : y ∈ U), E.Through y → ∀ (z : Fin n → Γ(X, U)), formOf U (gen_mem hy) (dOn p z) ≠ 0 →
    ∀ {J : Type} [Fintype J] (e : J → Fin n), Function.Injective e → ∀ (u : J → X.functionFieldˣ),
    (∀ j, (u j : X.functionField) = fnOf U (gen_mem hy) (z (e j))) →
    ∑ j, E.ord (u j) - 1 ≤ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn p z)) := by
  first | exact @GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn | exact GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn | (intros; apply GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

namespace GlobalTheory.CovTop.Sizes

theorem eventually_scale {eps : ℝ} (he : 0 < eps) (A M : ℝ) : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    M ≤ x ^ eps ∧ 10 ≤ x ^ eps ∧ 1 ≤ Real.log (Real.log x) ∧ (x ^ A) ^ M ≤ Real.exp (x ^ eps) ∧ 5 ≤ x ^ (eps / 5) ∧
      (10 : ℝ) ^ 60 ≤ x := by
  have h1 := (tendsto_rpow_atTop he).eventually_ge_atTop M
  have h2 := (tendsto_rpow_atTop he).eventually_ge_atTop 10
  have h3 := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  have h5 := (tendsto_rpow_atTop (by positivity : 0 < eps / 5)).eventually_ge_atTop 5
  have h6 := Filter.eventually_ge_atTop ((10 : ℝ) ^ 60)
  have h4 := ((isLittleO_log_rpow_atTop he).const_mul_left (A * M)).bound one_pos
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx0 x hx
  have hx0' : 0 < x := lt_of_lt_of_le (by norm_num) a6
  refine ⟨a1, a2, a3, ?_, a5, a6⟩
  rw [← Real.rpow_mul hx0'.le, Real.rpow_def_of_pos hx0', Real.exp_le_exp]
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0' eps)] at a4
  rw [mul_comm]
  exact (le_abs_self _).trans a4

theorem coprime_fifteen {g : ℕ} (hg : g.Prime) (h : 15 < g) : Nat.Coprime 15 g :=
  ((Nat.Prime.coprime_iff_not_dvd hg).2 fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (not_le.2 h)).symm

theorem hostNum_of_sizes {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (T : ParamsT D L P) (S : SizesAt L) {A M : ℝ}
    (hg : ∀ k, Real.log (D.host.g k : ℝ) ≤ 9 * L.sc.L + 1) (hA : 22 + L.Ct ≤ A)
    (a1 : M ≤ L.sc.L) (a2 : 10 ≤ L.sc.L) (a3 : 1 ≤ Real.log (Real.log L.sc.x)) (a4 : (L.sc.x ^ A) ^ M ≤ L.sc.b)
    (a5 : 5 ≤ L.sc.x ^ (L.sc.ez / 5)) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x) : HostNum D L T.PP A M := by
  have hfr := Pm.fr_le_pow S hx
  obtain ⟨sN, -, -, -, -, -, sQD, -, -, -, -, -, -, -, -, -, -, sW, -, -, sG, -, -⟩ := S
  have hx1 := L.sc.one_lt_alt.le
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hL := Pm.one_le_L L
  have hf := Pm.two_le_f D
  have hr := Pm.six_le_r D
  have hrt := Pm.r_le_alt_alt D
  have hLx : L.sc.L ≤ L.sc.x := by
    calc L.sc.L = L.sc.x ^ L.sc.eps := rfl
      _ ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = L.sc.x := Real.rpow_one _
  have hnV : (D.R.nV : ℝ) ≤ 2 * D.R.t := by
    have : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
    linarith
  have hnV0 : (0 : ℝ) < D.R.nV := by
    have : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
    linarith
  have hCt : 0 ≤ L.Ct := by
    by_contra hc
    have := Real.rpow_lt_one_of_one_lt_of_neg L.sc.one_lt_alt (not_le.1 hc)
    linarith [L.t_win.1, L.t_win.2]
  have hgl : ∀ k, 15 < D.host.g k := fun k => by
    have hk : (1 : ℝ) ≤ D.R.k := by
      have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
      exact_mod_cast this
    have hb : (2 : ℝ) ≤ L.sc.b := by
      have := Real.add_one_le_exp L.sc.L
      unfold Scale.b
      linarith
    have h2 : (2 : ℝ) ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h3 : (2 : ℝ) ^ 8 ≤ D.host.g k := (pow_le_pow_left₀ (by norm_num) h2 8).trans (sG k k).1
    have h4 : ((15 : ℕ) : ℝ) < D.host.g k := lt_of_lt_of_le (by norm_num) h3
    exact_mod_cast h4
  refine ⟨⟨a1, a2, hLx, a3⟩, ?_, ?_, ⟨?_, ?_⟩, hg, ?_, ?_, ?_, ?_, ?_, ⟨by linarith, ?_, ?_⟩, a4, sW⟩
  · have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
      calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
    have h2 : (4 : ℝ) ≤ D.R.n := le_trans (by norm_num) (hx.trans (h1.trans sN.1))
    have h3 : ((8 : ℕ) : ℝ) ≤ D.R.f := by rw [Pm.f_eq]; push_cast; linarith
    exact_mod_cast h3
  · have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    rw [h1]; unfold Ranks.f Ranks.n; ring
  · rw [Real.log_mul (by linarith) (by linarith)]
    linarith [Pm.log_f_le P, Pm.log_r_le P]
  · have h1 := Real.log_le_log hnV0 hnV
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith [(Pm.log_cond_le P).2, Real.log_two_lt_d9]
  · have h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L := logdE_le_two_f_L P
    nlinarith
  · exact sQD.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))
  · exact le_trans (Nat.le_floor (by exact_mod_cast a5)) L.split_tie
  · exact Nat.Coprime.mul_right (coprime_fifteen (D.host.g_prime 0) (hgl 0)) (coprime_fifteen (D.host.g_prime 1) (hgl 1))
  · have hZ := Pm.one_le_Z L
    have h1 : zBase L ^ 12 ≤ zBase L ^ T.eP := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)
    rw [T.PP_eq]
    exact h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)
  · exact T.PP_poly.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  · have h2 : (D.R.nV : ℝ) ≤ L.sc.x * L.sc.x ^ L.Ct :=
      hnV.trans (mul_le_mul (le_trans (by norm_num) hx) L.t_win.2 (by positivity) hx0.le)
    calc (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.x ^ (20 : ℝ) * (L.sc.x * L.sc.x ^ L.Ct) * L.sc.x := by gcongr
      _ = L.sc.x ^ (20 + (1 + L.Ct) + 1) := by
        rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

theorem hostN : ∀ M : ℝ, HostN M := by
  intro M
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := eventually_scale he (22 + |Fm.Ct|) M
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)
  refine ⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := hx0 x ((le_max_left _ _).trans hle)
  have a5 : 5 ≤ x ^ (Fm.ez / 5) := hx2 x ((le_max_right _ _).trans hle)
  have hsz : (Fm.L x ι).sc.ez = Fm.ez := Fm.toFamCore.L_ez x ι
  have hsx : (Fm.L x ι).sc.x = x := Fm.L_x x ι hx
  have hse : (Fm.L x ι).sc.eps = eps := Fm.L_eps x ι
  have hsL : (Fm.L x ι).sc.L = x ^ eps := by unfold Scale.L; rw [hsx, hse]
  have hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1 := fun k => by
    have hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ) := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    have := (Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)
    linarith
  refine hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Fm.Ct_eq]; linarith [le_abs_self Fm.Ct]
  · rwa [hsL]
  · rwa [hsL]
  · rwa [hsx]
  · unfold Scale.b; rwa [hsL, hsx]
  · rwa [hsx, hsz]
  · rwa [hsx]

end GlobalTheory.CovTop.Sizes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.OrbitSep

section Lin

variable {X : Scheme.{0}} [IsIntegral X] {Γ : Type} [Group Γ]

def fnAct (ρ : Γ →* Aut X) (γ : Γ) : X.functionFieldˣ →* X.functionFieldˣ :=
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  Units.map (GlobalTheory.functionFieldMap (ρ γ).asIso.hom).toMonoidHom

def RatLin (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB) : Prop :=
  ∃ (D : CartierDiv X) (c : Γ → X.functionFieldˣ), cls (toLB D) (isLB_toLB D) = cls L hL ∧
    (∀ γ δ, c (γ * δ) = fnAct ρ δ (c γ) * c δ) ∧
    (∀ γ x g, D.IsEqn ((ρ γ).asIso.hom x) g → D.IsEqn x (fnAct ρ γ g * (c γ)⁻¹)) ∧
    ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * (c γ)⁻¹ * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Base

variable (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

abbrev X₀ : Scheme.{0} := (barComp Y Z).toScheme

abbrev s₀ : X₀ Y Z ⟶ Sp c.F := (barComp Y Z).ι ≫ Y.s

abbrev V₀ : Scheme.{0} := (Y.j ⁻¹ᵁ barComp Y Z).toScheme

abbrev i₀ : V₀ Y Z ⟶ Xo.XF c := (Y.j ⁻¹ᵁ barComp Y Z).ι

abbrev j₀ : V₀ Y Z ⟶ X₀ Y Z := Y.j ∣_ barComp Y Z


variable {Y} in
abbrev π₀ (X : FlagCover Y) (Z : Comp Xo c) : Y₀ X Z ⟶ X₀ Y Z := X.π ∣_ barComp Y Z


variable {Y} in
theorem π₀_s₀ (X : FlagCover Y) (Z : Comp Xo c) : π₀ X Z ≫ s₀ Y Z = str₀ X Z := by
  dsimp only [π₀, s₀, str₀, inc₀, flagStr]
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

theorem j₀_ι : j₀ Y Z ≫ (barComp Y Z).ι = i₀ Y Z ≫ Y.j :=
  morphismRestrict_ι _ _


variable {Y Z} in
def ActsBy {Γ : Type} [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ Y Z)) : Prop :=
  (∀ γ, (ρ γ).asIso.hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z) ∧
    ∀ (γ : Γ) (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v : Sp R ⟶ V₀ Y Z), v ≫ i₀ Y Z = ptF y →
      v ≫ (ρ γ).asIso.hom ≫ i₀ Y Z = ptF (move Xo c (ι γ)⁻¹ y)

end Base


variable (Dw) in
def kapBase : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (Dw.q : ℤ) else -(Dw.p : ℤ)

def UnipAt (I : Ideal (𝓞 E)) (γ : LevelAut Dw l) : Prop :=
  ∃ m : ℕ, ∀ x : Dw.La, ((liftLa γ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)

def NeatPrime (I : Ideal (𝓞 E)) (g r : ℕ) : Prop :=
  g.Prime ∧ Ideal.absNorm I = g ∧ (g : 𝓞 E) ∉ I ^ 2 ∧ r + 1 < g

theorem gapGe_sub_kapBase (t : ℤ) (ht : ((Dw.p + Dw.q : ℕ) : ℤ) ≤ t) : GapGe 0 (t • hodgeWt Dw - kapBase Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [Pi.sub_apply, Pi.smul_apply, hodgeWt, GlobalTheory.CompHt.barWt, kapBase, smul_eq_mul]
  push_cast at ht ⊢
  split_ifs <;> omega

theorem gapGe_hodgeWt : GapGe 0 (hodgeWt Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [hodgeWt, GlobalTheory.CompHt.barWt]
  split_ifs <;> omega

end GlobalTheory.OrbitSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

section IntWeight

open _root_.Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type}
  {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
  {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
  {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}

theorem evalAt_borR_of_borChart_int [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have key : ∀ i, Units.map cB.toRingHom.toMonoidHom (tB i) = Units.map (locM K m).toRingHom.toMonoidHom (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map cB.toRingHom.toMonoidHom (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map (locM K m).toRingHom.toMonoidHom (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp_rw [map_zpow, key]

end IntWeight

open _root_.Formalism.L2.Pj AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem evR_frBor_of_mem_secZ (hS : Out.SecBaseChangeSt) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ)
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (hb : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  have hB := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1
  have hall := GlobalTheory.T.framedPoint_reduced_from_testRing hS E H Dw l Xo c
  exact evalAt_borR_of_borChart_int hB e hf.1 hf.2 S t y y' (hall S y) (hall S y') hb

theorem test_value_eq_const_mul_reading_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (p : TRing c.F)
    (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) :
    ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ secZ Xo c e,
      Formalism.L2.Pj.toC (ψ (f p y)) = u * rdU U f k x.1 := by
  obtain ⟨-, -, hW, -, -, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R (CAt σ) ψ y
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 z
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨k, x, Formalism.L2.Pj.toC ((∏ i, t i ^ e i : (CAt σ)ˣ) : CAt σ), fun f hf => ?_⟩
  have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
  have hev : evR Xo c f z = ψ (f p y) := by
    unfold evR evalAt
    rw [dite_eq_left hft]
    exact hW f hf.1 (CAt σ) _ p _ ψ _ y z hft.choose_spec.choose_spec.choose_spec hz
  have hw := evR_frBor_of_mem_secZ hS Xo c e hf (CAt σ) t _ _ ht
  rw [← hev, hw]
  classical
  show _ = _ * (if h : x.1 ∈ (U.X k).dom then Formalism.L2.Pj.toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0)
  rw [dite_eq_left x.2]
  rfl

theorem reading_linearIndependent_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (m : ℕ) (b : Fin m → Rul Xo c)
    (hb : ∀ i, b i ∈ secZ Xo c e) (hli : LinearIndependent c.F b) :
    LinearIndependent ℂ (fun i => rdU U (b i)) := by
  have h := fun p y ψ => test_value_eq_const_mul_reading_secZ hS U hU e p y ψ
  have : CharZero c.F := RingHom.charZero σ
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
    intro θ
    have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
      funext p y
      have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
        obtain ⟨k', x, u, hk⟩ := h p y ψ
        have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU U (b i) k' x.1) := by
          intro i; rw [show cvalR σ (ψ (b i p y)) = Formalism.L2.Pj.toC (ψ (b i p y)) from rfl, hk (b i) (hb i)]; ring
        have e2 := congrFun (congrFun hw k') x.1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
        simp_rw [e1]
        rw [← Finset.mul_sum, e2, mul_zero]) θ
      simpa [Finset.sum_apply] using hpt
    exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
  intro i
  exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i

theorem cuspW_finiteDimensional_of_isUnf (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (G : WTZ E) :
    FiniteDimensional c.F (cuspW Xo c U G) := by
  classical
  let W : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | P ∈ holSub (U σ).X (modelWt (U σ) G) ∧ ∀ k, ∀ x ∉ ((U σ).X k).dom, P k x = 0}
      add_mem' := fun {P Q} hP hQ => ⟨add_mem hP.1 hQ.1, fun k x hx => by
        change P k x + Q k x = 0
        rw [hP.2 k x hx, hQ.2 k x hx, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun k x hx => rfl⟩
      smul_mem' := fun t P hP => ⟨Submodule.smul_mem _ t hP.1, fun k x hx => by
        change t • P k x = 0
        rw [hP.2 k x hx, smul_zero]⟩ }
  haveI : FiniteDimensional ℂ W :=
    GlobalTheory.T.finiteDimensional_cuspSections_vanishing_offDomain E r (U σ).Comp (U σ).X (modelWt (U σ) G) W (fun P hP => hP.1) (fun P hP => hP.2)
  have key : ∀ s : Finset (cuspW Xo c U G),
      LinearIndependent c.F (fun i : s => (i : cuspW Xo c U G)) → s.card ≤ Module.finrank ℂ W := by
    intro s hs
    let e := s.equivFin
    have h0 : LinearIndependent c.F (fun j : Fin s.card => ((e.symm j : s) : cuspW Xo c U G)) :=
      hs.comp (fun j => e.symm j) e.symm.injective
    have hb : LinearIndependent c.F
        (fun j : Fin s.card => (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c)) :=
      h0.map' (cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := reading_linearIndependent_secZ hS (U σ) hU (exZ Dw G) s.card _
      (fun j => cuspW_le_secZ G ((e.symm j : s) : cuspW Xo c U G).2) hb
    have hmem : ∀ j : Fin s.card,
        rdU (U σ) (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c) ∈ W :=
      fun j => ⟨(mem_cuspW.1 ((e.symm j : s) : cuspW Xo c U G).2).2 σ hσ, fun k x hx => by
        simp [rdU, hx]⟩
    let b' : Fin s.card → W := fun j => ⟨_, hmem j⟩
    have hc' : LinearIndependent ℂ b' := LinearIndependent.of_comp W.subtype hc
    have := hc'.fintype_card_le_finrank
    simpa using this
  haveI : Module.Free c.F ↥(cuspW Xo c U G) := Module.Free.of_divisionRing _ _
  exact Module.rank_lt_aleph0_iff.mp ((rank_le key).trans_lt (Cardinal.natCast_lt_aleph0))

end GlobalTheory

theorem GlobalTheory.Deep.finiteDimensional_V_of_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, FiniteDimensional Y.d.c₂.F (Y.V G) := by
  intro D T j Y e o hY G
  have hσ : Formalism.L2.Pj.GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom) :=
    Formalism.L2.Pj.goodEmb_goodOf _ _
  exact GlobalTheory.cuspW_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ (hY.unf _ hσ) G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

def PhiAt (y : Y₀ X Z) (ν : Valuation ((Y₀ X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))) (φ : ℝ) : Prop :=
  ∃ (T : CDVR) (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V) (ρ φT : ℝ),
    0 < ρ ∧ GlobalTheory.SlopeRec.HasPhi y' φT ∧ φ = ρ * φT ∧
    (letI := io.toAlgebra; X.ptY y'.1 =
      Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ∧
    ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelNbhd

open GlobalTheory.GfCut

variable {D : D7}

def finIdem (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem finIdem_mul : finIdem D * finIdem D = finIdem D := by
  unfold finIdem
  rw [← map_mul]
  congr 1
  show ((0 : Ainf D.host.F) * 0, (1 : Af D.host.F) * 1) = (0, 1)
  simp

theorem cA_finIdem : cA D (finIdem D) = finIdem D := by
  unfold finIdem
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem fst_finIdem :
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 0 := by
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem snd_finIdem :
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (finIdem D) = 1 := by
  show sndA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 1
  rw [show sndA D.host.F (pairA D.host.F 0 1) = 1 from rfl]
  rfl

def finPartGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (AE D) :=
  ⟨finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • 1,
    finIdem D • ((matHom V g)⁻¹).1 + (1 - finIdem D) • 1,
    idem_mul _ finIdem_mul _ _ (matHom V g).mul_inv, idem_mul _ finIdem_mul _ _ (matHom V g).inv_mul⟩

theorem finPartGL_mem (V : HSp D) (g : GA D V) : finPartGL V g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have hgU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU := idem_unitary (cA D) _ cA_finIdem finIdem_mul _ _ hgU
  exact hKU

def finPartG (V : HSp D) (g : GA D V) : GA D V :=
  (⟨finPartGL V g, finPartGL_mem V g⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem finPartG_mem_GfC (V : HSp D) (g : GA D V) : finPartG V g ∈ GfC V := by
  show infHom V (finPartG V g) = 1
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = 1
  rw [map_idem, fst_finIdem, zero_smul, zero_add, sub_zero, one_smul]

theorem finHom_finPartG (V : HSp D) (g : GA D V) : finHom V (finPartG V g) = finHom V g := by
  apply Units.ext
  change (finIdem D • Formalism.L2.Theta.mt V g + (1 - finIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))).map _ = _
  rw [map_idem, snd_finIdem, one_smul, sub_self, zero_smul, add_zero]
  rfl

theorem inv_finPartG_mul_mem_GinfC (V : HSp D) (g : GA D V) : (finPartG V g)⁻¹ * g ∈ GinfC V := by
  show finHom V ((finPartG V g)⁻¹ * g) = 1
  rw [map_mul, map_inv, finHom_finPartG, inv_mul_cancel]

theorem finCong_finPartG_iff {V : HSp D} {N : ℕ} (g : GA D V) :
    GlobalTheory.Member.FinCong V N (finPartG V g) ↔ GlobalTheory.Member.FinCong V N g := by
  unfold GlobalTheory.Member.FinCong
  rw [finHom_finPartG]

theorem level_mul_inf_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N →
    IsLevelK V N Kf → ∀ g₀ : GA D V,
      {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hU := GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN
  have ht : Filter.Tendsto (fun x : GA D V => g₀⁻¹ * x) (𝓝 g₀) (𝓝 1) := by
    have := (continuous_const_mul g₀⁻¹).tendsto g₀
    rwa [inv_mul_cancel] at this
  refine Filter.mem_of_superset (ht hU) fun x hx => ?_
  have hx' : GlobalTheory.Member.FinCong V N (g₀⁻¹ * x) := hx
  refine ⟨finPartG V (g₀⁻¹ * x), (hK _).2 ⟨finPartG_mem_GfC V _, (finCong_finPartG_iff _).2 hx'⟩,
    (finPartG V (g₀⁻¹ * x))⁻¹ * (g₀⁻¹ * x), inv_finPartG_mul_mem_GinfC V _, ?_⟩
  group

end GlobalTheory.LevelNbhd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhdsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  first | exact @GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | exact GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | (intros; apply GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine
open GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.Reg

namespace GlobalTheory.KeyFourth

theorem prod_zpow_four_smul_keyEx {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    (∏ i, t i ^ ((4 : ℤ) • keyEx Dw) i) = kch t ^ 4 := by
  rw [kch, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  norm_cast


set_option maxHeartbeats 1000000 in
theorem exists_unit_secZ_keyRule : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), 1 ≤ Dw.p + Dw.q → ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro κ h₁ h₂ h₃ E _ _ _ H Dw l Xo c g e hpq
    obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
    have hex : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
        ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
          ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
      have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
        charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
      choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
      refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
      haveI := C.sm
      haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
      haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
      haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
      obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e C.R C.y hpq
      obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om C.Z) C.yg hpq
      obtain ⟨u, hu⟩ := h₃ C.R Φ.key
      refine ⟨Φ, u, hΦ, hu, ?_⟩
      rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
      exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm
    obtain ⟨v, hv⟩ := hex
    obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h ((4 : ℤ) • keyEx Dw) (fun Z => (v Z : Om Z)) fun C => by
      obtain ⟨-, u, -, -, huv⟩ := hv C
      rw [prod_zpow_four_smul_keyEx, ← Units.val_mul, ← huv]
      exact (u : C.R).2
    obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-((4 : ℤ) • keyEx Dw))
        (fun Z => (((v Z)⁻¹ : (Om Z)ˣ) : Om Z)) fun C => by
      obtain ⟨-, u, -, -, huv⟩ := hv C
      have hm : Units.map (C.R.val : C.R →* Om C.Z) u = kch C.t ^ 4 * v C.Z := Units.ext huv
      have hp : (∏ i, C.t i ^ (-((4 : ℤ) • keyEx Dw)) i) = (kch C.t ^ 4)⁻¹ := by
        rw [← prod_zpow_four_smul_keyEx, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.neg_apply, zpow_neg]
      have hq : (kch C.t ^ 4)⁻¹ * (v C.Z)⁻¹ = Units.map (C.R.val : C.R →* Om C.Z) u⁻¹ := by
        rw [map_inv, hm, mul_inv_rev, mul_comm]
      rw [hp, ← Units.val_mul, hq]
      exact ((u⁻¹ : (C.R)ˣ) : C.R).2
    have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
      rw [← GlobalTheory.AllWt.secZ_nat]
      congr 1
      funext i
      cases i <;> rfl
    have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
    rw [add_neg_cancel, h0] at hm
    have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
    rw [h0] at h1
    have hff : f * f' = 1 := by
      refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
      have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
      have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
      have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
        (f * f') 1
      refine e₃.trans ?_
      change evC h Z (f * f') - evC h Z 1 = 0
      rw [e₁, e₂, hfb, hfb', Units.mul_inv, sub_self]
    refine ⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf, ?_⟩
    intro F _ _ _ y Φ hΦ
    change evR Xo c f y = _
    obtain ⟨C, ψ, z, t', hz, hb⟩ := hA h F y
    obtain ⟨ΦC, u, hΦC, hu, huv⟩ := hv C
    obtain ⟨p, a, u₀, hu₀⟩ := hL.test C.R C.y
    have k₁ : evR Xo c f C.yg = C.R.val (evR Xo c f C.y) := by
      rw [GlobalTheory.FlagTan.evR_eq hf.1 hu₀, GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := C.R.val.comp a) hu₀ C.gen fun _ => rfl)]
      rfl
    have k₂ : evR Xo c f C.yg = ((u : C.R) : Om C.Z) := by
      rw [GlobalTheory.FlagTan.evR_frBor hf C.bor, prod_zpow_four_smul_keyEx, huv]
      have := hfb C.Z
      simp only [evC] at this
      rw [this, Units.val_mul]
    have k₃ : evR Xo c f C.y = (u : C.R) := Subtype.val_injective (k₁.symm.trans k₂)
    have k₄ : evR Xo c f z = ψ (u : C.R) := by
      rw [GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := ψ.comp a) hu₀ hz fun _ => rfl), ← k₃, GlobalTheory.FlagTan.evR_eq hf.1 hu₀]
      rfl
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e F z hpq
    have k₅ := GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e F t' z y Ψ Φ hb hΨ hΦ
    have k₆ : (κ F Ψ.key : F) = ψ (u : C.R) :=
      hu F ψ.toRingHom Ψ.key (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e C.R F ψ C.y z ΦC Ψ hz hΦC hΨ)
    rw [GlobalTheory.FlagTan.evR_frBor hf hb, prod_zpow_four_smul_keyEx, k₄, k₅, Units.val_mul, k₆]

end GlobalTheory.KeyFourth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFourStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), 1 ≤ Dw.p + Dw.q → ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) := by
  first | exact @GlobalTheory.KeyFourth.exists_unit_secZ_keyRule | exact GlobalTheory.KeyFourth.exists_unit_secZ_keyRule | (intros; apply GlobalTheory.KeyFourth.exists_unit_secZ_keyRule <;> assumption)
end
end

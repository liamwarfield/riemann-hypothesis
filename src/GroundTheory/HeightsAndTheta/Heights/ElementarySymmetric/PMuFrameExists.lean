module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.FlagLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.EventuallyInFrameDomain
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropTerm
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubInsertion
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists
section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.MuFrameExists
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

def MuFrameExists.Statement (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal D.y), Nonempty (MuFrameAt H z)

end GroundTheory.Heights₂.Heights.NineStatements
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

theorem MuFrameExists.proof (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) :
    MuFrameExists.Statement D H := by
  intro z hz
  choose c hc using hz.1
  have hx : segreCoord D.y c ≠ 0 := HermMetricEq.segreCoord_ne_zero hz hc
  obtain ⟨m, f, cc, hf, hcc, hsum, hdat⟩ := H.locally c hx
  choose vf hvf using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hf l)
  choose vc hvc using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hcc l)
  have hS : IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (∑ l, cc l * f l) z (∑ l, vc l * vf l) :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.sum _ fun l _ => (hvc l).mul (hvf l)
  rw [hsum] at hS
  have h1 : (∑ l, vc l * vf l) = 1 :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz hS IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one
  have hex : ∃ l, vf l ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    simp [hne] at h1
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hb, u, hu, heq⟩ := hdat l
  exact ⟨⟨c, f l, ⟨hc, vf l, HermMetricEq.isValueAt_iff.2 (hvf l), hl⟩, b, hb, u, hu, heq⟩⟩

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperSectionX
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionNonvanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem SectionNonvanish.proof : SectionNonvanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp _ hle ⟨i, hi⟩ D hD
  have hxi : x i ≠ 0 := fun h0 =>
    hi (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).mpr (by rw [aeval_X, h0])))
  refine not_forall_not.mp fun hcon => ?_
  let I : Chart x := singleChart hxi
  have hsec : ∀ s ∈ D.toSubSystem.secs, s ∈ idealMod pp I * D.toSubSystem.sub I := by
    intro s hs
    by_contra hs'
    refine hcon s ⟨hs, I, ?_⟩
    rwa [SubSystem.twist_sub_eq_mul_of_line]
  obtain ⟨P, hP⟩ := D.invertible I
  have hsub : D.toSubSystem.sub I ≤ idealMod pp I * D.toSubSystem.sub I := by
    rw [← hD I, Submodule.span_le]
    intro s hs
    rw [hD I]
    exact hsec s hs
  have hone : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I :=
    calc (1 : Submodule (chartRing k x I) Ω) = D.toSubSystem.sub I * P := hP.symm
      _ ≤ idealMod pp I * D.toSubSystem.sub I * P := mul_le_mul' hsub le_rfl
      _ = idealMod pp I := by rw [mul_assoc]; erw [hP]; rw [mul_one]
  have h1 : (1 : Ω) ∈ idealMod pp I := hone (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  refine SectionCount.Drop.Term.one_not_mem_idealMod hpp hle (I := I) (fun j hj => ?_) h1
  obtain rfl : j = i := Finset.mem_singleton.mp hj
  exact hi

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

namespace SnapperSectionClosed

theorem snapperFinite : SnapperFinite.Statement.{u, w, w} :=
  SnapperFinite.proof Extension.full Extension.full TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem quotAdd : SnapperQuotAdd.Statement.{u, w, w} :=
  SnapperQuotAdd.proof (SnapperSubquotFinite.proof snapperFinite)

theorem quotDevissage : SnapperQuotDevissage.Statement.{u, w, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof quotAdd SubFamilyTwist.proof

end SnapperSectionClosed


open SnapperSectionClosed in
theorem SnapperSection.full : SnapperSection.Statement.{u, w} :=
  SnapperSection.proof quotAdd quotDevissage MulQuotEq.proof SectionNonvanish.proof SectionMulInj.proof

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumTieX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem InterNumTie.proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumTie.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp b hsub
  classical
  obtain ⟨j, hjp⟩ := hsub.relevant
  have hj : x j ≠ 0 := fun h0 => hjp (hsub.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.full k Ω N x pp hsub.isPrime hsub.homog hsub.le j hj hjp
  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  let y : Fin (N + 1) → Ip.ResidueField := fun i => ψ (ratio hj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    change ψ (ratio hj i) = 0
    rw [h0, map_zero]
  have hpy : primeOf (S := k) y = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) y := hpy ▸ hsub.le
  have hsubW : IsSubvar y pp e := ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩
  have hyj : y j ≠ 0 := fun h0 => hjp (hpy ▸ (mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0))
  have hy0 : y ≠ 0 := fun h => hyj (congrFun h j)
  set I := pp.comap (oneBlock (S := k) (N := N)) with hI_def
  have hI : I = primeOfOne (S := k) y := by rw [primeOfOne, hpy]
  have hIp : NumbersDVR.IsMultiProjPrime I := hI ▸ isMultiProjPrime_primeOfOne y hy0
  have hIdim : FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, hI, HilbertPositive.ringKrullDim_primeOfOne, hpy,
      hsub.dim]
    simp
  let H : ℤ → ℤ := fun m => NumbersDVR.hilbFn I (fun _ : Unit => m)
  let R : ℤ → ℤ := fun m => restrLen pp (twistSys k x m)
  have hY : ∀ᶠ n : ℕ in atTop, restrLen pp (twistSys k y (n : ℤ)) = H n := by
    filter_upwards [TwistSections.full k _ N y hy0] with n hn
    rw [← hpy, SectionsOverLocalization.restrLen_primeOf_eq_finrank y hyj, hn, HilbertPositive.finrank_piece_eq_hilbFn, ← hI]
  obtain ⟨r₀, hr₀⟩ := RestrictTwist.full.1 k Ω N x _ y hxy hxy' 0
  have hXY := hRL k Ω N x _ y hxy hxy' pp e hsubW (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have hRH : ∀ᶠ n : ℕ in atTop, R n = H n := by
    filter_upwards [hY, hXY] with n h1 h2
    have e1 : (twistBundle k y 0).toSubSystem = twistSys k y 0 := rfl
    have e2 : (twistBundle k x 0).toSubSystem = twistSys k x 0 := rfl
    rw [e1, e2, twistSys_zero_twist, twistSys_zero_twist] at h2
    rw [← h1, h2]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hRH
  have hRH' : ∀ m : ℤ, (n₀ : ℤ) ≤ m → R m = H m := by
    intro m hm
    have h := hn₀ m.toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega)] at h
  let bs : Fin e → Unit → ℤ := fun i _ => b i
  have hMD := (FieldNumbers.MixedDiffConst.full k Unit (fun _ => Fin (N + 1)) I hIp.multiHomog hIp.relevant e
    hIdim).1 bs
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hMD
  set B : ℤ := ∑ i, b i with hB
  have hev : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => twistSys k x (b i)) c = NumbersDVR.intNum k I bs := by
    filter_upwards [eventually_ge_atTop (m₀ () - B).toNat,
      eventually_all.mpr fun T : Finset (Fin e) => eventually_ge_atTop ((n₀ : ℤ) - ∑ i ∈ T, b i).toNat]
      with c hc1 hc2
    rw [SectionsOverLocalization.interSum_twistSys, ← hm₀ (fun _ => (c : ℤ) + B)
      (fun u => by cases u; change m₀ () ≤ (c : ℤ) + B; omega), SectionsOverLocalization.mixedDiff_eq_sum]
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hsum : (∑ i ∈ Tᶜ, bs i) = fun _ : Unit => ∑ i ∈ Tᶜ, b i := by
      funext u
      rw [Finset.sum_apply]
    have hc : (n₀ : ℤ) ≤ ∑ i ∈ T, b i + c := by have := hc2 T; omega
    have hsplit := Finset.sum_add_sum_compl T b
    have hcard : Tᶜ.card = e - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [show restrLen pp (twistSys k x (∑ i ∈ T, b i + c)) = H (∑ i ∈ T, b i + c) from hRH' _ hc, hsum, hcard]
    change (-1) ^ (e - T.card) * H (∑ i ∈ T, b i + c) =
      (-1) ^ (e - T.card) * NumbersDVR.hilbFn I ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i)
    have hfun : ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i) =
        fun _ : Unit => ∑ i ∈ T, b i + c := by
      funext u
      simp only [Pi.sub_apply]
      omega
    rw [hfun]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hev.mono fun c h => h.symm)).limUnder_eq

theorem InterNumTie.of_restrictQuot (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) :
    InterNumTie.Statement.{u, w} :=
  InterNumTie.proof (RestrLenRestrict.proof
    (SurjectiveClosed.proof Extension.full.{u, w, w} IdealTwistFamily.proof
      (TildeVanish.proof SerreVanish.full.{u, w})) hRQ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

universe u w

section Combinatorics

end Combinatorics

section Snoc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

end Snoc

section Dim

end Dim

theorem InterNumCut.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hA : CutRestrLenExact.Statement.{u, w})
    (hB : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  _root_.UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.proof hF hA hB

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterSumTopVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

attribute [local instance] twistMonoid

theorem InterSumTopVanish.proof (hM : MixedTwistShift.Statement.{u, w}) : InterSumTopVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L hW
  classical
  set L₀ : Fin n → LineBundle k x := fun j => L (Fin.castSucc j) with hL₀
  have hdim : ringKrullDim (Poly k N ⧸ pp) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := hW.dim.le
  have hA := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (L (Fin.last n)) 0
  have hB := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (twistBundle k x 0) 0
  filter_upwards [hA, hB] with c hAc hBc
  have hL : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
      (fun j => (L₀ j).toSubSystem) (L (Fin.last n)).toSubSystem := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hL₀]
  rw [interSum_eq_mixDiff, hL, mixDiff_snoc]
  have eA : mixDiff (fun g => restrLen pp (((L (Fin.last n)).toSubSystem * g).twist (twistSys k x (c : ℤ))))
      (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (L (Fin.last n)).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hc : (L (Fin.last n)).toSubSystem * ∏ j ∈ T, (L₀ j).toSubSystem =
        (∏ j ∈ T, (L₀ j).toSubSystem).twist (L (Fin.last n)).toSubSystem := SubSystem.twist_comm _ _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hc]
  have eB : mixDiff (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ)))) (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (twistBundle k x 0).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hz : (∏ j ∈ T, (L₀ j).toSubSystem).twist (twistBundle k x 0).toSubSystem =
        ∏ j ∈ T, (L₀ j).toSubSystem := SubSystem.twist_twistSys_zero _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hz]
  rw [eA, eB, hAc, hBc, sub_self]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumEventual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumEventual

def ind {n : ℕ} (T : Finset (Fin n)) : Fin n → ℕ := fun i => if i ∈ T then 1 else 0

theorem sum_sign_prod_ind {n : ℕ} (e : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, ((ind T i : ℕ) : ℚ) ^ e i =
      ∏ i, (1 - (0 : ℚ) ^ e i) := by
  have h1 : ∏ i, (1 - (0 : ℚ) ^ e i) = ∏ i ∈ Finset.univ, (1 + -(0 : ℚ) ^ e i) := by
    simp only [sub_eq_add_neg]
  rw [h1, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_const_one, one_mul, Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin,
    ← Finset.prod_mul_prod_compl T, Finset.compl_eq_univ_sdiff]
  congr 1
  rw [Finset.prod_eq_one (fun i hi => by simp [ind, hi]), one_mul]
  exact Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_sdiff] at hi
    simp [ind, hi.2]

theorem mixed_eval {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℚ) (hQ : Q.totalDegree ≤ n) (c : ℚ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
        eval (Fin.snoc (α := fun _ => ℚ) (fun j => ((ind T j : ℕ) : ℚ)) c) Q =
      ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  trans ∑ T : Finset (Fin n), Q.coeff d * c ^ d (Fin.last n) *
      ((-1 : ℚ) ^ (n - T.card) * ∏ i : Fin n, ((ind T i : ℕ) : ℚ) ^ d i.castSucc)
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring
  rw [← Finset.mul_sum, sum_sign_prod_ind]
  by_cases h0 : ∃ i : Fin n, d i.castSucc = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, pow_zero, sub_self])]
    ring
  · push Not at h0
    have hdeg := (le_totalDegree hd).trans hQ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at hdeg
    have hge : n ≤ ∑ i : Fin n, d i.castSucc := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ ∑ i : Fin n, d i.castSucc :=
          Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (h0 i)
    rw [show d (Fin.last n) = 0 by omega, pow_zero, mul_one]

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | a :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = (twistSys k x 0).sub I * ∏ i, (L i).sub I ^ ind T i := by
  unfold tensorSub
  rw [foldl_twist_sub, Fin.prod_univ_def]
  congr 1
  induction List.finRange n with
  | nil => simp
  | cons a l ih => by_cases ha : a ∈ T <;> simp [ha, ind, ih]

theorem tensorSub_eq_twistPows {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (twistSys k x 0).twistPows n L (ind T) :=
  SubSystem.ext_sub fun I => by rw [tensorSub_sub, SnapperSections.twistPows_sub]

end InterNumEventual


open InterNumEventual in
theorem InterNumEventual.proof (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) : InterNumEventual.Statement.{u, w} := by
  have hR : RestrLenEuler.Statement.{u, w} := RestrLenEuler.proof
  intro k _ Ω _ _ N x n pp L hW
  have := hW.isPrime
  obtain ⟨Q, hQ, hev⟩ := pieceChar_isNumPolyLT hH hS SnapperDiffPoly.proof L (n + 1) pp hW.isPrime hW.homog
    hW.le hW.dim.le 0
  have hQn : Q.totalDegree ≤ n := by
    rcases hQ with h | h
    · rw [h, totalDegree_zero]; exact Nat.zero_le _
    · omega
  have hall : ∀ᶠ c : ℕ in atTop, ∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c := by
    refine Filter.eventually_all.mpr fun T => ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (hR k Ω N x pp hW.homog hW.le n L (ind T))] with c hc
    rw [tensorSub_eq_twistPows]
    exact hc
  have hval : ∀ c : ℕ, (∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c) →
      (interSum pp (fun i => (L i).toSubSystem) c : ℚ) =
        ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
    intro c hc
    rw [← mixed_eval Q hQn (c : ℚ)]
    unfold interSum
    push_cast
    refine Finset.sum_congr rfl fun T _ => ?_
    have hT := hev (ind T) (c : ℤ)
    simp only at hT
    rw [hc T, hT, Int.cast_natCast]
  obtain ⟨c₀, hc₀⟩ := hall.exists
  refine ⟨interSum pp (fun i => (L i).toSubSystem) c₀, hall.mono fun c hc => ?_⟩
  exact_mod_cast (hval c hc).trans (hval c₀ hc₀).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMixedTwistShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace MixedTwistShiftAlt

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | i :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem prod_map_filter {R : Type*} [CommMonoid R] {n : ℕ} (g : Fin n → R) (T : Finset (Fin n)) :
    ∀ l : List (Fin n),
      ((l.filter (· ∈ T)).map g).prod = (l.map fun j => g j ^ (if j ∈ T then 1 else 0)).prod
  | [] => rfl
  | j :: l => by
    by_cases hj : j ∈ T <;> simp [hj, prod_map_filter g T l]

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = ∏ j, (L j).sub I ^ (if j ∈ T then 1 else 0) := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [tensorSub, foldl_twist_sub, h0, one_mul, prod_map_filter, Fin.prod_univ_def]

theorem twistPows_snoc_sub {n : ℕ} (L : Fin n → LineBundle k x) (M : LineBundle k x) (T : Finset (Fin n))
    (m : ℕ) (I : Chart x) :
    ((twistSys k x 0).twistPows (n + 1)
        (fun j => (Fin.snoc (α := fun _ => LineBundle k x) L M j).toSubSystem)
        (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m)).sub I =
      M.sub I ^ m * (tensorSub (fun i => (L i).toSubSystem) T).sub I := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [SnapperSections.twistPows_sub, tensorSub_sub, h0, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

end MixedTwistShiftAlt


open MixedTwistShiftAlt in
theorem MixedTwistShift.proof (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) (hR : RestrLenEuler.Statement.{u, w}) (hD : SubsetDiffConst.Statement) :
    MixedTwistShift.Statement.{u, w} := by
  intro k _ Ω _ _ N x n qq hp hh hle hdim L M d
  set L' : Fin (n + 1) → LineBundle k x := Fin.snoc (α := fun _ => LineBundle k x) L M with hL'
  set ν : Finset (Fin n) → ℕ → Fin (n + 1) → ℕ :=
    fun T m => Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m with hν
  set f : (Fin (n + 1) → ℕ) → ℤ → ℚ := fun e c => (pieceChar k qq 0 L' e c : ℚ) with hf
  set Ls : Fin n → SubSystem k x Ω := fun i => (L i).toSubSystem with hLs

  have hA : ∀ T (c : ℤ), ((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 1)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, SubSystem.twist_sub_eq_mul_of_line, pow_one]
  have hB : ∀ T (c : ℤ), (tensorSub Ls T).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 0)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, pow_zero, one_mul]

  have hev : ∀ m : ℕ, ∀ᶠ c : ℤ in atTop, ∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c :=
    fun m => eventually_all.2 fun T => hR k Ω N x qq hh hle (n + 1) L' (ν T m)
  have hsum : ∀ (m : ℕ) (c : ℤ), (∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c) →
      ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
          (twistSys k x c)) : ℤ) : ℚ) = subsetDiff n f m c := by
    intro m c h
    rw [subsetDiff]
    push_cast
    exact Finset.sum_congr rfl fun T _ => by rw [h T]
  obtain ⟨hconst, hzero⟩ := hD n f (pieceChar_isNumPolyLT hH hS hP L' (n + 1) qq hp hh hle hdim 0)
  have hT1 : Tendsto (fun c : ℕ => (c : ℤ) + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d tendsto_natCast_atTop_atTop
  have hLhs : ∀ᶠ c : ℕ in atTop, ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
      restrLen qq (((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x ((c : ℤ) + d))) : ℤ) : ℚ) =
        subsetDiff n f 1 ((c : ℤ) + d) := by
    filter_upwards [hT1.eventually (hev 1)] with c hc
    simp only [hA]
    exact hsum 1 _ hc
  split_ifs with hW
  ·
    have hI : ∀ᶠ c : ℕ in atTop, (interSum qq Ls c : ℚ) = subsetDiff n f 0 (c : ℤ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (hev 0)] with c hc
      rw [interSum]
      simp only [hB]
      exact hsum 0 _ hc
    obtain ⟨c₀, hc₀⟩ := hI.exists_forall_of_atTop
    have hκ : ∀ᶠ c : ℕ in atTop, interSum qq Ls c = interSum qq Ls c₀ := by
      filter_upwards [eventually_ge_atTop c₀] with c hc
      exact_mod_cast (hc₀ c hc).trans ((hconst 0 0 c c₀).trans (hc₀ c₀ le_rfl).symm)
    have hlim : interNum qq Ls = interSum qq Ls c₀ :=
      (tendsto_const_nhds.congr' (hκ.mono fun _ hc => hc.symm)).limUnder_eq
    rw [hlim]
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans ((hconst 1 0 _ c₀).trans (hc₀ c₀ le_rfl).symm)
  ·
    have hlow : IsNumPolyLT (n + 1) n f := by
      by_cases hrel : ∃ i, (X i : Poly k N) ∉ qq
      · have := hp
        obtain ⟨e, he⟩ := SnapperSections.exists_dim_eq qq hh hrel
        have hen : e ≠ n := fun h => hW ⟨hp, hh, hle, hrel, by subst h; exact he⟩
        have hle' : e + 1 ≤ n + 1 := by
          rw [he] at hdim
          exact_mod_cast hdim
        refine pieceChar_isNumPolyLT hH hS hP L' n qq hp hh hle ?_ 0
        rw [he]
        exact_mod_cast (by omega : e + 1 ≤ n)
      · push Not at hrel
        exact ⟨0, Or.inl rfl, fun e c => by simp [hf, pieceChar_of_irrelevant qq hrel]⟩
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans (hzero hlow 1 _)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramAtLocalLog
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.SplitModelToPlaceModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ} {y : (Σ k, ι k) → Ω}
  {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}

namespace HermMetric

section ToTwin

variable {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}


open Classical in
def gramMatrixInFamily (hA : HermMetric y W Xo χ) (z : (Σ k, ι k) → ℂ) (b : Fin N → E) :
    Matrix (Fin N) (Fin N) ℂ :=
  if hz : ∃ l, InFrameDomain y (hA.chart l) (hA.fr l) z then
    if hS : ∃ S : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S p q • hA.b hz.choose p then
      (HermMetricEq.valM y hS.choose z)ᴴ * hA.gram hz.choose z * HermMetricEq.valM y hS.choose z
    else 0
  else 0

theorem gramMatrix_change_of_frame (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo) {l : Fin hA.m} (hd : InFrameDomain y (hA.chart l) (hA.fr l) z)
    {b : Fin N → E} {S : Matrix (Fin N) (Fin N) Ω}
    (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z) (hb : ∀ q, b q = ∑ p, S p q • hA.b l p) :
    hA.gramMatrixInFamily z b = (HermMetricEq.valM y S z)ᴴ * hA.gram l z * HermMetricEq.valM y S z := by
  have hzP := hXo hz
  have hex : ∃ l, InFrameDomain y (hA.chart l) (hA.fr l) z := ⟨l, hd⟩
  have hd0 : InFrameDomain y (hA.chart hex.choose) (hA.fr hex.choose) z := hex.choose_spec
  obtain ⟨T, hT, hTe⟩ := HermMetricEq.exists_coeff (hA.isFrame hex.choose) hzP hd0
    (HermMetricEq.isFrameAt_of_isFrameOver (hA.isFrame l) hzP hd).1
  have hbT : ∀ q, b q = ∑ p, (T * S) p q • hA.b hex.choose p := by
    intro q
    rw [hb q]
    simp only [hTe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  have hS' : ∃ S' : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S' p q • hA.b hex.choose p :=
    ⟨T * S, hbT⟩
  have hchoose : hS'.choose = T * S := HermMetricEq.coeff_unique (hA.isFrame hex.choose).2.2.2.1
    fun q => (hS'.choose_spec q).symm.trans (hbT q)
  have hTS : HermMetricEq.valM y (T * S) z = HermMetricEq.valM y T z * HermMetricEq.valM y S z :=
    HermMetricEq.valM_eq hzP (HermMetricEq.isValueAt_mul (fun p q => (hT p q).isValueAt hzP)
      (fun p q => (hS p q).isValueAt hzP))
  have hcompat := hA.compat hex.choose l z hz hd0 hd T hTe (HermMetricEq.valM y T z)
    (fun p q => HermMetricEq.isValueAt_iff.2 ((hT p q).isValueAt hzP))
  rw [gramMatrixInFamily, dite_eq_left hex, dite_eq_left hS', hchoose, hTS, hcompat]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem contDiffAt_valAt {m : ℕ} {O : Set (Fin m → ℂ)} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ}
    (hO : IsOpen O) (hγ : AnalyticOnNhd ℂ γ O) (hU : ∀ w ∈ O, γ w ∈ mcPts (mCoordIdeal y))
    {w : Fin m → ℂ} (hw : w ∈ O) {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w')) w := by
  obtain ⟨v, d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  have hcoord : ∀ p, AnalyticAt ℂ (fun w' => γ w' p) w := fun p =>
    ((ContinuousLinearMap.proj p : ((Σ k, ι k) → ℂ) →L[ℂ] ℂ).analyticAt (γ w)).comp (hγ w hw)
  have hG := analyticAt_eval_comp (F := γ) hcoord g
  have hH := analyticAt_eval_comp (F := γ) hcoord h
  have hF : AnalyticAt ℂ (fun w' => eval (γ w') (map (Int.castRingHom ℂ) g) /
      eval (γ w') (map (Int.castRingHom ℂ) h)) w := hG.div hH hz
  have hev : (fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w')) =ᶠ[𝓝 w] fun w' =>
      eval (γ w') (map (Int.castRingHom ℂ) g) / eval (γ w') (map (Int.castRingHom ℂ) h) := by
    have h1 : ∀ᶠ w' in 𝓝 w, eval (γ w') (map (Int.castRingHom ℂ) h) ≠ 0 :=
      hH.continuousAt.eventually_ne hz
    filter_upwards [h1, hO.mem_nhds hw] with w' h1 h2
    exact IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq (hU w' h2)
      ⟨d, g, h, hg, hh, hy, hyg, h1, by rw [div_mul_cancel₀ _ h1]⟩
  exact (hF.contDiffAt.restrict_scalars ℝ).congr_of_eventuallyEq hev

end ToTwin

section OfTwin

end OfTwin

namespace Example

open Line

end Example

end HermMetric

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open scoped Matrix ComplexOrder

namespace MuFrameNormLocal

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_eq_complexPoint_reading {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z := by
  classical
  by_cases h : ∃ v, IsValueAt y s z v
  · obtain ⟨v, hv⟩ := h
    rw [LowerBoundFree.valAt_eq hz hv,
      IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq hz (HermMetricEq.isValueAt_iff.1 hv)]
  · have h' : ¬ IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := fun ⟨v, hv⟩ =>
      h ⟨v, HermMetricEq.isValueAt_iff.2 hv⟩
    rw [LowerBoundFree.valAt, dite_eq_right h, IndefiniteRowSideFullHecke.LowerBoundFree.valAt, dite_eq_right h']

theorem regularAt_of_isUnitOn {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {f u : Ω}
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hd : InFrameDomain y c f z)
    (hu : IsUnitOn y c f u) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y u z ∧ IndefiniteRowSideFullHecke.LowerBoundFree.valAt y u z ≠ 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, hv0⟩ := hd.2
    exact hv0 (isValueAt_unique hz hv
      (HermMetricEq.isValueAt_iff.2 IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_zero))
  have hfi := HermMetricEq.regularAt_inv hf0 hd.2
  have hloc : ∀ s : Ω, (∃ n : ℕ, f ^ n * s ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := by
    rintro s ⟨n, hn⟩
    have h1 := (HermMetricEq.regularAt_pow hfi n).mul
      (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hd.1 hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  have h1 := hloc u hu.2.1
  have h2 := hloc u⁻¹ hu.2.2
  refine ⟨h1, fun h0 => ?_⟩
  have hm := (h1.isValueAt hz).mul (h2.isValueAt hz)
  rw [mul_inv_cancel₀ hu.1, h0, zero_mul] at hm
  exact one_ne_zero (IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one hm)

end Values

section Gram

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ} {y : (Σ k, ι k) → Ω}
  {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}
  {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}

theorem gramAt_eq_of_frame (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo) {l : Fin hA.m}
    (hd : InFrameDomain y (hA.chart l) (hA.fr l) z) {b : Fin N → E}
    {S : Matrix (Fin N) (Fin N) Ω} (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z)
    (hb : ∀ q, b q = ∑ p, S p q • hA.b l p) :
    LowerBoundFree.gramAt hA b z = (HermMetricEq.valM y S z)ᴴ * hA.gram l z * HermMetricEq.valM y S z := by
  rw [← hA.gramMatrix_change_of_frame hXo hz hd hS hb]
  have hv : ∀ s : Ω, LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z :=
    fun s => valAt_eq_complexPoint_reading (hXo hz)
  unfold LowerBoundFree.gramAt HermMetric.gramMatrixInFamily HermMetricEq.valM
  simp only [hv]

end Gram

section LogBounds

variable {X : Type*} {F : Filter X} {Q : X → Prop} {L : X → ℝ}

end LogBounds

section Local

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

end Local

end MuFrameNormLocal

end GroundTheory.Heights₂.Heights.NineStatements
end
end

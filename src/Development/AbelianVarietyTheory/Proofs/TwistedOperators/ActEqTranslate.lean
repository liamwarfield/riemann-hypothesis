module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormAction

theorem exists_rangeRestrict_eq {G H : Type} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : ∀ g, ∃ a ∈ f.ker, ∃ k ∈ K, g = a * k) (x : f.range) : ∃ k ∈ K, f.rangeRestrict k = x := by
  obtain ⟨_, g, rfl⟩ := x
  obtain ⟨a, ha, k, hk, rfl⟩ := h g
  refine ⟨k, hk, Subtype.ext ?_⟩
  show f k = f (a * k)
  rw [map_mul, MonoidHom.mem_ker.1 ha, one_mul]

theorem exists_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : ∃ κ, (finHom V).rangeRestrict κ = q.1 ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) q.1.1)) κ ∧
      ((((levEnv V β L).ch q)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine (exists_rangeRestrict_eq (finHom V) (GfC V) (GlobalTheory.UnitarySplit.real_finite_split D V).1 q.1).imp fun k hk => ?_
  have e0 : finHom V k = q.1.1 := congrArg Subtype.val hk.2
  have e1 : finE V k = Formalism.UG.bc (swapAE D) q.1.1 := (finE_eq V k).trans (congrArg (Formalism.UG.bc (swapAE D)) e0)
  have e2 : (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans e2.symm)
  have h1 : Formalism.UG.bc (swapAE D) q.1.1 ∈ lev D.sp.cm V.gram β (flagL L) := q.2
  have hp : finE V k ∈ parLev D.sp.cm V.gram β L := e1.symm ▸ h1.1
  exact ⟨hk.2, ⟨hk.1, hp, congrArg (rTup β L) e1⟩, (Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm)⟩

theorem act_eq_translate : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_red_R → R.models_jX → ∀ t (g : G) (x : (A.fam.R t).S.Forms), ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ h, (R.HX t).e (R.jX t ((A.fam.R t).r g x)) h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e (R.jX t x) (h * (finHom _).rangeRestrict κ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hred hj t g x
  refine ((R.B.R t).act_tie.red_surj g).elim fun q hq => ?_
  have hg : rTup R.βX (R.datXt t) (Formalism.UG.bc (swapAE D) q.1.1) = R.eG g := (hred t q).symm.trans (congrArg R.eG hq)
  have ha := (R.B.R t).act_tie.act_eq g q hq x
  refine (exists_lift D.sp.X' R.βX (R.datXt t) q).imp fun κ hκ => ⟨hg ▸ hκ.2.1, fun h => ?_⟩
  have e1 := congrFun (hj t ((A.fam.R t).r g x)) h
  have e2 := hj t x
  have e3 := congrFun ha h
  refine (e1.trans e3).trans ?_
  exact congrArg₂ (fun (a : ℂ) (z : R.cX.W) => a • z) hκ.2.2 ((congrFun e2 _).trans (congrArg (fun z => R.B.jR t x (h * z)) hκ.1)).symm

end GlobalTheory.FormAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistPlaces

theorem typePlaces_disjoint_twistPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  rw [Finset.disjoint_left]
  intro PP hPg hQ
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := R.C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = R.C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : PP.asIdeal.IsPrime := PP.isPrime
  haveI : Nontrivial (kP PP) := inferInstance
  haveI : Fintype (kP PP) := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hmemE
    simpa using this
  have h0q : ((q : ℕ) : kP PP) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP PP)
  have hd1 : ringChar (kP PP) ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP PP) ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP PP) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

end GlobalTheory.TwistPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disjoint_Pg_Q_of_core : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  first | exact @GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces | exact GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces | (intros; apply GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
open GlobalTheory.Doubling GlobalTheory.AdelicU

namespace GlobalTheory.Twist.OrthSum

variable {D : D7}

theorem pair_hsum (V W : HSp D) (x y : Fin (hsum V W).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (hsum V W).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * V.gram i j * y (finSumFinEquiv (Sum.inl j))) +
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * W.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hsum]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Doubling.blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

theorem selfDual_hsum {V W : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') :
    IsSelfDualC (hsum V W) (sumLat finSumFinEquiv L L') := by
  have hsumLat : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L') := by
    let φ : ((Fin V.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (V.rank + W.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L' =
        (L.prod L').map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL'.1.fg).map _)
  refine ⟨hsumLat, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL'.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ + b₂, ?_⟩
    rw [pair_hsum]
    push_cast
    linear_combination hb₁ + hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL'.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero] at hb
      exact ⟨b, hb⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add] at hb
      exact ⟨b, hb⟩

end GlobalTheory.Twist.OrthSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix
open scoped TensorProduct

namespace GlobalTheory.LocalThetaGL

section Abstract

variable {H V W U Y Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Y] [Module ℂ Y] {P : Subgroup H}

end Abstract

section Regular

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] {π : Representation ℂ G V}

end Regular

section Local

open GlobalTheory.IndefiniteRowSideFullHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem compact_open_basis (n : Type) [Fintype n] [DecidableEq n] : ∀ U ∈ nhds (1 : GL n k),
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end Local

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Main

section Final

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Final

end GlobalTheory.LocalThetaGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameExists

theorem exists_signFrame {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (hd : IsUnit H.det) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = H := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  let l := hH.eigenvalues
  let S : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => ((Real.sqrt |l a| : ℝ) : ℂ)
  have hs : H = U * diagonal (fun a => ((l a : ℝ) : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hS : Sᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * S = diagonal (fun a => ((l a : ℝ) : ℂ)) := by
    simp only [S, Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : ((Real.sqrt |l a| : ℝ) : ℂ) * ((Real.sqrt |l a| : ℝ) : ℂ) = ((|l a| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [mul_right_comm, h1]
    by_cases h : 0 < l a
    · simp [h, abs_of_pos h]
    · simp [h, abs_of_nonpos (not_lt.1 h)]
  have key : (S * Uᴴ)ᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * (S * Uᴴ) = H := by
    rw [hs, ← hS, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  refine ⟨_, S * Uᴴ, ?_, key⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [← key, det_mul] at hd
  exact isUnit_of_mul_isUnit_right hd

theorem exists_perm_of_card {n : ℕ} {ε η : Fin n → Bool}
    (h : Nat.card {a // ε a = true} = Nat.card {a // η a = true}) :
    ∃ σ : Fin n ≃ Fin n, ∀ a, ε (σ a) = η a := by
  have hf : ∀ b : Bool, Nonempty ({a // η a = b} ≃ {a // ε a = b}) := by
    intro b
    rw [← Finite.card_eq]
    cases b
    · have e : ∀ θ : Fin n → Bool, Nat.card {a // θ a = false} = n - Nat.card {a // θ a = true} := by
        intro θ
        have := Fintype.card_subtype_compl (fun a => θ a = true)
        simp only [Nat.card_eq_fintype_card]
        simpa using this
      rw [e, e, h]
    · exact h.symm
  exact ⟨Equiv.ofFiberEquiv fun b => (hf b).some, fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem exists_signCompat {n p q : ℕ} {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature (Pᴴ * Formalism.REAL.Jm ε * P) p q) :
    ∃ e : Fin p ⊕ Fin q ≃ Fin n, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e := by
  obtain ⟨e, Q, hQ⟩ := h
  have hc : Formalism.UG.cT (starRingEnd ℂ) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := rfl
  rw [hc] at hQ
  have h1 : (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e)ᴴ * Formalism.REAL.Jm ε *
      (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e) =
      Formalism.REAL.Jm fun a => (e a).isLeft := by
    have h2 := congrArg (fun M => Matrix.submatrix M e e) hQ
    simp only [← submatrix_mul_equiv _ _ _ e, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self,
      submatrix_id_id] at h2
    rw [conjTranspose_mul, conjTranspose_submatrix]
    simp only [Matrix.mul_assoc] at h2 ⊢
    rw [h2]
    ext a b
    obtain ⟨x, rfl⟩ := e.symm.surjective a
    obtain ⟨y, rfl⟩ := e.symm.surjective b
    simp only [submatrix_apply, Formalism.REAL.Jm, Formalism.UG.Jpq, diagonal_apply, Equiv.apply_symm_apply]
    rcases x with i | i <;> rcases y with j | j <;> simp [Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨σ, hσ⟩ := exists_perm_of_card (GlobalTheory.SignCount.card_true_eq _ h1)
  exact ⟨e.symm.trans σ, fun a => by simp [hσ]⟩

theorem frame_exists_signCompat : ∀ (D : D7) (V : HSp D), Nonempty (GlobalTheory.ChainFr.Fr V) ∧ ∀ (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) (p q : ℕ), Formalism.UG.HasSignature (gramAt D V τ) p q → ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (A.ε τ) e := by
  intro D V
  refine ⟨?_, fun A τ p q h => exists_signCompat (P := A.fr τ) (by rw [A.fr_gram]; exact h)⟩
  choose ε P h1 h2 using fun τ => exists_signFrame (H := gramAt D V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  exact ⟨⟨ε, P, h1, h2⟩⟩

end GlobalTheory.FrameExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSizeRWordNeTopOfLe
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} {N : ℕ}

private lemma rderC_sum_smul (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (M : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ (∑ a ∈ s, c a • M a) φ = ∑ a ∈ s, c a • RderC θ V τ (M a) φ := by
  induction s using Finset.induction_on with
  | empty =>

    have h0 := GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs τ (0 : ℂ) (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    rw [zero_smul, zero_smul] at h0
    rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.Mem.RealTranslate.RderC_add hθ hs,
      GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs, ih]

theorem RderC_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z φ = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ := by

  have hZ : Z = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • Matrix.single a.1 a.2 (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Fintype.sum_prod_type]

    rw [Fintype.sum_eq_single i fun x hx => by simp [hx], Fintype.sum_eq_single j fun y hy => by simp [hy]]
    simp
  conv_lhs => rw [hZ]
  rw [rderC_sum_smul hθ hs τ]
  simp only [glDer]

theorem Rder_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X φ = ∑ a : Fin V.rank × Fin V.rank, X a.1 a.2 • glDer θ V (τ, a) φ := by

  rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
  exact RderC_eq_sum_glDer hθ hs τ X


variable (θ V N) in
def wordFin (l : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | f ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l f) ≠ ∞}
  add_mem' h h' := ⟨add_mem h.1 h'.1, by
    rw [(linOnSm_glWord l).add _ h.1 _ h'.1]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2, h'.2⟩) growthSize_add_le⟩
  zero_mem' := ⟨zero_mem _, by
    have := (linOnSm_glWord (θ := θ) l).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top⟩
  smul_mem' c _ h := ⟨(SmFun θ V).smul_mem c h.1, by
    rw [(linOnSm_glWord l).smul, growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top h.2⟩

theorem rWord_mem_wordFin (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : IsLieWord V l) :
    ∀ l', l'.length + l.length ≤ d → rWord θ V l φ ∈ wordFin θ V N l' := by
  have hsum : wordSum (glDer θ V) (growthSize V N) d φ ≠ ∞ := h
  induction l with
  | nil =>

    intro l' hl'
    have hlen : l'.length ≤ d := by simpa using hl'
    have hw : rWord θ V [] φ = φ := wordAct_nil _ φ
    rw [hw]
    show φ ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l' φ) ≠ ∞
    exact ⟨hs, wordSum_ne_top_iff.1 hsum l' hlen⟩
  | cons p t ih =>

    intro l' hl'
    have hp : p.2 ∈ lieAt V p.1 := hl p (List.mem_cons_self ..)
    have ht : IsLieWord V t := fun q hq => hl q (List.mem_cons_of_mem p hq)
    have hψ : rWord θ V t φ ∈ SmFun θ V :=
      (show _ ∧ _ from ih ht [] (by simp only [List.length_cons, List.length_nil] at hl' ⊢; omega)).1
    have hw : rWord θ V (p :: t) φ = Rder θ V p.1 p.2 (rWord θ V t φ) := wordAct_cons _ p t φ
    rw [hw, Rder_eq_sum_glDer hθ hψ hp]
    refine sum_mem fun a _ => Submodule.smul_mem _ _ ?_
    have hm : growthSize V N (wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ)) ≠ ∞ :=
      (show _ ∧ _ from ih ht (l' ++ [(p.1, a)])
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hl' ⊢; omega)).2
    have he : wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ) =
        wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ)) := by
      rw [wordAct_append, wordAct_cons, wordAct_nil]
    show glDer θ V (p.1, a) (rWord θ V t φ) ∈ SmFun θ V ∧
      growthSize V N (wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ))) ≠ ∞
    rw [← he]
    exact ⟨(linOnSm_RderC p.1 _).mem _ hψ, hm⟩

theorem growthSize_rWord_ne_top_of_le (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) (hd : l.length ≤ d) :
    growthSize V N (rWord θ V l φ) ≠ ∞ := by
  have hm := rWord_mem_wordFin hθ hs h l hl [] (by simpa using hd)
  have h2 : growthSize V N (wordAct (glDer θ V) [] (rWord θ V l φ)) ≠ ∞ := (show _ ∧ _ from hm).2
  rwa [wordAct_nil] at h2

theorem growthSize_rWord_ne_top (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (h : ∀ d, growthSob θ V d N φ ≠ ∞) :
    ∀ l, IsLieWord V l → growthSize V N (rWord θ V l φ) ≠ ∞ := fun l hl =>
  growthSize_rWord_ne_top_of_le hθ hs (h l.length) hl le_rfl

theorem unifModGrowth_iff_growthSob (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) :
    UnifModGrowth V θ φ ↔ ∃ N, ∀ d, growthSob θ V d N φ ≠ ∞ := by
  refine ⟨exists_growthSob_ne_top hs, ?_⟩
  rintro ⟨M, hM⟩
  exact unifModGrowth_iff.2 ⟨M, growthSize_rWord_ne_top hθ hs hM⟩

end GlobalTheory.Size

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ}

theorem mt_emb_one (o : OrthDec S₀ A L) : mt S₀ (o.emb (1, 1)) = 1 := by
  rw [show ((1 : GA D A), (1 : GA D L)) = 1 from rfl, map_one, mt_one]

theorem mt_emb_mul (o : OrthDec S₀ A L) (h h' : GA D A) :
    mt S₀ (o.emb (h * h', 1)) = mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h', 1)) := by
  rw [← mt_mul, ← map_mul, Prod.mk_mul_mk, mul_one]

def Good (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A)) (g : GA D S) : Prop :=
  (∃ M : GL (Fin ρ) (AE D), mt S g * d.jX = d.jX * M.1) ∧
    ∃ h ∈ T, ∃ B : Mx D ρ S₀.rank, mt S g * d.j0 = d.j0 * mt S₀ (o.emb (h, 1)) + d.jX * B

section Good

variable (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A))

theorem good_one : Good d o T 1 :=
  ⟨⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩,
    1, T.one_mem, 0, by rw [mt_one, Matrix.one_mul, mt_emb_one, Matrix.mul_one, Matrix.mul_zero, add_zero]⟩

theorem good_mul {g g' : GA D S} (hg : Good d o T g) (hg' : Good d o T g') : Good d o T (g * g') := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  obtain ⟨⟨M', hM'⟩, h', hT', B', hB'⟩ := hg'
  refine ⟨⟨M * M', ?_⟩, h * h', T.mul_mem hT hT', B * mt S₀ (o.emb (h', 1)) + M.1 * B', ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, hM', ← Matrix.mul_assoc, hM, Matrix.mul_assoc, Units.val_mul]
  · rw [mt_mul, Matrix.mul_assoc, hB', Matrix.mul_add, ← Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hM, mt_emb_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]

theorem good_inv {g : GA D S} (hg : Good d o T g) : Good d o T g⁻¹ := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  have hI : mt S g⁻¹ * mt S g = 1 := mt_inv_mul S g
  have hMM : (M.1 : Mx D ρ ρ) * (M⁻¹).1 = 1 := M.mul_inv
  have hX : mt S g⁻¹ * d.jX = d.jX * (M⁻¹).1 := by
    calc mt S g⁻¹ * d.jX = mt S g⁻¹ * (d.jX * M.1) * (M⁻¹).1 := by
          rw [Matrix.mul_assoc (mt S g⁻¹), Matrix.mul_assoc d.jX, hMM, Matrix.mul_one]
      _ = d.jX * (M⁻¹).1 := by rw [← hM, ← Matrix.mul_assoc, hI, Matrix.one_mul]
  refine ⟨⟨M⁻¹, hX⟩, h⁻¹, T.inv_mem hT, -((M⁻¹).1 * B * mt S₀ (o.emb (h⁻¹, 1))), ?_⟩
  have hH : mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h⁻¹, 1)) = 1 := by
    rw [← mt_emb_mul, mul_inv_cancel, mt_emb_one]
  have h1 : mt S g⁻¹ * d.j0 * mt S₀ (o.emb (h, 1)) + d.jX * (M⁻¹).1 * B = d.j0 := by
    have h2 : mt S g⁻¹ * (mt S g * d.j0) = d.j0 := by rw [← Matrix.mul_assoc, hI, Matrix.one_mul]
    rw [hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX] at h2
    exact h2
  calc mt S g⁻¹ * d.j0 = mt S g⁻¹ * d.j0 * mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h⁻¹, 1)) := by
        rw [Matrix.mul_assoc _ (mt S₀ _), hH, Matrix.mul_one]
    _ = (d.j0 - d.jX * (M⁻¹).1 * B) * mt S₀ (o.emb (h⁻¹, 1)) := by rw [eq_sub_of_add_eq h1]
    _ = _ := by simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]

def goodSub : Subgroup (GA D S) where
  carrier := {g | Good d o T g}
  one_mem' := good_one d o T
  mul_mem' := fun {g g'} hg hg' => good_mul d o T (g := g) (g' := g') hg hg'
  inv_mem' := fun {g} hg => good_inv d o T (g := g) hg

end Good

end GlobalTheory.BesProj

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

theorem eH_gram_i₀ : d.eᴴ * S.gram * d.i₀ = 0 := by
  have := congrArg Matrix.conjTranspose d.i₀e
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at this

theorem flagN_le_goodSub (T : Subgroup (GA D A)) : flagN d ≤ goodSub d o T := by
  show Subgroup.closure _ ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨h1, h2⟩
  choose a ha1 ha2 using h1
  have hz : ∀ k : Fin S₀.rank, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * S.gram).mulVec
      (fun l => d.i₀ l k) = 0 := by
    intro k; funext j
    exact congrFun (congrFun (eH_gram_i₀ d) j) k
  choose b hb using fun k => h2 _ (hz k)
  let U : Mx D ρ ρ := Matrix.of fun j i => a i j
  let B : Mx D ρ S₀.rank := Matrix.of fun i k => b k i
  have hU : (mt S g - 1) * d.jX = d.jX * U := by
    ext k i
    exact congrFun (ha2 i) k
  have hB : (mt S g - 1) * d.j0 = d.jX * B := by
    ext k i
    exact congrFun (hb i) k
  have hdet : (1 + U).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [U, ha1 i i le_rfl]
    · intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      simp [U, ha1 j i hji.le, Matrix.one_apply_ne hij]
  have hdu : IsUnit (1 + U).det := by rw [hdet]; exact isUnit_one
  let M : GL (Fin ρ) (AE D) := ⟨1 + U, (1 + U)⁻¹, Matrix.mul_nonsing_inv _ hdu, Matrix.nonsing_inv_mul _ hdu⟩
  refine ⟨⟨M, ?_⟩, 1, T.one_mem, B, ?_⟩
  · show mt S g * d.jX = d.jX * (1 + U)
    rw [Matrix.mul_add, Matrix.mul_one, ← hU, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  · rw [mt_emb_one, Matrix.mul_one, ← hB, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

theorem embA_mem_goodSub (h : GA D A) : embA d o h ∈ goodSub d o ⊤ :=
  ⟨⟨1, by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩, h, Subgroup.mem_top h, 0,
    by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_zero, add_zero]⟩

theorem besGrp_le_goodSub : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) ≤ goodSub d o ⊤ :=
  sup_le (flagN_le_goodSub d o ⊤) (by rintro _ ⟨h, rfl⟩; exact embA_mem_goodSub d o h)

def matP (g : GA D S) : Mx D A.rank A.rank := o.pA * (d.p0 * mt S g * d.j0) * o.jA

theorem bessel_flag_stabilizer_anisotropic_block_exists {T : Subgroup (GA D A)} {g : GA D S} (hg : g ∈ goodSub d o T) :
    ∃ h ∈ T, d.p0 * mt S g * d.j0 = mt S₀ (o.emb (h, 1)) := by
  obtain ⟨-, h, hT, B, hB⟩ := hg
  refine ⟨h, hT, ?_⟩
  rw [Matrix.mul_assoc, hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.one_mul,
    Matrix.zero_mul, add_zero]

theorem pA_emb_jA (h : GA D A) : o.pA * mt S₀ (o.emb (h, 1)) * o.jA = mt A h := by
  rw [Matrix.mul_assoc, o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]

theorem anisotropicBlock_unitary {g : GA D S} (hg : g ∈ (flagN d ⊔ (embA d o).range : Subgroup (GA D S))) :
    adj (matP d o g) * (gA A * matP d o g) = gA A := by
  obtain ⟨h, -, hh⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (besGrp_le_goodSub d o hg)
  rw [matP, hh, pA_emb_jA]
  exact mt_unitary A h

theorem anisotropicBlock_mul_embA (n : flagN d) (h : GA D A) : matP d o (n.1 * embA d o h) = mt A h := by
  obtain ⟨h', hh', hn⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (flagN_le_goodSub d o ⊥ n.2)
  rw [Subgroup.mem_bot] at hh'
  rw [hh', mt_emb_one] at hn
  have : d.p0 * mt S (n.1 * embA d o h) * d.j0 = mt S₀ (o.emb (h, 1)) := by
    rw [mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hn,
      Matrix.one_mul]
  rw [matP, this, pA_emb_jA]

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    ∃ p : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) → GA D A, Continuous p ∧
      ∀ (h : GA D A) (n : flagN d), p ⟨n.1 * embA d o h, mul_mem (Subgroup.mem_sup_left n.2)
        (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ A L ρ d o
  refine ⟨fun g => ofMat A (matP d o g.1) (anisotropicBlock_unitary d o g.2), ?_, fun h n => ?_⟩
  · refine continuous_of_mt A ?_
    show Continuous fun g : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) => matP d o g.1
    exact (continuous_const.matrix_mul ((continuous_const.matrix_mul ((continuous_mt S).comp continuous_subtype_val)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  · exact mt_injective A (by rw [mt_ofMat]; exact anisotropicBlock_mul_embA d o n h)

end GlobalTheory.BesProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace ClassSumTranslate

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)

theorem card_stab (γ : Γ) (y : G) (k : J) :
    Nat.card (Bridge.stab ι J (ι γ * y * k)) = Nat.card (Bridge.stab ι J y) := by
  refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun δ => ?_)
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (ι γ * y * k)⁻¹ * ι δ * (ι γ * y * k) =
      (k : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * k := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInnerIndep : Bridge.AdInnerIndep ι ρ J χ := by
  intro hρ hχ I I' _ _ y y' hy hy' F hF F' hF'
  choose σ hσ using fun i => (hy' (y i)).exists
  have hinj : Function.Injective σ := by
    intro i j hij
    obtain ⟨γ, k, h1⟩ := hσ i
    obtain ⟨γ', k', h2⟩ := hσ j
    refine (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨γ * γ'⁻¹, k'⁻¹ * k, ?_⟩
    rw [h1, h2, hij]; simp [mul_assoc]
  have hsurj : Function.Surjective σ := by
    intro j
    obtain ⟨i, γ, k, h1⟩ := (hy (y' j)).exists
    obtain ⟨γ', k', h2⟩ := hσ i
    refine ⟨i, (hy' (y' j)).unique ⟨γ * γ', k' * k, ?_⟩ ⟨1, 1, by simp⟩⟩
    rw [h1, h2]; simp [mul_assoc]
  unfold Bridge.adInner
  refine Fintype.sum_bijective σ ⟨hinj, hsurj⟩ _ _ fun i => ?_
  obtain ⟨γ, k, h⟩ := hσ i
  rw [h, card_stab, hF γ _ k, hF' γ _ k, inner_smul_left, inner_smul_right, hρ, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ]
  simp

variable {J} in
theorem stab_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) (y : G) :
    Bridge.stab ι J (y * κ) = Bridge.stab ι J y := by
  ext δ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← hκ (y⁻¹ * ι δ * y)]
  simp [mul_assoc]

variable {J} in
theorem isReps_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) {I : Type} {y : I → G}
    (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * κ := by
  intro h
  refine (existsUnique_congr fun i => ?_).1 (hy (h * κ⁻¹))
  constructor
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨_, (hκ k).2 k.2⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at e
    rw [e]; simp [mul_assoc]
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨κ * k * κ⁻¹, (hκ _).1 (by simpa [mul_assoc] using k.2)⟩, ?_⟩
    rw [e]; simp [mul_assoc]

theorem translate (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (κ : l.Q) {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) :
    (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) ∈ Bridge.AdForms ι ρ l.J l.χ ∧
      Bridge.adInner ι l.J y (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ))
        (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) = Bridge.adInner ι l.J y F F := by
  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := fun k =>
    ⟨fun h => by simpa [mul_assoc] using hn _ (l.Q.inv_mem κ.2) _ h, hn _ κ.2 _⟩
  constructor
  · intro γ h k
    have e := hF γ (h * κ) ⟨_, (hκ k).2 k.2⟩
    have e2 : l.χ ⟨_, (hκ k).2 k.2⟩ = l.χ k := by
      rw [← l.ch_J, ← l.ch_J]
      have : (⟨(κ : G)⁻¹ * k * κ, l.J_le ((hκ k).2 k.2)⟩ : l.Q) = κ⁻¹ * ⟨k, l.J_le k.2⟩ * κ := rfl
      simp only
      rw [this, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    rw [e2] at e
    simp only
    rw [map_smul, smul_comm, ← e]
    simp [mul_assoc]
  · rw [adInnerIndep ι ρ l.J l.χ hρ (fun k => by rw [← l.ch_J]; exact hch _) I I y _ hy
      (isReps_mul ι hκ hy) F hF F hF]
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stab_mul ι hκ, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
      Complex.conj_mul', norm_inv, hch]
    simp

theorem translate_model (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (M : Links.HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ l.J l.χ) (Bridge.adInner ι l.J y)) (κ : l.Q) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖ := by
  have hx : M.e x ∈ Bridge.AdForms ι ρ l.J l.χ := by
    rw [← hM.2.1]; exact ⟨x, rfl⟩
  obtain ⟨h1, h2⟩ := translate ι ρ l hρ hn hch hy κ hx
  rw [← hM.2.1] at h1
  obtain ⟨x', hx'⟩ := h1
  refine ⟨x', fun h => congrFun hx' h, ?_⟩
  have h3 : inner ℂ x' x' = inner ℂ x x := by
    rw [hM.2.2, hM.2.2, hx']; exact h2
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h3]

end Generic

theorem norm_char {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) (x : M) : ‖(c x : ℂ)‖ = 1 := by
  have h : IsOfFinOrder (((Units.coeHom ℂ).comp c) x) := MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite x)
  exact h.norm_eq_one

variable {D : D7}

theorem norm_levFn (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) x) = 1 := subgroupCharExtension_one_apply _ _
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => by
    first | infer_instance | exact Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  unfold levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_char _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_char _ _

theorem lev_conj (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {q k : GL (Fin V.rank) (Lev.EAf D)} (hq : q ∈ lev D.sp.cm V.gram β (flagL L))
    (hk : k ∈ lev D.sp.cm V.gram β (flag1L L)) : q⁻¹ * k * q ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have hq' : q ∈ parLev D.sp.cm V.gram β L := hq.1
  have hk' : k ∈ parLev D.sp.cm V.gram β L := hk.1
  have hk2 : rTup β L k ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2
  have h1 : q⁻¹ * k * q ∈ parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq'
  have h2 : rTup β L (q⁻¹ * k * q) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := by
    rw [Subgroup.mem_bot] at hk2 ⊢
    rw [rTup_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq', rTup_mul (Subgroup.inv_mem _ hq') hk',
      rTup_inv hq', hk2, mul_one, inv_mul_cancel]
  exact ⟨h1, h2⟩

theorem comap_conj {G H : Type} [Group G] [Group H] (f : G →* H) {Q J : Subgroup H}
    (h : ∀ q ∈ Q, ∀ k ∈ J, q⁻¹ * k * q ∈ J) : ∀ q ∈ Q.comap f, ∀ k ∈ J.comap f, q⁻¹ * k * q ∈ J.comap f := by
  intro q hq k hk
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact h _ hq _ hk

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ q ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, q⁻¹ * k * q ∈ (levEnv V β L).J :=
  comap_conj (finHom V).range.subtype (comap_conj (Formalism.UG.bc (swapAE D)) fun _ hq _ hk => lev_conj V β L hq hk)

theorem model (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (levEnv_normal V β L) (fun q => norm_levFn V β L _) hy M hM ⟨_, hq⟩ x

end ClassSumTranslate

theorem translate_unitary_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HV → R.models_cV → ∀ i t g0 κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∀ y : (R.HV i t).H, ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) ∧ ‖y'‖ = ‖y‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hH hc i t g0 κ hκ y
  exact ClassSumTranslate.model _ _ _ _ (hc i) _ _ (R.B.L i t).pres.reps (hH i t) g0 κ hκ y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem phiC_zero_rule {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) : phiC T hV a (0 : T.R j) = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  unfold CoreJ.phiJ
  rw [map_zero, map_zero, smul_zero]


set_option linter.unusedVariables false in
theorem evaluates_of_unif : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀), R.LUnif → fw.Evaluates := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hU i σ hσ hV f
    by_cases hj : ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H,
        ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
          ((R.HW i σ).e (j' ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
            hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))
    · exact fw.ev i σ hσ hV hj f
    · exfalso
      have hz : (R.FW i).j σ = 0 := fw.ev0 i σ hσ hV hj

      have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := by
        intro x
        by_contra hne
        have hli := (hU i σ).1 1 (fun _ => x) (linearIndependent_unique_iff.mpr hne)
        simp only [hz, LinearMap.zero_apply] at hli
        exact hli.ne_zero 0 rfl

      apply hj
      refine ⟨0, fun f' => ?_⟩
      have hf' : f' = 0 := by
        simpa using hx ((fw.e i f' : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
      subst hf'
      simp
      exact (phiC_zero_rule T hV (wtA (κ i))).symm

end GlobalTheory
end

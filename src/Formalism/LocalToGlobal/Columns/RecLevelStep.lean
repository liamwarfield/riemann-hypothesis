module

public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
public import Formalism.LocalToGlobal.Columns.TiedCG
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.RecLevelStep
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG : Finset (Pl E)} (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))
  {π : 𝓞 E} {T f : ℕ}

def stepOf (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) →* ℂˣ) :
    Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f (plUnder F SG) where
  Lb := baseLb E n ST
  Lb_fin := baseLb_fin n ST
  Lb_span := baseLb_span n ST
  Lb_int := baseLb_int hc n ST
  Lb_dual := baseLb_dual hc n ST (fun P hP => (hST P).1 hP) hTπ
  Lb_index := hidx
  Uloc := levLoc hc n ST SG (Subgroup.pi Set.univ Hw)
  Uloc_le := levLoc_le hc n ST SG _
  Uloc_lev := levLoc_le_levelVL hc n ST SG _
  Uloc_hyp v hv hT := levLoc_eq_levelVL hc n ST SG _ v
    (fun h => hT ((mem_plUnder_iff_norm hc hST T hTπ v).1 h)) hv
  fM v _ := fMod hc n ST v
  fT v _ := fLoc hc n ST v
  fT_ne v h := fLoc_ne hc n v hB ((mem_plUnder_iff_norm hc hST T hTπ v).2 h)
  fT_T v _ x := fLoc_natCast_smul_eq_zero_of_dvd hc n v hB T ⟨cO E π, hTπ.symm⟩ x
  fM_card v h := by
    obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc hST T hTπ v).2 h
    rw [fMod_card hc n v hB hP hov (hB.over_unique hc hP hov), hcard P hP]
  fT_L v _ x hx := fLoc_L hc n v x hx
  UlocAlt v h := levLoc_eq_stabFun hc n SG _ v hB (hSG v h)
  U := levU hc n ST SG (Subgroup.pi Set.univ Hw)
  U_eq x := levU_eq_prod hc n ST SG Hw x
  U_compact := levU_compact hc n ST SG _
  U_open := levU_open hc n ST SG _
  chi := levTyp lam
  chi_triv x h := levTyp_eq_one hc n ST SG _ lam x h

end Gen

section Col

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem rls_T_notUnder (hPr : Pr.Ok) (u : Pr.Word) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal) :
    v ∉ plUnder X.F Pr.vGs := by
  rintro ⟨w, hw, hov⟩
  apply T_notMem_vGs hPr u ⟨w, hw⟩
  have : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ h
  rwa [Ideal.mem_comap, map_natCast] at this

theorem rls_vT_iff (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (P : Pl X.E) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal :=
  mem_divs (basePi_of_ok hX hPr u).ne_zero P

end Col

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.NonDeg
open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host

section TBig

variable {X : Fields} {Pr : Primes X}

end TBig

section Gen

open GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end Gen

section ColsRam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColsRam

section Delta

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end Delta

section ColsUD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColsUD

section SeenEx

variable {X : Fields} {Pr : Primes X}

end SeenEx

section Pos

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def GSD.pairEmb (σ : K →+* ℂ) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

theorem GSD.map_pair (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) :
    σ (S.pair x y) = S.pairEmb σ x y := by
  conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, map_mul, hσ, GSD.pairEmb, GSD.gramV, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def GSD.ipEmb (h : S.Ok) (σ : K →+* ℂ) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairEmb σ (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

theorem GSD.ipAt_eq_ipEmb (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) :
    S.ipAt h v φ ψ = S.ipEmb h v.embedding φ ψ := rfl

theorem GSD.map_ip (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (φ ψ : S.D → S.V) :
    σ (S.ip h φ ψ) = S.ipEmb h σ φ ψ := by
  let _ : Fintype S.Cl := h.fintypeCl
  unfold GSD.ip GSD.ipOf GSD.ipEmb CSD.csum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  congr 1
  exact S.map_pair σ hσ _ _

end Pos

section ColPos

open ComplexOrder

variable {X : Fields}

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColPos

section LatGen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end LatGen

section ColLat

variable {X : Fields}

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColLat

section Cert

end Cert

section GaussInst

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end GaussInst

def ndIota : Qb →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb)).toRingHom

section OfSizes

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end OfSizes

section InstThms

open ComplexOrder

end InstThms

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.BrzColLatOneLattice
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
  (b : Basis ι K V) (P : V →ₗ⋆[K] V →ₗ[K] K)

theorem isSesq_formAt : IsSesq (formAt b P) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [formAt, map_add (f := _), Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  · simp only [formAt, map_add (f := _), Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem gramOf_formAt [DecidableEq ι] (v : InfinitePlace K) :
    gramOf b (formAt b P v) = Matrix.of fun i j => v.embedding (P (b i) (b j)) := by
  ext i j
  simp only [gramOf, Matrix.of_apply, formAt, Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i' _ hi
    simp [Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem posAt_formAt [DecidableEq ι] (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef) :
    PosAt b (formAt b P) := fun v => by rw [gramOf_formAt]; exact hpos v

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [DecidableEq ι]

theorem formH_spec (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef)
    (L : Submodule (𝓞 K) V) :
    FrameOK (ofFormB b L (formAt b P)) ∧
    (∀ v (x y : V), Formalism.HermitianLatticesTheory.majAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x y = formAt b P v x y) ∧
    (∀ v (x : V), Formalism.HermitianLatticesTheory.normAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x =
      Real.sqrt (formAt b P v x x).re) :=
  of_form_spec K V ι b L (formAt b P) (isSesq_formAt b P) (posAt_formAt b P hpos)

end Forms

theorem isLattice_ne_bot {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Nontrivial V] {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) : L ≠ ⊥ := by
  intro h
  letI := hL
  have h2 := Submodule.IsFullLattice.span_eq_top (A := K) (M := L)
  rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at h2
  exact bot_ne_top h2

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end Val

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

theorem brz_colLat_one_lattice : Submodule.IsLattice K (colLat (1 : GL (Fin n) K)) := by
  have e : colLat (1 : GL (Fin n) K) = stdLat K n := by
    ext x
    rw [lc_mem_colLat_one]
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact stdLat_lattice

end Std

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TiedCB
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)


end Formalism.L2.Col.CF

end
end

section -- merged from Formalism.LocalToGlobal.Columns.RowFormsRat
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Mat

variable {K : Type} [Field K]

theorem rf_inv_entries_mem (K0 : Subfield K) {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (hA : ∀ i j, A i j ∈ K0) (i j : Fin d) :
    A⁻¹ i j ∈ K0 := by
  let A0 : Matrix (Fin d) (Fin d) K0 := fun i j => ⟨A i j, hA i j⟩
  have e : A = A0.map K0.subtype := rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', e, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← RingHom.map_adjugate]
  exact mul_mem (inv_mem (A0.det).2) ((A0.adjugate i j).2)

end Mat

namespace CSDRat

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem pair_mem (R : S.Rat) (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (hy : ∀ i, S.bV.repr y i ∈ cmMax K) :
    S.pair x y ∈ cmMax K := by
  rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply]
  refine sum_mem fun j _ => mul_mem (hy j) (sum_mem fun i _ => ?_)
  exact mul_mem (Formalism.L2.DIV.star_mem_cmMax (hx i)) (R.pair_rat i j)

theorem csum_mem (R : S.Rat) (f g : S.Cl → S.V) (hf : S.IsRat f) (hg : S.IsRat g) : S.csum f g ∈ cmMax K := by
  unfold CSD.csum
  exact sum_mem fun c _ => mul_mem (inv_mem (natCast_mem _ _)) (pair_mem S R _ _ (hf c) (hg c))

theorem H_mem (R : S.Rat) (hb : S.HasRatBasis) (i j : Fin S.dim) : S.H i j ∈ cmMax K :=
  csum_mem S R _ _ (S.basis_rat hb i) (S.basis_rat hb j)

theorem csum_basis (i : Fin S.dim) (x : Fin S.dim → K) :
    S.csum (S.basis i : S.Cl → S.V) (S.I x) = (S.H *ᵥ x) i := by
  have h := S.csum_sum (Pi.single i 1) x
  have e : S.I (Pi.single i 1) = (S.basis i : S.Cl → S.V) := by
    rw [S.I_eq_sum, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e, Finset.sum_eq_single i] at h
  · rw [h]
    simp [Matrix.mulVec, dotProduct]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem repr_mem (R : S.Rat) (hb : S.HasRatBasis) (hdet : S.H.det ≠ 0) (f : S.Forms) (hf : S.IsRat (f : S.Cl → S.V))
    (i : Fin S.dim) : S.basis.repr f i ∈ cmMax K := by
  set x : Fin S.dim → K := S.basis.equivFun f with hx
  have hI : S.I x = (f : S.Cl → S.V) := by
    rw [S.I_apply, hx, LinearEquiv.symm_apply_apply]
  have h1 : S.H *ᵥ x = fun i => S.csum (S.basis i : S.Cl → S.V) (f : S.Cl → S.V) := by
    funext i
    rw [← csum_basis, hI]
  have h2 : x = S.H⁻¹ *ᵥ fun i => S.csum (S.basis i : S.Cl → S.V) (f : S.Cl → S.V) := by
    rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  show x i ∈ cmMax K
  rw [h2]
  show ∑ j, S.H⁻¹ i j * S.csum (S.basis j : S.Cl → S.V) (f : S.Cl → S.V) ∈ cmMax K
  exact sum_mem fun j _ => mul_mem (rf_inv_entries_mem _ _ (H_mem S R hb) i j) (csum_mem S R _ _ (S.basis_rat hb j) hf)

theorem actRat_of (R : S.Rat) (hb : S.HasRatBasis) (hdet : S.H.det ≠ 0) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms)
    (hr : ∀ (t : G) (f : S.Forms), S.IsRat (f : S.Cl → S.V) → S.IsRat (r t f : S.Cl → S.V)) : S.ActRat r := by
  intro t i j
  unfold CSD.actMat
  rw [LinearMap.toMatrix_apply]
  exact repr_mem S R hb hdet _ (hr t _ (S.basis_rat hb j)) i

end CSDRat

section GSDRat

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem GSD.rho_mem (R : S.Rat) (g : S.G) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    S.bV.repr (S.ρ g x) i ∈ cmMax K := by
  have e : S.ρ g x = S.ρ g (∑ j, S.bV.repr x j • S.bV j) := by rw [S.bV.sum_repr x]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hx j) (R.act_rat g i j)

theorem GSD.det_H_ne_zero (R : S.Rat) (h : S.Ok) : (S.toCSD h).H.det ≠ 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hp := (R.posH h v).det_pos
  intro h0
  have e : ((S.toCSD h).H.map v.embedding).det = v.embedding (S.toCSD h).H.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hp' : 0 < ((S.toCSD h).H.map v.embedding).det := hp
  rw [e, h0, map_zero] at hp'
  exact lt_irrefl _ hp'

theorem GSD.repCSD_actRat (h : S.Ok) (R : S.Rat) {A : Type} [Group A] [Fintype A] (r : Representation K A S.EqFun)
    (hr : ∀ (a : A) (φ : S.EqFun) (d : S.D), ∃ d' : S.D, (r a φ : S.D → S.V) d = (φ : S.D → S.V) d') :
    (S.toCSD h).ActRat (S.repCSD h r) := by
  refine CSDRat.actRat_of _ (S.toCSDOf_rat h R _) (csd_hasRatBasis _ (S.toCSDOf_rat h R _)) (S.det_H_ne_zero R h) _ ?_
  intro t f hf c i
  obtain ⟨d', hd'⟩ := hr t ((S.res h).symm f) (S.outSec.rep c)
  show S.bV.repr ((r t ((S.res h).symm f) : S.D → S.V) (S.outSec.rep c)) i ∈ cmMax K
  rw [hd']
  show S.bV.repr (S.ρ (S.outSec.mv d') ((f.1 : S.Cl → S.V) (S.cls d'))) i ∈ cmMax K
  exact S.rho_mem R _ _ (hf _) i

end GSDRat

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem unipotentActionForms_rational (hX : X.Ok) (h : (mtildeKGSD W Ch sel mu).Ok) :
    (MtildeKCSD W Ch sel mu h).ActRat (g0Act W Ch sel mu h) :=
  GSD.repCSD_actRat _ h (mtildeK_rat W Ch sel mu hX) _ fun _ _ _ => ⟨_, rfl⟩

theorem unipotentActionClassSum_rational (hX : X.Ok) (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) :
    (MtKCSD W Ch sel mu j h).ActRat (unipotentRightActionOnForms W Ch sel mu j h) :=
  GSD.repCSD_actRat _ h (mtK_rat W Ch sel mu hX j) _ fun _ _ _ => ⟨_, rfl⟩

end Rows

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.DGamAut
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.Col

section One

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def autLcm : ℕ := sInf {D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D}

variable {E n}

theorem autLcm_mem {D : ℕ} (hD : 0 < D) (h : ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D) :
    0 < autLcm E n ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ autLcm E n := by
  have hne : ({D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D} : Set ℕ).Nonempty := ⟨D, hD, h⟩
  exact Nat.sInf_mem hne

theorem autLcm_dvd {D : ℕ} (hD : 0 < D) (h : ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D) : autLcm E n ∣ D := by
  obtain ⟨hpos, hdvd⟩ := autLcm_mem hD h
  have hg : 0 < Nat.gcd (autLcm E n) D := Nat.gcd_pos_of_pos_left _ hpos
  have hmem : Nat.gcd (autLcm E n) D ∈ {D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D} :=
    ⟨hg, fun N => Nat.dvd_gcd (hdvd N) (h N)⟩
  have hle : autLcm E n ≤ Nat.gcd (autLcm E n) D := Nat.sInf_le hmem
  have hge : Nat.gcd (autLcm E n) D ≤ autLcm E n := Nat.le_of_dvd hpos (Nat.gcd_dvd_left _ _)
  have heq : Nat.gcd (autLcm E n) D = autLcm E n := le_antisymm hge hle
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

theorem card_autU_dvd_minkM (hE : PosStar E) (N : UniLat E n) :
    Nat.card (autU E n N) ∣ minkM (Module.finrank ℚ E * n) := by
  let φ : autU E n N →* GL (Fin n) E := (ufGL E n).comp (autU E n N).subtype
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext ((toGLm E n).injective hab))
  have hfin : Finite (autU E n N) := finite_autU hE N
  have hfin' : Finite φ.range := Finite.of_equiv _ (MonoidHom.ofInjective hφ).toEquiv
  have hst : φ.range ≤ Formalism.UG.stabGL N.1 := by
    rintro _ ⟨a, rfl⟩ x
    have ha : gmap (a.1 : UF E n).1 N.1 = N.1 := congrArg Subtype.val a.2
    show x ∈ _ ↔ ((toGLm E n (a.1 : UF E n).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).mulVec x ∈ _
    rw [toGLm_mulVec]
    constructor
    · intro hx
      rw [← ha]
      exact Submodule.mem_map_of_mem hx
    · intro hx
      rw [← ha] at hx
      obtain ⟨y, hy, e⟩ := hx
      have : y = x := (a.1 : UF E n).1.injective e
      rwa [← this]
  have h1 := mk_card_dvd minkowskiBound_holds N.1 (hcnt_isFullLattice_of_unimodular N.2.1 N.2.2) φ.range hfin' hst
  rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h1
  exact h1

theorem autLcm_pos (hE : PosStar E) : 0 < autLcm E n := (autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).1

theorem card_autU_dvd_autLcm (hE : PosStar E) (N : UniLat E n) : Nat.card (autU E n N) ∣ autLcm E n := (autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).2 N

def UniLat.til (N : UniLat E n) : UniLat E (n + 1) := ⟨tilN N.1, tilN_lattice N.2.1, tilN_unimodular N.2.2⟩

def autU_til (N : UniLat E n) : autU E n N →* autU E (n + 1) N.til :=
  (extU.comp (autU E n N).subtype).codRestrict _ fun a => by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    show gmap (extE (a.1 : UF E n).1) (tilN N.1) = tilN N.1
    rw [← tilN_gmap]
    exact congrArg tilN (congrArg Subtype.val a.2)

theorem autU_til_injective (N : UniLat E n) : Function.Injective (autU_til N) := by
  intro a b hab
  have h1 : extE (a.1 : UF E n).1 = extE (b.1 : UF E n).1 :=
    congrArg (fun u : autU E (n + 1) N.til => (u.1 : UF E (n + 1)).1) hab
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, hy⟩ : ∃ y : Sp E (n + 1), initL E n y = x := by
    refine ⟨Fin.snoc (α := fun _ => E) x 0, ?_⟩
    change (fun i : Fin n => (Fin.snoc (α := fun _ => E) x 0 : Fin (n + 1) → E) (Fin.castSucc i)) = x
    funext i
    simp
  subst hy
  calc (a.1 : UF E n).1 (initL E n y) = initL E n (extE (a.1 : UF E n).1 y) := (initL_extE _ _).symm
    _ = initL E n (extE (b.1 : UF E n).1 y) := by rw [h1]
    _ = (b.1 : UF E n).1 (initL E n y) := initL_extE _ _

theorem autLcm_dvd_succ (hE : PosStar E) : autLcm E n ∣ autLcm E (n + 1) := autLcm_dvd (autLcm_pos (E := E) (n := n + 1) hE) fun N =>
    (Subgroup.card_dvd_of_injective (autU_til N) (autU_til_injective N)).trans (card_autU_dvd_autLcm hE N.til)

theorem autLcm_mono (hE : PosStar E) {n n' : ℕ} (h : n ≤ n') : autLcm E n ∣ autLcm E n' := by
  induction h with
  | refl => exact dvd_rfl
  | step _ ih => exact ih.trans (autLcm_dvd_succ hE)

end One

section DGam

def dGamRanks (R : Ranks) : Finset ℕ :=
  (Finset.Icc 1 R.m).image R.N ∪ {R.rankX', R.rankY (R.m - 1), R.nV}

def dGamAut (X : Fields) (R : Ranks) : ℕ := (dGamRanks R).lcm fun n => autLcm X.E n

variable {X : Fields} {R : Ranks}

theorem dga_N_mono (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  simp only [Ranks.N]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem dGamRanks_le (R : Ranks) {n : ℕ} (hn : n ∈ dGamRanks R) : n ≤ R.N R.m := by
  have hm := R.two_le_m
  have hX : R.rankX' ≤ R.N R.m := by
    simp only [Ranks.rankX', Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  have hY : R.rankY (R.m - 1) ≤ R.N R.m := by
    have h1 : (R.m - 1) * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    simp only [Ranks.rankY, Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  have hV : R.nV ≤ R.N R.m := by
    have h2 : 1 * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (by omega)
    simp only [Ranks.nV, Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  unfold dGamRanks at hn
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with ⟨j, ⟨_, hj⟩, rfl⟩ | rfl | rfl | rfl
  · exact dga_N_mono R hj
  · exact hX
  · exact hY
  · exact hV

theorem N_m_mem_dGamRanks (R : Ranks) : R.N R.m ∈ dGamRanks R := by
  have hm := R.two_le_m
  unfold dGamRanks
  apply Finset.mem_union_left
  exact Finset.mem_image.2 ⟨R.m, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, rfl⟩

theorem dGamAut_eq (hX : X.Ok) : dGamAut X R = autLcm X.E (R.N R.m) := by
  have hE := posStar_of_ok hX
  apply Nat.dvd_antisymm
  · exact Finset.lcm_dvd fun n hn => autLcm_mono hE (dGamRanks_le R hn)
  · exact Finset.dvd_lcm (N_m_mem_dGamRanks R)

theorem dGamAut_pos (hX : X.Ok) : 0 < dGamAut X R := by
  rw [dGamAut_eq hX]
  exact autLcm_pos (posStar_of_ok hX)

theorem autLcm_dvd_dGamAut (hX : X.Ok) {n : ℕ} (hn : n ≤ R.N R.m) : autLcm X.E n ∣ dGamAut X R := by
  rw [dGamAut_eq hX]
  exact autLcm_mono (posStar_of_ok hX) hn

theorem card_autU_dvd_dGamAut (hX : X.Ok) {n : ℕ} (hn : n ≤ R.N R.m) (N : UniLat X.E n) :
    Nat.card (autU X.E n N) ∣ dGamAut X R := (card_autU_dvd_autLcm (posStar_of_ok hX) N).trans (autLcm_dvd_dGamAut hX hn)

end DGam

section Stab

variable {X : Fields} {R : Ranks} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem formGSD_stab_dvd_autU (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    Nat.card (MulAction.stabilizer (formGSD C Λ).G d) ∣ Nat.card (autU X.E n d.lat) := by
  let φ : MulAction.stabilizer (formGSD C Λ).G d →* autU X.E n d.lat :=
    ((MonoidHom.fst (UF X.E n) ↥Λ.grp).comp (MulAction.stabilizer (formGSD C Λ).G d).subtype).codRestrict _ fun a => by
      rw [MulAction.mem_stabilizer_iff]
      exact congrArg DecoSet.lat a.2
  refine Subgroup.card_dvd_of_injective φ fun a b hab => ?_
  have h1 : (a.1.1 : UF X.E n) = b.1.1 := congrArg Subtype.val hab
  exact Subtype.ext (formGSD_stab_inj C Λ d a.2 b.2 h1)

theorem formGSD_stab_dvd_dGamAut (hX : X.Ok) (hn : n ≤ R.N R.m) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)
    (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : Nat.card (MulAction.stabilizer (formGSD C Λ).G d) ∣ dGamAut X R := (formGSD_stab_dvd_autU C Λ d).trans (card_autU_dvd_dGamAut hX hn _)

theorem dga_frm_stab_inj (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) {a b : FrmG Λ Θ}
    (ha : a • p = p) (hb : b • p = p) (hab : a.1 = b.1) : a = b := by
  have hda : ((a.1, (a.2.1 : GLG (E := X.E) (n := n) (SG := SG))) • p.deco : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) ha
  have hdb : ((b.1, (b.2.1 : GLG (E := X.E) (n := n) (SG := SG))) • p.deco : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) hb
  have h1 := DecoSet.stab_fst_injective p.deco hda hdb hab
  have h2 : (a.2.1 : GLG (E := X.E) (n := n) (SG := SG)) = b.2.1 := congrArg Prod.snd h1
  have h3 : ∀ P : Q, (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 := by
    intro P
    have ea : a.1.1 * p.fr P * (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) ha
    have eb : b.1.1 * p.fr P * (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) hb
    rw [← hab] at eb
    exact mul_left_cancel (ea.trans eb.symm)
  refine Prod.ext hab (Prod.ext (Subtype.ext h2) (Subtype.ext (funext fun P => ?_)))
  exact inv_injective (Subtype.ext (h3 P))

end Stab

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.FiniteDimensionalForms
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

abbrev outSec : ∀ b, (F.mem b).Sec := fun b => (F.mem b).outSec

abbrev rep (c : F.Cl) : F.D c.1 := (F.mem c.1).outSec.rep c.2

def res (h : F.Ok) : F.Forms ≃ₗ[K] (F.toCSD h).Forms := F.resOf h F.outSec

def gramV : Matrix F.ιV F.ιV K := Matrix.of fun i j => F.pair (F.bV i) (F.bV j)

structure Rat : Prop where
  pair_rat : ∀ i j, F.gramV i j ∈ cmMax K
  act_rat : ∀ (b : F.β) (g : F.G b) i j, F.bV.repr (F.ρ b g (F.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef

def Free : Prop := ∀ b, (F.mem b).Free

@[reducible] def toH (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : HLat K where
  V := F.Forms
  ι := Fin (F.toCSD h).dim
  b := (F.toCSD h).basis.map (F.res h).symm
  X := stdFrame (F.toCSD h).H
  L := L



variable {F}

variable (F)

variable {F}

variable (F)

variable {F}

end GFam

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

def intOf (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) : Submodule (𝓞 K) F.Forms :=
  Submodule.pi Set.univ fun b => (F.mem b).intOf (N b)

end GFam

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end GSD

section FormFam

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {β : Type} [Fintype β] [DecidableEq β]


variable (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : β → LevFam X.E X.K n SG)

end FormFam

end Formalism.L2.Col
end
end

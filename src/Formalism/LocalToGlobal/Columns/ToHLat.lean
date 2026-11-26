module

public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalToGlobal.GlobalTheory.HLatOps
public import Formalism.LocalToGlobal.Columns.RowFormsSym
public import Formalism.LocalToGlobal.Columns.HeckeSpCount

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.ToHLat
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def pairAt (v : InfinitePlace K) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (S.bV.repr x i)) * v.embedding (S.gramV i j) * v.embedding (S.bV.repr y j)

def ipAt (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

abbrev hDim (h : S.Ok) : ℕ := (S.toCSD h).dim

def hB (h : S.Ok) : Basis (Fin (S.hDim h)) K S.EqFun := (S.toCSD h).basis.map (S.res h).symm

abbrev hGram (h : S.Ok) : Matrix (Fin (S.hDim h)) (Fin (S.hDim h)) K := (S.toCSD h).H

def PosH (h : S.Ok) : Prop := ∀ v : InfinitePlace K, ((S.hGram h).map v.embedding).PosDef

@[reducible] def toH (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K where
  V := S.EqFun
  ι := Fin (S.hDim h)
  b := S.hB h
  X := stdFrame (S.hGram h)
  L := L

abbrev hCoord (h : S.Ok) : S.EqFun ≃ₗ[K] (Fin (S.hDim h) → K) := S.coordOf h S.outSec

def toHc (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K :=
  toHLat (stdFrame (S.hGram h)) (L.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)))

def subZ (h : S.Ok) (U : Submodule K S.EqFun) : Submodule K (Fin (S.hDim h) → K) :=
  U.map (S.hCoord h).toLinearMap

def subEq (h : S.Ok) (U : Submodule K S.EqFun) : U ≃ₗ[K] S.subZ h U := (S.hCoord h).submoduleMap U

abbrev subD (h : S.Ok) (U : Submodule K S.EqFun) : ℕ := subDim (S.subZ h U)

def subB (h : S.Ok) (U : Submodule K S.EqFun) : Basis (Fin (S.subD h U)) K U :=
  (subBasis (S.subZ h U)).map (S.subEq h U).symm

def subMat (h : S.Ok) (U : Submodule K S.EqFun) : Matrix (Fin (S.hDim h)) (Fin (S.subD h U)) K :=
  subE (S.subZ h U)

@[reducible] def subH (h : S.Ok) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) : HLat K where
  V := U
  ι := Fin (S.subD h U)
  b := S.subB h U
  X := restrFrame (S.subMat h U) (S.hGram h)
  L := L

end GSD

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)

@[reducible] def latH (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (colGSD W Ch u j).toH (colOk W Ch hX u j) (ColL W Ch u j)

@[reducible] def Mu0H (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).toH (colOk W Ch hX u 0) (MfL W Ch u)

@[reducible] def MramH (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).subH (colOk W Ch hX u 0) (MramV W Ch u) (MramL W Ch u)

def ramInclH (u : Pr.Word) : (MramH W Ch hX u).V →ₗ[X.K] (Mu0H W Ch hX u).V := ramIncl W Ch u

end Cols

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

@[reducible] def MtildeH (P : LevFam X.E X.K R.r Pr.vGs) : HLat X.K :=
  (mtildeGSD W Ch sel mu P).toH (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)

end Rows

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_asAlgebraHom_eq (a : MonoidAlgebra K A) : ρ.asAlgebraHom a = ∑ t : A, a.coeff t • ρ t := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp [Finsupp.sum_fintype]

theorem rf_coord_act (t : A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ t φ) = ((S.toCSD h).actMat (S.repCSD h ρ) t).mulVec (S.coordOf h S.outSec φ) := by
  have c : ∀ x, S.coordOf h S.outSec x = (S.toCSD h).basis.equivFun (S.res h x) := fun x => rfl
  have e1 : (S.repCSD h ρ) t (S.res h φ) = S.res h (ρ t φ) := by
    show (S.res h) (ρ t ((S.res h).symm (S.res h φ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [c, c]
  unfold CSD.actMat
  simp only [Basis.equivFun_apply]
  rw [LinearMap.toMatrix_mulVec_repr, e1]

theorem rf_coord_ga (a : MonoidAlgebra K A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ.asAlgebraHom a φ) =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVec (S.coordOf h S.outSec φ) := by

  have hsum : ∀ {m : ℕ} (M : A → Matrix (Fin m) (Fin m) K) (c : A → K) (v : Fin m → K),
      (∑ t, c t • M t).mulVec v = ∑ t, c t • (M t).mulVec v := by
    intro m M c v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rf_asAlgebraHom_eq, LinearMap.sum_apply, map_sum]
  unfold CSD.gaMat
  rw [hsum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [LinearMap.smul_apply, map_smul, rf_coord_act]

theorem rf_range_ga (a : MonoidAlgebra K A) :
    (LinearMap.range (ρ.asAlgebraHom a)).map (S.coordOf h S.outSec).toLinearMap =
      LinearMap.range ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin := by
  have e : (S.coordOf h S.outSec).toLinearMap ∘ₗ ρ.asAlgebraHom a =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin ∘ₗ (S.coordOf h S.outSec).toLinearMap := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    exact rf_coord_ga S h ρ a φ
  rw [← LinearMap.range_comp, e, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

private theorem range_subE_lemma {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (Z : Submodule K (Fin n → K)) :
    LinearMap.range (subE Z).mulVecLin = Z := by
  rw [Matrix.range_mulVecLin]
  have e : (subE Z).col = ⇑Z.subtype ∘ ⇑(subBasis Z) := by
    funext j i
    rfl
  rw [e, Set.range_comp, Submodule.span_image, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem invariantSubspace_coords_X (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : (mtildeKGSD W Ch sel mu).Ok) :
    (V0X W Ch sel mu Xg P).map ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).toLinearMap =
      LinearMap.range ((V0C W Ch sel mu h Xg P).E).mulVecLin := by
  unfold V0X
  rw [rf_range_ga]
  exact (range_subE_lemma _).symm

end Rows

section LvlPart

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_mem_lvlPart_iff (P : Subgroup A) (ψ : P →* Kˣ) (φ : S.EqFun) :
    S.coordOf h S.outSec φ ∈ (S.toCSD h).lvlPart (S.repCSD h ρ) P ψ ↔
      ∀ a : P, ρ (a : A) φ = ((ψ a : Kˣ) : K) • φ := by
  show (∀ a : P, ((S.toCSD h).actMat (S.repCSD h ρ) (a : A)).mulVec (S.coordOf h S.outSec φ) =
      ((ψ a : Kˣ) : K) • S.coordOf h S.outSec φ) ↔ _
  refine forall_congr' (fun a => ?_)
  rw [← rf_coord_act, ← map_smul]
  exact (S.coordOf h S.outSec).injective.eq_iff

end LvlPart

section RowsLvl

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem mem_lvlPartX_iff (h : (mtildeKGSD W Ch sel mu).Ok) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec φ ∈
        (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr ↔
      φ.1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine Iff.trans ?_ (mem_MtildeV_iff W Ch sel mu P φ.1).symm
  exact (rf_mem_lvlPart_iff _ h (g0HatRepEqFunX W Ch sel mu) P.grp P.chr φ).trans ⟨fun H => ⟨φ.2, H⟩, fun ⟨_, H⟩ => H⟩

end RowsLvl

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.AtTRank
open Module

noncomputable section

namespace Formalism.L2.Col

namespace RamFun

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, CommGroup (G i)]
  [∀ i, Fintype (G i)] {M : Type} [AddCommGroup M] [Module K M]


variable (K M) in
def trl (b : ∀ i, G i) : Module.End K ((∀ i, G i) → M) := LinearMap.funLeft K M fun c => b * c

theorem trl_apply (b : ∀ i, G i) (F : (∀ i, G i) → M) (c : ∀ i, G i) : trl K M b F c = F (b * c) := rfl

theorem trl_one : trl K M (1 : ∀ i, G i) = 1 := by
  refine LinearMap.ext fun F => funext fun c => ?_
  show F (1 * c) = F c
  rw [one_mul]

theorem trl_mul (b b' : ∀ i, G i) : trl K M b * trl K M b' = trl K M (b * b') := by
  refine LinearMap.ext fun F => funext fun c => ?_
  show F (b' * (b * c)) = F (b * b' * c)
  congr 1
  rw [mul_left_comm, mul_assoc]

theorem trl_comm (b b' : ∀ i, G i) : Commute (trl K M b) (trl K M b') := by
  show trl K M b * trl K M b' = trl K M b' * trl K M b
  rw [trl_mul, trl_mul, mul_comm]


variable (K M) in
def nmF (i : ι) : Module.End K ((∀ i, G i) → M) := ∑ g : G i, trl K M (Pi.mulSingle i g)


variable (K M G) in
def ramFun : Submodule K ((∀ i, G i) → M) := ⨅ i, LinearMap.ker (nmF K M (G := G) i)


variable (K M G) in
def offAlg (i : ι) : Submodule K (Module.End K ((∀ i, G i) → M)) :=
  Submodule.span K {x | ∃ b : ∀ i, G i, b i = 1 ∧ x = trl K M b}

theorem one_mem_offAlg (i : ι) : (1 : Module.End K ((∀ i, G i) → M)) ∈ offAlg K G M i := by
  have h : trl K M (1 : ∀ i, G i) ∈ offAlg K G M i := Submodule.subset_span ⟨1, rfl, rfl⟩
  rwa [trl_one] at h

theorem mul_mem_offAlg (i : ι) {x y : Module.End K ((∀ i, G i) → M)} (hx : x ∈ offAlg K G M i)
    (hy : y ∈ offAlg K G M i) : x * y ∈ offAlg K G M i := by
  unfold offAlg at *
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨b, hb, rfl⟩ := hx'
      obtain ⟨b', hb', rfl⟩ := hy'
      exact Submodule.subset_span ⟨b * b', by rw [Pi.mul_apply, hb, hb', one_mul], trl_mul b b'⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

theorem nmF_mem_offAlg {i j : ι} (h : j ≠ i) : nmF K M (G := G) j ∈ offAlg K G M i := by
  unfold nmF
  exact Submodule.sum_mem _ fun g _ =>
    Submodule.subset_span ⟨Pi.mulSingle j g, Pi.mulSingle_eq_of_ne h.symm g, rfl⟩

theorem nmF_comm_trl (i : ι) (b : ∀ i, G i) : Commute (nmF K M (G := G) i) (trl K M b) :=
  Commute.sum_left _ _ _ fun _ _ => trl_comm _ _

theorem nmF_comm (i j : ι) : Commute (nmF K M (G := G) i) (nmF K M (G := G) j) :=
  Commute.sum_left _ _ _ fun _ _ => (nmF_comm_trl j _).symm

theorem nmF_sq (i : ι) : nmF K M (G := G) i * nmF K M i = (Fintype.card (G i) : K) • nmF K M i := by
  have key : ∀ g : G i, nmF K M (G := G) i * trl K M (Pi.mulSingle i g) = nmF K M i := by
    intro g
    show (∑ h : G i, trl K M (Pi.mulSingle i h)) * trl K M (Pi.mulSingle i g) =
      ∑ h : G i, trl K M (Pi.mulSingle i h)
    rw [Finset.sum_mul]
    simp_rw [trl_mul, ← Pi.mulSingle_mul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl
  calc nmF K M (G := G) i * nmF K M i = ∑ g : G i, nmF K M (G := G) i * trl K M (Pi.mulSingle i g) := by
        rw [← Finset.mul_sum]; rfl
    _ = ∑ _g : G i, nmF K M (G := G) i := Finset.sum_congr rfl fun g _ => key g
    _ = (Fintype.card (G i) : K) • nmF K M i := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K]

section Trace

variable [FiniteDimensional K M]

theorem trace_trl {b : ∀ i, G i} (hb : b ≠ 1) : LinearMap.trace K _ (trl K M b) = 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basis fun _ : (∀ i, G i) => Module.finBasis K M), Matrix.trace]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨c, k⟩ := p
  have hc : b * c ≠ c := fun h => hb (mul_right_cancel (h.trans (one_mul c).symm))
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr, trl_apply]
  rw [Pi.single_eq_of_ne hc]
  simp

theorem trace_mul_offAlg {i : ι} {g : G i} (hg : g ≠ 1) {x : Module.End K ((∀ i, G i) → M)}
    (hx : x ∈ offAlg K G M i) : LinearMap.trace K _ (trl K M (Pi.mulSingle i g) * x) = 0 := by
  unfold offAlg at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [trl_mul]
    refine trace_trl fun h => hg ?_
    have := congrFun h i
    simpa [hb] using this
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => rw [mul_smul_comm, map_smul, hx, smul_zero]

theorem trace_nmF_mul {i : ι} {x : Module.End K ((∀ i, G i) → M)} (hx : x ∈ offAlg K G M i) :
    LinearMap.trace K _ (nmF K M i * x) = LinearMap.trace K _ x := by
  show LinearMap.trace K _ ((∑ g : G i, trl K M (Pi.mulSingle i g)) * x) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, Finset.sum_eq_single (1 : G i)]
  · rw [Pi.mulSingle_one, trl_one, one_mul]
  · intro g _ hg
    exact trace_mul_offAlg hg hx
  · intro h
    exact absurd (Finset.mem_univ _) h

end Trace

end RamFun

namespace RamFun

section Proj

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
  [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] {M : Type} [AddCommGroup M] [Module K M]


variable (K M G) in
def eF (i : ι) : Module.End K ((∀ i, G i) → M) := 1 - ((Fintype.card (G i) : K)⁻¹) • nmF K M i

theorem card_ne (i : ι) : (Fintype.card (G i) : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem nmF_mul_eF (i : ι) : nmF K M i * eF K G M i = 0 := by
  unfold eF
  rw [mul_sub, mul_one, mul_smul_comm, nmF_sq, smul_smul, inv_mul_cancel₀ (card_ne (K := K) (G := G) i),
    one_smul, sub_self]

theorem eF_mem_offAlg {i j : ι} (h : j ≠ i) : eF K G M j ∈ offAlg K G M i :=
  Submodule.sub_mem _ (one_mem_offAlg i) (Submodule.smul_mem _ _ (nmF_mem_offAlg h))

theorem nmF_comm_eF (i j : ι) : Commute (nmF K M (G := G) i) (eF K G M j) :=
  (Commute.one_right _).sub_right ((nmF_comm i j).smul_right _)


variable (K M G) in
def eL (l : List ι) : Module.End K ((∀ i, G i) → M) := (l.map (eF K G M)).prod

theorem eL_mem_offAlg {i : ι} {l : List ι} (h : i ∉ l) : eL K G M l ∈ offAlg K G M i := by
  induction l with
  | nil =>
    simp only [eL, List.map_nil, List.prod_nil]
    exact one_mem_offAlg i
  | cons a l ih =>
    rw [List.mem_cons, not_or] at h
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    exact mul_mem_offAlg i (eF_mem_offAlg (Ne.symm h.1)) (ih h.2)

theorem nmF_mul_eL {i : ι} {l : List ι} (h : i ∈ l) : nmF K M i * eL K G M l = 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h'
    · rw [← mul_assoc, nmF_mul_eF, zero_mul]
    · rw [← mul_assoc, (nmF_comm_eF i a).eq, mul_assoc, ih h', mul_zero]

theorem eL_fix {F : (∀ i, G i) → M} (hF : F ∈ ramFun K G M) (l : List ι) : eL K G M l F = F := by
  have h1 : ∀ j, eF K G M j F = F := by
    intro j
    have h0 : nmF K M j F = 0 := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hF j)
    simp [eF, h0]
  induction l with
  | nil => simp [eL]
  | cons a l ih =>
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    show eF K G M a ((List.map (eF K G M) l).prod F) = F
    rw [ih, h1]

variable [FiniteDimensional K M]

theorem trace_eL {l : List ι} (hl : l.Nodup) :
    LinearMap.trace K _ (eL K G M l) =
      (l.map fun i => (1 - (Fintype.card (G i) : K)⁻¹)).prod * LinearMap.trace K ((∀ i, G i) → M) 1 := by
  induction l with
  | nil => simp [eL]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hx : eL K G M l ∈ offAlg K G M a := eL_mem_offAlg hl.1
    have e : eL K G M (a :: l) = eF K G M a * eL K G M l := by simp [eL]
    rw [e, eF, _root_.sub_mul, one_mul, smul_mul_assoc, map_sub, map_smul, trace_nmF_mul hx, ih hl.2,
      List.map_cons, List.prod_cons, smul_eq_mul]
    ring

theorem isProj_eL : LinearMap.IsProj (ramFun K G M) (eL K G M Finset.univ.toList) := by
  refine ⟨?_, fun F hF => eL_fix hF _⟩
  refine fun F => (Submodule.mem_iInf _).2 fun i => ?_
  show nmF K M i (eL K G M Finset.univ.toList F) = 0
  rw [← mul_apply_eq_comp, nmF_mul_eL (Finset.mem_toList.2 (Finset.mem_univ i))]
  rfl

theorem finrank_ramFun : finrank K (ramFun K G M) = finrank K M * ∏ i, (Fintype.card (G i) - 1) := by
  have h := (isProj_eL (K := K) (G := G) (M := M)).trace
  rw [trace_eL (Finset.nodup_toList _), LinearMap.trace_one, Finset.prod_map_toList] at h
  have hV : finrank K ((∀ i, G i) → M) = (∏ i, Fintype.card (G i)) * finrank K M := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_pi, smul_eq_mul]
  have hc : ∀ i, ((Fintype.card (G i) - 1 : ℕ) : K) =
      (Fintype.card (G i) : K) * (1 - (Fintype.card (G i) : K)⁻¹) := by
    intro i
    rw [Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card (G i)), Nat.cast_one, mul_sub, mul_one,
      mul_inv_cancel₀ (card_ne (K := K) (G := G) i)]
  rw [hV] at h
  apply Nat.cast_injective (R := K)
  rw [← h]
  simp only [Nat.cast_mul, Nat.cast_prod]
  rw [Finset.prod_congr rfl fun i _ => hc i, Finset.prod_mul_distrib]
  ring

end Proj

end RamFun

section ColsRank

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)




end ColsRank

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.DiamondPreservesRamified
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


theorem Deco.L_dia (d : Deco E n ST SG) (c : DiaG (E := E) (ST := ST)) : (d.dia c).L = d.L := by
  unfold Deco.L
  congr 1
  ext x
  show (x ∈ d.N ∧ ∀ P : ST, (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ ∀ P : ST, d.f P x = 0)
  simp only [Units.mul_right_eq_zero]

theorem Deco.Lsh_dia (d : Deco E n ST SG) (c : DiaG (E := E) (ST := ST)) : (d.dia c).Lsh = d.Lsh := by
  unfold Deco.Lsh
  rw [Deco.L_dia]

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end Cols

section Adj

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Adj

section AtW

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AtW

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.HeckeInertLemmas
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.inertSet_finite {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    (d.inertSet P s).Finite := by
  have hPk : P ^ s.sum ≠ ⊥ := pow_ne_zero _ hP
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPk
  have hI : Ideal.span {a} * P ^ s.sum ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hPk⟩
  have hfin := finite_between ((Ideal.span {a} * P ^ s.sum) • d.1.N) d.1.N
    (finite_quot_smul d.1.N d.2.lat.fg _ hI)
  refine Set.Finite.of_injOn (f := fun e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) => Ideal.span {a} • e.1.N) ?_ ?_ hfin
  · intro e he
    obtain ⟨h1, h2⟩ := he.1.smul_le
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact Submodule.smul_mono le_rfl h1
    · exact (Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem _).2 haP) le_rfl).trans h2
  · intro e he e' he' h
    have hN : e.1.N = e'.1.N := by
      simp only [Submodule.ideal_span_singleton_smul] at h
      have hinj : Function.Injective fun x : Sp E n => a • x := smul_right_injective (Sp E n) ha
      have hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B := by
        intro A B hAB x hx
        have : a • x ∈ a • B := hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx
        obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        rwa [← hinj hyx]
      exact le_antisymm (hsub _ _ h) (hsub _ _ h.symm)
    exact Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))

theorem DecoSet.mem_inertNb {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    e ∈ d.inertNb P s ↔ e ∈ d.inertSet P s := by
  unfold DecoSet.inertNb
  rw [dite_eq_left (DecoSet.inertSet_finite hP s d), Set.Finite.mem_toFinset]

theorem DecoSet.sum_inertNb_smul {M : Type} [AddCommMonoid M] (P : Ideal (𝓞 E)) (s : List ℕ)
    (g : UF E n × GLG (E := E) (n := n) (SG := SG)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (ψ : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → M) :
    ∑ e ∈ (g • d).inertNb P s, ψ e = ∑ e ∈ d.inertNb P s, ψ (g • e) := by
  symm
  exact Finset.sum_equiv (MulAction.toPerm g) (fun e => (DecoSet.smul_mem_inertNb_iff g).symm) (fun e _ => rfl)

end Fin

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Op

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.WmLemmas
open NumberField IsDedekindDomain Module Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nb

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (V : Type) [AddCommGroup V] [Module X.K V]

theorem trF_nbFun (a : GLG (E := X.E) (n := n) (SG := SG)) (P : Ideal (𝓞 X.E)) (i : ℕ) (ψ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → V) :
    trF X n ST SG V a (nbFun X.K V P i ψ) = nbFun X.K V P i (trF X n ST SG V a ψ) := by
  funext d
  rw [trF_apply]
  show ∑ d₁ ∈ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d).heckeNb P i, ψ d₁ =
    ∑ d₁ ∈ d.heckeNb P i, ψ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d₁)
  set g : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) := ((1 : UF X.E n), a⁻¹)
  refine Finset.sum_nbij' (fun e => g⁻¹ • e) (fun e => g • e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have : g • (g⁻¹ • e) ∈ (g • d).heckeNb P i := by rwa [smul_inv_smul]
    exact (DecoSet.smul_mem_heckeNb_iff g).1 this
  · intro e he
    exact (DecoSet.smul_mem_heckeNb_iff g).2 he
  · intro e _
    exact smul_inv_smul g e
  · intro e _
    exact inv_smul_smul g e
  · intro e _
    rw [smul_inv_smul]

end Nb

section Poly

variable {L : Type} [Field L]

end Poly

section HV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end HV

section FromRel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end FromRel

section Inh

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end Inh

section Fub

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Fub

section Rev

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


end Rev

section PhiLem

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {K : Type} [Field K] {a b : ℕ}


end PhiLem

section Gauss

variable {L : Type} [Field L]

end Gauss

section Count

variable (E : Type) [Field E] [NumberField E] [StarRing E]


end Count

section ClassRel

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ClassRel

section RelOf

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end RelOf

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Main

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.AtTOwedV
section -- merged from Formalism.LocalToGlobal.Columns.AtTOwedU
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem SameAt.symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

theorem SameAt.trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', k1, k2⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]
    exact h1 _ (k1 _ hx)
  · rw [mul_smul]
    exact k2 _ (h2 _ hx)

theorem SameAt.sup {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (S : Submodule (𝓞 E) (Sp E n)) : SameAt Q (N ⊔ S) (N' ⊔ S) := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨a, ha, a', ha', fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h1 y hy) (S.smul_mem a hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h2 y hy) (S.smul_mem a' hz)

end Loc

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.IsUp.sameAt {d d' : Deco E n ST SG} (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (h : Deco.IsUp P q d d') {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ≠ P.1) (hQ' : Q ≠ conjPrime₂ P.1) :
    SameAt Q d.N d'.N := by
  obtain ⟨x, hx, -, rfl⟩ := h
  exact (upN_spec hd.lat hd.uni P.1 hP.ne hx).2.2.1 Q hQ hQ'

theorem Deco.IsUp.f_ne {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') {Q : ST}
    (hQ : Q ≠ P) : d'.f Q = d.f Q := by
  obtain ⟨x, _, _, rfl⟩ := h
  simp only [Deco.up, Function.update, dif_neg hQ]

theorem Deco.IsUp.be_eq {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') : d'.be = d.be := by
  obtain ⟨x, _, _, rfl⟩ := h
  rfl

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideTwistedConsistent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfAutomorphismMapsParahoric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenve
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductLevelEqOfLocalAgreement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingClassGroupDescentsDifferByPowerPrimeToL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEtaOfAdmissibleTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricFor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricFor
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaRigid

theorem det_mem_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (hM : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  have e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O)).map O.subtype := by ext i j; rfl
  have h := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O))
  rw [RingHom.mapMatrix_apply] at h
  rw [e, ← h]
  exact SetLike.coe_mem _

theorem inv_entry_mem {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : ∀ i j, (x⁻¹).1 i j ∈ O := by
  intro i j
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine O.mul_mem ?_ (det_mem_of O _ ?_)
  · rw [Ring.inverse_eq_inv']; exact hd
  · intro k l
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    · exact h1 k l

theorem mem_GLint_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : x ∈ Formalism.UG.GLint (Fin m) O :=
  GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨h1, inv_entry_mem O x h1 hd⟩

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

def colVecAt (j : Fin m) (t : K) : Matrix (Fin m) Unit K := Matrix.of fun i _ => if i = j then t else 0

def rowVecAt (K : Type) [Field K] (i : Fin m) : Matrix Unit (Fin m) K := Matrix.of fun _ j => if j = i then 1 else 0

def Gmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + (h * colVecAt j0 t) * rowVecAt K i0

def Pmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + colVecAt j0 t * (rowVecAt K i0 * h)

theorem det_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Gmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Gmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem det_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Pmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Pmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem G_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Gmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if j = i0 then h i j0 * t else 0 := by
  simp [Gmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem P_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Pmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if i = j0 then t * h i0 j else 0 := by
  simp [Pmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem conj_G (h h' : Matrix (Fin m) (Fin m) K) (hh : h' * h = 1) (i0 j0 : Fin m) (t : K) :
    h' * Gmat h i0 j0 t * h = Pmat h i0 j0 t := by
  simp only [Gmat, Pmat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hh, Matrix.one_mul]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

theorem detDD_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hi0 : r ≤ i0.val) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1).det = 1 + h i0 j0 * t := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1) =
      1 + ((Matrix.of fun a (_ : Unit) => h a.1 j0 * t : Matrix {x : Fin m // r ≤ x.val} Unit K) *
        (Matrix.of fun (_ : Unit) b => if b = ⟨i0, hi0⟩ then 1 else 0 : Matrix Unit {x : Fin m // r ≤ x.val} K)) := by
    ext a b
    simp [G_apply, Matrix.one_apply, Matrix.mul_apply, Subtype.ext_iff]
  rw [e, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [Matrix.mul_apply]

theorem detDD_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hj0 : j0.val < r) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1).det = 1 := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1) = 1 := by
    ext a b
    have ha : (a.1 : Fin m) ≠ j0 := fun e => by have := a.2; rw [e] at this; omega
    simp [P_apply, Matrix.one_apply, Subtype.ext_iff, ha]
  rw [e, Matrix.det_one]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

theorem mem_para_of_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  intro L _ _ _ n r s V _ _ F J χ a hF ha hJ hEig h1 ha' κ hκU hκT hc
  obtain ⟨c, hc⟩ := hc
  classical
  set O := (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  have hOv : ∀ x, x ∈ O ↔ Valued.v x ≤ 1 := fun x => by
    rw [hO, ValuationSubring.mem_toSubring, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hint := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκT).2 hκU
  refine ⟨hint, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, j0, hi0, hj0, hv⟩ := hcon
  set h := s.loc n κ with hh
  have hent : ∀ i j, Valued.v (h.val i j) ≤ 1 := fun i j =>
    (hOv _).1 ((GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hint).1 i j)
  have hv1 : Valued.v (h.val i0 j0) = 1 := le_antisymm (hent i0 j0) hv
  have hne : h.val i0 j0 ≠ 0 := by
    intro e; rw [e, map_zero] at hv1; exact zero_ne_one hv1
  have ha0 : a ≠ 0 := by
    intro e; rw [e, map_zero] at ha; exact zero_ne_one ha
  set t := (a - 1) / h.val i0 j0 with ht
  have htv : Valued.v t ≤ 1 := by
    rw [ht, map_div₀, hv1, div_one]
    refine (Valuation.map_sub _ _ _).trans (max_le ha.le (by rw [map_one]))
  have hth : 1 + h.val i0 j0 * t = a := by rw [ht]; field_simp; ring
  have hdinv : a⁻¹ ∈ O := by rw [hOv, map_inv₀, ha, inv_one]
  have hone : ∀ i j, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]; split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have hGint : ∀ i j, Gmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, G_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' (hent _ _) htv
    · rw [map_zero]; exact zero_le'
  have hPint : ∀ i j, Pmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, P_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' htv (hent _ _)
    · rw [map_zero]; exact zero_le'
  have hdG : (Gmat h.val i0 j0 t).det = a := by rw [det_G, hth]
  have hdP : (Pmat h.val i0 j0 t).det = a := by rw [det_P, hth]
  let Gg := Matrix.GeneralLinearGroup.mkOfDetNeZero (Gmat h.val i0 j0 t) (by rw [hdG]; exact ha0)
  have hGg : Gg.val = Gmat h.val i0 j0 t := rfl
  obtain ⟨g, ⟨hgT, hgl⟩, -⟩ := (GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 Gg
  set p := κ⁻¹ * g * κ with hp
  have hpT : TrivOutside {s.v} p :=
    GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hκT) hgT) hκT
  have hinv : (h⁻¹).val * h.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpl : (s.loc n p).val = Pmat h.val i0 j0 t := by
    rw [hp, map_mul, map_mul, map_inv, hgl, ← hh, Units.val_mul, Units.val_mul, hGg]
    exact conj_G h.val (h⁻¹).val hinv i0 j0 t
  have hgl' : (s.loc n g).val = Gmat h.val i0 j0 t := by rw [hgl]; exact hGg
  have hgP : NG.ParaRT s r (s.loc n g) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hgl']; exact hGint i j) (by rw [hgl', hdG]; exact hdinv), ?_⟩
    intro i j hi hj
    have hji : j ≠ i0 := fun e => by rw [e] at hj; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hgl', G_apply, if_neg hji, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hpP : NG.ParaRT s r (s.loc n p) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hpl]; exact hPint i j) (by rw [hpl, hdP]; exact hdinv), ?_⟩
    intro i j hi hj
    have hij0 : i ≠ j0 := fun e => by rw [e] at hi; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hpl, P_apply, if_neg hij0, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hgJ : g ∈ J := (hJ g hgT).2 hgP
  have hpJ : p ∈ J := (hJ p hpT).2 hpP
  have hχg : χ ⟨g, hgJ⟩ ≠ 1 := ha' g hgJ hgT (by unfold NG.detDD; simp only [hgl']; rw [detDD_G _ _ _ _ r hi0, hth])
  have hχp : χ ⟨p, hpJ⟩ = 1 := h1 p hpJ hpT (by unfold NG.detDD; simp only [hpl]; rw [detDD_P _ _ _ _ r hj0])
  have eg := hEig ⟨g, hgJ⟩
  have ep := hEig ⟨p, hpJ⟩
  rw [hχp] at ep
  have hkp : κ * p = g * κ := by rw [hp]; group
  obtain ⟨x0, hx0⟩ : ∃ x, F x ≠ 0 := by
    by_contra hn; push_neg at hn; exact hF (funext hn)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx0
    have := hc (x0 * κ⁻¹)
    rwa [inv_mul_cancel_right, zero_smul] at this
  have key : ∀ x, c • ((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) • F x = c • F x := by
    intro x
    have e1 := hc (x * g)
    have e2 := ep (x * κ)
    rw [eg x] at e1
    rw [mul_assoc, hkp, ← mul_assoc, e1, hc x] at e2
    simpa using e2
  apply hχg
  have k0 := key x0
  rw [smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at k0
  rcases k0 with k0 | k0
  · apply Units.ext
    have : c * (((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) - 1) = 0 := by rw [mul_sub, mul_one]; exact k0
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hc0
    · simpa [sub_eq_zero] using h'
  · exact absurd k0 hx0

end GlobalTheory.ParaRigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricForStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_parahoric_of_scalar_action_on_ramifiedParahoricForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  first | exact @GlobalTheory.ParaRigid.mem_para_of_eig | exact GlobalTheory.ParaRigid.mem_para_of_eig | (intros; apply GlobalTheory.ParaRigid.mem_para_of_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistReadingInducesSideEmbeddingFixedField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistReadingInducesSideEmbeddingFixedField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem mem_range_map_iff_of_isLocalHom {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f) (t : FractionRing A) :
    IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t ∈ (algebraMap B (FractionRing B)).range ↔
      t ∈ (algebraMap A (FractionRing A)).range := by
  have hmap : ∀ a : A, IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf (algebraMap A _ a) =
      algebraMap B _ (f a) := fun a => by simp [IsFractionRing.map]
  constructor
  · rintro ⟨c, hc⟩
    by_cases ht : t = 0
    · exact ⟨0, by rw [ht, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger A t with ⟨a, ha⟩ | ⟨m, hm⟩
    · exact ⟨a, ha⟩
    · have h1 : IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t *
          IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      rw [← hc, ← hm, hmap, ← map_mul] at h1
      have h2 : c * f m = 1 := IsFractionRing.injective B (FractionRing B) (by rw [h1, map_one])
      have hu : IsUnit m := (isUnit_map_iff f m).1 (IsUnit.of_mul_eq_one_right c h2)
      refine ⟨((hu.unit⁻¹ : Aˣ) : A), ?_⟩
      rw [← inv_inv t, ← hm]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul]
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨f a, (hmap a).symm⟩

end GlobalTheory.LevCmp

namespace GlobalTheory.LevCmp

theorem reading_sidePl_emb : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  intro D i k b v ρ
  haveI := GlobalTheory.TwistChoice.isLocalHom_phiK i k
  haveI := ρ.loc
  have hinj : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp (BlochKatoReduction.Gen.phiK D.ntw i k)) :=
    ρ.inj.comp ((D.ntw.Ok_inj i k).comp (D.ntw.O_inj i))
  have hmap : ∀ a : D.ntw.O0 i, IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
      (algebraMap _ _ a) = algebraMap ρ.Oe _ (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k a)) := fun a => by
    simp [IsFractionRing.map]
  have key : ∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) =
      IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
        (GlobalTheory.TwistChoice.sideEmb i b x) := by
    intro x
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have hz0 : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
    have hside : GlobalTheory.TwistChoice.sideEmb i b x * algebraMap _ (FractionRing (D.ntw.O0 i)) z =
        algebraMap _ (FractionRing (D.ntw.O0 i)) y := by
      rw [← hyz, div_mul_cancel₀ _ hz0]
    have h1 := ρ.emb_side x y z hside
    have hz' : algebraMap ρ.Oe (FractionRing ρ.Oe) (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k z)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), ← RingHom.comp_apply,
        map_eq_zero_iff _ hinj]
      exact nonZeroDivisors.ne_zero hz
    rw [← hyz, map_div₀, hmap, hmap, eq_div_iff hz']
    exact h1
  have hside : ∀ x : ↥D.LL0, GlobalTheory.TwistChoice.sideEmb i b x =
      (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := fun x => by
    cases b <;> rfl
  refine ⟨fun x => ?_, fun x => ?_, fun h x => ?_⟩
  · rw [ρ.emb_w, key, ← hside]
    exact mem_range_map_iff_of_isLocalHom _ hinj _
  · rw [key]
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have e : GlobalTheory.SeriesTie.sideEmb D.ntw i b x = IsFractionRing.map (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) (GlobalTheory.TwistChoice.sideEmb i b x) := by
      cases b <;> rfl
    rw [e, ← hyz]
    simp [map_div₀, IsFractionRing.map, NX.toKk, BlochKatoReduction.Gen.phiK]
  · rw [key, ← hside]
    rfl

end GlobalTheory.LevCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistReadingInducesSideEmbeddingFixedFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  first | exact @GlobalTheory.LevCmp.reading_sidePl_emb | exact GlobalTheory.LevCmp.reading_sidePl_emb | (intros; apply GlobalTheory.LevCmp.reading_sidePl_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsAvoidExcludedPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsAvoidExcludedPrimes
noncomputable section

namespace GlobalTheory.LowAvoid

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

def lowPre (P : Pre) : Finset ℕ := by
  classical
  exact if h : ∃ X : Stages, X.B.toPre = P then lowAll h.choose.toD7 else ∅

theorem lowAll_congr {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : lowAll s.toD7 = lowAll s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem lowAll_eq_lowPre (s : Stages) : lowAll s.toD7 = lowPre s.B.toPre := by
  have h : ∃ X : Stages, X.B.toPre = s.B.toPre := ⟨s, rfl⟩
  simp only [lowPre, dif_pos h]
  exact lowAll_congr h.choose_spec.symm

theorem prime_of_mem_lowAll (D : D7) {p : ℕ} (hp : p ∈ lowAll D) : p.Prime := by
  simp only [lowAll, lowPr, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with ((rfl | rfl | hp | hp) | rfl | rfl | rfl | rfl)
  · exact Nat.prime_two
  · exact (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  · exact Nat.prime_of_mem_primeFactors hp
  · exact Nat.prime_of_mem_primeFactors hp
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1
  · exact D.host.pde_prime
  · exact D.host.pde'_prime

theorem eq_of_mem_placesOver {E : Type} [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hu : (Ideal.absNorm u.asIdeal).Prime) (h : u ∈ placesOver E p) : Ideal.absNorm u.asIdeal = p := by
  by_contra e
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem _
  obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ((p : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hu hp).2 e)
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ (show ((p : ℕ) : 𝓞 E) ∈ u.asIdeal from h))))

theorem conductors_avoid_lowAll :
    AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  refine evG_all fun K => ?_
  refine large₂.imp (p := fun B _ T => T.Avoids fun _ => lowPre B.toPre)
    ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun B _ _ _ _ => lowPre B, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ h => h⟩ ?_
  intro B f T _ hA _ _ _ w _ P x v u hu p hp hup
  have hl : lowAll (Dof x) = lowPre B.toPre := lowAll_eq_lowPre (w.st x.o.Z)
  obtain ⟨-, h1, -, -⟩ := (T.psi_tw v).2.2.2 u fun h => ((T.psi_is v).ram u).1 h hu
  have e : Ideal.absNorm u.asIdeal = p := eq_of_mem_placesOver u (prime_of_mem_lowAll _ hp) h1 hup
  exact hA v u hu (by rw [e, ← hl]; exact hp)

end GlobalTheory.LowAvoid

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsAvoidExcludedPrimesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistConductors_avoid_excludedPrimes : AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  first | exact @GlobalTheory.LowAvoid.conductors_avoid_lowAll | exact GlobalTheory.LowAvoid.conductors_avoid_lowAll | (intros; apply GlobalTheory.LowAvoid.conductors_avoid_lowAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankAlgebraicModularFormsComplexification
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankAlgebraicModularFormsComplexification
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

theorem exists_finset_eval_eq_zero {X K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (V : Submodule K (X → W)) [FiniteDimensional K V] :
    ∃ P : Finset X, ∀ f ∈ V, (∀ x ∈ P, f x = 0) → f = 0 := by
  classical
  let N : Finset X → Submodule K V := fun P =>
    ⨅ x ∈ P, LinearMap.ker ((LinearMap.proj (R := K) (φ := fun _ : X => W) x).comp V.subtype)
  have hN : ∀ P (f : V), f ∈ N P ↔ ∀ x ∈ P, (f : X → W) x = 0 := by
    intro P f; simp [N, Submodule.mem_iInf]
  obtain ⟨_, ⟨P, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range N) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨P, fun f hf h0 => ?_⟩
  have key : ∀ x, N P ≤ N (insert x P) := by
    intro x
    have hle : N (insert x P) ≤ N P := fun g hg =>
      (hN _ _).2 fun y hy => (hN _ _).1 hg y (Finset.mem_insert_of_mem hy)
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle fun h => hne h.ge)
  funext x
  exact (hN _ _).1 (key x ((hN P ⟨f, hf⟩).2 h0)) x (Finset.mem_insert_self x P)

section Omega
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
  [Fintype ι] [DecidableEq ι]

def coordCx (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') : W →ₛₗ[e] W' where
  toFun w := b'.equivFun.symm fun i => e (b.equivFun w i)
  map_add' x y := b'.equivFun.injective (by
    simp only [map_add (f := _), LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.add_apply, map_add (f := _)])
  map_smul' a x := b'.equivFun.injective (by
    simp only [map_smul, LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply])

theorem coordCx_coord (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') (w : W) (i : ι) :
    b'.equivFun (coordCx e b b' w) i = e (b.equivFun w i) := by
  simp only [coordCx, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]

end Omega

theorem finrank_typeSp_cx : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (W W' : Type) [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') (J : Subgroup (GAf L n)) (χ : J →* Kˣ), WtMatch e ρ ρ' → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional K (NX.TypeSpF L n K ρ J χ) → Module.finrank ℂ (NG.TypeSp ρ' J (cx e χ)) = Module.finrank K (NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ e W W' _ _ _ _ ρ ρ' J χ hW hN hfin
  classical
  obtain ⟨ι, _, _, b, b', hM⟩ := hW
  letI : Algebra K ℂ := e.toAlgebra
  let β := Module.Basis.ofVectorSpace K ℂ
  let ω := coordCx e b b'
  have hωc : ∀ w i, b'.equivFun (ω w) i = e (b.equivFun w i) := fun w i => coordCx_coord e b b' w i
  have hρ : ∀ γ w i, b.equivFun (ρ γ w) i = ∑ k, LinearMap.toMatrix b b (ρ γ) i k * b.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b b (ρ γ) w) i
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hρ' : ∀ γ w i, b'.equivFun (ρ' γ w) i = ∑ k, e (LinearMap.toMatrix b b (ρ γ) i k) * b'.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b' b' (ρ' γ) w) i
    rw [hM γ] at this
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hωρ : ∀ γ w, ω (ρ γ w) = ρ' γ (ω w) := fun γ w =>
    b'.equivFun.injective (funext fun i => by rw [hωc, hρ, hρ', map_sum]; simp only [map_mul, hωc])
  have hβ1 : ∀ (y : K) (z : ℂ) α, β.repr (e y * z) α = y * β.repr z α := by
    intro y z α
    rw [show e y * z = y • z from rfl, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let V := NX.TypeSpF L n K ρ J χ
  let v := Module.finBasis K V
  have hωV : ∀ f ∈ V, (fun g => ω (f g)) ∈ NG.TypeSp ρ' J (cx e χ) := by
    rintro f ⟨h1, h2⟩
    obtain ⟨N, hN0, hNc⟩ := hN
    refine ⟨⟨fun γ g => by simp only [h1, hωρ], N, hN0, fun κ hκ g => ?_⟩, fun κ => ?_⟩
    · obtain ⟨h, h1'⟩ := hNc κ hκ
      show ω (f (g * κ)) = ω (f g)
      have := h2 ⟨κ, h⟩ g
      rw [this, h1', Units.val_one, one_smul]
    · funext g
      show ω (f (g * κ)) = ((cx e χ κ : ℂˣ) : ℂ) • ω (f g)
      rw [h2, map_smulₛₗ, cx_apply]

  have hlinK : LinearIndependent K (fun j => ((v j : V) : GAf L n → W)) :=
    v.linearIndependent.map' V.subtype V.ker_subtype
  have hli : LinearIndependent ℂ (fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    rw [Fintype.linearIndependent_iff] at hlinK ⊢
    intro c hc j
    have hcoord : ∀ g i, ∑ j, c j * e (b.equivFun (((v j : V) : GAf L n → W) g) i) = 0 := by
      intro g i
      have := congrArg (fun F => b'.equivFun (F g) i) hc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, hωc,
        Pi.zero_apply, map_zero] using this
    have hα : ∀ α, ∀ j, β.repr (c j) α = 0 := by
      intro α
      apply hlinK
      funext g
      apply b.equivFun.injective
      funext i
      have := congrArg (fun z => β.repr z α) (hcoord g i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, mul_comm (c _), hβ1, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, map_zero, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact β.repr.injective (by ext α; simp [hα α j])

  have hspanV : ∀ a : Fin (Module.finrank K V) → K,
      (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) ∈
        Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    intro a
    have : (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) =
        ∑ j, e (a j) • fun g => ω (((v j : V) : GAf L n → W) g) := by
      funext g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hspan : NG.TypeSp ρ' J (cx e χ) = Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    refine le_antisymm ?_ (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hωV _ (v j).2))
    rintro F ⟨⟨hF1, -⟩, hF2⟩
    have hFk : ∀ (κ : J) g, F (g * κ) = e (χ κ) • F g := fun κ g => congrFun (hF2 κ) g
    let fa : _ → GAf L n → W := fun α g => b.equivFun.symm fun i => β.repr (b'.equivFun (F g) i) α
    have hfa : ∀ α g i, b.equivFun (fa α g) i = β.repr (b'.equivFun (F g) i) α := by
      intro α g i; simp only [fa, LinearEquiv.apply_symm_apply]
    have hfaV : ∀ α, fa α ∈ V := by
      intro α
      refine ⟨fun γ g => b.equivFun.injective (funext fun i => ?_), fun κ g => b.equivFun.injective (funext fun i => ?_)⟩
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hfa, hF1, hρ', hρ, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
          simp only [hβ1, hfa]
      · rw [hfa, hFk]
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, hβ1, hfa]
    obtain ⟨P, hP⟩ := exists_finset_eval_eq_zero V
    let S := P.biUnion fun g => Finset.univ.biUnion fun i => (β.repr (b'.equivFun (F g) i)).support
    have hzero : ∀ α ∉ S, fa α = 0 := by
      intro α hα
      refine hP _ (hfaV α) fun g hg => b.equivFun.injective (funext fun i => ?_)
      rw [hfa, map_zero, Pi.zero_apply]
      by_contra h
      exact hα (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 h⟩⟩)
    have hsub : ∀ g i, (β.repr (b'.equivFun (F g) i)).support ⊆ S := by
      intro g i α hα
      by_contra hS
      have := congrArg (fun f => b.equivFun (f g) i) (hzero α hS)
      simp only [hfa, Pi.zero_apply, map_zero] at this
      exact (Finsupp.mem_support_iff.1 hα) this
    have hFeq : F = ∑ α ∈ S, β α • fun g => ω (fa α g) := by
      funext g
      apply b'.equivFun.injective
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, hωc, hfa]
      conv_lhs => rw [← β.linearCombination_repr (b'.equivFun (F g) i)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hsub g i) (fun a c => c • β a) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    rw [hFeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    have hrep := congrArg Subtype.val (v.sum_repr ⟨fa α, hfaV α⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    rw [← hrep]
    exact hspanV _
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LevCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankAlgebraicModularFormsComplexificationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_algebraicModularForms_complexification : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (W W' : Type) [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') (J : Subgroup (GAf L n)) (χ : J →* Kˣ), WtMatch e ρ ρ' → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional K (NX.TypeSpF L n K ρ J χ) → Module.finrank ℂ (NG.TypeSp ρ' J (cx e χ)) = Module.finrank K (NX.TypeSpF L n K ρ J χ) := by
  first | exact @GlobalTheory.LevCmp.finrank_typeSp_cx | exact GlobalTheory.LevCmp.finrank_typeSp_cx | (intros; apply GlobalTheory.LevCmp.finrank_typeSp_cx <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

variable {D : D7}

theorem grpShape_of {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} {χ : J →* ℂˣ} (h1 : NG.IsProdLevel J)
    (h2 : ParaShape D η J χ)
    (h3 : ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∃ ψ₀ ξ, NG.LevelUni J χ s D.R.r ψ₀ ξ)
    (h4 : NG.HypOutside J χ (gPl D ∪ qPl D η)) : GrpShape D η J :=
  ⟨h1, fun v hv => let ⟨s, _, a, _, c⟩ := h2 v hv; ⟨s, a, c.mem⟩, fun k v s hs => let ⟨_, _, c⟩ := h3 k v s hs; c.mem,
    fun κ hκ => (h4 κ hκ).1⟩

theorem exists_form {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} (hG : GPlaces D) (h : GrpShape D η J)
    (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] (ρ : Representation K (GQ D.host.E D.R.nV) W)
    (hρ : ρ.IsIrreducible) (χ : J →* Kˣ) : ∃ f ∈ NX.TypeSpF D.host.E D.R.nV K ρ J χ, f ≠ 0 := by
  obtain ⟨k, ⟨v⟩⟩ := hG.2.2
  obtain ⟨h1, s, hs⟩ := hG.1 k v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_class_trivial_stabiliser_at_typePlace D k s (hs ▸ h1)
  haveI : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have := hρ
    have h2 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    exact h2 (Subrepresentation.ext (Subsingleton.elim _ _))
  exact GlobalTheory.T.exists_ne_zero_algebraicModularForm_of_trivial_stabiliser _ _ K W ρ J χ g fun γ hγ hm =>
    hg γ hγ (GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces D η J hG h _ hm).1 ((GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces D η J hG h _ hm).2 k v s hs)

theorem para_rigid {L : Type} [Field L] [NumberField L] [IsCMField L] {n r : ℕ} {s : SplitPlace L} {V : Type} [AddCommGroup V]
    [Module ℂ V] {F : GAf L n → V} {J : Subgroup (GAf L n)} {χ χ' : J →* ℂˣ}
    {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ} (hF : F ≠ 0) (h : NG.LevelPara J χ s r ξ)
    (hr : ∃ a : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield L)) = 1 ∧ ξ a ≠ 1)
    (h1 : ∀ κ, χ' κ = 1 ↔ χ κ = 1) (hE : ∀ κ : J, Eig F κ (χ' κ : ℂˣ)) :
    ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  obtain ⟨a, ha, ha'⟩ := hr
  refine GlobalTheory.T.mem_parahoric_of_scalar_action_on_ramifiedParahoricForm L n r s V F J χ' a hF ha h.mem hE (fun κ hκ ht hd => (h1 _).2 ?_) fun κ hκ ht hd e => ha' ?_
  · rw [h.chr κ hκ ht 1 hd.symm, map_one]
  · rw [← h.chr κ hκ ht a hd.symm]
    exact (h1 _).1 e

theorem cx_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ)
    {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) : cx e χ κ = 1 ↔ χ κ = 1 := by
  rw [← Units.val_inj, cx_apply, Units.val_one, map_eq_one_iff e e.injective, Units.val_eq_one]

theorem levEq {η : HChar D.host.E} {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (he : SideRead i b k e) (hG : GPlaces D)
    (hram : ∀ (s : SplitPlace D.host.E) ξ, s.v ∈ qPl D η → NG.IsCompAt η s ξ →
      ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
        Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1)
    (m1 : NG.IsProdLevel m.J) (m2 : ParaShape D η m.J m.χ)
    (m3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ)
    (m4 : NG.HypOutside m.J m.χ (gPl D ∪ qPl D η)) (x0 : NX.badV D i Q ⊆ gPl D ∪ qPl D η)
    (x2 : ParaShape D η (cell X b hA j).J (cx e (cell X b hA j).χ))
    (x3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      ∀ e, SideRead i b k e → NG.LevelUni (cell X b hA j).J (cx e (cell X b hA j).χ) s D.R.r ψ₀ ξ)
    (hJ : Joint η m X b hA j) : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ) := by
  have x1 := GlobalTheory.T.isProductLevel_definiteFormsRealisationAtTwist D X i b k Q ψ hA j
  have x4 : NG.HypOutside (cell X b hA j).J (cx e (cell X b hA j).χ) (gPl D ∪ qPl D η) := fun κ hκ => by
    have h := (cell X b hA j).hyp κ fun v hv => hκ v fun h => hv fun h' => h (x0 h')
    exact ⟨h.1, fun h' => (cx_eq_one _ _ _).2 (h.2 h')⟩
  have gm := grpShape_of m1 m2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := m3 k v s hs; ⟨a, c, d⟩) m4
  have gx := grpShape_of x1 x2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := x3 k v s hs; ⟨a, c, d e he⟩) x4
  obtain ⟨θ, J₁, e', V, _, _, ω, hθ, he', hω, j1, j2, j3⟩ := hJ
  obtain ⟨f, hf, hf0⟩ := exists_form hG gm ℂ _ m.wt.ρ m.wt.irr m.χ
  obtain ⟨f', hf', hf0'⟩ := exists_form hG gx _ _ (cell X b hA j).ρ (cell X b hA j).irr (cell X b hA j).χ
  obtain ⟨y, rfl⟩ : f ∈ LinearMap.range m.real := by
    rw [m.real_range]
    obtain ⟨N, hN, h⟩ := m.J_open
    refine ⟨⟨hf.1, N, hN, fun κ hκ g => ?_⟩, fun κ => funext fun g => hf.2 κ g⟩
    obtain ⟨h1, h2⟩ := h κ hκ
    have := hf.2 ⟨κ, h1⟩ g
    rwa [h2, Units.val_one, one_smul] at this
  obtain ⟨y', hy'⟩ := (cell X b hA j).real.surjective ⟨f', hf'⟩
  set F' : GAf D.host.E D.R.nV → V := fun g => ω (((cell X b hA j).real y').1 g) with hF'
  have hF0 : F' ≠ 0 := fun h => hf0' (funext fun g => hω (by
    have := congrFun h g
    rw [hF'] at this
    simp only [hy'] at this
    exact this.trans (map_zero ω).symm))
  have E1 : ∀ κ : m.J, Eig (m.real y) κ (m.χ κ : ℂˣ) := fun κ g => hf.2 κ g
  have E2 : ∀ κ : (cell X b hA j).J, Eig F' κ (cx e' (cell X b hA j).χ κ : ℂˣ) := fun κ g => by
    have := ((cell X b hA j).real y').2.2 κ g
    simp only [hF', this, map_smulₛₗ, cx_apply]
  have hr0 : 2 ≤ D.R.r := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; unfold Ranks.r; omega
  have hr1 : D.R.r < D.R.nV := by have := D.R.rank_add_five_le; unfold Ranks.nV; omega
  refine GlobalTheory.T.productLevel_eq_of_local_agreement _ _ _ _ _ _ _ (GlobalTheory.T.typePlaces_union_ramifiedPlaces_finite D η) m1 x1 m4 x4 fun u hu => ?_
  rcases hu with hu | hu
  · obtain ⟨kk, v, s, rfl, hs⟩ := hG.2.1 u hu
    obtain ⟨p, ξ, a1, a2, a3⟩ := m3 kk v s hs
    obtain ⟨p', ξ', b1, b2, b3⟩ := x3 kk v s hs
    obtain rfl := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique _ η s ξ ξ' a2 b2
    have hg := D.host.g_prime kk
    have hab : s.Above (D.host.g kk) := by
      have h1 : ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := hs ▸ (hG.1 kk v).1
      show _ ∈ s.v.asIdeal
      rw [← s.w_under]
      show algebraMap _ (𝓞 D.host.E) _ ∈ s.w.asIdeal
      rwa [map_natCast]
    have key := GlobalTheory.T.additiveCharacter_eq_of_common_unipotentLevel_eigenvector _ _ _ s (D.host.g kk) (D.host.g kk - 1) θ _ _ (m.real y) F' _ _ _ _ p p' ξ ξ hg hab
      ((Nat.coprime_self_sub_left hg.one_le).2 (Nat.coprime_one_left _)) hr0 hr1.le hθ hf0 hF0 a1 b1 a3 (b3 e' he') E1 E2
      fun κ hκ hU => let ⟨c, c', h1, h2, h3⟩ := j3 κ (j2 kk v s hs κ hκ hU); ⟨c, c', h1 y, h2 y', h3 kk v s hs hκ⟩
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans ((b3 e he).mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, u2⟩ := GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral _ _ _ s _ ((a3.mem κ hκ).1 h).1
    have hne : NG.detDD s D.R.r (s.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    apply Units.ext
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, (b3 e he).chr κ h' hκ (Units.mk0 _ hne) rfl, key _ u2]
  · obtain ⟨s, ξ, rfl, a2, a3⟩ := m2 u hu
    obtain ⟨s', ξ', b1, b2, b3⟩ := x2 _ hu
    obtain ⟨s₁, c1, c2⟩ := j1 _ hu
    have hU : ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s₁ D.R.r (s₁.loc _ κ) → κ ∈ Umax D.host.E D.R.nV := fun κ hκ hP =>
      (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s₁ (c1 ▸ hκ)).1 hP.1
    have hs : s' = s := GlobalTheory.T.splitPlace_eq_of_automorphism_maps_parahoric _ _ _ s s' s₁ θ (by omega) hr1 b1 c1 hθ fun κ hκ hP => by
      obtain ⟨c, c', h1, h2, -⟩ := j3 κ (c2 κ (c1 ▸ hκ) hP)
      have h3 := (hθ.1 κ).2 (hU κ hκ hP)
      have h4 := (hθ.2 _ κ).2 hκ
      exact ⟨para_rigid hf0 a3 (hram s ξ hu a2) (fun _ => Iff.rfl) E1 _ h3 h4 ⟨c, h1 y⟩,
        para_rigid hF0 b3 (hram s' ξ' (b1 ▸ hu) b2) (fun κ => (cx_eq_one _ _ _).trans (cx_eq_one _ _ _).symm) E2 _ h3
          (b1 ▸ h4) ⟨c', h2 y'⟩⟩
    subst hs
    obtain rfl := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique _ η s' ξ ξ' a2 b2
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans (b3.mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, -⟩ := GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral _ _ _ s' _ ((a3.mem κ hκ).1 h)
    have hne : NG.detDD s' D.R.r (s'.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, b3.chr κ h' hκ (Units.mk0 _ hne) rfl]

theorem unpack {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : GlobalTheory.TwistChoice.HasReading p b w ψ₀) {i : D.ntw.Tw} {Q : Finset (PlE D.host)} {k : ℕ} (h1 : p.1 = i) (h2 : p.2.1 = Q)
    (h3 : p.2.2.1 = k) : ∃ (ρ : Reading i k b w) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ), ρ.Pulls ψ ψ₀ ∧ twPack D i b Q k ψ = p := by
  obtain ⟨i', Q', k', φ⟩ := p
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, _, hρ, congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) (psiAt_psiAt b φ)⟩

theorem pack_pow {i i' : D.ntw.Tw} {k k' : ℕ} {b b' : Bool} {v v' : D.what₂.places.Pl} (ρ : Reading i k b v) (ρ' : Reading i' k' b' v')
    {Q Q' : Finset (PlE D.host)} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ' : D.ntw.RCG i' Q' →* (D.ntw.Ok i' k')ˣ}
    {ψ₀ ψ₀' : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h1 : i' = i) (h2 : Q' = Q) (h3 : k' = k) (h4 : ψ₀' = ψ₀)
    (hz : ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) (ho : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hp : ρ.Pulls ψ ψ₀)
    (hp' : ρ'.Pulls ψ' ψ₀') :
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ twPack D i' b' Q' k' ψ' = GlobalTheory.HeightCounting.twPackPow D a (twPack D i b Q k ψ) := by
  subst h1 h2 h3 h4
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.T.ringClassGroup_descents_differ_by_power_prime_to_l D _ _ b b' v v' ρ ρ' _ ψ ψ' _ hz ho hp hp'
  refine ⟨if b = b' then a else -a, by split_ifs <;> simpa using ha, ?_⟩
  refine congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) ?_
  cases b <;> cases b'
  · exact (inv_zpow ψ a).symm
  · exact ((inv_zpow' ψ (-a)).trans (congrArg (ψ ^ ·) (neg_neg a))).symm
  · exact (zpow_neg ψ a).symm
  · rfl

theorem exists_data (hG : IsGalois ℚ ↥D.LL0) (s : D.what₂.places.Pl → D.ntw.Tw) (Q : D.what₂.places.Pl → Finset (PlE D.host))
    (k : D.what₂.places.Pl → ℕ) (ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ))
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v) (c2 : ∀ v, Q (D.what₂.places.conj v) = Q v)
    (c3 : ∀ v, k (D.what₂.places.conj v) = k v) (c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v)
    (hex : ∀ v b (ρ : Reading (s v) (k v) b v), ∃ ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ, ρ.Pulls ψ (ψ₀ v)) :
    ∃ (b : D.what₂.places.Pl → Bool) (ρ : ∀ v, Reading (s v) (k v) (b v) v)
      (ψ : ∀ v, D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), (∀ v, ReadsAt (s v) (b v) v) ∧ (∀ v, (ρ v).Pulls (ψ v) (ψ₀ v)) ∧
      (∀ v, D.what₂.places.conj v ≠ v → b (D.what₂.places.conj v) = !b v) ∧
      ∀ v, twPack D (s (D.what₂.places.conj v)) (b (D.what₂.places.conj v)) (Q (D.what₂.places.conj v)) (k (D.what₂.places.conj v))
        (ψ (D.what₂.places.conj v)) = twPack D (s v) (b v) (Q v) (k v) (ψ v) := by
  classical
  choose b₀ hb using hs
  have h0 : ∀ v, ∃ p : TwPack D, GlobalTheory.TwistChoice.HasReading p (b₀ v) v (ψ₀ v) ∧ p.1 = s v ∧ p.2.1 = Q v ∧ p.2.2.1 = k v := fun v => by
    obtain ⟨ρ⟩ := (hb v).nonempty_reading (k v)
    obtain ⟨ψ, hψ⟩ := hex v _ ρ
    refine ⟨twPack D (s v) (b₀ v) (Q v) (k v) ψ, ⟨ρ, ?_⟩, rfl, rfl, rfl⟩
    show ρ.Pulls (BlochKatoReduction.Gen.psiAt (b₀ v) (BlochKatoReduction.Gen.psiAt (b₀ v) ψ)) _
    rwa [psiAt_psiAt]
  choose p hp using h0
  obtain ⟨o, ho⟩ := GlobalTheory.TwistChoice.exists_orbitRep (D := D)
  let b : D.what₂.places.Pl → Bool := fun w => if o w = w then b₀ w else !b₀ (D.what₂.places.conj w)
  have h1 : ∀ v, ReadsAt (s v) (b v) v ∧ ∃ (ρ : Reading (s v) (k v) (b v) v)
      (ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), ρ.Pulls ψ (ψ₀ v) ∧ twPack D (s v) (b v) (Q v) (k v) ψ = p (o v) := fun v => by
    by_cases h2 : o v = v
    · have e : b v = b₀ v := if_pos h2
      rw [e, h2]
      exact ⟨hb v, unpack (hp v).1 (hp v).2.1 (hp v).2.2.1 (hp v).2.2.2⟩
    · have e : b v = !b₀ (D.what₂.places.conj v) := if_neg h2
      have h3 := (hb (D.what₂.places.conj v)).conj hG
      have h4 := (hp (D.what₂.places.conj v)).1.conj hG
      rw [D.what₂.places.conj_conj] at h3 h4
      rw [c1] at h3
      rw [c4] at h4
      rw [e, (ho v).1.resolve_left h2]
      exact ⟨h3, unpack h4 ((hp _).2.1.trans (c1 v)) ((hp _).2.2.1.trans (c2 v)) ((hp _).2.2.2.trans (c3 v))⟩
  choose hr ρ ψ h2 h3 using h1
  refine ⟨b, ρ, ψ, hr, h2, fun w hne => ?_, fun v => by rw [h3, h3, (ho v).2]⟩
  simp only [b, (ho w).2, D.what₂.places.conj_conj]
  rcases (ho w).1 with h | h
  · rw [if_neg (by rw [h]; exact hne.symm), if_pos h]
  · rw [if_pos h, if_neg (by rw [h]; exact hne), Bool.not_not]

abbrev kMap {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) : NX.Kk D i k →+* FractionRing ρ.Oe :=
  IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj

theorem reads_of_pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) {Q : Finset (PlE D.host)}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} {χ : HChar D.host.E} (hp : ρ.Pulls ψ ψ₀)
    (hg : GalOf D χ ψ₀) {ι : FractionRing ρ.Oe →+* ℂ} (hι : ∀ x, ι (ρ.emb x) = D.what₂.embLL x) :
    SideRead i b k (ι.comp (kMap ρ)) ∧ ReadsHecke (ι.comp (kMap ρ)) (ψ.comp (D.ntw.art i Q)) χ := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [RingHom.comp_apply, ← (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D i k b v ρ).2.1 x, hι]
    rfl
  · obtain ⟨-, art, ha, h⟩ := hg
    refine ⟨art, ha, fun x σ e => (h x σ e).trans (Units.ext ?_)⟩
    show D.what₂.embLL (ψ₀ σ : D.what₂.LLˣ) = ι (kMap ρ (algebraMap _ _ ((ψ (D.ntw.art i Q σ) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)))
    rw [← hι, hp σ]
    simp [IsFractionRing.map]

theorem rank_of_levEq {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (h : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ)) (hw : CellWt m X b hA j e) :
    Module.finrank D.what₂.LL (D.what₂.MtL μ j') = Module.finrank (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
  haveI : FiniteDimensional (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
    obtain ⟨S, hS⟩ := D.nexp.MtLat_fg i (j.1 + 1) b k Q ψ
    refine ⟨S, ?_⟩
    rw [← D.nexp.MtLat_span i (j.1 + 1) b k Q ψ, ← hS, Submodule.span_span_of_tower]
  have h1 := GlobalTheory.T.finrank_algebraicModularForms_complexification _ _ _ e _ _ _ _ _ (cell X b hA j).χ hw (cell X b hA j).J_open
    (Module.Finite.equiv (cell X b hA j).real)
  rw [(cell X b hA j).real.finrank_eq, ← h1]
  have h2 : NG.TypeSp m.wt.ρ (cell X b hA j).J (cx e (cell X b hA j).χ) = NG.TypeSp m.wt.ρ m.J m.χ := by
    obtain ⟨h3, h4⟩ := h
    ext f
    refine and_congr_right fun _ => ⟨fun H κ => ?_, fun H κ => ?_⟩
    · rw [h4 κ.1 κ.2 (h3 ▸ κ.2)]
      exact H ⟨κ.1, h3 ▸ κ.2⟩
    · rw [← h4 κ.1 (h3.symm ▸ κ.2) κ.2]
      exact H ⟨κ.1, h3.symm ▸ κ.2⟩
  rw [h2, ← m.real_range, LinearMap.finrank_range_of_inj m.real_inj]
  obtain ⟨h3, h4⟩ := D.what₂.jMt_basis μ j' (Module.Free.chooseBasis _ _)
  rw [Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis _ _),
    Module.finrank_eq_nat_card_basis (Module.Basis.mk h3 h4.ge)]

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem muIsW (x : St P) : V4.MuIsW (w.st x.o.Z) f T P.Wt w.I.xi := by
  refine ⟨w.ok.xi_inj, w.xi_range, w.l.xi0, ?_, ?_, P.q.mu.tw, P.q.mu.on, P.q.mu.off,
    P.sub, P.supp⟩
  · show w.I.xi w.I.muStar = f.del
    rw [w.ok.xi_star, w.C_eq]
  · show w.I.xi w.I.muStar' = f.del'
    rw [w.ok.xi_star', w.C_eq]

theorem cfOf_eq (x : St P) : cfOf x = Fr.at (w.st x.o.Z) f :=
  congrArg (Fr.at (w.st x.o.Z)) w.C_eq

theorem exists_tp (x : St P) (C : NChoice (Dof x)) (h : C.Q = QOf P) :
    ∃ tp : TupTied (Dof x) (cfOf x) C, tp.xi = w.I.xi ∧ tp.psi = T.psi := by
  rw [cfOf_eq]
  exact (GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW x)).2.2.2 C fun v _ =>
    (congrFun h v).trans (Model.qOf_eq v)

theorem disjoint_conductorPlaces_excludedSet {Q : Finset (PlE D.host)} {i : D.ntw.Tw} (h : OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D)))
    (h1 : ∀ u ∈ Q, u ∉ placesOver D.host.E (D.ntw.l i)) (h2 : ∀ u ∈ Q, ∀ p ∈ lowAll D, u ∉ placesOver D.host.E p) :
    Disjoint Q (D.ntw.S0 i) := Finset.disjoint_left.2 fun u hu hS => by
  obtain ⟨p, hp, h3⟩ := h u hS
  rcases Finset.mem_insert.1 hp with rfl | hp
  exacts [h1 u hu h3, h2 u hu p hp h3]

end GlobalTheory.LevCmp

end

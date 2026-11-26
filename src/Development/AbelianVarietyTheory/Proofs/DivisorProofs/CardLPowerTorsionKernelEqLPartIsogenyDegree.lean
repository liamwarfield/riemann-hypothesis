module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientOfGaloisStableFiniteSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdDegOfNoTorsionInKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.TorsKer

theorem pow_eq_one_of_points : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n m : ℕ), (n : K) ≠ 0 →
    (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1) →
    ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1 := by
  intro K _ A C f n m hn hpt T x hx hf
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    have : IsUnit (n : K) := isUnit_iff_ne_zero.2 hn
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hZf, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let Z := torsion A.X n
  let iZ : Z ⟶ A.X := torsion.ι A.X n
  have hiZ : iZ ^ n = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact (pullback.condition (f := mulN A.X n) (g := (η : 𝟙_ (Over (Sp K)) ⟶ A.X))).trans
      (by rw [CategoryTheory.Hom.one_def]; congr 1; exact toUnit_unique _ _)
  let a : Z.left ⟶ C.X.left := (iZ ≫ f.hom).left
  have : IsClosedImmersion (η[C.X]).left :=
    isClosedImmersion_of_comp_eq_id (Y := Sp K) C.X.hom _ (Over.w _)
  let H : Over (Sp K) := Over.mk (pullback.fst a (η[C.X]).left ≫ Z.hom)
  let j : H ⟶ Z := Over.homMk (pullback.fst a (η[C.X]).left) rfl
  have hHf : IsFinite H.hom := by
    haveI := hZf; show IsFinite (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
  have hHe : Etale H.hom := by
    haveI := hZe
    haveI : FormallyUnramified Z.hom := by infer_instance
    haveI : LocallyOfFinitePresentation Z.hom := by infer_instance
    haveI : IsClosedImmersion (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified H.hom := by
      show FormallyUnramified (pullback.fst a (η[C.X]).left ≫ Z.hom)
      exact MorphismProperty.comp_mem @FormallyUnramified _ _ ‹_› ‹FormallyUnramified Z.hom›
    haveI : LocallyOfFinitePresentation H.hom := by
      show LocallyOfFinitePresentation (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
    exact Etale.of_formallyUnramified_of_flat _
  have hjf : j ≫ iZ ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    have h1 : (toUnit H).left = H.hom := by simpa using Over.w (toUnit H)
    have h2 : (η[C.X]).left ≫ C.X.hom = 𝟙 _ := by simpa using Over.w (η[C.X])
    have h3 : a ≫ C.X.hom = Z.hom := Over.w (iZ ≫ f.hom)
    have hs : pullback.snd a (η[C.X]).left = (toUnit H).left := by
      rw [h1]
      show pullback.snd a _ = pullback.fst a _ ≫ Z.hom
      rw [← h3, ← Category.assoc, pullback.condition, Category.assoc, h2]
      exact (Category.comp_id _).symm
    rw [CategoryTheory.Hom.one_def]
    show pullback.fst a _ ≫ a = (toUnit H).left ≫ (η[C.X]).left
    rw [← hs]
    exact pullback.condition
  have hsep : IsSeparated A.X.hom := by
    have := A.ab.proper; infer_instance
  have key : (j ≫ iZ) ^ m = 1 := by
    refine GlobalTheory.GenTorsMap.hom_ext_points hHf hHe hsep _ _ fun y => ?_
    rw [MonObj.comp_one, MonObj.comp_pow]
    refine hpt (y ≫ j ≫ iZ) ?_ ?_
    · rw [← MonObj.comp_pow, ← MonObj.comp_pow, hiZ, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hjf, MonObj.comp_one]
  have hx1 : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by
    rw [GlobalTheory.GrpTangent.comp_mulN, hx, CategoryTheory.Hom.one_def]
  let x₁ : T ⟶ Z := pullback.lift x (toUnit T) hx1
  have hx₁ : x₁ ≫ iZ = x := pullback.lift_fst _ _ _
  have hw : x₁.left ≫ a = T.hom ≫ (η[C.X]).left := by
    have e := congrArg (fun g => g.left) hf
    simp only [CategoryTheory.Hom.one_def, Over.comp_left] at e
    have hT : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
    rw [← hT, ← e, ← hx₁]
    simp [a]
  let x₂ : T ⟶ H := Over.homMk (pullback.lift x₁.left T.hom hw)
    (by show _ ≫ pullback.fst a _ ≫ Z.hom = _; rw [← Category.assoc, pullback.lift_fst]; exact Over.w x₁)
  have hx₂ : x₂ ≫ j ≫ iZ = x := by
    rw [← hx₁, ← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simp [x₂, j]
  rw [← hx₂, ← MonObj.comp_pow, key, MonObj.comp_one]

end GlobalTheory.AV.TorsKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdDegOfNoTorsionInKernel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.DegPrime

theorem pow_comp_mon {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem pow_prime_pow {K : Type} [Field K] (l : ℕ) {A B : AbVar K} (f : A ⟶ B)
    (hf : ∀ x : A.Pt, x ^ l = 1 → x ≫ f.hom = 1 → x = 1) :
    ∀ (b : ℕ) (x : A.Pt), x ^ (l ^ b) = 1 → x ≫ f.hom = 1 → x = 1 := by
  intro b
  induction b with
  | zero => intro x hx _; simpa using hx
  | succ b ih =>
    intro x hx hxf
    apply ih x _ hxf
    apply hf (x ^ (l ^ b))
    · rw [← pow_mul, ← pow_succ]; exact hx
    · rw [pow_comp_mon, hxf, one_pow]

end GlobalTheory.AV.AbVar.DegPrime

theorem GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (h : A ⟶ B), IsIsogeny h → (∀ x : A.Pt, x ^ l = 1 → x ≫ h.hom = 1 → x = 1) →
      ¬ l ∣ deg h := by
  intro K _ l hl hlK A B h hh hker
  have hp : l.Prime := hl.out
  obtain ⟨hdim, -, -, -⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B h hh
  obtain ⟨N, hN, hkill⟩ := GlobalTheory.AV.KerKill.kernel_killed K A B h hh.1
  obtain ⟨b, m, hlm, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.ne_one
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hNm; omega
    · exact h0
  have hlb : ((l ^ b : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK
  have hpts := GlobalTheory.AV.TorsKer.pow_eq_one_of_points K A B h (l ^ b) 1 hlb
    (fun x hx hxf => by rw [pow_one]; exact GlobalTheory.AV.AbVar.DegPrime.pow_prime_pow l h hker b x hx hxf)
  have hkm : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ h.hom = 1 → x ^ m = 1 := by
    intro T x hx
    have h1 : (x ^ m) ^ (l ^ b) = 1 := by
      rw [← pow_mul, mul_comm, ← hNm]; exact hkill T x hx
    have h2 : (x ^ m) ≫ h.hom = 1 := by
      rw [GlobalTheory.AV.AbVar.DegPrime.pow_comp_mon, hx, one_pow]
    simpa using hpts T (x ^ m) h1 h2
  have hB := B.smooth
  have hA := A.smooth
  rw [hdim] at hA
  obtain ⟨h', hh', hhh', -⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A.X B.X B.dim A.ab B.ab hA hB
    h.hom inferInstance m hm hkm
  let g : B ⟶ A := Hom.mk (A := B) (B := A) h' (h := hh')
  have e1 : h ≫ g = ((m : ℤ)) • 𝟙 A := by
    apply Subtype.ext
    change h.hom ≫ h' = (𝟙 A.X) ^ (m : ℤ)
    simpa using hhh'
  obtain ⟨-, hdeg⟩ := GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A B A h g hdim hdim.symm
  obtain ⟨-, hdm⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A (m : ℤ) (by exact_mod_cast hm.ne')
  rw [e1, hdm, Int.natAbs_natCast] at hdeg
  intro hdvd
  have : l ∣ m ^ (2 * A.dim) := by rw [hdeg]; exact Dvd.dvd.mul_right hdvd _
  exact hlm (hp.dvd_of_dvd_pow this)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdDegOfNoTorsionInKernelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (h : A ⟶ B), IsIsogeny h → (∀ x : A.Pt, x ^ l = 1 → x ≫ h.hom = 1 → x = 1) → ¬ l ∣ deg h := by
  first | (exact @GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (exact GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (intros; apply GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegree
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

def kerLPart (l : ℕ) {A B : AbVar K} (f : A ⟶ B) : Subgroup A.Pt where
  carrier := {x | x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  one_mem' := ⟨(ptMap f).map_one, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, n, hn⟩ ⟨hy, m, hm⟩
    refine ⟨?_, n + m, ?_⟩
    · have := (ptMap f).map_mul x y
      simp only [ptMap_apply] at this
      rw [this, hx, hy, _root_.one_mul]
    · rw [mul_pow, pow_add, pow_mul, hn, one_pow, mul_comm (l ^ n), pow_mul, hm, one_pow, _root_.one_mul]
  inv_mem' := by
    rintro x ⟨hx, n, hn⟩
    refine ⟨?_, n, ?_⟩
    · have := (ptMap f).map_inv x
      simp only [ptMap_apply] at this
      rw [this, hx, inv_one]
    · rw [inv_pow, hn, inv_one]

theorem kerLPart_le (l : ℕ) {A B : AbVar K} (f : A ⟶ B) : kerLPart l f ≤ (ptMap f).ker :=
  fun _ hx => hx.1

theorem card_kerLPart_eq (K : Type) [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0)
    (A B : AbVar K) (f : A ⟶ B) (hf : IsIsogeny f) :
    Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} = l ^ padicValNat l (deg f) := by
  set G := kerLPart l f with hG
  change Nat.card G = _
  have hker : Finite (ptMap f).ker := (GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 hf.1
  haveI hGfin : Finite G := Finite.of_injective (Subgroup.inclusion (kerLPart_le l f))
    (Subgroup.inclusion_injective _)
  have hpG : IsPGroup l G := fun g => by
    obtain ⟨n, hn⟩ := g.2.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hpG)
  have hcardK : ((Nat.card G : ℕ) : K) ≠ 0 := by
    rw [hk, Nat.cast_pow]; exact pow_ne_zero _ hl
  have hgal : ∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G := by
    rintro σ x ⟨hx, n, hn⟩
    refine ⟨?_, n, ?_⟩
    · have h1 : galPts A.X σ x ≫ f.hom = galPts B.X σ (x ≫ f.hom) := Category.assoc _ _ _
      rw [h1, hx, map_one]
    · rw [← map_pow, hn, map_one]
  obtain ⟨B', q, hq, hdq, hkq, huniv⟩ := GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup K A G hGfin hcardK hgal
  obtain ⟨h, hqh⟩ := huniv B f (kerLPart_le l f)
  have hdAB := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf).1
  have hdAB' := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B' q hq).1
  have hcomp := GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A B' B q h hdAB' (hdAB'.symm.trans hdAB)
  rw [hqh] at hcomp
  have hh : IsIsogeny h := (hcomp.1.mp hf).2
  have hsurj := (GlobalTheory.T.abVar_surjective_iff_ptMap_surjective K A B' q).1 hq.2
  have hnot : ¬ l ∣ deg h := by
    refine GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' K l hl B' B h hh ?_
    intro y hyl hyh
    obtain ⟨x, rfl⟩ := hsurj y
    have hxf : x ≫ f.hom = 1 := by
      rw [← hqh, comp_hom, ← Category.assoc]; exact hyh
    have hxl : x ^ l ∈ G := by
      rw [← hkq, MonoidHom.mem_ker, map_pow, hyl]
    obtain ⟨n, hn⟩ := hxl.2
    have hx : x ∈ G := ⟨hxf, n + 1, by rw [pow_succ', pow_mul]; exact hn⟩
    rw [← hkq] at hx
    exact hx
  have hdh : deg h ≠ 0 := fun h0 => hnot (h0 ▸ dvd_zero l)
  rw [hcomp.2, hdq, hk, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hdh,
    Nat.padicValNat_def, Nat.multiplicity_prime_pow, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnot, add_zero]

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegreeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} = l ^ padicValNat l (deg f) := by
  first | (exact @GlobalTheory.AV.AbVar.card_kerLPart_eq) | (exact GlobalTheory.AV.AbVar.card_kerLPart_eq) | (intros; apply GlobalTheory.AV.AbVar.card_kerLPart_eq  <;> assumption)
end

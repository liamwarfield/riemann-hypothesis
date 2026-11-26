module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.StarRingOfInvolution
namespace KStar.Cstarloc

structure UnramDatum (R : Type*) [CommRing R] [StarRing R] : Prop where
  trace_one : ∃ e : R, e + star e = 1
  norm_onto : ∀ u : R, IsUnit u → star u = u → ∃ a : R, a * star a = u

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

abbrev Sesq (R : Type*) [CommRing R] [StarRing R] (M : Type*) [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R

def IsHerm (h : Sesq R M) : Prop := ∀ x y, h y x = star (h x y)

def IsUnimod (h : Sesq R M) : Prop := Function.Bijective (h.flip : M → Module.Dual R M)

def gram {ι : Type*} (h : Sesq R M) (b : ι → M) : Matrix ι ι R := Matrix.of fun i j => h (b i) (b j)

def IsOrthonormal {ι : Type*} [DecidableEq ι] (h : Sesq R M) (b : ι → M) : Prop := gram h b = 1

def perp (h : Sesq R M) (x : M) : Submodule R M := LinearMap.ker (h.flip x)

def restr (h : Sesq R M) (N : Submodule R M) : Sesq R N := h.domRestrict₁₂ N N

theorem mem_perp (h : Sesq R M) (x y : M) : y ∈ perp h x ↔ h y x = 0 := by
  rw [perp, LinearMap.mem_ker, LinearMap.flip_apply]

end KStar.Cstarloc
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.IsUnimodIffGram
namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem isHerm_iff_gram {ι : Type*} [Fintype ι] (h : Sesq R M) (b : Module.Basis ι R M) :
    IsHerm h ↔ (gram h b).IsHermitian := by
  constructor
  · intro hh
    ext i j
    simp only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact (hh (b j) (b i)).symm
  · intro hG x y
    have hb : ∀ i j, star (h (b i) (b j)) = h (b j) (b i) := fun i j => by
      have := congrFun (congrFun hG j) i
      simpa [gram, Matrix.conjTranspose_apply] using this
    rw [← b.sum_repr x, ← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply,
      starRingEnd_apply, smul_eq_mul, star_sum, star_mul', star_star, hb, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem isUnimod_iff_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Sesq R M)
    (b : Module.Basis ι R M) : IsUnimod h ↔ IsUnit (gram h b).det := by
  have hmv : Function.Bijective (gram h b).mulVec ↔ IsUnit (gram h b).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    refine ⟨fun hb => hb.2, fun hs => ⟨?_, hs⟩⟩
    have hu : IsUnit (gram h b).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hs)
    intro v w hvw
    have := congrArg (gram h b)⁻¹.mulVec hvw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
  have hcomp : (b.dualBasis.equivFun ∘ (LinearMap.flip h) ∘ b.equivFun.symm) =
      (gram h b).mulVec ∘ star := by
    funext v i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Module.Basis.equivFun_symm_apply, Module.Basis.dualBasis_repr, gram, Matrix.mulVec, dotProduct,
      map_sum, map_smulₛₗ, mul_comm, starRingEnd_apply]
  have hfl : Function.Bijective (LinearMap.flip h) ↔ Function.Bijective ((gram h b).mulVec ∘ star) := by
    rw [← hcomp, EquivLike.comp_bijective, EquivLike.bijective_comp]
  rw [IsUnimod, hfl, Function.Bijective.of_comp_iff _ (Function.Involutive.bijective star_involutive), hmv]

theorem gram_comb {ι κ : Type*} [Fintype κ] (h : Sesq R M) (x : κ → M) (P : Matrix ι κ R) :
    gram h (fun i => ∑ j, P i j • x j) = P * gram h x * P.conjTranspose := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    starRingEnd_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end KStar.Cstarloc
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.UnitVector
namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

private theorem norm_one_of_unit (hR : UnramDatum R) (h : Sesq R M) (hh : IsHerm h) (z : M)
    (hz : IsUnit (h z z)) : ∃ x, h x x = 1 := by
  obtain ⟨a, ha⟩ := hR.norm_onto (h z z) hz (hh z z).symm
  have hau : IsUnit a := isUnit_of_mul_isUnit_left (ha ▸ hz)
  obtain ⟨u, rfl⟩ := hau
  refine ⟨(↑u⁻¹ : R) • z, ?_⟩
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← ha]
  have h1 : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
  have h2 : star (↑u⁻¹ : R) * star (↑u : R) = 1 := by rw [← star_mul', Units.inv_mul, star_one]
  linear_combination (star (↑u⁻¹ : R) * star (↑u : R)) * h1 + h2

theorem exists_norm_one [IsLocalRing R] (hR : UnramDatum R) [Module.Free R M] [Nontrivial M]
    (h : Sesq R M) (hh : IsHerm h) (hu : IsUnimod h) : ∃ x, h x x = 1 := by
  obtain ⟨e, he⟩ := hR.trace_one
  let b := Module.Free.chooseBasis R M
  have : Nonempty (Module.Free.ChooseBasisIndex R M) := b.index_nonempty
  obtain ⟨i⟩ := this
  obtain ⟨y, hy⟩ := hu.2 (b.coord i)
  have hxy : h (b i) y = 1 := by
    have := LinearMap.congr_fun hy (b i)
    simpa using this
  have hyx : h y (b i) = 1 := by rw [hh (b i) y, hxy, star_one]
  by_cases hx : IsUnit (h (b i) (b i))
  · exact norm_one_of_unit hR h hh _ hx
  by_cases hyy : IsUnit (h y y)
  · exact norm_one_of_unit hR h hh _ hyy
  refine norm_one_of_unit hR h hh (b i + e • y) ?_
  have key : h (b i + e • y) (b i + e • y) = 1 + (h (b i) (b i) + e * star e * h y y) := by
    simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hxy, hyx]
    linear_combination he
  have hw : ¬ IsUnit (e * star e * h y y) := fun hw => hyy (isUnit_of_mul_isUnit_right hw)
  have hs : ¬ IsUnit (h (b i) (b i) + e * star e * h y y) :=
    IsLocalRing.nonunits_add (mem_nonunits_iff.mpr hx) (mem_nonunits_iff.mpr hw)
  rw [key]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (show (1 + (h (b i) (b i) + e * star e * h y y)) + -(h (b i) (b i) + e * star e * h y y) = 1 by ring)
    with h' | h'
  · exact h'
  · exact absurd (by simpa using h'.neg) hs

private theorem sub_mem_perp (h : Sesq R M) (x : M) (hx : h x x = 1) (z : M) :
    z - h z x • x ∈ perp h x := by
  rw [mem_perp]
  simp [map_sub, map_smul, hx]

theorem isUnimod_restr_perp (h : Sesq R M) (hh : IsHerm h) (hu : IsUnimod h) (x : M)
    (hx : h x x = 1) : IsUnimod (restr h (perp h x)) := by
  have hperp : ∀ n ∈ perp h x, h x n = 0 := fun n hn => by
    rw [mem_perp] at hn
    rw [hh n x, hn, star_zero]
  constructor
  · intro n1 n2 heq
    have hsub : ∀ m : perp h x, h m ((n1 : M) - n2) = 0 := fun m => by
      have := LinearMap.congr_fun heq m
      simp only [LinearMap.flip_apply, restr, LinearMap.domRestrict₁₂_apply] at this
      rw [map_sub, this, sub_self]
    have hxn : h x ((n1 : M) - n2) = 0 := hperp _ (Submodule.sub_mem _ n1.2 n2.2)
    have hall : LinearMap.flip h ((n1 : M) - n2) = LinearMap.flip h 0 := by
      ext z
      simp only [LinearMap.flip_apply, map_zero, LinearMap.zero_apply]
      have hz := hsub ⟨z - h z x • x, sub_mem_perp h x hx z⟩
      have hdec : h z = h (z - h z x • x) + h z x • h x := by
        rw [map_sub, map_smul, sub_add_cancel]
      rw [hdec, LinearMap.add_apply, LinearMap.smul_apply, hxn, smul_zero, add_zero]
      simpa using hz
    exact Subtype.ext (sub_eq_zero.mp (hu.1 hall))
  · intro f
    let P : M →ₗ[R] perp h x := (LinearMap.id - (LinearMap.flip h x).smulRight x).codRestrict (perp h x)
      (fun z => by simpa using sub_mem_perp h x hx z)
    obtain ⟨y, hy⟩ := hu.2 (f ∘ₗ P)
    have hPm : ∀ m : perp h x, P m = m := fun m => Subtype.ext (by simp [P, (mem_perp h x m).mp m.2])
    have hPx : P x = 0 := Subtype.ext (by simp [P, hx])
    have h1 : h x y = 0 := by
      have := LinearMap.congr_fun hy x
      simpa [hPx] using this
    have hyx : h y x = 0 := by rw [hh x y, h1, star_zero]
    refine ⟨⟨y, (mem_perp h x y).mpr hyx⟩, ?_⟩
    ext m
    have := LinearMap.congr_fun hy m
    simp [restr, hPm] at this ⊢
    exact this

end KStar.Cstarloc
end

namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

private theorem projection_mem_orthogonal (h : Sesq R M) (x : M) (hx : h x x = 1) (z : M) :
    z + (-(h z x)) • x ∈ perp h x := by
  rw [mem_perp]
  simp [hx]

private theorem orthogonal_complement_independent (h : Sesq R M) (x : M) (hx : h x x = 1) (c : R) (y : M)
    (hy : y ∈ perp h x) (e : c • x + y = 0) : c = 0 := by
  rw [mem_perp] at hy
  have := congrArg (fun z => h z x) e
  simpa [hx, hy] using this

private theorem orthogonal_complement_free_finite [IsLocalRing R] [Module.Free R M] [Module.Finite R M]
    (h : Sesq R M) (x : M) (hx : h x x = 1) :
    Module.Finite R (perp h x) ∧ Module.Free R (perp h x) := by
  let p : M →ₗ[R] perp h x :=
    LinearMap.codRestrict (perp h x) (LinearMap.id - (h.flip x).smulRight x) (fun z => by
      have := projection_mem_orthogonal h x hx z
      simpa [sub_eq_add_neg] using this)
  have hp : p.comp (perp h x).subtype = LinearMap.id := by
    ext ⟨z, hz⟩
    rw [mem_perp] at hz
    simp [p, hz]
  have hs : Function.Surjective p := fun z => ⟨z, by
    have := LinearMap.congr_fun hp z
    simpa using this⟩
  haveI : Module.Finite R (perp h x) := Module.Finite.of_surjective p hs
  haveI : Module.Projective R (perp h x) := Module.Projective.of_split _ p hp
  exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩

universe u in
private theorem exists_orthonormal_basis_unimodular [IsLocalRing R] (hR : UnramDatum R) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
      (h : Sesq R M), IsHerm h → IsUnimod h → Module.finrank R M = n →
      ∃ b : Module.Basis (Fin n) R M, IsOrthonormal h b := by
  induction n with
  | zero =>
    intro M _ _ _ _ h _ _ hn
    refine ⟨Module.finBasisOfFinrankEq R M hn, ?_⟩
    ext i
    exact i.elim0
  | succ n ih =>
    intro M _ _ _ _ h hh hu hn
    haveI : Nontrivial M := Module.nontrivial_of_finrank_eq_succ hn
    obtain ⟨x, hx⟩ := exists_norm_one hR h hh hu
    obtain ⟨hfin, hfree⟩ := orthogonal_complement_free_finite h x hx
    have hli := orthogonal_complement_independent h x hx
    have hsp : ∀ z : M, ∃ c : R, z + c • x ∈ perp h x :=
      fun z => ⟨_, projection_mem_orthogonal h x hx z⟩
    have hr : Module.finrank R (perp h x) = n := by
      have := Module.finrank_eq_card_basis
        (Module.Basis.mkFinCons x (Module.finBasis R (perp h x)) hli hsp)
      rw [hn, Fintype.card_fin] at this
      omega
    obtain ⟨b, hb⟩ := ih (perp h x) (restr h (perp h x)) (fun a c => hh a c)
      (isUnimod_restr_perp h hh hu x hx) hr
    refine ⟨Module.Basis.mkFinCons x b hli hsp, ?_⟩
    rw [Module.Basis.coe_mkFinCons]
    have h1 : ∀ j, h (b j) x = 0 := fun j => (b j).2
    have h2 : ∀ j, h x (b j) = 0 := fun j => by rw [hh, h1, star_zero]
    have h3 : ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := fun i j => by
      have := congrFun (congrFun hb i) j
      simpa [gram, Matrix.one_apply, restr, LinearMap.domRestrict₁₂, LinearMap.domRestrict₂_apply,
        LinearMap.domRestrict_apply] using this
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [gram, hx]
    · simp [gram, h2, Matrix.one_apply, (Fin.succ_ne_zero j).symm]
    · simp [gram, h1, Matrix.one_apply]
    · simp [gram, h3, Matrix.one_apply]

theorem exists_congr_one [IsLocalRing R] (hR : UnramDatum R) {n : Type*} [Fintype n]
    [DecidableEq n] (G : Matrix n n R) (hG : G.IsHermitian) (hd : IsUnit G.det) :
    ∃ P : Matrix n n R, IsUnit P.det ∧ P * G * P.conjTranspose = 1 := by
  let h : Sesq R (n → R) :=
    LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) (fun x y => x ⬝ᵥ G.mulVec (star y))
      (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [Matrix.mulVec_add]) (fun _ _ _ => by
        simp [Matrix.mulVec_smul, starRingEnd_apply])
  have hg : gram h (Pi.basisFun R n) = G := by
    ext i j
    simp [gram, h, ← Pi.single_star]
  have hh : IsHerm h := (isHerm_iff_gram h (Pi.basisFun R n)).2 (by rw [hg]; exact hG)
  have hu : IsUnimod h := (isUnimod_iff_gram h (Pi.basisFun R n)).2 (by rw [hg]; exact hd)
  obtain ⟨b, hb⟩ := exists_orthonormal_basis_unimodular hR (Fintype.card n) (n → R) h hh hu
    (Module.finrank_fintype_fun_eq_card R)
  let e := Fintype.equivFin n
  let P : Matrix n n R := Matrix.of fun i j => b (e i) j
  have key : P * G * P.conjTranspose = 1 := by
    rw [← hg, ← gram_comb]
    have : (fun i => ∑ j, P i j • (Pi.basisFun R n) j) = fun i => b (e i) := by
      funext i
      have := (Pi.basisFun R n).sum_repr (b (e i))
      simpa [P] using this
    rw [this]
    ext i j
    have := congrFun (congrFun hb (e i)) (e j)
    simpa [gram, Matrix.one_apply] using this
  refine ⟨P, ?_, key⟩
  rw [Matrix.mul_assoc] at key
  exact Matrix.isUnit_det_of_right_inverse key

end KStar.Cstarloc

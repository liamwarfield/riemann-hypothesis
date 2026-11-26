module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFrameTranscendentalSpecialisingTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFrameTranscendentalSpecialisingTwo
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFrame

open Matrix ReciprocityTheory.ChartRestriction.G.PullbackSections

def mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) R := (1 - u) • (1 : Matrix (Fin n) (Fin n) R) + u • A.map κ

theorem mixM_map {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {n : ℕ} (κ : K →+* R) (u : R)
    (A : Matrix (Fin n) (Fin n) K) (ψ : R →+* R') : (mixM κ u A).map ψ = mixM (ψ.comp κ) (ψ u) A := by
  ext a b
  by_cases h : a = b
  · subst h; simp [mixM]
  · simp [mixM, Matrix.one_apply_ne h]

def detPoly {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Polynomial K :=
  (mixM Polynomial.C Polynomial.X A).det

theorem det_mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    (mixM κ u A).det = (detPoly A).eval₂ κ u := by
  rw [detPoly, ← Polynomial.coe_eval₂RingHom, RingHom.map_det, RingHom.mapMatrix_apply, mixM_map]
  congr 2
  · ext a; simp
  · simp

theorem mixM_zero {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 0 A = 1 := by
  simp [mixM]

theorem mixM_one {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 1 A = A := by
  simp [mixM]

theorem detPoly_ne_zero {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : detPoly A ≠ 0 := by
  intro h
  have := det_mixM (RingHom.id K) 0 A
  rw [h, mixM_zero, Polynomial.eval₂_zero, det_one] at this
  exact one_ne_zero this

end GlobalTheory.GenFrame

namespace GlobalTheory.GenFrame

open Matrix Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions GlobalTheory.CxPts GlobalTheory.LieMet

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_co_eq {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (hT : ∀ τ, IsUnit (T τ).det) :
    ∃ g : EigFrame Z φ x, ∀ τ, f.co g τ = T τ := by
  have hsum : ∀ τ (a : Fin (Dw.mult τ) → R),
      ∑ i, a i • ∑ j, T τ j i • f.vec τ j = ∑ j, (T τ *ᵥ a) j • f.vec τ j := by
    intro τ a
    simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  let g : EigFrame Z φ x := EigFrame.ofVec (fun τ i => ∑ j, T τ j i • f.vec τ j)
    (fun τ i a => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _)
    (fun τ w hw => by
      obtain ⟨b, hb, hbu⟩ := f.existsUnique_sum τ w hw
      refine ⟨(T τ)⁻¹ *ᵥ b, ?_, fun a ha => ?_⟩
      · show w = ∑ i, ((T τ)⁻¹ *ᵥ b) i • ∑ j, T τ j i • f.vec τ j
        rw [hsum, mulVec_mulVec, mul_nonsing_inv _ (hT τ), one_mulVec]
        exact hb
      · have h1 : T τ *ᵥ a = b := hbu _ (ha.trans (hsum τ a))
        rw [← h1, mulVec_mulVec, nonsing_inv_mul _ (hT τ), one_mulVec])
  refine ⟨g, fun τ => EigFrame.co_eq fun i => ?_⟩
  exact (isComb_iff (f.vec τ) (fun a => T τ a i) (∑ j, T τ j i • f.vec τ j)).2 rfl

theorem co_eq_one {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f₀ f₁ f₂ : EigFrame Z φ x}
    {τ : E →+* ℂ} (h : f₀.co f₁ τ = f₀.co f₂ τ) : f₁.co f₂ τ = 1 := by
  rw [← f₁.co_mul f₀ f₂ τ, ← h, f₁.co_mul f₀ f₁ τ, f₁.co_self τ]

theorem tri_of_co_eq_one {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'}
    (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f') (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) (h : ∀ τ, f'.co g τ = 1) : f.Tri ψ g 1 := by
  refine ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, by simp [h], fun k hk => by
    simp [h, Matrix.one_apply_ne hk.ne'], ?_⟩⟩
  rw [← funext (hf τ)]
  exact f'.co_spec g τ i

theorem isMap_id {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) :
    (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (RingHom.id R) f := fun τ i => by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  rw [h1, Category.id_comp]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenFrame


open Matrix in
theorem GlobalTheory.GenFrame.exists_generic_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x) (L : Type) [Field L] (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) → ∀ (xL : Sp L ⟶ Z.X), xL = spMap ι ≫ x → ∃ gL : EigFrame Z (ι.comp χ) xL, ∀ (V : Type) [CommRing V] [IsLocalRing V] (ν : V →+* L) (ιV : K →+* V) (r : V →+* K) (sV : V), ν.comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V → ν sV = s → (r sV = 0 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g tk) ∧ (r sV = 1 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g' tk) := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ χ x g g' L _ ι s hs xL hxL
  have hP : ∀ τ, (GlobalTheory.GenFrame.detPoly (g.co g' τ)).eval₂ ι s ≠ 0 := fun τ h =>
    GlobalTheory.GenFrame.detPoly_ne_zero _ (hs _ h)
  obtain ⟨gB, hgB⟩ := g.exists_isMap ι (φ' := ι.comp χ) rfl hxL
  obtain ⟨gL, hgL⟩ := GlobalTheory.GenFrame.exists_co_eq gB (fun τ => GlobalTheory.GenFrame.mixM ι s (g.co g' τ)) fun τ => by
    rw [GlobalTheory.GenFrame.det_mixM]
    exact (hP τ).isUnit
  refine ⟨gL, fun V _ _ ν ιV r sV hνι hrι hker hνs => ?_⟩
  obtain ⟨gVB, hgVB⟩ := g.exists_isMap ιV (φ' := ιV.comp χ) (x' := spMap ιV ≫ x) rfl rfl
  have hxν : xL = spMap ν ≫ spMap ιV ≫ x := by
    rw [hxL, ← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hνι]
  have hxr : x = spMap r ≫ spMap ιV ≫ x := by
    rw [← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hrι]
    exact (Category.id_comp x).symm.trans (congrArg (· ≫ x) (Spec.map_id _).symm)
  have hφν : ι.comp χ = ν.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hνι]
  have hφr : χ = r.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hrι]; rfl
  have hBν : gVB.IsMap ν gB := fun τ i => by
    rw [hgB τ i, hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hνι]
  have hBr : gVB.IsMap r g := fun τ i => by
    rw [hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hrι]
    exact (GlobalTheory.GenFrame.isMap_id g τ i)

  have main : ∀ (hu : ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det),
      ∃ gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x), gV.Tri ν gL 1 ∧
        ∃ gVr : EigFrame Z χ x, (_root_.GlobalTheory.ShFam.EigFrame.IsMap gV) r gVr ∧ ∀ τ, g.co gVr τ = GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ) := by
    intro hu
    obtain ⟨gV, hgV⟩ := GlobalTheory.GenFrame.exists_co_eq gVB (fun τ => GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)) hu
    obtain ⟨gVν, hgVν⟩ := gV.exists_isMap ν hφν hxν
    obtain ⟨gVr, hgVr⟩ := gV.exists_isMap r hφr hxr
    refine ⟨gV, GlobalTheory.GenFrame.tri_of_co_eq_one hgVν hφν hxν fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := gB) ?_, gVr, hgVr,
      fun τ => ?_⟩
    · rw [hBν.co τ hgVν hxν, hgV, hgL, GlobalTheory.GenFrame.mixM_map, hνι, hνs]
    · rw [hBr.co τ hgVr hxr, hgV, GlobalTheory.GenFrame.mixM_map, hrι]
  have hunit : (∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det ≠ 0) →
      ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det := fun h τ => by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hker, RingHom.mem_ker]
    exact h τ
  have hr : ∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det =
      (GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ)).det := fun τ => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.GenFrame.mixM_map, hrι]
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h0, GlobalTheory.GenFrame.mixM_zero, det_one]; exact one_ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h0, GlobalTheory.GenFrame.mixM_zero, g.co_self]
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h1, GlobalTheory.GenFrame.mixM_one]; exact (g.isUnit_det_co g' τ).ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h1, GlobalTheory.GenFrame.mixM_one]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFrameTranscendentalSpecialisingTwoStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFrame_transcendental_specialising_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x) (L : Type) [Field L] (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) → ∀ (xL : Sp L ⟶ Z.X), xL = spMap ι ≫ x → ∃ gL : EigFrame Z (ι.comp χ) xL, ∀ (V : Type) [CommRing V] [IsLocalRing V] (ν : V →+* L) (ιV : K →+* V) (r : V →+* K) (sV : V), ν.comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V → ν sV = s → (r sV = 0 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g tk) ∧ (r sV = 1 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g' tk) := by
  first | exact @GlobalTheory.GenFrame.exists_generic_frame | exact GlobalTheory.GenFrame.exists_generic_frame | (intros; apply GlobalTheory.GenFrame.exists_generic_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgClosedTranscendentalSpecialisingEverywh
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgClosedTranscendentalSpecialisingEverywh
open Polynomial IsLocalRing

namespace GlobalTheory

theorem genval_descent {K : Type} [Field K] {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ιV : K →+* V) (sV v : V) (a : K) (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0) :
    ∀ n : ℕ, ∀ p : Polynomial (Polynomial K), p.leadingCoeff.natDegree = n → p ≠ 0 →
      p.eval₂ (eval₂RingHom ιV sV) v = 0 →
      ∃ q : Polynomial K, q ≠ 0 ∧ q.eval₂ ((residue V).comp ιV) (residue V v) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp hpv
  by_cases hq : p.map (evalRingHom a) = 0
  · have hdvd : C (X - C a) ∣ p := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      rw [dvd_iff_isRoot]
      have := congrArg (fun q => q.coeff i) hq
      simpa [coeff_map] using this
    obtain ⟨p', rfl⟩ := hdvd
    have hp' : p' ≠ 0 := by rintro rfl; simp at hp
    have hXa : (X - C a : Polynomial K) ≠ 0 := X_sub_C_ne_zero a
    refine ih p'.leadingCoeff.natDegree ?_ p' rfl hp' ?_
    · rw [← hn, leadingCoeff_mul, leadingCoeff_C,
        natDegree_mul hXa (leadingCoeff_ne_zero.mpr hp'), natDegree_X_sub_C]
      omega
    · rw [eval₂_mul, eval₂_C] at hpv
      have h2 : (eval₂RingHom ιV sV) (X - C a) = sV - ιV a := by simp
      rw [h2] at hpv
      exact (mul_eq_zero.mp hpv).resolve_left hne
  · refine ⟨_, hq, ?_⟩
    have h1 : (residue V).comp (eval₂RingHom ιV sV) =
        ((residue V).comp ιV).comp (evalRingHom a) := by
      apply Polynomial.ringHom_ext
      · intro c; simp
      · have : residue V sV = residue V (ιV a) := by
          rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
        simpa using this
    rw [eval₂_map, ← h1, ← hom_eval₂, hpv, map_zero]

theorem genval_residue_bij {K : Type} [Field K] [IsAlgClosed K] {L : Type} [Field L]
    (V : ValuationSubring L) (ιV : K →+* V) (sV : V) (a : K)
    (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0)
    (halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
      p.eval₂ (eval₂RingHom ιV sV) v = 0) :
    Function.Bijective ((residue V).comp ιV) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro x
  obtain ⟨v, rfl⟩ := residue_surjective x
  obtain ⟨p, hp, hpv⟩ := halg v
  obtain ⟨q, hq, hqv⟩ := genval_descent ιV sV v a hsa hne _ p rfl hp hpv
  refine ⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, ?_⟩
  rw [eval₂_mul, hqv, zero_mul]

theorem genval (K : Type) [Field K] [IsAlgClosed K] : ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by
  let L := AlgebraicClosure (RatFunc K)
  let φ0 : Polynomial K →+* L := algebraMap (Polynomial K) L
  have hφ0 : Function.Injective φ0 := by
    have : φ0 = (algebraMap (RatFunc K) L).comp (algebraMap (Polynomial K) (RatFunc K)) :=
      IsScalarTower.algebraMap_eq _ _ _
    rw [this]
    exact (algebraMap (RatFunc K) L).injective.comp (IsFractionRing.injective _ _)
  let ι : K →+* L := φ0.comp C
  let s : L := φ0 X
  have hev : ∀ P : Polynomial K, P.eval₂ ι s = φ0 P := by
    intro P
    have : eval₂RingHom ι s = φ0 := Polynomial.ringHom_ext (fun c => by simp [ι]) (by simp [s])
    exact congrArg (fun f => f P) this
  refine ⟨L, inferInstance, inferInstance, ι, s, ?_, ?_⟩
  · intro P hP
    rw [hev] at hP
    exact hφ0 (by rw [hP, map_zero])
  · intro a
    let e : Polynomial K ≃+* φ0.range := RingEquiv.ofBijective φ0.rangeRestrict
      ⟨fun x y h => hφ0 (congrArg Subtype.val h), φ0.rangeRestrict_surjective⟩
    let ψ : φ0.range →+* K := (evalRingHom a).comp e.symm.toRingHom
    obtain ⟨V, hAV, hI⟩ :=
      Ideal.image_subset_nonunits_valuationSubring (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
    have hmemA : ∀ P, φ0 P ∈ V := fun P => hAV ⟨P, rfl⟩
    let ιV : K →+* V := ι.codRestrict V (fun c => hmemA (C c))
    let sV : V := ⟨s, hmemA X⟩
    have hsaL : s - ι a ∈ V.nonunits := by
      apply hI
      refine ⟨φ0.rangeRestrict (X - C a), ?_, ?_⟩
      · rw [SetLike.mem_coe, RingHom.mem_ker]
        have : e.symm (φ0.rangeRestrict (X - C a)) = X - C a :=
          e.symm_apply_apply (X - C a)
        show evalRingHom a (e.symm (φ0.rangeRestrict (X - C a))) = 0
        rw [this]
        simp
      · simp [ι, s]
    have hsa : sV - ιV a ∈ maximalIdeal V := by
      have hsaL' : s - ι a ∈ ((↑) : V → L) '' (maximalIdeal V : Set V) := by
        rw [ValuationSubring.image_maximalIdeal]; exact hsaL
      obtain ⟨w, hw, hw'⟩ := hsaL'
      have heq : sV - ιV a = w := by
        apply Subtype.ext
        exact hw'.symm
      rw [heq]
      exact hw
    have hne : sV - ιV a ≠ 0 := by
      intro h
      have h1 := congrArg Subtype.val h
      have h2 : φ0 (X - C a) = 0 := by simpa [ι, s, sV, ιV] using h1
      exact X_sub_C_ne_zero a (hφ0 (by rw [h2, map_zero]))
    have hcomp : (algebraMap V L).comp (eval₂RingHom ιV sV) = φ0 :=
      Polynomial.ringHom_ext (fun c => by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]; rfl)
        (by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]; rfl)
    have halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
        p.eval₂ (eval₂RingHom ιV sV) v = 0 := by
      intro v
      have h1 : IsAlgebraic (Polynomial K) (v : L) :=
        (IsFractionRing.isAlgebraic_iff (Polynomial K) (RatFunc K) L).mpr
          (Algebra.IsAlgebraic.isAlgebraic _)
      obtain ⟨p, hp, hpv⟩ := h1
      refine ⟨p, hp, ?_⟩
      apply IsFractionRing.injective V L
      rw [hom_eval₂, hcomp, map_zero]
      exact hpv
    have hbij := genval_residue_bij V ιV sV a hsa hne halg
    let E := RingEquiv.ofBijective _ hbij
    have hres : residue V sV = E a := by
      show residue V sV = residue V (ιV a)
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
    refine ⟨V, ιV, E.symm.toRingHom.comp (residue V), sV, ?_, ?_, ?_, rfl, ?_⟩
    · exact RingHom.ext fun c => rfl
    · ext c
      exact E.symm_apply_apply c
    · ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        map_eq_zero_iff _ E.symm.injective, residue_eq_zero_iff]
    · show E.symm (residue V sV) = a
      rw [hres, E.symm_apply_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgClosedTranscendentalSpecialisingEverywhStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosed_transcendental_specialising_everywhere : ∀ (K : Type) [Field K] [IsAlgClosed K], ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by
  first | exact @GlobalTheory.genval | exact GlobalTheory.genval | (intros; apply GlobalTheory.genval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlag
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.FlagFibre

theorem sp_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (a : B →+* C') (b : A →+* B) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]; exact Spec.map_id _

theorem carries_every : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U), ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ i K _ _ χ x hx g g' p hp hc
  obtain ⟨L, _, _, ι, s, hs, hV⟩ := GlobalTheory.T.exists_algClosed_transcendental_specialising_everywhere K
  obtain ⟨gL, hgL⟩ := GlobalTheory.T.exists_genericFrame_transcendental_specialising_two E H Dw l Xo c O β Z K χ (x ≫ genι Z) g g' L ι s hs ((spMap ι ≫ x) ≫ genι Z)
    (Category.assoc _ _ _)
  have hxL : (spMap ι ≫ x) ≫ genStr Z = spMap (ι.comp χ) := by
    rw [Category.assoc, hx, sp_comp]
  obtain ⟨⟨j, pL⟩, ⟨hpL, hcL⟩, -⟩ := Φ.lifts L (ι.comp χ) (spMap ι ≫ x) hxL gL
  have spec : ∀ (a : K) (b : EigFrame Z χ (x ≫ genι Z)), (∀ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K)
      (sV : V), (algebraMap V L).comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V →
      algebraMap V L sV = s → r sV = a → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x ≫ genι Z))
        (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ),
        gV.Tri (algebraMap V L) gL tL ∧ gV.Tri r b tk) →
      ∃ p' : Sp K ⟶ (Φ.C j).Y.X, p' ≫ (Φ.C j).π = x ∧ (Φ.C j).Carries p' b := by
    intro a b hb
    obtain ⟨V, ιV, r, sV, h1, h2, h3, h4, h5⟩ := hV a
    obtain ⟨gV, tL, tk, hTL, hTk⟩ := hb V ιV r sV h1 h2 h3 h4 h5
    have hpL' : pL ≫ (Φ.C j).π = spMap (algebraMap V L) ≫ (spMap ιV ≫ x) := by
      rw [hpL, ← Category.assoc, ← sp_comp, h1]
    obtain ⟨q, hq1, hq2⟩ := GlobalTheory.T.exists_flagComponent_point_lift_valuationRing E H Dw l Xo c O β Z F e (Φ.C j) V L (spMap ιV ≫ x) pL hpL'
    have hc' : (Φ.C j).Carries (spMap (algebraMap V L) ≫ q) gL := by rw [hq2]; exact hcL
    have hxV : spMap ιV ≫ x ≫ genι Z = q ≫ (Φ.C j).π ≫ genι Z := by
      rw [← Category.assoc q, hq1, Category.assoc]
    refine ⟨spMap r ≫ q, ?_, GlobalTheory.T.carriedFrames_specialise_flagComponent_localRing E H Dw l Xo c O β Z F e (Φ.C j) V L (algebraMap V L)
      (IsFractionRing.injective V L) K r h3 q (ιV.comp χ) _ hxV gV (ι.comp χ) _ gL tL hTL hc' χ _ b tk hTk⟩
    rw [Category.assoc, hq1, ← Category.assoc, ← sp_comp, h2, sp_id, Category.id_comp]
  obtain ⟨p₀, hp₀, hc₀⟩ := spec 0 g fun V ιV r sV h1 h2 h3 h4 h5 => (hgL V _ ιV r sV h1 h2 h3 h4).1 h5
  obtain ⟨p₁, hp₁, hc₁⟩ := spec 1 g' fun V ιV r sV h1 h2 h3 h4 h5 => (hgL V _ ιV r sV h1 h2 h3 h4).2 h5
  obtain ⟨_, -, hu⟩ := Φ.lifts K χ x hx g
  have hij : i = j := congrArg Sigma.fst ((hu ⟨i, p⟩ ⟨hp, hc⟩).trans (hu ⟨j, p₀⟩ ⟨hp₀, hc₀⟩).symm)
  subst hij
  exact ⟨p₁, hp₁, hc₁⟩

end GlobalTheory.FlagFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlagStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U), ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g' := by
  first | exact @GlobalTheory.FlagFibre.carries_every | exact GlobalTheory.FlagFibre.carries_every | (intros; apply GlobalTheory.FlagFibre.carries_every <;> assumption)
end

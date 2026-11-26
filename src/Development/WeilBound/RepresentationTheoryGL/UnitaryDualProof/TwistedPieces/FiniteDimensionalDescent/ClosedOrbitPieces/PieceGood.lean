module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.Rdata
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RatioOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Transfer
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.RqLift
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

def Iq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Ideal A[X] :=
  Ideal.span {χ.map (algebraMap k A)} ⊔
    Ideal.span {y | ∃ r ∈ (Ideal.span {χ.map (algebraMap k A)}).radical, y = r ^ q}

abbrev Rq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Type _ := A[X] ⧸ Iq A χ q

theorem rq_fin [FiniteDimensional k A] (χ : k[X]) (hχ : χ.Monic) (q : ℕ) :
    FiniteDimensional k (Rq A χ q) := by
  classical
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have : Module.Finite A (A[X] ⧸ Ideal.span {χ.map (algebraMap k A)}) := (AdjoinRoot.powerBasis' hmon).finite
  have hle : Ideal.span {χ.map (algebraMap k A)} ≤ Iq A χ q := le_sup_left
  let φ := Ideal.Quotient.factorₐ A hle
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ P, rfl⟩
  have : Module.Finite A (Rq A χ q) := Module.Finite.of_surjective φ.toLinearMap hsurj
  exact Module.Finite.trans A (Rq A χ q)

theorem rq_nil (χ : k[X]) (q : ℕ) (r : Rq A χ q) (hr : IsNilpotent r) : r ^ q = 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨m, hm⟩ := hr
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [pow_zero]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, Ideal.zero_mem _, (pow_zero _).symm⟩)
  · have hle : Iq A χ q ≤ (Ideal.span {χ.map (algebraMap k A)}).radical := by
      refine sup_le Ideal.le_radical ?_
      rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      exact Ideal.pow_mem_of_mem _ hr q hq
    have hP : P ∈ (Ideal.span {χ.map (algebraMap k A)}).radical :=
      (Ideal.radical_isRadical _) ⟨m, hle hm⟩
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, rfl⟩)
private theorem isPrincipalIdealRing_pi {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommRing (R i)]
    (hR : ∀ i, IsPrincipalIdealRing (R i)) : IsPrincipalIdealRing (∀ i, R i) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun J => ?_⟩
  have hsurj : ∀ i, Function.Surjective (Pi.evalRingHom R i) := fun i y => ⟨Pi.single i y, by simp⟩
  have hgen : ∀ i, ∃ a : R i, J.map (Pi.evalRingHom R i) = Ideal.span {a} := fun i => by
    obtain ⟨a, ha⟩ := (hR i).principal (J.map (Pi.evalRingHom R i))
    exact ⟨a, ha⟩
  choose g hg using hgen
  have hgJ : g ∈ J := by
    have hpre : ∀ i, ∃ h ∈ J, h i = g i := fun i => by
      have hm : g i ∈ J.map (Pi.evalRingHom R i) := by
        rw [hg i]
        exact Ideal.subset_span rfl
      obtain ⟨h, hh, he⟩ := (Ideal.mem_map_iff_of_surjective _ (hsurj i)).mp hm
      exact ⟨h, hh, he⟩
    choose h hh he using hpre
    have e : g = ∑ i, Pi.single i (1 : R i) * h i := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_mul, he]
      · intro i _ hij
        rw [Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [e]
    exact J.sum_mem (fun i _ => J.mul_mem_left _ (hh i))
  refine ⟨g, le_antisymm ?_ ?_⟩
  · intro x hx
    have hc : ∀ i, ∃ c : R i, c * g i = x i := fun i => by
      have hm : x i ∈ J.map (Pi.evalRingHom R i) := Ideal.mem_map_of_mem _ hx
      rw [hg i] at hm
      exact Ideal.mem_span_singleton'.mp hm
    choose c hc using hc
    exact Ideal.mem_span_singleton'.mpr ⟨c, funext hc⟩
  · exact (Ideal.span_le).mpr (Set.singleton_subset_iff.mpr hgJ)

theorem rq_pir [FiniteDimensional k A] [IsReduced A] (χ : k[X]) (q : ℕ) :
    IsPrincipalIdealRing (Rq A χ q) := by
  classical
  have hA : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hPI : IsPrincipalIdealRing ((I : MaximalSpectrum A) → (A ⧸ I.asIdeal)[X]) :=
    isPrincipalIdealRing_pi _ (fun I => by
      have := I.isMaximal
      letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field _
      exact EuclideanDomain.instIsPrincipalIdealRing)
  have hPI' : IsPrincipalIdealRing ((∀ I : MaximalSpectrum A, A ⧸ I.asIdeal)[X]) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.piEquiv (fun I : MaximalSpectrum A => A ⧸ I.asIdeal)).symm
      (Polynomial.piEquiv _).symm.surjective
  have hAX : IsPrincipalIdealRing A[X] :=
    IsPrincipalIdealRing.of_surjective (Polynomial.mapEquiv (IsArtinianRing.equivPi A).symm.toRingEquiv)
      (Polynomial.mapEquiv _).surjective
  exact IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk (Iq A χ q)) Ideal.Quotient.mk_surjective

theorem rq_rep (χ : k[X]) (hχ : χ.Monic) (q d : ℕ) (hd : χ.natDegree ≤ d) (r : Rq A χ q) :
    ∃ a : Fin d → A, r = Ideal.Quotient.mk _ (∑ l : Fin d, C (a l) * X ^ (l : ℕ)) := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, by congr 1; exact Subsingleton.elim _ _⟩
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have hmem : P - P %ₘ χ.map (algebraMap k A) ∈ Iq A χ q := by
    have e : P - P %ₘ χ.map (algebraMap k A) = χ.map (algebraMap k A) * (P /ₘ χ.map (algebraMap k A)) := by
      have h := modByMonic_add_div P (χ.map (algebraMap k A))
      linear_combination -h
    rw [e]
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hdeg : (P %ₘ χ.map (algebraMap k A)).degree < d :=
    calc (P %ₘ χ.map (algebraMap k A)).degree < (χ.map (algebraMap k A)).degree := degree_modByMonic_lt _ hmon
      _ ≤ (χ.map (algebraMap k A)).natDegree := degree_le_natDegree
      _ ≤ d := by exact_mod_cast natDegree_map_le.trans hd
  refine ⟨fun l => (P %ₘ χ.map (algebraMap k A)).coeff l, ?_⟩
  rw [Ideal.Quotient.eq.mpr hmem]
  congr 1
  rw [show (∑ l : Fin d, C ((P %ₘ χ.map (algebraMap k A)).coeff (l : ℕ)) * X ^ (l : ℕ)) =
      ∑ i ∈ Finset.range d, C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i from
    (Finset.sum_range (fun i => C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i)).symm]
  by_cases h0 : P %ₘ χ.map (algebraMap k A) = 0
  · rw [h0]
    simp
  · have h := as_sum_range' _ d ((natDegree_lt_iff_degree_lt h0).mpr hdeg)
    simp only [← C_mul_X_pow_eq_monomial] at h
    exact h

theorem rq_lift {B : Type*} [Ring B] [Algebra k B] (ι : A →ₐ[k] B) (x : B) (hc : ∀ a, Commute (ι a) x)
    (χ : k[X]) (hχ : aeval x χ = 0) (q : ℕ)
    (hq : ∀ P : A[X], IsNilpotent (P.eval₂ ι.toRingHom x) → (P.eval₂ ι.toRingHom x) ^ q = 0) :
    ∃ ρ : Rq A χ q →ₐ[k] B, ∀ P : A[X], ρ (Ideal.Quotient.mk _ P) = P.eval₂ ι.toRingHom x := by
  let f : A[X] →+* B := Polynomial.eval₂RingHom' ι.toRingHom x hc
  have hf : ∀ P : A[X], f P = P.eval₂ ι.toRingHom x := fun P => rfl
  have hχ0 : f (χ.map (algebraMap k A)) = 0 := by
    rw [hf, Polynomial.eval₂_map]
    have e : ι.toRingHom.comp (algebraMap k A) = algebraMap k B := by
      ext c
      exact ι.commutes c
    rw [e, ← Polynomial.aeval_def, hχ]
  have hspan : ∀ P ∈ Ideal.span {χ.map (algebraMap k A)}, f P = 0 := by
    intro P hP
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp hP
    rw [map_mul, hχ0, mul_zero]
  have hle : Iq A χ q ≤ RingHom.ker f := by
    unfold Iq
    apply sup_le
    · intro P hP
      exact (RingHom.mem_ker).mpr (hspan P hP)
    · rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨m, hm⟩ := hr
      have hnil : IsNilpotent (r.eval₂ ι.toRingHom x) := ⟨m, by rw [← hf, ← map_pow, hspan _ hm]⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, hf]
      exact hq r hnil
  let F : A[X] →ₐ[k] B :=
    { f with
      commutes' := fun c => by
        show Polynomial.eval₂ ι.toRingHom x (algebraMap k A[X] c) = algebraMap k B c
        rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
        exact ι.commutes c }
  exact ⟨Ideal.Quotient.liftₐ _ F (fun a ha => hle ha), fun P => rfl⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RootsFinite
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

open Polynomial PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_pow' {N : ℕ} (g : GL (Fin N) k) (y : Matrix (Fin N) (Fin N) k) (n : ℕ) :
    (g.val * y * g⁻¹.val) ^ n = g.val * y ^ n * g⁻¹.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem roots_finite {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]} (hχ : χ ≠ 0) :
    {c : Matrix (Fin N) (Fin N) k | c ∈ Z ∧ aeval c χ = 0}.Finite := by
  letI : CommRing Z := { (inferInstance : Ring ↥Z) with mul_comm := fun a b => Subtype.ext (hZ.1 a a.2 b b.2) }
  haveI : IsReduced Z := hZ.2
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  have hT : {c : Z | aeval c χ = 0}.Finite := by
    refine Set.Finite.of_finite_image ?_ (IsArtinianRing.equivPi Z).injective.injOn
    refine (Set.Finite.pi (t := fun I : MaximalSpectrum Z => χ.rootSet (Z ⧸ I.asIdeal))
      fun I => χ.rootSet_finite _).subset ?_
    rintro _ ⟨c, hc, rfl⟩
    refine Set.mem_univ_pi.2 fun I => ?_
    rw [mem_rootSet_of_ne hχ, IsArtinianRing.equivPi_apply]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I.asIdeal) c χ
    rw [show aeval c χ = 0 from hc, map_zero] at h
    exact h
  refine (hT.image Subtype.val).subset ?_
  rintro c ⟨hc, h0⟩
  refine ⟨⟨c, hc⟩, ?_, rfl⟩
  show aeval (⟨c, hc⟩ : Z) χ = 0
  exact Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact h0)

theorem root_of_nil {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]}
    {x c : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hc : c ∈ Z) (hχx : aeval x χ = 0)
    (hn : IsNilpotent (x - c)) : aeval c χ = 0 := by
  have hxc : x * c = c * x := (hx c hc).symm
  have hcomm : ∀ a ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxc
    · exact hxc.symm
    · rfl
  let A := Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))
  haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin k (fun a ha b hb _ => hcomm a ha b hb)
  letI : CommRing A := { (inferInstance : Ring A) with mul_comm := fun a b => mul_comm' a b }
  let xa : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  let ca : A := ⟨c, Algebra.subset_adjoin (by simp)⟩
  have hna : IsNilpotent (xa - ca) := (IsNilpotent.map_iff (f := A.val) Subtype.val_injective).1 hn
  have h1 := isNilpotent_aeval_sub_of_isNilpotent_sub χ hna
  have h2 : aeval xa χ = 0 := Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact hχx)
  have h3 : IsNilpotent (aeval ca χ) := by simpa [h2] using h1.neg
  have h4 : IsNilpotent (aeval c χ) := by
    have := h3.map A.val
    rwa [← Polynomial.aeval_algHom_apply] at this
  let c' : Z := ⟨c, hc⟩
  have h5 : IsNilpotent (aeval c' χ) := by
    refine (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 ?_
    rw [← Polynomial.aeval_algHom_apply]
    exact h4
  have h6 : aeval c' χ = 0 := by
    haveI : IsReduced Z := hZ.2
    exact h5.eq_zero
  have h7 := congrArg Subtype.val h6
  rwa [Polynomial.aeval_subalgebra_coe] at h7


variable (k) in
theorem pieceGood_of (hF : PositivityTheory.PfBern.Frob.FrobeniusReciprocity) (hS : Sect k) (hP : PieceTop k) (hD : Dich k)
    (hT : Transfer k) : PieceGood k := by
  classical
  intro p _ _ hU N q Z hZ hq hR hB χ
  by_cases hχ : χ.Monic ∧ χ.natDegree = N
  swap
  · refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun x _ hc => ?_⟩, fun i => i.elim0⟩
    exact (hχ ⟨hc ▸ x.charpoly_monic, by rw [← hc, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩).elim
  obtain ⟨D⟩ := hS p N q Z hZ hq hR hB χ hχ.1 hχ.2
  have hfin := roots_finite hZ hχ.1.ne_zero
  have hrt : ∀ j : Fin hfin.toFinset.card, (hfin.toFinset.equivFin.symm j).1 ∈ Z ∧
      aeval (hfin.toFinset.equivFin.symm j).1 χ = 0 := fun j => hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm j).2
  let rt : Fin hfin.toFinset.card → Matrix (Fin N) (Fin N) k := fun j => (hfin.toFinset.equivFin.symm j).1
  have rt_inj : Function.Injective rt := fun j j' h => hfin.toFinset.equivFin.symm.injective (Subtype.ext h)
  have hred : ∀ c ∈ Z, IsNilpotent c → c = 0 := fun c hc hn => by
    have h : IsNilpotent (⟨c, hc⟩ : Z) := (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 hn
    haveI : IsReduced Z := hZ.2
    exact congrArg Subtype.val h.eq_zero
  have hcz : ∀ c ∈ Z, ∀ x ∈ Bz Z, x - c ∈ Bz Z := fun c hc x hx a ha => by
    rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
  let e := (finFunctionFinEquiv (m := N + 1) (n := D.m)).symm
  let τ : Fin ((N + 1) ^ D.m) → Fin D.m → ℕ := fun i t => (e i t : ℕ)
  have τ_inj : Function.Injective τ := fun i j h => e.injective (funext fun t => Fin.ext (congrFun h t))
  let bad : Fin ((N + 1) ^ D.m) → Prop := fun i => ∃ x₀ ∈ piece D (τ i), mu (Sx D x₀) < mu Z
  let G : Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card) → Set (Matrix (Fin N) (Fin N) k) := fun is =>
    if bad is.1 then (if is.2 = none then piece D (τ is.1) else ∅)
    else is.2.elim ∅ (fun j => {x | x ∈ piece D (τ is.1) ∧ (x - rt j) ^ q = 0})
  have hsub : ∀ is x, x ∈ G is → x ∈ piece D (τ is.1) := by
    rintro ⟨i, s⟩ x hx
    simp only [G] at hx
    split_ifs at hx
    · exact hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j => exact hx.1
  have huniq : ∀ is js x, x ∈ G is → x ∈ G js → is = js := by
    rintro ⟨i, s⟩ ⟨j, t⟩ x hx hy
    have hij : i = j := τ_inj ((hsub _ x hx).2.2.symm.trans (hsub _ x hy).2.2)
    subst hij
    have hxB : x ∈ Bz Z := (hsub _ x hx).1
    simp only [G] at hx hy
    by_cases hb : bad i
    · rw [if_pos hb] at hx hy
      split_ifs at hx hy with h1 h2
      · rw [h1, h2]
      · simp at hy
      · simp at hx
      · simp at hx
    · rw [if_neg hb] at hx hy
      cases s with
      | none => simp at hx
      | some a =>
        cases t with
        | none => simp at hy
        | some b =>
          have ha : IsNilpotent (x - rt a) := ⟨q, hx.2⟩
          have hb' : IsNilpotent (x - rt b) := ⟨q, hy.2⟩
          have hca : Commute (rt a) x := hxB _ (hrt a).1
          have hcb : Commute (rt b) x := hxB _ (hrt b).1
          have hab : Commute (rt b) (rt a) := hZ.1 _ (hrt b).1 _ (hrt a).1
          have hcomm : Commute (x - rt b) (x - rt a) :=
            ((Commute.refl x).sub_right hca.symm).sub_left (hcb.sub_right hab)
          have hn : IsNilpotent (rt a - rt b) := by
            have := hcomm.isNilpotent_sub hb' ha
            rwa [sub_sub_sub_cancel_left] at this
          have h0 := hred _ (Z.sub_mem (hrt a).1 (hrt b).1) hn
          rw [rt_inj (sub_eq_zero.1 h0)]
  have hclosed : ∀ is, IsClosed (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs
    · exact (hP N q Z hZ χ D (τ i)).1
    · exact isClosed_empty
    · cases s with
      | none => exact isClosed_empty
      | some j =>
        exact (hP N q Z hZ χ D (τ i)).1.inter
          (isClosed_eq ((continuous_id.sub continuous_const).pow q) continuous_const)
  have hinvar : ∀ is, ∀ g ∈ Gz Z, ∀ x ∈ G is, g.val * x * g⁻¹.val ∈ G is := by
    rintro ⟨i, s⟩ g hg x hx
    have hP2 := (hP N q Z hZ χ D (τ i)).2.1 g hg
    simp only [G] at hx ⊢
    split_ifs at hx ⊢
    · exact hP2 x hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j =>
        refine ⟨hP2 x hx.1, ?_⟩
        have e1 : g.val * x * g⁻¹.val - rt j = g.val * (x - rt j) * g⁻¹.val := by
          rw [mul_sub, sub_mul, ← hg (rt j) (hrt j).1, mul_assoc (rt j), Units.mul_inv, mul_one]
        rw [e1, conj_pow', hx.2, mul_zero, zero_mul]
  have hcover : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ is, x ∈ G is := by
    intro x hx hc
    have hle : ∀ t, typ D x t < N + 1 := fun t =>
      Nat.lt_succ_of_le ((Matrix.rank_le_width _).trans (by simp))
    let i := e.symm fun t => ⟨typ D x t, hle t⟩
    have hxp : x ∈ piece D (τ i) :=
      ⟨hx, by rw [← hc]; exact Matrix.aeval_self_charpoly x, by funext t; simp [τ, i]⟩
    by_cases hb : bad i
    · refine ⟨(i, none), ?_⟩
      simp only [G, if_pos hb, if_true]
      exact hxp
    · rcases hD N q Z hZ χ D (τ i) x hxp with h | ⟨c, hc, hn⟩
      · exact (hb ⟨x, hxp, h⟩).elim
      · have hroot : aeval c χ = 0 := root_of_nil hZ hx hc hxp.2.1 hn
        have hmem : c ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨hc, hroot⟩
        refine ⟨(i, some (hfin.toFinset.equivFin ⟨c, hmem⟩)), ?_⟩
        have hrtc : rt (hfin.toFinset.equivFin ⟨c, hmem⟩) = c := by simp [rt]
        simp only [G, if_neg hb, Option.elim_some]
        refine ⟨hxp, ?_⟩
        rw [hrtc]
        exact hB _ (hcz c hc x hx) hn
  have hgood : ∀ is, Good Z (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs with h1
    · obtain ⟨x₀, hx₀, hlt⟩ := h1
      exact Or.inr ⟨N, Sx D x₀, (hP N q Z hZ χ D (τ i)).2.2 x₀ hx₀, hlt, hT hF p hU N q Z hZ χ D (τ i) x₀ hx₀⟩
    · exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
    · cases s with
      | none => exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
      | some j => exact Or.inl ⟨rt j, (hrt j).1, fun x hx => ⟨q, hx.2⟩⟩
  let eqv := Fintype.equivFin (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card))
  refine ⟨Fintype.card (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card)), fun i => G (eqv.symm i),
    ⟨fun i => ⟨hclosed _, fun x hx => (hsub _ x hx).1, hinvar _⟩,
      fun i j hij => Set.disjoint_left.2 fun x h1 h2 => hij (eqv.symm.injective (huniq _ _ x h1 h2)),
      fun x hx hc => ?_⟩, fun i => hgood _⟩
  obtain ⟨is, his⟩ := hcover x hx hc
  exact ⟨eqv is, by simpa using his⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TwFin
noncomputable section

open Matrix Polynomial Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece


open ValuativeRel in
theorem twFin (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p c : ℕ) [Fact p.Prime] [CharP k p] : FiniteDimensional k (Tw k p c) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  have hc : CompleteSpace k := inferInstance
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  have : CompleteSpace k := hc
  letI : TopologicalSpace (Tw k p c) := inferInstanceAs (TopologicalSpace k)
  have : IsTopologicalAddGroup (Tw k p c) := inferInstanceAs (IsTopologicalAddGroup k)
  have : T2Space (Tw k p c) := inferInstanceAs (T2Space k)
  have : LocallyCompactSpace (Tw k p c) := inferInstanceAs (LocallyCompactSpace k)
  have : ContinuousSMul k (Tw k p c) := ⟨by
    show Continuous fun q : k × k => (iterateFrobenius k p c q.1) * q.2
    simp only [iterateFrobenius_def]
    exact (continuous_fst.pow _).mul continuous_snd⟩
  exact FiniteDimensional.of_locallyCompactSpace k

theorem pad {M : Type*} [AddCommMonoid M] {q d : ℕ} (hqd : q ≤ d) (f : Fin q → M) :
    ∑ l : Fin q, f l = ∑ l : Fin d, if h : (l : ℕ) < q then f ⟨l, h⟩ else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if h : n < q then f ⟨n, h⟩ else 0) d]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hqd) (fun n _ hn => by
    rw [Finset.mem_range] at hn; rw [dif_neg hn])]
  rw [← Fin.sum_univ_eq_sum_range (fun n => if h : n < q then f ⟨n, h⟩ else 0) q]
  exact Finset.sum_congr rfl fun l _ => by rw [dif_pos l.2]

theorem sect (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Sect k := by
  intro p _ _ N q Z hZ hqc hroots hnilb χ hχm hχd
  obtain ⟨c, rfl⟩ := hqc
  haveI := twFin k p c
  letI : CommRing Z := { (inferInstance : Ring Z) with
    mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }
  haveI : IsReduced Z := hZ.2
  haveI : FiniteDimensional k Z := inferInstance
  haveI := rq_fin (A := Z) χ hχm (p ^ c)
  haveI := rq_pir (A := Z) χ (p ^ c)
  have hnilR : ∀ r : Rq Z χ (p ^ c), IsNilpotent r → r ^ (p ^ c) = 0 := rq_nil χ (p ^ c)
  have hrootR : ∀ a : k, ∃ w : Rq Z χ (p ^ c), w ^ (p ^ c) = algebraMap k _ a := by
    intro a
    obtain ⟨w, hw, hwa⟩ := hroots a
    refine ⟨Ideal.Quotient.mk _ (C ⟨w, hw⟩), ?_⟩
    have h1 : (⟨w, hw⟩ : Z) ^ (p ^ c) = algebraMap k Z a := Subtype.ext (by simpa using hwa)
    rw [← map_pow, ← map_pow, h1]
    rfl
  obtain ⟨r, s, c', u, ε, m, κ, h1, hu, hε, hrep, hid, hsum, horth, hcorner⟩ :=
    rdata (R := Rq Z χ (p ^ c)) p c hnilR hrootR
  have hdN : χ.natDegree ≤ max N (p ^ c) := hχd ▸ le_max_left _ _
  have hdq : p ^ c ≤ max N (p ^ c) := le_max_right _ _
  choose ar har using fun j => rq_rep (A := Z) χ hχm (p ^ c) (max N (p ^ c)) hdN (s j)
  obtain ⟨br, hbr⟩ := rq_rep (A := Z) χ hχm (p ^ c) (max N (p ^ c)) hdN ε
  choose γ0 hγ0 using fun i => hrep (Ideal.Quotient.mk _ (C (Module.finBasis k Z i)))
  obtain ⟨β0, hβ0⟩ := hrep (Ideal.Quotient.mk _ X)
  let ext : (Fin (p ^ c) → Fin r → k) → Fin (max N (p ^ c)) → Fin r → k :=
    fun g l j => if h : (l : ℕ) < p ^ c then g ⟨l, h⟩ j else 0
  let E : Fin m → Rq Z χ (p ^ c) := fun t => ∑ j, κ t j • s j
  refine ⟨{
    r := r
    d := max N (p ^ c)
    a := fun j l => (ar j l : Matrix (Fin N) (Fin N) k)
    ha := fun j l => (ar j l).2
    b := fun l => (br l : Matrix (Fin N) (Fin N) k)
    hb := fun l => (br l).2
    c := c'
    u := u
    a0 := finrank k Z
    z := fun i => (Module.finBasis k Z i : Matrix (Fin N) (Fin N) k)
    hz := ?_
    γ := fun i => ext (γ0 i)
    β := ext β0
    m := m
    κ := κ
    dd := fun t => finrank k (Submodule.span k (Set.range fun j => E t * s j))
    K := fun t => LinearMap.ker ((LinearMap.mulLeft k (E t)).comp (Fintype.linearCombination k s))
    spec := ?_ }⟩
  · apply le_antisymm
    · intro y hy
      have h := congrArg Subtype.val ((Module.finBasis k Z).sum_repr ⟨y, hy⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (Module.finBasis k Z i).2)
  · intro x hx hχx
    have hB : ∀ P : Z[X], P.eval₂ Z.val.toRingHom x ∈ Bz Z := by
      intro P a ha
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ => rw [eval₂_add, mul_add, add_mul, hP, hQ]
      | monomial n b =>
        rw [eval₂_monomial]
        have e1 : a * (b : Matrix (Fin N) (Fin N) k) = b * a := hZ.1 a ha b b.2
        have e2 : Commute a (x ^ n) := Commute.pow_right (hx a ha) n
        show a * ((b : Matrix (Fin N) (Fin N) k) * x ^ n) = (b : Matrix (Fin N) (Fin N) k) * x ^ n * a
        rw [← mul_assoc, e1, mul_assoc, e2.eq, mul_assoc]
    obtain ⟨ρ, hρ⟩ := rq_lift (A := Z) Z.val x (fun a => hx a a.2) χ hχx (p ^ c)
      (fun P hP => hnilb _ (hB P) hP)
    have hpe : ∀ g : Fin (max N (p ^ c)) → Z, pe (fun l => (g l : Matrix (Fin N) (Fin N) k)) x =
        ρ (Ideal.Quotient.mk _ (∑ l : Fin (max N (p ^ c)), C (g l) * X ^ (l : ℕ))) := by
      intro g
      rw [hρ, eval₂_finsetSum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul_X_pow_eq_monomial, eval₂_monomial]
      rfl
    have hs : ∀ j, pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x = ρ (s j) := fun j => by
      rw [hpe, ← har j]
    have hε' : pe (fun l => (br l : Matrix (Fin N) (Fin N) k)) x = ρ ε := by rw [hpe, ← hbr]
    have hlin : ∀ v : Fin r → k, ∑ j, v j • ρ (s j) = ρ (∑ j, v j • s j) := fun v => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp only [map_smul]
    have hspan : ∀ y, y ∈ Submodule.span k (Set.range fun j => ρ (s j)) →
        ∃ v : Fin r → k, y = ρ (∑ j, v j • s j) := by
      intro y hy
      obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hy
      exact ⟨v, by rw [← hv, hlin]⟩
    have hE : ∀ t, ∑ j, κ t j • ρ (s j) = ρ (E t) := fun t => hlin (κ t)
    have hsum' : ∑ t, E t = 1 := hsum
    have hid' : ∀ t, IsIdempotentElem (E t) := hid
    have hcor : ∀ t (v : Fin r → k), (∑ j, v j • s j) * E t = 0 ∨
        ∃ w : Rq Z χ (p ^ c), (∑ j, v j • s j) * E t * w = E t := hcorner
    have hre : ∀ g : Fin (p ^ c) → Fin r → k, re (ext g) (fun j => ρ (s j)) (ρ ε) =
        ρ (∑ l, ∑ j, g l j • (s j * ε ^ (l : ℕ))) := by
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, pad hdq]
      unfold re
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : (l : ℕ) < p ^ c
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [dif_pos h, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [ext, dif_pos h, map_smul, map_mul, map_pow]
      · rw [dif_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [ext, dif_neg h, zero_smul]
    have nilmul : ∀ a b : Matrix (Fin N) (Fin N) k, Commute a b → IsNilpotent a → IsNilpotent (a * b) :=
      fun a b h ⟨n, hn⟩ => ⟨n, by rw [h.mul_pow, hn, zero_mul]⟩
    have hcomm : ∀ a b : Rq Z χ (p ^ c), Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    dsimp only
    simp only [hs, hε']
    refine ⟨fun j j' => ?_, ?_, fun j j' => ?_, fun j => ?_, ?_, ?_, fun i => ?_, ?_, fun t => ?_, ?_,
      fun t t' htt => ?_, fun t y hy hyi hye => ?_, fun t => ?_, fun v => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [← map_mul, h1 j j', map_sum]; simp only [map_smul]
    · rw [hlin, hu, map_one]
    · rw [← map_mul, mul_comm, map_mul]
    · rw [← map_mul, mul_comm, map_mul]
    · rw [← map_pow, hε, map_zero]
    · intro y hy hnil
      obtain ⟨v, rfl⟩ := hspan y hy
      have hz0 : ∀ t, ρ ((∑ j, v j • s j) * E t) = 0 := by
        intro t
        rcases hcor t v with h | ⟨w', hw'⟩
        · rw [h, map_zero]
        · have hEn : IsNilpotent (ρ (E t)) := by
            rw [← hw', mul_assoc, map_mul]
            exact nilmul _ _ (hcomm _ _) hnil
          have hE0 : ρ (E t) = 0 := by
            obtain ⟨n, hn⟩ := hEn
            have := ((hid' t).map ρ).pow_succ_eq n
            rw [pow_succ, hn, zero_mul] at this
            exact this.symm
          rw [← (hid' t).eq, ← mul_assoc, map_mul, hE0, mul_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← mul_one (∑ j, v j • s j), ← hsum', Finset.mul_sum, map_sum]
      exact Finset.sum_eq_zero fun t _ => hz0 t
    · rw [hre, ← hγ0 i, hρ, eval₂_C]
      rfl
    · rw [hre, ← hβ0, hρ, eval₂_X]
    · rw [hE]; exact (hid' t).map ρ
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [hE]; rw [← map_sum, hsum', map_one]
    · rw [hE, hE, ← map_mul, horth t t' htt, map_zero]
    · rw [hE] at hye ⊢
      obtain ⟨v, rfl⟩ := hspan y hy
      rcases hcor t v with h | ⟨w', hw'⟩
      · left; rw [← hye, ← map_mul, h, map_zero]
      · right
        have e1 : ρ (E t) = ρ (∑ j, v j • s j) * ρ (E t) * ρ w' := by rw [← map_mul, ← map_mul, hw']
        rw [hye] at e1
        calc ρ (∑ j, v j • s j) = ρ (∑ j, v j • s j) * ρ (E t) := hye.symm
          _ = ρ (∑ j, v j • s j) * (ρ (∑ j, v j • s j) * ρ w') := by rw [← e1]
          _ = ρ (∑ j, v j • s j) * ρ w' := by rw [← mul_assoc, hyi.eq]
          _ = ρ (E t) := e1.symm
    · have hfun : (fun j => (∑ j', κ t j' • pe (fun l => (ar j' l : Matrix (Fin N) (Fin N) k)) x) *
          pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x) = fun j => ρ (E t) * ρ (s j) := by
        funext j; simp only [hs, hE]
      have hE2 : ∑ j, κ t j • pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x = ρ (E t) := by
        simp only [hs, hE]
      rw [hfun, hE2]
      have hmap : Submodule.span k (Set.range fun j => ρ (E t) * ρ (s j)) =
          (Submodule.span k (Set.range fun j => E t * s j)).map ρ.toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        congr 1
        ext j
        simp [map_mul]
      split_ifs with h0
      · have : (fun j => ρ (E t) * ρ (s j)) = fun _ => 0 := by funext j; rw [h0, zero_mul]
        rw [this, Submodule.span_eq_bot.2 (by rintro _ ⟨j, rfl⟩; rfl), finrank_bot]
      · rw [hmap]
        set V := Submodule.span k (Set.range fun j => E t * s j)
        have hinj : Function.Injective (ρ.toLinearMap.comp V.subtype) := by
          rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
          rintro ⟨y, hyV⟩ hy0
          obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hyV
          have hy2 : y = (∑ j, v j • s j) * E t := by
            rw [← hv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_mul_assoc, mul_comm]
          have hy0' : ρ y = 0 := hy0
          rcases hcor t v with h | ⟨w', hw'⟩
          · exact Subtype.ext (show y = 0 by rw [hy2, h])
          · exact absurd (by rw [← hw', map_mul, ← hy2, hy0', zero_mul]) h0
        rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, Submodule.range_subtype]
    · simp only [hE, hlin, LinearMap.mem_ker, LinearMap.comp_apply, Fintype.linearCombination_apply,
        LinearMap.mulLeft_apply]
      constructor
      · intro h0 t hEt
        rcases hcor t v with h | ⟨w', hw'⟩
        · rw [mul_comm]; exact h
        · exact absurd (by rw [← hw', map_mul, map_mul, h0, zero_mul, zero_mul]) hEt
      · intro h
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← mul_one (∑ j, v j • s j), ← hsum', Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun t _ => ?_
        by_cases hEt : ρ (E t) = 0
        · rw [map_mul, hEt, mul_zero]
        · rw [mul_comm, h t hEt, map_zero]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

namespace PositivityTheory.RgUd.TP.Desc.Piece.Final

open PositivityTheory.RgUd.TP.Desc

theorem pieceGood (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PieceGood k :=
  PositivityTheory.RgUd.TP.Desc.Piece.PAsm2.pieceGood_of k PositivityTheory.PfBern.Frob.frobeniusReciprocity (PositivityTheory.RgUd.TP.Desc.Piece.PSect.sect k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTop.pieceTop k) (PositivityTheory.RgUd.TP.Desc.Piece.PDich.dich k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTr.transfer k)

end PositivityTheory.RgUd.TP.Desc.Piece.Final

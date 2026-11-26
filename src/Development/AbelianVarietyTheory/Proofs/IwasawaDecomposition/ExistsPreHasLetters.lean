module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstMapInjective
open Formalism.MainNotions.G MvPolynomial

noncomputable section

namespace GlobalTheory.PrescribedRank

variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def noPlaces : Places p O Kf where
  w := 0
  nV := 0
  n' := fun _ => 0
  W := fun _ => O
  Qq := fun _ => Kf
  ι := fun _ => RingHom.id Kf
  σ := fun _ => RingEquiv.refl Kf
  j := fun _ => RingHom.id O
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun _ _ _ => 0
  dom := fun v => v.elim0

instance : IsEmpty (Fin (noPlaces p O Kf).nV) := inferInstanceAs (IsEmpty (Fin 0))

def trivLevel : Level (noPlaces p O Kf) where
  Γ := PUnit
  act := fun _ => 1
  χ := 1

theorem tup_eq (L L' : (noPlaces p O Kf).Tup) : L = L' := funext fun v => isEmptyElim v

theorem isLatTup (L : (noPlaces p O Kf).Tup) : (noPlaces p O Kf).IsLatTup L := fun v => isEmptyElim v

theorem actX_apply (γ : (trivLevel p O Kf).Γ) (x : (noPlaces p O Kf).Xsp) :
    (trivLevel p O Kf).actX γ x = x := by
  have h : ∀ G, (noPlaces p O Kf).subst G = AlgHom.id Kf _ := fun G =>
    MvPolynomial.algHom_ext fun i => isEmptyElim i.1
  unfold Level.actX Places.natAct
  rw [h, Fintype.prod_empty]
  simp

theorem htupW_eq (L : (noPlaces p O Kf).Tup) :
    (noPlaces p O Kf).HtupW L = Submodule.span O {1} := by
  unfold Places.HtupW Places.tenV
  congr 1
  ext X
  constructor
  · rintro ⟨F, -, rfl⟩
    rw [Fintype.prod_empty]
    rfl
  · rintro rfl
    exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v, by rw [Fintype.prod_empty]⟩

theorem mem_funMod (Hv : (noPlaces p O Kf).Tup → Submodule O (noPlaces p O Kf).Xsp)
    (F : (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) :
    F ∈ (trivLevel p O Kf).funMod Hv ↔ ∀ L, F L ∈ Hv L := by
  unfold Level.funMod
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩ L
    exact h L (isLatTup p O Kf L)
  · intro h
    refine ⟨⟨fun L _ => h L, fun L hL => absurd (isLatTup p O Kf L) hL⟩, fun γ L => ?_⟩
    have hχ : (trivLevel p O Kf).χ γ = 1 := rfl
    rw [tup_eq p O Kf ((trivLevel p O Kf).smul γ L) L, hχ]
    simp [actX_apply]

theorem finClasses : (trivLevel p O Kf).FinClasses :=
  ⟨{fun v => isEmptyElim v}, fun L _ => isLatTup p O Kf L, fun L _ =>
    ⟨_, Finset.mem_singleton_self _, (1 : (trivLevel p O Kf).Γ), tup_eq p O Kf _ _⟩⟩

def gat (d : ℕ) : GAtP p where
  O := O
  Kf := Kf
  P := noPlaces p O Kf
  comp := Fin d
  lev := fun _ => trivLevel p O Kf
  e := 0

def constMap (d : ℕ) : (Fin d → O) →ₗ[O] (Fin d → (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) where
  toFun c := fun i _ => c i • (1 : (noPlaces p O Kf).Xsp)
  map_add' a b := by
    funext i L
    simp [add_smul]
  map_smul' a b := by
    funext i L
    simp [mul_smul]

theorem constMap_injective (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) :
    Function.Injective (constMap p O Kf d) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  have h : c i • (1 : (noPlaces p O Kf).Xsp) = 0 := congrFun (congrFun hc i) (fun v => isEmptyElim v)
  have h2 := congrArg (AddMonoidAlgebra.coeff · 0) h
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_one, MvPolynomial.coeff_zero,
    Algebra.smul_def, mul_one] at h2
  apply hinj
  rw [h2]
  simp

theorem range_constMap (d : ℕ) :
    LinearMap.range (constMap p O Kf d) =
      Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW := by
  ext F
  rw [Submodule.mem_pi]
  simp only [Set.mem_univ, true_imp_iff, mem_funMod, htupW_eq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩ i L
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    refine ⟨fun i => c i (fun v => isEmptyElim v), ?_⟩
    funext i L
    rw [tup_eq p O Kf L (fun v => isEmptyElim v)]
    exact hc i _

theorem gat_d (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) : (gat p O Kf d).d = d := by
  have h : (gat p O Kf d).d = Module.finrank O
      (Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW) := rfl
  rw [h, ← range_constMap, LinearMap.finrank_range_of_inj (constMap_injective p O Kf d hinj)]
  simp

theorem GAtP₂ : ∀ (p d : ℕ), p.Prime → ∃ G : GAtP p, G.d = d ∧ G.FinClasses := by
  intro p d hp
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨gat p ℤ_[p] ℚ_[p] d, gat_d p _ _ d (IsFractionRing.injective ℤ_[p] ℚ_[p]),
    fun _ => finClasses p _ _⟩

end GlobalTheory.PrescribedRank
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsAllLifts
noncomputable section

namespace GlobalTheory.Mem.GJModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_place (B : Base) {l : ℕ} (hl : l.Prime) : ∃ w : B.places.Pl, B.places.resChar w = l := by
  have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 B.LL)
    (Ideal.span {((l : ℕ) : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 B.LL)).injective_int]
      exact bot_le)
  have hmem : ((l : ℕ) : 𝓞 B.LL) ∈ P := by
    have : ((l : ℕ) : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 B.LL)) := by
      change ((l : ℕ) : ℤ) ∈ Ideal.under ℤ P
      rw [hPl]; exact Ideal.mem_span_singleton_self _
    simpa using this
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hl.ne_zero (by exact_mod_cast hmem)
  let w : HeightOneSpectrum (𝓞 B.LL) := ⟨P, hP.isPrime, hne⟩
  exact ⟨w, Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime w) hl
    (Examples₂.PlacesToy.resCharW_mem w) hmem⟩

theorem tau_nonempty (B : Base) : Nonempty (Tau B.R) := by
  rw [← Fintype.card_pos_iff, card_Tau B.host]
  unfold Ranks.f Ranks.n
  have := B.R.ord_pos
  omega

theorem exists_inert {R : Ranks} (H : Host R) :
    ∃ l : ℕ, l.Prime ∧ 5 ≤ l ∧ (H.cls l = .signal ∨ H.cls l = .inertClass) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  obtain ⟨l, hgt, hl, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (5 + H.q + H.d + H.QS) (q := 4 * H.d) (a := -1)
    (by have := hd.pos; omega) isCoprime_one_left.neg_left
  have h4 : l % 4 = 3 := by
    have : (l : ℤ) ≡ -1 [ZMOD 4] := hmod.of_dvd ⟨H.d, by push_cast; ring⟩
    unfold Int.ModEq at this
    omega
  have hd4 : H.d % 4 = 3 := by omega
  have hmd : (l : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) := hmod.of_dvd ⟨4, by push_cast; ring⟩
  have hj : jacobiSym (-(H.d : ℤ)) l = -1 := by
    rw [show (-(H.d : ℤ)) = -1 * (H.d : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), jacobiSym.quadratic_reciprocity_three_mod_four hd4 h4,
      jacobiSym.mod_left' hmd, jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)),
      ZMod.χ₄_nat_three_mod_four h4, ZMod.χ₄_nat_three_mod_four hd4]
    norm_num
  refine ⟨l, hl, by omega, ?_⟩
  have hs : l ∉ H.small := fun h => by
    have := Nat.le_of_mem_primeFactors h
    omega
  unfold Host.cls primeClass
  rw [if_neg hs, if_neg (by omega), if_neg (by omega), if_neg (by rw [hj]; norm_num)]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_of_jet (B : Base) (C : Cols B) (vol : @HSpace B.host.E _ _ B.host.cmStar → ℝ)
    (hvol : ∀ W, 0 < vol W) (cd : CDHaar) (jet : ThetaJet B.R B.host) (gx : GlobalExtra B.LL (Tau B.R))
    (h : ∀ i, ∃ u, Nonempty ((C.mem u).C.cls (jet.jOf i - 1)) ∧ Nonempty ((C.mem u).C.cls (jet.jOf i)))
    (h1 : ∀ i, ∃ u, Nonempty ((C.mem u).C.cls (jet.j1Of i - 1)) ∧ Nonempty ((C.mem u).C.cls (jet.j1Of i))) :
    ∃ G : GJStage B C, G.vol = vol ∧ G.cd = cd ∧ G.jet = jet ∧ G.gx = gx ∧
      ∀ u w h, (G.gat u w h).FinClasses := by
  choose U hU hU' using h
  choose U1 hU1 hU1' using h1
  choose w hw using fun i : jet.Sit => exists_place B (jet.loc i).hl.out
  choose w1 hw1 using fun i : jet.Sit1 => exists_place B (jet.loc1 i).hl.out
  obtain ⟨τ⟩ := tau_nonempty B
  choose g hg hg' using fun (u : B.Word) (v : B.places.Pl)
      (hh : GIdx B.host (C.mem u).A.T (B.places.resChar v)) =>
    GlobalTheory.PrescribedRank.GAtP₂ (B.places.resChar v) (Module.finrank ℂ (C.mem u).A.Mu0) hh.1
  exact ⟨{ vol := vol, vol_pos := hvol, cd := cd, jet := jet, jetU := U
           jetL := fun i => (hU i).some, jetL' := fun i => (hU' i).some
           jetW := w, jetW_l := hw, jetTau := fun _ _ => τ
           jetW1 := w1, resChar_thetaJetPlaceDegOne := hw1, jetTau1 := fun _ => τ, jetU1 := U1
           jetL1 := fun i => (hU1 i).some, jetL1' := fun i => (hU1' i).some
           gx := gx, gat := g, gat_d := hg }, rfl, rfl, rfl, rfl, hg'⟩

def gxOne (B : Base) : GlobalExtra B.LL (Tau B.R) :=
  ⟨fun _ _ => 1, fun _ _ => one_pos, fun _ => 1, fun _ => one_pos⟩

end GlobalTheory.Mem.GJModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocStageInhabited
open Formalism Formalism.BasicNotions

namespace GlobalTheory.Mem

theorem locStage_inhabited : Nonempty GlobalTheory.Mem.LocStage := by
  classical
  choose P AI hT using GlobalTheory.MemLoc.exists_locPrime_tied
  exact ⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInnerProductSpace
noncomputable section

namespace GlobalTheory.Mem.SStageInhab

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

theorem ncard_primesOver_eq (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime) :
    ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).ncard = (placesOver E l).ncard := by
  symm
  apply Set.ncard_congr (fun v _ => v.asIdeal)
  · intro v hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl)) (by simpa using hl.ne_zero)
    refine hm.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ v.asIdeal)) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [Ideal.under, placesOver] using hv
  · intro a b _ _ h; exact HeightOneSpectrum.ext h
  · rintro P ⟨hP, hP'⟩
    have hmem : ((l:ℕ) : 𝓞 E) ∈ P := by
      have : (l:ℤ) ∈ P.under ℤ := by rw [← hP'.over]; exact Ideal.mem_span_singleton_self _
      simpa [Ideal.under] using this
    refine ⟨⟨P, hP, ?_⟩, hmem, rfl⟩
    rintro rfl
    exact hl.ne_zero (by simpa using hmem)

theorem conjF_ne_id (B : Base) : B.toPre.conjF ≠ AlgHom.id _ _ := by
  letI := B.host.cmStar
  intro h
  have h2 := B.sp.cm.deg2
  have hs : Function.Surjective (algebraMap B.host.F B.host.E) := fun a => by
    have : B.toPre.conjF a = a := by rw [h]; rfl
    exact (B.sp.cm.fixed a).1 this
  have : Module.finrank B.host.F B.host.E = 1 := by
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap.symm] ; exact ⟨(algebraMap B.host.F B.host.E).injective, hs⟩
  omega

theorem exists_locAt_split_iff (B : Base) (h2 : Module.finrank B.host.F B.host.E = 2) (hne : B.toPre.conjF ≠ AlgHom.id _ _) (p) :
    ∃ L : Formalism.MainNotions.S.Loc.LocAt B.host.F B.host.E B.toPre.conjF p, (L.split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt _ _ B.toPre.conjF h2 p
  by_cases h : Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt _ _ _ h2 hne p L (by
      rw [ncard_primesOver_eq _ _ L.ellPrime.out]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> rw [h] <;> exact B.toPre.g_split _)
    exact ⟨{L with split := some S}, by simp [h]⟩
  · exact ⟨L, by simp [hL, h]⟩

theorem nonempty_conj_embedding (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] (d D : ℕ) (h : d ≤ D)
    (b : OrthonormalBasis (Fin d) ℂ EE) : Nonempty (EE →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin D)) := by
  let e := EuclideanSpace.basisFun (Fin D) ℂ
  have ho : Orthonormal ℂ (fun i : Fin d => e (Fin.castLE h i)) := e.orthonormal.comp _ (Fin.castLE_injective h)
  let f : EE →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ (Fin D) :=
    { toFun := fun x => ∑ i, (inner ℂ x (b i)) • e (Fin.castLE h i)
      map_add' := by intro x y; simp [inner_add_left, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul, mul_comm] }
  refine ⟨⟨f, fun x => ?_⟩⟩
  have h1 : inner ℂ (f x) (f x) = ∑ i, (starRingEnd ℂ) (inner ℂ x (b i)) * inner ℂ x (b i) :=
    ho.inner_sum _ _ _
  have h2 := b.sum_inner_mul_inner x x
  have h3 : inner ℂ (f x) (f x) = inner ℂ x x := by
    rw [h1, ← h2]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_conj_symm, mul_comm]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  have h4 : ‖f x‖^2 = ‖x‖^2 := by exact_mod_cast h3
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4

theorem exists_innerProductSpace (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ip : V → V → ℂ)
    (hs : ∀ x y, (starRingEnd ℂ) (ip y x) = ip x y) (hp : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (ha : ∀ x y z, ip (x+y) z = ip x z + ip y z) (hm : ∀ x y (r:ℂ), ip (r • x) y = (starRingEnd ℂ) r * ip x y) :
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U) (e : U ≃ₗ[ℂ] V),
      ∀ x y, inner ℂ x y = ip (e x) (e y) := by
  let c : InnerProductSpace.Core ℂ V :=
    { inner := ip, conj_inner_symm := hs
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · have := hm x x 0; subst h; simp at this; simp [this]
        · exact (hp x h).le
      add_left := ha, smul_left := hm
      definite := fun x h => by by_contra h'; have := hp x h'; rw [h] at this; simp at this }
  letI n : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI i : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  exact ⟨V, n, i, inferInstance, LinearEquiv.refl _ _, fun x y => rfl⟩

theorem exists_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) :
    ∃ S : SStage B C W, S.s.Del = Del ∧ S.s.letter = letter ∧ (∀ u u', Nonempty (S.s.Term u u')) ∧
      ∀ u u', Nonempty (S.s.Pair u u') := by
  have hloc := by
    letI := B.host.cmStar
    exact exists_locAt_split_iff B B.sp.cm.deg2 (conjF_ne_id B)
  choose L hL using hloc
  let pt : Formalism.MainNotions.S.Point B.host.E (B.R.rS + 1) := ⟨[(1, B.R.rS + 1)], by simp, by simp⟩
  have hU := fun u => by
    haveI := (C.mem u).A.Mu0_fd
    exact exists_innerProductSpace (C.mem u).A.Mu0 (fun x y => (C.fm u).ipC 0 x.1 y.1) (fun x y => hs u _ x.2 _ y.2)
      (fun x hx => hp u _ x.2 (fun h => hx (Subtype.ext h)))
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun x y r => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  choose U n i f e he using hU
  obtain ⟨sE⟩ := nonempty_conj_embedding W.EE _ _ hDD W.onb
  let s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW :=
    { cdScale := fun _ _ => 1, cdScale_pos := fun _ _ => one_pos, Del := Del, Del_pos := hD, cloud_gap := gap
      letter := letter, letter_inj := hinj, u_letter := hu, HH := EuclideanSpace ℂ (Fin W.Dall)
      Cu := U, cuN := n, cuI := i, cuF := f, Pu := fun _ => 0, volN := fun _ => 1, volH := fun _ => 1
      volN_pos := fun _ => one_pos, volH_pos := fun _ => one_pos, Term := fun _ _ => Unit
      aTerm := fun _ _ _ => 0, isId := fun _ => True, inS := fun _ => True, relevant := fun _ => True
      FeqF := fun _ => True, Gterm := fun _ => 0, atP := L, PlF := HeightOneSpectrum (𝓞 B.host.F)
      BBne := fun _ _ => False, generic := fun _ => False, Pair := fun _ _ => Unit
      pfst := fun _ => (), psnd := fun _ => (), s0 := fun _ => 0, scalarPair := fun _ => True
      pval := fun _ => 0, ptOf := fun _ => pt, cTerm := fun _ => 1, massPair := fun _ => 1
      meanCount := fun _ _ _ => 0 }
  exact ⟨{ dsig := fun _ => 1, dsig_pos := fun _ => one_pos, s := s, s_split := hL, s_HH := by simp [s]
           s_Cu := e, s_PlF := Equiv.refl _, s_Cu_isom := he, sEE := sE },
    rfl, rfl, fun _ _ => ⟨()⟩, fun _ _ => ⟨()⟩⟩

theorem nonempty_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) : Nonempty (SStage B C W) :=
  (exists_sStage B C W Del hD gap letter hinj hu hs hp hDD).elim fun S _ => ⟨S⟩

end GlobalTheory.Mem.SStageInhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InhabitedStage
noncomputable section

namespace GlobalTheory.Mem.GJInhab

open Formalism.BasicNotions NumberField IsDedekindDomain

def baseVol (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : ℝ :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

theorem baseVol_pos (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : 0 < baseVol B cd W :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol_pos B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

def noJet {R : Ranks} (H : Host R) : ThetaJet R H where
  Sit := Empty
  loc := fun i => i.elim
  l_inert := fun i => i.elim
  jOf := fun i => i.elim
  j_mem := fun i => i.elim
  N0_eq := fun i => i.elim
  N1_eq_exponentN1 := fun i => i.elim
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

def oneJet {R : Ranks} (H : Host R) (hm : 1 ≤ R.m) (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l)
    (hc : H.cls l = .signal ∨ H.cls l = .inertClass) : ThetaJet R H where
  Sit := Unit
  loc := fun _ =>
    haveI : Fact l.Prime := ⟨hl⟩
    { l := l
      five_le_l := h5
      d := 2
      d_even := even_two
      two_le_d := le_rfl
      N0 := R.N 0
      N1 := R.N 1
      Th := 1 }
  l_inert := fun _ => hc
  jOf := fun _ => 1
  j_mem := fun _ => ⟨le_rfl, hm⟩
  N0_eq := fun _ => rfl
  N1_eq_exponentN1 := fun _ => rfl
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

theorem exists_noJet (B : Base) (C : Cols B) (cd : CDHaar) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = noJet B.host ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (noJet B.host) (GJModel.gxOne B) (fun i => i.elim) (fun i => i.elim)
  exact ⟨J, hcd, by rw [hv, hcd], hj, hf⟩

theorem exists_oneJet (B : Base) (C : Cols B) (cd : CDHaar) (hm : 1 ≤ B.R.m) (u : B.Word)
    (h0 : Nonempty ((C.mem u).C.cls 0)) (h1 : Nonempty ((C.mem u).C.cls 1))
    (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l) (hc : B.host.cls l = .signal ∨ B.host.cls l = .inertClass) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = oneJet B.host hm l hl h5 hc ∧
      (∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
        B.places.resChar (J.jetW i) = l) ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (oneJet B.host hm l hl h5 hc) (GJModel.gxOne B) (fun _ => ⟨u, h0, h1⟩) (fun i => i.elim)
  have key : ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 := by
    rw [hj]
    exact ⟨(), rfl, rfl, rfl⟩
  obtain ⟨i, hi1, hil, hid⟩ := key
  exact ⟨J, hcd, by rw [hv, hcd], hj, ⟨i, hi1, hil, hid, (J.jetW_l i).trans hil⟩, hf⟩

theorem nonempty_stage (B : Base) (C : Cols B) : Nonempty (GJStage B C) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  obtain ⟨J, -⟩ := exists_noJet B C cd
  exact ⟨J⟩

theorem inhabited_stage (B : Base) (C : Cols B) :
    (∃ J : GJStage B C, J.vol = baseVol B J.cd) ∧
    (1 ≤ B.R.m → Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∀ l : ℕ, l.Prime → 5 ≤ l → (B.host.cls l = .signal ∨ B.host.cls l = .inertClass) →
        ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit ∧
          ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
            B.places.resChar (J.jetW i) = l) ∧
    (Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  refine ⟨?_, fun hm h0 h1 l hl h5 hc => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨J, -, hv, -⟩ := exists_noJet B C cd
    exact ⟨J, hv⟩
  · obtain ⟨J, -, hv, -, ⟨i, hi⟩, -⟩ := exists_oneJet B C cd hm B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩, i, hi⟩
  · obtain ⟨l, hl, h5, hc⟩ := GJModel.exists_inert B.host
    have hm := B.R.two_le_m
    obtain ⟨J, -, hv, -, ⟨i, -⟩, -⟩ := exists_oneJet B C cd (by omega) B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩⟩

end GlobalTheory.Mem.GJInhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColsRowsRestPos
noncomputable section

namespace GlobalTheory.Mem.RowsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

abbrev Euc (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def stdOLat (O : Type) [CommRing O] (φ : O →+* ℂ) (n : ℕ) : Rows.OLat O φ (Euc n) := by
  classical
  exact
    { gen := Finset.univ.image (fun i => EuclideanSpace.basisFun (Fin n) ℂ i)
      span_top := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq }

theorem mem_stdOLat {O : Type} [CommRing O] {φ : O →+* ℂ} {n : ℕ} {x : Euc n}
    (hx : x ∈ (stdOLat O φ n).gen) : ∃ i, EuclideanSpace.basisFun (Fin n) ℂ i = x := by
  classical
  simpa [stdOLat] using hx

def coordEmb {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) : (Fin n → K) →ₛₗ[σ] Euc n where
  toFun x := WithLp.toLp 2 (fun i => σ (x i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem coordEmb_single {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) (i : Fin n) :
    coordEmb σ n (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℂ i := by
  ext j
  by_cases h : j = i
  · subst h; simp [coordEmb]
  · simp [coordEmb, h]

theorem coordEmb_basis {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) {ι : Type}
    (b : Module.Basis ι K (Fin n → K)) :
    LinearIndependent ℂ (fun i => coordEmb σ n (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) = ⊤ := by
  classical
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs : ⊤ ≤ Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [OrthonormalBasis.coe_toBasis, ← coordEmb_single σ, ← b.sum_repr (Pi.single i 1), map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hs ?_, top_le_iff.mp hs⟩
  rw [← Module.finrank_eq_card_basis b]
  simp

theorem exists_frame {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : InnerProductSpace.Core ℂ V) :
    ∃ e : Euc (Module.finrank ℂ V) ≃ₗ[ℂ] V, ∀ x y, inner ℂ x y = c.inner (e x) (e y) := by
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  refine ⟨(stdOrthonormalBasis ℂ V).repr.symm.toLinearEquiv, fun x y => ?_⟩
  exact ((stdOrthonormalBasis ℂ V).repr.symm.inner_map_map x y).symm

variable {B : Base} (C : Cols B)

def ramCore (u : B.Word)
    (h1 : ∀ φ ∈ (C.mem u).A.Mram, ∀ ψ ∈ (C.mem u).A.Mram,
      (C.fm u).ipC 0 ψ φ = starRingEnd ℂ ((C.fm u).ipC 0 φ ψ))
    (h2 : ∀ φ ∈ (C.mem u).A.Mram, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) :
    InnerProductSpace.Core ℂ (C.mem u).A.Mram where
  inner φ ψ := (C.fm u).ipC 0 φ.1 ψ.1
  conj_inner_symm φ ψ := (h1 ψ.1 ψ.2 φ.1 φ.2).symm
  re_inner_nonneg φ := by
    by_cases h : φ.1 = 0
    · show 0 ≤ ((C.fm u).ipC 0 φ.1 φ.1).re
      rw [h]
      simp [MemberForms.ipC]
    · exact (h2 φ.1 φ.2 h).le
  add_left φ ψ χ := by
    show (C.fm u).ipC 0 (φ.1 + ψ.1) χ.1 = _
    simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left φ ψ r := by
    show (C.fm u).ipC 0 (r • φ.1) ψ.1 = _
    simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm]
  definite φ h := by
    by_contra hne
    have := h2 φ.1 φ.2 (fun h0 => hne (Subtype.ext h0))
    change (C.fm u).ipC 0 φ.1 φ.1 = 0 at h
    rw [h] at this
    simp at this

theorem mram_fd (u : B.Word) : FiniteDimensional ℂ (C.mem u).A.Mram := by
  have := (C.mem u).A.Mu0_fd
  exact Submodule.finiteDimensional_of_le (show (C.mem u).A.Mram ≤ (C.mem u).A.Mu0 from inf_le_left)

def eucCast {a b : ℕ} (h : a = b) : Euc a ≃ₗᵢ[ℂ] Euc b :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)


open Classical in
def model (n : C.Tup → ℕ) (D : ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Euc (n C.mu0)) (eTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Euc (n μ))
    (eM : ∀ u, Euc (C.mem u).A.du ≃ₗ[ℂ] (C.mem u).A.Mram)
    (heM : ∀ u φ ψ, inner ℂ φ ψ = (C.fm u).ipC 0 (eM u φ).1 (eM u ψ).1) : RowsRest B C where
  muAt _ := C.mu0
  muAt_conj _ := rfl
  muTw _ := C.mu0
  muTw_conj _ := rfl
  muAt_or _ := Or.inl rfl
  EE := Euc D
  Drows := D
  onb := EuclideanSpace.basisFun (Fin D) ℂ
  Dall := D
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Euc D
  D0 := D
  onb0 := EuclideanSpace.basisFun (Fin D) ℂ
  FT := Unit
  ft _ := ()
  ft0 _ := ()
  Amb μ := Euc (n μ)
  Mult μ j := Euc (if j = 0 then D else n μ)
  multZero _ := eucCast (if_pos rfl)
  multTop _ := eucCast (if_neg (by have := B.R.two_le_m; omega))
  io _ _ := Matrix.toEuclideanLin (Matrix.of fun a b => if (a : ℕ) = (b : ℕ) then 1 else 0)
  Mtilde μ := stdOLat _ _ (n μ)
  eOp _ := LinearMap.id
  eOp_idem _ := rfl
  eOp_sa _ _ _ := rfl
  Mu u := Euc (C.mem u).A.du
  perCol u μ φ F :=
    if h : μ = C.mu0 then (C.mem u).P.PtilCol (eM u φ).1 ((e0 u).symm (eucCast (congrArg n h) F))
    else (C.PTw u μ).PtilCol (C.e0Tw u μ (eM u φ).1) ((eTw u μ).symm F)
  Bu _ φ F := (∑ a, φ a) * ∑ b, F b
  ze _ _ := 1
  rowsRest_wordColumnUnit_baseTuple _ := rfl
  Mj _ := Euc D
  MjLat _ := stdOLat _ _ D
  kaBig _ _ _ := 0
  kaSmall _ _ _ := 0
  Mt _ _ := Euc D
  MtLat _ _ := stdOLat _ _ D
  MtL _ _ := Fin D → B.LL
  jMt _ _ := coordEmb B.embLL D
  jMt_basis _ _ b := coordEmb_basis B.embLL D b
  MtLat_sub _ _ x hx := by
    obtain ⟨i, rfl⟩ := mem_stdOLat hx
    exact ⟨_, coordEmb_single _ _ i⟩
  eMt _ _ := LinearMap.id
  eMt_idem _ _ := rfl
  eMt_sa _ _ _ _ := rfl
  eMt_LL _ _ x := ⟨x, rfl⟩
  thetaP _ _ := LinearMap.id
  isot _ _ := ⊤
  lamP _ _ _ := 1
  Ij _ _ _ := 0
  jw _ _ _ := 0
  etaJ _ _ := 0
  etaJ_nonneg _ _ := le_rfl
  shaLen _ _ := 0
  shaLen_nonneg _ _ := le_rfl
  eMu := eM
  eMt0 := e0
  perCol_base_eq_PtilCol u φ F := by
    rw [dite_eq_left rfl]
    rfl
  Bu_linL _ F := ⟨fun φ ψ => by simp [Finset.sum_add_distrib, add_mul],
    fun a φ => by simp [← Finset.mul_sum, mul_assoc]⟩
  Bu_linR _ φ := ⟨fun F G => by simp [Finset.sum_add_distrib, mul_add],
    fun a F => by simp [← Finset.mul_sum, mul_left_comm]⟩
  eMtTw := eTw
  perCol_tie u μ h φ F := dif_neg h
  eMu_isom := heM

end GlobalTheory.Mem.RowsModel

namespace GlobalTheory.Mem


theorem RowsModel.ipC_cols (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 φ ψ = ∑ c, starRingEnd ℂ (φ c ()) * ψ c () := by
  refine Finset.sum_congr rfl fun c _ => ?_
  show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ * (starRingEnd ℂ (φ c ()) * ψ c ()) = _
  simp


end GlobalTheory.Mem

end
end

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace StagesInhab

def HasLetters (P : Pre) : Prop :=
  ∃ (Del : ℚ) (letter : P.Word → Fin (P.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧
    (∀ w τ (l : ℕ) (h : l + 1 < P.R.k - 1), (P.hcW w τ).v ⟨l, by omega⟩ - (P.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧
    ∀ w τ (l : ℕ) (h : l < P.R.k - 2), (P.hcW w τ).u ⟨l + 1, by omega⟩ =
      (P.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

theorem ipC_conj (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 ψ φ = starRingEnd ℂ (((ColsModel.cols B).fm u).ipC 0 φ ψ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [RowsModel.ipC_cols, RowsModel.ipC_cols, map_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]

theorem ipC_pos (B : Base) (u : B.Word)
    (φ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) (hφ : φ ≠ 0) :
    0 < (((ColsModel.cols B).fm u).ipC 0 φ φ).re := by
  rw [RowsModel.ipC_cols, Complex.re_sum]
  obtain ⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by
    by_contra h
    exact hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

theorem exists_rows (B : Base) (D : ℕ) :
    ∃ W : RowsRest B (ColsModel.cols B), W.Drows = D ∧ W.Dall = D ∧ ∀ u, Nontrivial (W.Mu u) := by
  classical
  have hf : ∀ u, ∃ e : RowsModel.Euc ((ColsModel.cols B).mem u).A.du ≃ₗ[ℂ] ((ColsModel.cols B).mem u).A.Mram,
      ∀ φ ψ, inner ℂ φ ψ = ((ColsModel.cols B).fm u).ipC 0 (e φ).1 (e ψ).1 := fun u =>
    haveI := RowsModel.mram_fd (ColsModel.cols B) u
    RowsModel.exists_frame (RowsModel.ramCore (ColsModel.cols B) u (fun φ _ ψ _ => ipC_conj B u φ ψ)
      (fun φ _ h => ipC_pos B u φ h))
  choose eM heM using hf
  let e : ℂ ≃ₗ[ℂ] RowsModel.Euc 1 :=
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans (WithLp.linearEquiv 2 ℂ _).symm
  refine ⟨RowsModel.model (ColsModel.cols B) (fun _ => 1) D (fun _ => e) (fun _ _ => e) eM heM, rfl, rfl,
    fun u => ?_⟩
  have : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  have hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥ :=
    MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)
  have := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (eM u).toEquiv.nontrivial

theorem exists_stages_over (B : Base) (hB : HasLetters B.toPre) (D : ℕ) :
    ∃ X : Stages, X.B = B ∧ X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  obtain ⟨W, h1, h2, h3⟩ := exists_rows B D
  have hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i) :=
    fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => (ipC_conj B u y x).symm) (fun u x _ h => ipC_pos B u x h)
    (show W.Drows ≤ W.Dall by omega)
  obtain ⟨G, -, hG⟩ := (GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)
  exact ⟨⟨B, _, GaloisStage.adapt W, V, S, N, G⟩, rfl, h1, h2, h3, hc, hG⟩

end StagesInhab

end GlobalTheory.Mem

end

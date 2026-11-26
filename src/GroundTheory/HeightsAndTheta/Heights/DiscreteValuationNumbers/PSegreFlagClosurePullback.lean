module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCut

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Blocks

variable (K : Type*)

def closureBlockEquiv : Option (Option K) ≃ K ⊕ Option Unit where
  toFun
    | none => Sum.inr none
    | some none => Sum.inr (some ())
    | some (some k) => Sum.inl k
  invFun
    | Sum.inl k => some (some k)
    | Sum.inr none => none
    | Sum.inr (some _) => some none
  left_inv := by rintro (_ | (_ | k)) <;> rfl
  right_inv := by rintro (k | (_ | ⟨⟩)) <;> rfl

variable {K} (ι : K → Type) (M M' : ℕ)

def closureVarEquiv :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) ≃ (Σ s, Sum.elim ι (lineBlocks M M') s) where
  toFun
    | ⟨none, l⟩ => ⟨Sum.inr none, l⟩
    | ⟨some none, l⟩ => ⟨Sum.inr (some ()), l⟩
    | ⟨some (some k), i⟩ => ⟨Sum.inl k, i⟩
  invFun
    | ⟨Sum.inl k, i⟩ => ⟨some (some k), i⟩
    | ⟨Sum.inr none, l⟩ => ⟨none, l⟩
    | ⟨Sum.inr (some _), l⟩ => ⟨some none, l⟩
  left_inv := by rintro ⟨_ | (_ | k), l⟩ <;> rfl
  right_inv := by rintro ⟨k | (_ | ⟨⟩), l⟩ <;> rfl

theorem closureVarEquiv_fst (v : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    (closureVarEquiv ι M M' v).1 = closureBlockEquiv K v.1 := by
  rcases v with ⟨_ | (_ | k), l⟩ <;> rfl

theorem joinDeg_comp_closureBlockEquiv (L : K → ℤ) :
    joinDeg (K' := Option Unit) L ∘ closureBlockEquiv K = liftPairDeg L := by
  funext o
  rcases o with _ | (_ | k) <;> rfl

theorem rename_liftPairForm {R : Type*} [CommRing R] (F : MRing ι R) :
    rename (closureVarEquiv ι M M') (liftPairForm M M' F) = joinForm (ι' := lineBlocks M M') F := by
  rw [liftPairForm, rename_rename]
  rfl

end Blocks

section Data

variable {K : Type} {ι : K → Type} {m : ℕ}

def joinClosureDeg (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) : Fin (1 + m) → K ⊕ Option Unit → ℤ :=
  Fin.append (fun _ : Fin 1 => ζ ∘ (closureBlockEquiv K).symm) (fun j => joinDeg (L j))

def joinClosureForm {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : Fin (1 + m) → MRing (Sum.elim ι (lineBlocks M M')) R :=
  Fin.append (fun _ : Fin 1 => h) (fun j => joinForm (F j))

theorem joinClosureDeg_comp (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    (fun i => joinClosureDeg ζ L i ∘ closureBlockEquiv K) = closureDeg ζ L := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureDeg, closureDeg, Fin.append_left]
    funext o
    simp
  · simp only [joinClosureDeg, closureDeg, Fin.append_right]
    exact joinDeg_comp_closureBlockEquiv _

theorem joinClosureDeg_natAdd (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    joinClosureDeg ζ L ∘ Fin.natAdd 1 = fun j => joinDeg (L j) := by
  funext j
  simp [joinClosureDeg, Fin.append_right]

theorem rename_closureForm {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (bundleIdx (bundleIdx ι M) M') R)
    (F : Fin m → MRing ι R) :
    (fun i => rename (closureVarEquiv ι M M') (closureForm M M' h F i)) =
      joinClosureForm M M' (rename (closureVarEquiv ι M M') h) F := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureForm, closureForm, Fin.append_left]
  · simp only [joinClosureForm, closureForm, Fin.append_right]
    exact rename_liftPairForm ι M M' _

theorem joinClosureForm_natAdd {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : joinClosureForm M M' h F ∘ Fin.natAdd 1 = fun j => joinForm (F j) := by
  funext j
  simp [joinClosureForm, Fin.append_right]

end Data

section PointIdeal

theorem pointIdeal_map_rename {K₁ K₂ : Type*} {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*} {R Φ : Type*} [CommRing R]
    [Field Φ] [Algebra R Φ] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Φ) : (pointIdeal R (y ∘ σ)).map (rename σ) = pointIdeal R y := by
  have key : ∀ f, pointConeMap R y (rename σ f) = rename e (pointConeMap R (y ∘ σ) f) := by
    intro f
    have h : (pointConeMap R y).toRingHom.comp (rename σ).toRingHom =
        (rename e).toRingHom.comp (pointConeMap R (y ∘ σ)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, MvPolynomial.algebraMap_eq]
      · intro v
        simp [pointConeMap, hσ]
    have := RingHom.congr_fun h f
    simpa using this
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    rw [key, hf, map_zero]
  · intro f hf
    have hf' : rename σ (rename σ.symm f) = f := by
      rw [rename_rename]
      simp
    rw [← hf']
    apply Ideal.mem_map_of_mem
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    apply rename_injective _ e.injective
    rw [map_zero, ← key, hf', hf]

theorem pointIdeal_algebraMap {K : Type*} {ι : K → Type*} {O Ω Φ : Type*} [CommRing O] [Field Ω] [Field Φ]
    [Algebra O Ω] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ] (y : (Σ k, ι k) → Ω) :
    pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := by
  have key : ∀ f, pointConeMap O (fun p => algebraMap Ω Φ (y p)) f =
      MvPolynomial.map (algebraMap Ω Φ) (pointConeMap O y f) := by
    intro f
    have h : (pointConeMap O (fun p => algebraMap Ω Φ (y p))).toRingHom =
        (MvPolynomial.map (algebraMap Ω Φ)).comp (pointConeMap O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, IsScalarTower.algebraMap_apply O Ω Φ]
      · intro v
        simp [pointConeMap]
    have := RingHom.congr_fun h f
    simpa using this
  ext f
  simp only [pointIdeal, RingHom.mem_ker, key]
  exact ⟨fun h => map_injective _ (algebraMap Ω Φ).injective (by rw [h, map_zero]),
    fun h => by rw [h, map_zero]⟩

end PointIdeal

theorem SegreFlagClosurePullback.proof (hPull : PairNumberPullback.Statement)
    (hExp : PairNumberExpansionIndependence.Statement) (hMod : SegreFlagClosureModel.Statement)
    (hRel : PairNumberRelabel.Statement) (hVJ : VerticalDivisorJoinPullback.Statement)
    (hBir : SegreFlagClosureBirational.Statement) : SegreFlagClosurePullback.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ'
    hφ hφ' Φ _ _ _ _ e t ht k hk1 hkN f₁ g₁ hD₁ _ n z z' fz gz hz r Bf hBf As Bs hAs hBs Q hQ
  classical
  let : ∀ s, Fintype (Sum.elim ι (lineBlocks M M') s) := fun s =>
    match s with
    | Sum.inl k => inferInstanceAs (Fintype (ι k))
    | Sum.inr o => inferInstanceAs (Fintype (lineBlocks M M' o))

  have hpt : joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k) ∘ closureVarEquiv ι M M' =
      flagClosurePt y w e φ φ' t k := by
    funext p
    rcases p with ⟨_ | (_ | o), l⟩ <;> rfl
  have hPJ : (pointIdeal O (flagClosurePt y w e φ φ' t k)).map (rename (closureVarEquiv ι M M')) =
      pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k)) := by
    rw [← hpt]
    exact pointIdeal_map_rename (closureBlockEquiv K) _ (closureVarEquiv_fst ι M M') _
  have hPV : pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := pointIdeal_algebraMap y
  obtain ⟨hRmod, hRvert, hRnum⟩ := hRel O ϖ (Option (Option K)) (bundleIdx (bundleIdx ι M) M')
    (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) (closureBlockEquiv K) (closureVarEquiv ι M M')
    (closureVarEquiv_fst ι M M') (pointIdeal O (flagClosurePt y w e φ φ' t k))
  rw [hPJ] at hRmod hRvert hRnum
  have hJmod : IsModelOver (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) (d + (k - 1)) :=
    hRmod _ (hMod O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k
      hk1 hkN).1

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O (fun p => algebraMap Ω Φ (y p))) ϖ
      (Fin.append x z i - Fin.append x' z' i) (Fin.append f fz i) (Fin.append g gz i) := by
    rw [hPV]
    exact fun i => Fin.addCases (fun i => by simpa only [Fin.append_left] using hF.vertical i)
      (fun j => by simpa only [Fin.append_right] using hz j) i

  have hT := hRnum (1 + (N + n)) (joinClosureDeg (zetaFirst a₀) (Fin.append x z))
    (joinClosureDeg (zetaSecond a₀') (Fin.append x' z')) (closureForm M M' f₁ (Fin.append f fz))
    (closureForm M M' g₁ (Fin.append g gz)) As (Q.map joinDeg)
  have hQ' : (Q.map joinDeg).map (· ∘ closureBlockEquiv K) = Q.map liftPairDeg := by
    rw [List.map_map]
    exact List.map_congr_left fun L _ => joinDeg_comp_closureBlockEquiv L
  rw [rename_closureForm, rename_closureForm, joinClosureDeg_comp, joinClosureDeg_comp, hQ'] at hT
  rw [← hT]

  have hvJ : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) ϖ
      (joinClosureDeg (zetaFirst a₀) (Fin.append x z) i - joinClosureDeg (zetaSecond a₀') (Fin.append x' z') i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') f₁) (Fin.append f fz) i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') g₁) (Fin.append g gz) i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_left]
      apply hRvert
      have hζ : (zetaFirst a₀ ∘ (closureBlockEquiv K).symm - zetaSecond a₀' ∘ (closureBlockEquiv K).symm) ∘
          closureBlockEquiv K = zetaFirst a₀ - zetaSecond a₀' := by
        funext o
        simp
      rw [hζ]
      exact hD₁
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_right]
      have hd : joinDeg (K' := Option Unit) (Fin.append x z j) - joinDeg (Fin.append x' z' j) =
          joinDeg (Fin.append x z j - Fin.append x' z' j) := by
        funext s
        rcases s with s | s <;> simp [joinDeg]
      rw [hd]
      exact hVJ O ϖ Φ K ι (Option Unit) (lineBlocks M M') _ _ _ _ _ (hvert j)

  rw [hExp O ϖ hϖ (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) _ (d + (k - 1)) hJmod (1 + (N + n)) _ _ _ _
    hvJ r (rename (Fin.natAdd 1) Bf) (hBf.rename_isHomogeneous) As (pushExpansion (Fin.natAdd 1) Bs) hAs
    (isPairExpansion_push _ hBs) (Q.map joinDeg) (by rw [List.length_map]; omega),
    pairNum_pushExpansion, joinClosureDeg_natAdd, joinClosureDeg_natAdd, joinClosureForm_natAdd,
    joinClosureForm_natAdd]

  have hPB := hPull O ϖ hϖ Φ K ι (Option Unit) (lineBlocks M M') (fun p => algebraMap Ω Φ (y p))
    (flagLinePt w e φ φ' t k) d (k - 1) (by rw [hPV]; exact hV) hJmod (N + n) (Fin.append x z)
    (Fin.append x' z') (Fin.append f fz) (Fin.append g gz) hvert r Bf hBf Bs hBs Q (by omega)
  split_ifs with hk
  · obtain rfl := hk
    rw [hPB.2 (hBir O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht hkN),
      hPV]
  · exact hPB.1 (by omega)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinCkOnFlagPair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace ChernClassOnFlagPair

theorem fieldNum_spec (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type) [∀ k, Fintype (κ k)] :
    IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem append_pullDeg {K K' : Type} {a b : ℕ} (u : Fin a → K → ℤ) (v : Fin b → K → ℤ) :
    Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (u i))
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (v j)) =
      fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (Fin.append u v l) := by
  funext l
  induction l using Fin.addCases with
  | left i => simp
  | right j => simp

theorem isVertDiv_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    (b : K → ℤ) (hb : b = 0) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b 1 1 := by
  subst hb
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι O) 0 := by
    simpa using IndefiniteRowSideFullHecke.NumbersDVR.Bundles.isMultiHomog_C O (ι := ι) (1 : O)
  refine ⟨⟨0, 0, h1, h1, by simp⟩, ?_, ?_, fun Q hQ _ _ => ⟨1, 1, ⟨0, h1⟩, ⟨0, h1⟩, ?_, ?_, by simp⟩⟩
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)

theorem length_classList {K σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls μ).length = μ.degree := by
  simp [classList, Finsupp.card_toMultiset, Finsupp.sum]
  rfl

theorem isFlagPair_self {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime] {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
    {B : ChartBundle O (segreVec y) N E} {w : Module.Basis (Fin N) Ω E} {x : Fin N → K → ℤ}
    (h : IsFlagFrame y B w x) :
    IsFlagPair ϖ y B B w w x x (fun _ => 1) (fun _ => 1) := by
  refine ⟨h, h, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hij.ne]
  · intro i
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  · intro i
    simp [Module.Basis.repr_self]

end ChernClassOnFlagPair


open ChernClassOnFlagPair in
theorem ChernClassOnFlagPair.proof (h1 : JoinPointFlagModel.Statement)
    (h2 : JoinPointNumbers.Statement) (h3 : FlagModelValueIndependence.Statement)
    (h4 : FlagModelRootIndependence.Statement) (h5 : plainPolynomialPairNumber.Statement)
    (h6 : RootPolynomialNumber.Statement) (h7 : PairNumberExpansionIndependence.Statement)
    (h8 : dividedDifferenceExpansion.Statement) : ChernClassOnFlagPair.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hK hW N E _ _ B B' hBB' w w' x x' f g hfp
  have hW2 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) d :=
    (BundleExamples.isModelOver_iff O _ d).mpr ⟨hK, hW⟩
  have hprime : (pointIdeal O y).IsPrime := hW2.2.1.1
  refine ⟨fun k hk1 hk2 Gs hGs q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, hd', hf, hg⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B' hBB' w w' x x' f g hfp
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B' :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B') := ⟨F₀⟩
    have hv : F₀.value O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _) (Fin.append φ.deg' _)
        (Fin.append φ.f _) (Fin.append φ.g _) _ = _
      rw [hd, hd', hf, hg]
    have hW' : ∀ H : MvPolynomial (Fin (N + q)) ℤ, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1) H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O y) d (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1)
          (Fin.append g fun _ => 1) H := by
      intro H
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
      simp only [append_pullDeg]
      refine Finset.sum_congr rfl fun l _ => ?_
      induction l using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact (h2 O ϖ hϖ Ω K ι y d hW _ _ _).1 _ _ _ (hfp.vertical i)
      | right j =>
        simp only [Fin.append_right, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, sub_self,
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval, Finsupp.sum_zero_index]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ck
    rw [dite_eq_left hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h3 O Ω K ι y d N E B B' hW2 ((BundleExamples.sameGeneric_iff hϖ y B B').mpr hBB')
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => isVertDiv_one hprime _ (sub_self _)) k Q hk2 (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((hW' _).trans ((h5 O K ι (pointIdeal O y) d N x x' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q L Q hQ).trans ?_))
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList L μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [h7 O ϖ hϖ K ι (pointIdeal O y) d hW N x x' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ Gs (h8 N k _ (isHomogeneous_psum N k)) hGs (classList L μ) hlen]
  · have hsame : SameGenericFibre ϖ B B := fun c _ =>
      ⟨fun v hv => ⟨0, by simpa using hv⟩, fun v hv => ⟨0, by simpa using hv⟩⟩
    obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, -, -, -⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B hsame w w x x _ _ (isFlagPair_self hfp.flag)
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B) := ⟨F₀⟩
    have hv : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι F₀.ι')) W d
          (Fin.append F₀.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₀.K') (L l))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y F₀.z)) (C a))) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) W d
          (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (Fin.append x L j))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum _ W d
          (Fin.append φ.deg _) _) _ = _
      rw [hd, append_pullDeg]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.rootNum
    rw [dite_eq_left hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h4 O Ω K ι y d N E B B hW2 ((BundleExamples.sameGeneric_iff hϖ y B B).mpr hsame)
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) c G hsym hG hc q L Q hQ a
      ha).trans ?_
    refine hv.trans (((h2 O ϖ hϖ Ω K ι y d hW _ _ _).2 a ha).trans ?_)
    exact h6 O K ι (pointIdeal O y) d N x c G hG hc q L Q hQ a

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HsymmShiftProof

open NumericalSegreProof

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [Fintype K] [DecidableEq K] in
theorem length_rootList {n : ℕ} (x : Fin n → K → ℤ) (α : Fin n → ℕ) :
    (rootList x α).length = ∑ i, α i := by
  unfold rootList
  simp [List.length_flatMap, Fin.sum_univ_def]

theorem cons_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F W ((c + c') :: l) = intNumL F W (c :: l) + intNumL F W (c' :: l) := by
  have key : ∀ e, Function.update (c :: l).get (0 : Fin (l.length + 1)) e = (e :: l).get := by
    intro e
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := FieldNumbers.IntNumAdd.full.{u} F K ι W hW.multiHomog hW.relevant (l.length + 1) hd
    ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

theorem replicate_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W)
    (z s : K → ℤ) : ∀ (n : ℕ) (L : List (K → ℤ)),
    FieldNumbers.relDim W = ((n + L.length : ℕ) : WithBot (WithTop ℤ)) →
    intNumL F W (List.replicate n (z + s) ++ L) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) *
        intNumL F W (List.replicate (n - k) z ++ List.replicate k s ++ L)
  | 0, L, _ => by simp
  | n + 1, L, hd => by
    have hd' : ∀ c : K → ℤ,
        FieldNumbers.relDim W = ((n + (c :: L).length : ℕ) : WithBot (WithTop ℤ)) := by
      intro c
      rw [hd, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    rw [List.replicate_succ, List.cons_append,
      cons_add W hW _ (by rw [hd, List.length_append, List.length_replicate]; congr 1; omega) z s,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s))).symm,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s)) (a := s)).symm,
      replicate_add W hW z s n (z :: L) (hd' z), replicate_add W hW z s n (s :: L) (hd' s),
      ProjectiveBundleNumbers.sum_choose_succ n (fun k => intNumL F W (List.replicate (n + 1 - k) z ++ List.replicate k s ++ L))]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      congr 1
      refine intNumL_perm F W ?_
      rw [show n + 1 - k = (n - k) + 1 by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]
      exact List.Perm.append_left _ List.perm_middle
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [show n + 1 - (k + 1) = n - k by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]

def H (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ) (L : List (K → ℤ)) : ℤ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple n c, intNumL F W (rootList x α ++ L)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_zero (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (L : List (K → ℤ)) :
    H W x 0 L = intNumL F W L := by
  simp [H, Finset.Nat.antidiagonalTuple_zero_right, rootList_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_one (W : Ideal (MRing ι F)) (x : Fin 1 → K → ℤ) (c : ℕ) (L : List (K → ℤ)) :
    H W x c L = intNumL F W (List.replicate c (x 0) ++ L) := by
  unfold H
  rw [Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton, rootList_succ]
  simp [rootList]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_perm (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ)
    {L L' : List (K → ℤ)} (h : L.Perm L') : H W x c L = H W x c L' :=
  Finset.sum_congr rfl fun _ _ => intNumL_perm F W (h.append_left _)

theorem H_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) {n : ℕ} (x : Fin n → K → ℤ)
    (c : ℕ) (L : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((c + 1 + L.length : ℕ) : WithBot (WithTop ℤ))) (a b : K → ℤ) :
    H W x c ((a + b) :: L) = H W x c (a :: L) + H W x c (b :: L) := by
  unfold H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlen : (rootList x α).length = c := by
    rw [length_rootList]
    exact Finset.Nat.mem_antidiagonalTuple.mp hα
  rw [intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a + b)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := b))]
  exact cons_add W hW _
    (by rw [hd, List.length_append, hlen, show c + 1 + L.length = c + L.length + 1 by omega]) a b


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_succ (W : Ideal (MRing ι F)) {i : ℕ} (x : Fin (i + 1) → K → ℤ) (c : ℕ)
    (L : List (K → ℤ)) :
    H W x (c + 1) L = H W (fun j => x (Fin.castSucc j)) (c + 1) L + H W x c (x (Fin.last i) :: L) := by
  unfold H
  rw [sum_antidiagonalTuple_succ]
  congr 1
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [rootList_snoc_zero]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [rootList_update_last, List.append_assoc, List.singleton_append]

theorem sum_choose_pascal (M r : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((M + 1).choose k : ℤ) * f k =
      ∑ k ∈ Finset.range (r + 1 + 1), (M.choose k : ℤ) * f k +
        ∑ k ∈ Finset.range (r + 1), (M.choose k : ℤ) * f (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (M.choose k : ℤ) * f k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  ring

theorem main (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (s : K → ℤ) :
    ∀ (N : ℕ) (x : Fin (N + 1) → K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
    FieldNumbers.relDim W = ((r + Y.length : ℕ) : WithBot (WithTop ℤ)) →
    H W (fun i => x i + s) r Y =
      ∑ k ∈ Finset.range (r + 1), ((N + r).choose k : ℤ) * H W x (r - k) (List.replicate k s ++ Y)
  | 0, x, r, Y, hd => by
    rw [H_one, replicate_add W hW (x 0) s r Y hd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [H_one, List.append_assoc, show 0 + r = r from Nat.zero_add r]
  | N + 1, x, r, Y, hd => by
    induction r generalizing Y with
    | zero => simp [H_zero]
    | succ r ih =>
      have e1 := main W hW s N (fun j => x (Fin.castSucc j)) (r + 1) Y hd
      have e2 := ih (x (Fin.last (N + 1)) :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have e3 := ih (s :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have hadd := H_add W hW (fun i => x i + s) r Y hd (x (Fin.last (N + 1))) s
      have hAB : ∑ k ∈ Finset.range (r + 1 + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - k) (List.replicate k s ++ Y) =
          ∑ k ∈ Finset.range (r + 1 + 1), ((N + (r + 1)).choose k : ℤ) *
              H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y) +
            ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
              H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y) := by
        rw [show N + (r + 1) = N + 1 + r by omega, Finset.sum_range_succ,
          Finset.sum_range_succ (fun k => ((N + 1 + r).choose k : ℤ) *
            H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y)),
          Nat.sub_self, H_zero, H_zero,
          add_right_comm _ _ (∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y)),
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [show r + 1 - k = (r - k) + 1 by omega, H_succ W x (r - k) (List.replicate k s ++ Y),
          ← mul_add, H_perm W x (r - k) (List.perm_middle (l₁ := List.replicate k s)).symm]
      have hC : ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - (k + 1)) (List.replicate (k + 1) s ++ Y) =
          ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ s :: Y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.add_sub_add_right, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [H_succ W (fun i => x i + s) r Y]
      beta_reduce at e1 ⊢
      rw [e1, hadd, e2, e3, show N + 1 + (r + 1) = N + 1 + r + 1 by omega,
        sum_choose_pascal (N + 1 + r) r (fun k => H W x (r + 1 - k) (List.replicate k s ++ Y)), hAB, hC]
      ring

end HsymmShiftProof

theorem HsymmShift.proof : HsymmShift.Statement.{u} := by
  intro F _ K _ _ ι _ W hW d hd N hN x s r Y hrY
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := HsymmShiftProof.main W hW s M x r Y (by rw [hd, ← hrY])
  simp only [HsymmShiftProof.H] at h
  rw [h, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.append_assoc]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMult
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpHorizontalMult.proof (hmin : BlowUpHorizontalMinimal.Statement.{u})
    (hchart : BlowUpHorizontalChartLength.Statement.{u}) : BlowUpHorizontalMult.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  have hm := hmin O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW
  obtain ⟨hWp, hBW, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  obtain ⟨-, -, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hrel
  have hcond : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    unfold divCycle at hW
    rw [dite_eq_right h] at hW
    exact hW rfl
  have hch := hchart O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  have := hWp
  have hp := PolynomialLocalizedLength.full (MRing ι O) (W.comap (liftForm (ι := ι) (J := J) (R := O))) (P ⊔ Ideal.span {x})
  unfold divCycle
  rw [dite_eq_left ⟨hm, hrel₀⟩, dite_eq_left hcond]
  congr 2
  exact (hp.symm.trans hch.symm : _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelValueIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace FlagModelValueIndependence

theorem fieldNum_isFieldIntersection (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type)
    [∀ k, Fintype (κ k)] : IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem pullDeg_sub {K K' : Type} (a b : K → ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (a - b) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') a - IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') b := by
  funext k
  cases k <;> simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]

theorem proof (hOne : FlagPairValueIndependence.Statement) (hCommon : FlagModelCommonModel.Statement) :
    FlagModelValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂ I₁ I₂ hI₁ hI₂ G hG r y y' f g hv c Q hc hGc hQ
  obtain ⟨K'', _, ι'', _, z, EB, E'B, φ₁, φ₂, hZ, -, -, -, hS, hpull, hval⟩ :=
    hCommon O Ω K ι x d N V E E' hW hE F₁ F₂
  have hI := fieldNum_isFieldIntersection (IsLocalRing.ResidueField O) (Sum.elim ι ι'')
  obtain ⟨h₁, h₂⟩ := hval _ I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hGc hQ
  rw [h₁, h₂]
  refine hOne O Ω (K ⊕ K'') (Sum.elim ι ι'') (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) d N V EB E'B hZ hS
    φ₁ φ₂ _ hI G hG r (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y l))
    (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y' l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l)) (fun l => ?_) c Q hc hGc hQ
  rw [← pullDeg_sub]
  exact hpull _ _ _ (hv l)

end FlagModelValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinRight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord midDeg midVar assocDeg assocVar midSwapBlocks midSwapVars
  midSwapVars_fst joinCoord_comp_midSwapVars)

namespace PairNumberJoinRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_comp_midSwapBlocks (a : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) a ∘ midSwapBlocks = midDeg (K₂ := K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midSwapVars_comp_midVar :
    ⇑(midSwapVars ι ι' ι₂) ∘ midVar (ι := ι) (ι' := ι') ι₂ = assocVar ι₂ := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem midDeg_sub (a b : K ⊕ K' → ℤ) :
    midDeg (K₂ := K₂) a - midDeg (K₂ := K₂) b = midDeg (K₂ := K₂) (a - b) := by
  funext k
  rcases k with k | k | k <;> simp [midDeg]

end PairNumberJoinRight


open PairNumberJoinRight in
theorem PairNumberJoinRight.proof (hLeft : PairNumberJoinLeft.Statement)
    (hVert : JoinVerticalDivisorRight.Statement) (hRel : PairNumberRelabelAlt.Statement) :
    PairNumberJoinRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  classical
  have hy := joinCoord_comp_midSwapVars x z w
  obtain ⟨hZL, hfnL, -, hnum⟩ := hRel O Ω (K ⊕ (K₂ ⊕ K')) (Sum.elim ι (Sum.elim ι₂ ι'))
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) midSwapBlocks (midSwapVars ι ι' ι₂) midSwapVars_fst
    (joinCoord x (joinCoord z w)) d (by rw [hy]; exact hZ)
  have hIL : IsFieldIntersection (F := IsLocalRing.ResidueField O) (ι := Sum.elim ι (Sum.elim ι' ι₂))
      (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) :=
    IntNumIsFieldIntersection.full _ _ _
  rw [hLeft O Ω K ι x K' ι' z K₂ ι₂ w d hF hZL (hfnL.trans (by rw [hy]; exact hfn)) _ I₁ hIL hI₁ n a a'
    f g hv H hH]
  have key := hnum I _ hI hIL n (fun i => assocDeg (K₂ := K₂) (a i)) (fun i => assocDeg (K₂ := K₂) (a' i))
    (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) (fun i => by
      rw [hy, assocDeg_comp_midSwapBlocks, assocDeg_comp_midSwapBlocks, midDeg_sub]
      exact hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)) H hH
  simp only [hy, assocDeg_comp_midSwapBlocks, rename_rename, midSwapVars_comp_midVar] at key
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinRight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar midDeg midVar FlagModel)

namespace FlagModelJoinRightAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem midDeg_pullDeg (a : K → ℤ) :
    midDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K₂ ⊕ K') a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midVar_comp_liftVar :
    midVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι₂ ι') :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinRightAlt


open FlagModelJoinRightAlt in
theorem FlagModelJoinRightAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinRight.Statement) (hNum : PairNumberJoinRight.Statement) :
    FlagModelJoinRightAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  rw [hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r)
    _ _ _ _ hvert _ hH]
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, midDeg_pullDeg, midVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence

@[expose] public section

section -- merged from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityInSection
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

namespace E7

section Gr

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def IsGrHom (G H : GMod B R k) (φ : G.M →ₗ[R] H.M) : Prop :=
  ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m

def IsGrHom.dsMap {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ) :
    (DirectSum (Deg k) fun i => G.gr i) →+ DirectSum (Deg k) fun i => H.gr i :=
  DirectSum.map fun i => ((φ.restrictScalars B).restrict (hφ i)).toAddMonoidHom

theorem IsGrHom.coe_dsMap {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ)
    (a : DirectSum (Deg k) fun i => G.gr i) :
    DirectSum.coeAddMonoidHom H.gr (hφ.dsMap a) = φ (DirectSum.coeAddMonoidHom G.gr a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [IsGrHom.dsMap, DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem IsGrHom.strict {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) (hH : DirectSum.IsInternal H.gr) {m : Deg k} {x : G.M}
    (hx : φ x ∈ H.gr m) : ∃ y ∈ G.gr m, φ y = φ x := by
  obtain ⟨a, rfl⟩ := hG.2 x
  have h : hφ.dsMap a = DirectSum.of (fun i => H.gr i) m ⟨_, hx⟩ := by
    apply hH.1
    rw [hφ.coe_dsMap, DirectSum.coeAddMonoidHom_of]
  have h2 := congrArg (fun b => ((b m : H.gr m) : H.M)) h
  simp only [DirectSum.of_eq_same] at h2
  refine ⟨a m, (a m).2, ?_⟩
  rw [← h2, IsGrHom.dsMap, DirectSum.map_apply]
  rfl

theorem IsGrHom.range_hom {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) : H.IsHomSub (LinearMap.range φ) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hG.2 x
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [DirectSum.coeAddMonoidHom_of]
      exact Submodule.subset_span ⟨⟨_, rfl⟩, i, hφ i _ x.2⟩
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    exact fun x hx => hx.1

def sesOfExact {G' G H : GMod B R k} (f : G'.M →ₗ[R] G.M) (φ : G.M →ₗ[R] H.M)
    (hf : Function.Injective f) (hex : Function.Exact f φ)
    (hfgr : ∀ m, G'.gr m = (G.gr m).comap (f.restrictScalars B)) (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) (hH : DirectSum.IsInternal H.gr) :
    SES G' G (H.sub (LinearMap.range φ)) where
  f := f
  g := φ.rangeRestrict
  inj := hf
  surj := φ.surjective_rangeRestrict
  exact y := by
    rw [← hex y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  f_gr := hfgr
  g_gr m := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := z.2
      have hz' : φ x ∈ H.gr m := by
        rw [hx]
        exact hz
      obtain ⟨y, hy, hyx⟩ := hφ.strict hG hH hz'
      exact ⟨y, hy, Subtype.ext (hyx.trans hx)⟩
    · rintro ⟨y, hy, rfl⟩
      exact hφ m y hy

def sesOfKer {G H : GMod B R k} (N : Submodule R G.M) (φ : G.M →ₗ[R] H.M)
    (hN : ∀ y, φ y = 0 ↔ y ∈ N) (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) (hH : DirectSum.IsInternal H.gr) :
    SES (G.sub N) G (H.sub (LinearMap.range φ)) :=
  sesOfExact (G' := G.sub N) N.subtype φ N.injective_subtype
    (fun y => by
      rw [hN y]
      exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩)
    (fun _ => rfl) hφ hG hH

theorem ann_le_sub (F : GMod B R k) (N : Submodule R F.M) : F.Ann ≤ (F.sub N).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro x
  exact Subtype.ext (ha x.1)

theorem ann_le_quo (F : GMod B R k) (N : Submodule R F.M) : F.Ann ≤ (F.quo N).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro y
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  exact (map_smul N.mkQ a x).symm.trans ((congrArg N.mkQ (ha x)).trans (map_zero _))

theorem secs_cons_le_sup (δ : Deg k) (σ : R) (ts : List (Deg k × R)) :
    secs ((δ, σ) :: ts) ≤ Ideal.span {σ} ⊔ secs ts := by
  rw [secs, Ideal.span_le]
  rintro x ⟨d, hd⟩
  rcases List.mem_cons.1 hd with h | h
  · have : x = σ := congrArg Prod.snd h
    subst this
    exact Ideal.mem_sup_left (Ideal.subset_span rfl)
  · exact Ideal.mem_sup_right (Ideal.subset_span ⟨d, h⟩)

theorem admissible_tail_of_cons_mem_ideal [IsLocalRing B] (𝒜 : Deg k → Submodule B R) {δ : Deg k} {σ : R}
    {ts : List (Deg k × R)} {J J' : Ideal R} (h : admitted 𝒜 ((δ, σ) :: ts) J) (hJ : J ≤ J')
    (hσ : σ ∈ J') : admitted 𝒜 ts J' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le (le_sup_of_le_left hJ) ((secs_cons_le_sup δ σ ts).trans
    (sup_le (le_sup_of_le_left ?_) le_sup_right)))⟩
  rwa [Ideal.span_singleton_le_iff_mem]

end Gr

section Maps

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable (F : GMod B R k) (s s' : R) (d d' : Deg k)

def phi1 : ((F.shift d).ann s' d').M →ₗ[R] (F.ann (s * s') (d + d')).M :=
  LinearMap.codRestrict (LinearMap.ker (LinearMap.lsmul R F.M (s * s')))
    (LinearMap.ker (LinearMap.lsmul R F.M s')).subtype (fun x => by
      have hx : s' • x.1 = 0 := x.2
      show (s * s') • x.1 = 0
      rw [mul_smul, hx, smul_zero])

def phi2 : (F.ann (s * s') (d + d')).M →ₗ[R] (F.ann s d).M :=
  LinearMap.codRestrict (LinearMap.ker (LinearMap.lsmul R F.M s))
    ((LinearMap.lsmul R F.M s').comp (LinearMap.ker (LinearMap.lsmul R F.M (s * s'))).subtype)
    (fun x => by
      have hx : (s * s') • x.1 = 0 := x.2
      show s • s' • x.1 = 0
      rw [← mul_smul, hx])

def phi3 : (F.ann s d).M →ₗ[R] ((F.shift d).quot s').M :=
  (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ.comp
    (LinearMap.ker (LinearMap.lsmul R F.M s)).subtype

def phi4 : ((F.shift d).quot s').M →ₗ[R] (F.quot (s * s')).M :=
  Submodule.mapQ (LinearMap.range (LinearMap.lsmul R F.M s'))
    (LinearMap.range (LinearMap.lsmul R F.M (s * s'))) (LinearMap.lsmul R F.M s) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, mul_smul s s' x⟩)

def phi5 : (F.quot (s * s')).M →ₗ[R] (F.quot s).M :=
  Submodule.mapQ (LinearMap.range (LinearMap.lsmul R F.M (s * s')))
    (LinearMap.range (LinearMap.lsmul R F.M s)) LinearMap.id (by
      rintro _ ⟨x, rfl⟩
      exact ⟨s' • x, (mul_smul s s' x).symm⟩)

end Maps

section Main

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable (𝒜 : Deg k → Submodule B R) (F : GMod B R k) (s s' : R) (d d' : Deg k)

theorem kernel_inclusion_product_injective : Function.Injective (phi1 F s s' d d') :=
  fun x y h => by
    have h' : x.1 = y.1 :=
      congrArg (fun z : LinearMap.ker (LinearMap.lsmul R F.M (s * s')) => z.1) h
    exact Subtype.ext h'

theorem kernel_inclusion_grading_comap (m : Deg k) : ((F.shift d).ann s' d').gr m =
    ((F.ann (s * s') (d + d')).gr m).comap ((phi1 F s s' d d').restrictScalars B) := by
  ext x
  show x.1 ∈ F.gr (m - d' - d) ↔ x.1 ∈ F.gr (m - (d + d'))
  rw [show m - d' - d = m - (d + d') by abel]

theorem kernel_inclusion_product_exact : Function.Exact (phi1 F s s' d d') (phi2 F s s' d d') := by
  intro y
  constructor
  · intro h
    have h' : s' • y.1 = 0 := congrArg Subtype.val h
    exact ⟨⟨y.1, h'⟩, Subtype.ext rfl⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext x.2

theorem product_kernel_to_kernel_isGraded (hF : F.IsGr 𝒜) (hs' : s' ∈ 𝒜 d') :
    IsGrHom (F.ann (s * s') (d + d')) (F.ann s d) (phi2 F s s' d d') := by
  intro m x hx
  have hx' : x.1 ∈ F.gr (m - (d + d')) := hx
  show s' • x.1 ∈ F.gr (m - d)
  have h := hF.smul_mem hs' hx'
  rwa [show d' + (m - (d + d')) = m - d by abel] at h

theorem ker3 (y : (F.ann s d).M) :
    phi3 F s s' d y = 0 ↔ y ∈ LinearMap.range (phi2 F s s' d d') := by
  constructor
  · intro h
    have h' : y.1 ∈ LinearMap.range (LinearMap.lsmul R F.M s') :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨x, hx⟩ := h'
    have hx' : s' • x = y.1 := hx
    have hy : s • y.1 = 0 := y.2
    refine ⟨⟨x, ?_⟩, Subtype.ext hx'⟩
    show (s * s') • x = 0
    rw [mul_smul, hx', hy]
  · rintro ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x.1, rfl⟩

theorem kernel_to_shift_quotient_isGraded : IsGrHom (F.ann s d) ((F.shift d).quot s') (phi3 F s s' d) :=
  fun _ x hx => ⟨x.1, hx, rfl⟩

theorem ker4 (y : ((F.shift d).quot s').M) :
    phi4 F s s' d y = 0 ↔ y ∈ LinearMap.range (phi3 F s s' d) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective y
    have h' : s • x ∈ LinearMap.range (LinearMap.lsmul R F.M (s * s')) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨z, hz⟩ := h'
    have hz' : (s * s') • z = s • x := hz
    refine ⟨⟨x - s' • z, ?_⟩, ?_⟩
    · show s • (x - s' • z) = 0
      rw [smul_sub, ← mul_smul, hz', sub_self]
    · show (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ (x - s' • z) = _
      rw [map_sub, sub_eq_self]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : s • w.1 = 0 := w.2
    show (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ (s • w.1) = 0
    rw [hw, map_zero]

theorem quotient_to_product_quotient_isGraded (hF : F.IsGr 𝒜) (hs : s ∈ 𝒜 d) :
    IsGrHom ((F.shift d).quot s') (F.quot (s * s')) (phi4 F s s' d) := by
  rintro m _ ⟨x, hx, rfl⟩
  have hx' : x ∈ F.gr (m - d) := hx
  have h := hF.smul_mem hs hx'
  rw [show d + (m - d) = m by abel] at h
  exact ⟨s • x, h, rfl⟩

theorem ker5 (y : (F.quot (s * s')).M) :
    phi5 F s s' y = 0 ↔ y ∈ LinearMap.range (phi4 F s s' d) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ_surjective y
    have h' : x ∈ LinearMap.range (LinearMap.lsmul R F.M s) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨z, hz⟩ := h'
    have hz' : s • z = x := hz
    refine ⟨(LinearMap.range (LinearMap.lsmul R F.M s')).mkQ z, ?_⟩
    show (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ (s • z) = _
    rw [hz']
  · rintro ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩

def ses5 : SES ((F.quot (s * s')).sub (LinearMap.range (phi4 F s s' d))) (F.quot (s * s'))
    (F.quot s) where
  f := (LinearMap.range (phi4 F s s' d)).subtype
  g := phi5 F s s'
  inj := Submodule.injective_subtype _
  surj y := by
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ_surjective y
    exact ⟨(LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ x, rfl⟩
  exact y := by
    rw [ker5 F s s' d]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  f_gr _ := rfl
  g_gr m := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩

theorem mul_mem_annihilator_product_kernel : s * s' ∈ (F.ann (s * s') (d + d')).Ann :=
  Module.mem_annihilator.2 fun x => Subtype.ext x.2

theorem mul_mem_annihilator_kernel : s * s' ∈ (F.ann s d).Ann :=
  Module.mem_annihilator.2 fun x => Subtype.ext (by
    have hx : s • x.1 = 0 := x.2
    show (s * s') • x.1 = 0
    rw [mul_comm, mul_smul, hx, smul_zero])

theorem mul_mem_annihilator_shift_quotient : s * s' ∈ ((F.shift d).quot s').Ann :=
  Module.mem_annihilator.2 fun y => by
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective y
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨s • x, ?_⟩
    show s' • s • x = (s * s') • x
    rw [← mul_smul, mul_comm]

theorem mul_mem_annihilator_product_quotient : s * s' ∈ (F.quot (s * s')).Ann :=
  Module.mem_annihilator.2 fun y => by
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ_surjective y
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

end Main

end E7

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

section -- merged from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIrr
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

theorem ruleIrr : RuleIrr := by
  rintro k X F hF ⟨N, hN⟩
  filter_upwards [hF.eventually_gr_le X.std X.iSup_eq_top N] with m hm
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  refine Submodule.smul_induction_on (hm y hy) ?_ ?_
  · intro a ha z _
    exact Module.mem_annihilator.1 (hN ha) z
  · intro x y hx hy
    rw [hx, hy, add_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

section -- merged from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerRuleProductZero
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter


open E7 in
theorem euler_char_product_eventually_add (hE1 : EulerAdditivityExactSequence) (hGr : RuleGr) {k : ℕ} (X : HidaSetting k)
    (ts : List (Deg k × X.R)) (F : X.Mod) (d d' : Deg k) (s s' : X.R)
    (hV : Valid X.𝒜 ((d, s) :: (d', s') :: ts)) (hF : F.IsGr X.𝒜)
    (hA : admitted X.𝒜 ((d + d', s * s') :: ts) F.Ann) :
    ∀ᶠ m in atTop, chi ((d + d', s * s') :: ts) F m =
      chi ((d, s) :: ts) F m + chi ((d', s') :: ts) (F.shift d) m := by
  have hs : 0 ≤ d ∧ s ∈ X.𝒜 d := hV (d, s) List.mem_cons_self
  have hs' : 0 ≤ d' ∧ s' ∈ X.𝒜 d' := hV (d', s') (List.mem_cons_of_mem _ List.mem_cons_self)
  have hVt : Valid X.𝒜 ts :=
    fun p hp => hV p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hss : s * s' ∈ X.𝒜 (d + d') := SetLike.mul_mem_graded hs.2 hs'.2
  have hFd := (hGr k X F hF).2.1 d
  have hP14 := (hGr k X _ hFd).2.2 d' s' hs'.2
  have hP25 := (hGr k X F hF).2.2 (d + d') (s * s') hss
  have hP36 := (hGr k X F hF).2.2 d s hs.2
  have g2 := product_kernel_to_kernel_isGraded X.𝒜 F s s' d d' hF hs'.2
  have g3 := kernel_to_shift_quotient_isGraded F s s' d
  have g4 := quotient_to_product_quotient_isGraded X.𝒜 F s s' d hF hs.2
  have hI2 := ((hGr k X _ hP36.2).1 _ (g2.range_hom hP25.2.internal)).1
  have hI3 := ((hGr k X _ hP14.1).1 _ (g3.range_hom hP36.2.internal)).1
  have hI4 := ((hGr k X _ hP25.1).1 _ (g4.range_hom hP14.1.internal)).1
  have a2 : admitted X.𝒜 ts (F.ann (s * s') (d + d')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_product_kernel F s s' d d')
  have a3 : admitted X.𝒜 ts (F.ann s d).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_kernel F s s' d)
  have a4 : admitted X.𝒜 ts ((F.shift d).quot s').Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo (F.shift d) _) (mul_mem_annihilator_shift_quotient F s s' d)
  have a5 : admitted X.𝒜 ts (F.quot (s * s')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo F _) (mul_mem_annihilator_product_quotient F s s')
  have e2 := hE1 k X ts _ _ _ hVt hP14.2 hP25.2 hI2
    (sesOfExact (phi1 F s s' d d') (phi2 F s s' d d') (kernel_inclusion_product_injective F s s' d d')
      (kernel_inclusion_product_exact F s s' d d') (kernel_inclusion_grading_comap F s s' d d') g2 hP25.2.internal hP36.2.internal) a2
  have e3 := hE1 k X ts _ _ _ hVt hI2 hP36.2 hI3
    (sesOfKer _ (phi3 F s s' d) (ker3 F s s' d d') g3 hP36.2.internal hP14.1.internal) a3
  have e4 := hE1 k X ts _ _ _ hVt hI3 hP14.1 hI4
    (sesOfKer _ (phi4 F s s' d) (ker4 F s s' d) g4 hP14.1.internal hP25.1.internal) a4
  have e5 := hE1 k X ts _ _ _ hVt hI4 hP25.1 hP36.1 (ses5 F s s' d) a5
  filter_upwards [e2, e3, e4, e5] with m h2 h3 h4 h5
  show chi ts (F.quot (s * s')) m - chi ts (F.ann (s * s') (d + d')) m =
    (chi ts (F.quot s) m - chi ts (F.ann s d) m) +
      (chi ts ((F.shift d).quot s') m - chi ts ((F.shift d).ann s' d') m)
  linarith

theorem euler_rule_product_zero : EulerAdditivityDegreeZero := by
  intro k X ts F d s s' hV hF hA
  have hA' : admitted X.𝒜 ((0 + d, s * s') :: ts) F.Ann := by rwa [zero_add]
  have h := euler_char_product_eventually_add (euler_additivity_of_rules ruleGr ruleFin ruleIso) ruleGr X ts F 0 d s s' hV hF hA'
  rw [zero_add] at h
  filter_upwards [h] with m hm
  rw [hm, chi_shift, sub_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

section -- merged from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleCong
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

namespace Cong

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem lsmul_eq (F : GMod B R k) {s s' : R} (h : s - s' ∈ F.Ann) :
    LinearMap.lsmul R F.M s = LinearMap.lsmul R F.M s' := by
  ext x
  have hx : (s - s') • x = 0 := Module.mem_annihilator.1 h x
  rw [sub_smul, sub_eq_zero] at hx
  exact hx

theorem quot_eq (F : GMod B R k) {s s' : R} (h : s - s' ∈ F.Ann) : F.quot s = F.quot s' := by
  unfold GMod.quot
  rw [lsmul_eq F h]

theorem ann_eq (F : GMod B R k) {s s' : R} (d : Deg k) (h : s - s' ∈ F.Ann) :
    F.ann s d = F.ann s' d := by
  unfold GMod.ann
  rw [lsmul_eq F h]

theorem ann_le_quot (F : GMod B R k) (s : R) : F.Ann ≤ (F.quot s).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro y
  obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ_surjective y
  exact (map_smul (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ a x).symm.trans
    ((congrArg _ (ha x)).trans (map_zero _))

theorem ann_le_ann (F : GMod B R k) (s : R) (d : Deg k) : F.Ann ≤ (F.ann s d).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro x
  exact Subtype.ext (ha x.1)

theorem chi_cong {ts ts' : List (Deg k × R)} : ∀ (F : GMod B R k),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ F.Ann) ts ts' →
      ∀ m, chi ts F m = chi ts' F m := by
  induction ts generalizing ts' with
  | nil =>
    intro F h m
    cases h
    rfl
  | cons p ts ih =>
    intro F h m
    cases h with
    | @cons _ q _ ts'' hpq hrest =>
      obtain ⟨d, s⟩ := p
      obtain ⟨d', s'⟩ := q
      obtain ⟨hd, hs⟩ := hpq
      have hd' : d = d' := hd
      subst hd'
      have hs' : s - s' ∈ F.Ann := hs
      show chi ts (F.quot s) m - chi ts (F.ann s d) m =
        chi ts'' (F.quot s') m - chi ts'' (F.ann s' d) m
      rw [← quot_eq F hs', ← ann_eq F d hs',
        ih (F.quot s) (hrest.imp fun _ _ h => ⟨h.1, ann_le_quot F s h.2⟩) m,
        ih (F.ann s d) (hrest.imp fun _ _ h => ⟨h.1, ann_le_ann F s d h.2⟩) m]

end Cong

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

section -- merged from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleSmall
section -- merged from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.SumPowersetFinSucc
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open Finset

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem sum_powerset_fin_succ {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    ∑ I ∈ (univ : Finset (Fin (n + 1))).powerset, f I =
      ∑ J ∈ (univ : Finset (Fin n)).powerset, f (J.image Fin.succ) +
        ∑ J ∈ (univ : Finset (Fin n)).powerset, f (insert 0 (J.image Fin.succ)) := by
  have hu : (univ : Finset (Fin (n + 1))) = insert 0 ((univ : Finset (Fin n)).image Fin.succ) := by
    ext i
    simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h.symm⟩
  have h0 : (0 : Fin (n + 1)) ∉ (univ : Finset (Fin n)).image Fin.succ := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun j => Fin.succ_ne_zero j
  have hinj : Function.Injective (fun J : Finset (Fin n) => J.image Fin.succ) :=
    Finset.image_injective (Fin.succ_injective n)
  rw [hu, Finset.sum_powerset_insert h0, Finset.powerset_image,
    Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_image (fun a _ b _ hab => hinj hab)]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter Finset

namespace Sm

section Gen

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def hdiff (ts : List (Deg k × R)) (F : GMod B R k) (m : Deg k) : ℤ :=
  ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
    (-1 : ℤ) ^ I.card * ((Module.length B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ)

theorem hdiff_nil (F : GMod B R k) (m : Deg k) :
    hdiff ([] : List (Deg k × R)) F m = ((Module.length B (F.gr m)).toNat : ℤ) := by
  have : (Finset.univ : Finset (Fin ([] : List (Deg k × R)).length)) = ∅ := rfl
  rw [hdiff, this, Finset.powerset_empty, Finset.sum_singleton, Finset.sum_empty, sub_zero,
    Finset.card_empty, pow_zero, one_mul]

theorem hdiff_cons (d : Deg k) (s : R) (ts : List (Deg k × R)) (F : GMod B R k) (m : Deg k) :
    hdiff ((d, s) :: ts) F m = hdiff ts F m - hdiff ts F (m - d) := by
  show ∑ I ∈ (Finset.univ : Finset (Fin (ts.length + 1))).powerset,
        (-1 : ℤ) ^ I.card *
          ((Module.length B (F.gr (m - ∑ i ∈ I, (((d, s) :: ts).get i).1))).toNat : ℤ) = _
  rw [hdiff, hdiff, sum_powerset_fin_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hsum : ∀ J : Finset (Fin ts.length),
      ∑ i ∈ J.image Fin.succ, (((d, s) :: ts).get i).1 = ∑ j ∈ J, (ts.get j).1 := fun J => by
    rw [Finset.sum_image (fun a _ b _ hab => Fin.succ_injective _ hab)]
    rfl
  have h0 : ∀ J : Finset (Fin ts.length), (0 : Fin (ts.length + 1)) ∉ J.image Fin.succ :=
    fun J => by
      simp only [mem_image, not_exists, not_and]
      exact fun j _ => Fin.succ_ne_zero j
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [hsum, Finset.card_image_of_injective _ (Fin.succ_injective _)]
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.sum_insert (h0 J), Finset.card_insert_of_notMem (h0 J), hsum,
      Finset.card_image_of_injective _ (Fin.succ_injective _), pow_succ]
    have : m - d - ∑ j ∈ J, (ts.get j).1
        = m - ((((d, s) :: ts).get (0 : Fin (ts.length + 1))).1 + ∑ j ∈ J, (ts.get j).1) := by
      show _ = m - (d + _)
      rw [sub_sub]
    rw [this]
    ring

theorem ev_shift {p : Deg k → Prop} (d : Deg k) (h : ∀ᶠ m in atTop, p m) :
    ∀ᶠ m in atTop, p (m - d) := by
  rw [eventually_atTop] at h ⊢
  obtain ⟨a, ha⟩ := h
  exact ⟨a + d, fun b hb => ha _ (le_sub_iff_add_le.mpr hb)⟩

theorem admissible_of_admissible_nil [IsLocalRing B] (𝒜 : Deg k → Submodule B R) {J : Ideal R}
    (ts : List (Deg k × R)) (h : admitted 𝒜 [] J) : admitted 𝒜 ts J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨d, hd⟩
  exact absurd hd List.not_mem_nil

def sesSubQuo (F : GMod B R k) (N : Submodule R F.M) : SES (F.sub N) F (F.quo N) where
  f := N.subtype
  g := N.mkQ
  inj := N.injective_subtype
  surj := N.mkQ_surjective
  exact y := by
    constructor
    · intro h
      exact ⟨⟨y, (Submodule.Quotient.mk_eq_zero N).1 h⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero N).2 x.2
  f_gr _ := rfl
  g_gr _ := rfl

def mulS (F : GMod B R k) (s : R) (d : Deg k) : (F.shift d).M →ₗ[R] F.M := LinearMap.lsmul R F.M s

theorem mulS_gr (𝒜 : Deg k → Submodule B R) {F : GMod B R k} (hF : F.IsGr 𝒜) {s : R} {d : Deg k}
    (hs : s ∈ 𝒜 d) : E7.IsGrHom (F.shift d) F (mulS F s d) := by
  intro m x hx
  have hx' : x ∈ F.gr (m - d) := hx
  have h := hF.smul_mem hs hx'
  rwa [show d + (m - d) = m by abel] at h

end Gen

theorem step (hE1 : EulerAdditivityExactSequence) (hGr : RuleGr) {k : ℕ} (X : HidaSetting k) (ts : List (Deg k × X.R))
    (F : X.Mod) (d : Deg k) (s : X.R) (hV : Valid X.𝒜 ts) (hs : s ∈ X.𝒜 d) (hF : F.IsGr X.𝒜)
    (hA : admitted X.𝒜 [] F.Ann) :
    ∀ᶠ m in atTop, chi ((d, s) :: ts) F m = chi ts F m - chi ts F (m - d) := by
  have hFd := (hGr k X F hF).2.1 d
  obtain ⟨hq, ha⟩ := (hGr k X F hF).2.2 d s hs
  have g := mulS_gr X.𝒜 hF hs
  have hI := ((hGr k X F hF).1 _ (g.range_hom hFd.internal)).1
  have hAt : admitted X.𝒜 ts F.Ann := admissible_of_admissible_nil X.𝒜 ts hA
  have e1 := hE1 k X ts (F.ann s d) (F.shift d) _ hV ha hFd hI
    (E7.sesOfKer (G := F.shift d) (H := F) (LinearMap.ker (LinearMap.lsmul X.R F.M s)) (mulS F s d)
      (fun _ => Iff.rfl) g hFd.internal hF.internal) hAt
  have e2 := hE1 k X ts _ F (F.quot s) hV hI hF hq
    (sesSubQuo F (LinearMap.range (LinearMap.lsmul X.R F.M s))) hAt
  filter_upwards [e1, e2] with m h1 h2
  rw [chi_shift] at h1
  show chi ts (F.quot s) m - chi ts (F.ann s d) m = _
  have h2' : chi ts F m = chi ts (F.sub (LinearMap.range (mulS F s d))) m + chi ts (F.quot s) m := h2
  linarith

end Sm


open Sm in
theorem ruleSmall : RuleSmall := by
  intro k X ts
  induction ts with
  | nil =>
    intro F _ _ _
    refine Eventually.of_forall fun m => ?_
    exact (hdiff_nil F m).symm
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hV hF hA
    have hs : s ∈ X.𝒜 d := (hV (d, s) List.mem_cons_self).2
    have hV' : Valid X.𝒜 ts := fun p hp => hV p (List.mem_cons_of_mem _ hp)
    have h0 : ∀ᶠ m in atTop, chi ts F m = hdiff ts F m := ih F hV' hF hA
    filter_upwards [step (euler_additivity_of_rules ruleGr ruleFin ruleIso) ruleGr X ts F d s hV' hs hF hA, h0,
      ev_shift d h0] with m h1 h2 h3
    rw [h1, h2, h3]
    exact (hdiff_cons d s ts F m).symm

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

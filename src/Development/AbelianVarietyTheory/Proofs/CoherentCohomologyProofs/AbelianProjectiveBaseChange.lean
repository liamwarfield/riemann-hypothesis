module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbProj

theorem isProjBy_of_isPullback {S : Scheme.{0}} (P : PolAV S) {R : Type} [CommRing R]
    {t : Spec (CommRingCat.of R) ⟶ S} {X : Scheme.{0}} {π : X ⟶ P.A.left}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : IsPullback π f P.A.hom t) : IsProjBy f := by
  obtain ⟨N, -, m, s, hL, hs⟩ := polAV_veryAmpleBy
    (polBaseChange_of_relAmple_local AmpleLocal.relAmple_of_locally) S P R t X π f h
  exact ⟨_, hL, m, s, hs⟩

theorem abelian_projective_baseChange : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (IsProjBy P.A.hom ∧ IsSeparated P.A.hom) ∧ ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsProjBy f ∧ IsSeparated f ∧ Smooth f ∧ UniversallyClosed f ∧ Surjective f ∧ IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := by
  intro K _ _ P
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have hsur : Surjective P.A.hom := inferInstance
  refine ⟨⟨isProjBy_of_isPullback P (IsPullback.id_horiz _), inferInstance⟩, ?_⟩
  intro R _ t Y π f h
  have h₀ : IsPullback (snd P.A P.A).left (fst P.A P.A).left P.A.hom P.A.hom :=
    (IsPullback.of_hasPullback P.A.hom P.A.hom).flip
  have h₁ : IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := h.paste_horiz h₀
  exact ⟨isProjBy_of_isPullback P h₁,
    MorphismProperty.of_isPullback (P := @IsSeparated) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Smooth) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective) h₁ hsur, h₁⟩

end GlobalTheory.AbProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw.HighTwist

theorem nontrivial_of_invertible (A L : Type) [CommRing A] [Nontrivial A] [AddCommGroup L]
    [Module A L] [Module.Invertible A L] : Nontrivial L := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact not_subsingleton A
    (Module.Invertible.bijective (R := A) (M := L)).2.subsingleton

variable {Y : Scheme.{0}} {H M : LB Y}

theorem sec_eq_zero (σ : LB.Sec M) (h : ∀ i, σ.f i = 0) : σ = 0 := by
  have key : ∀ s t : LB.Sec M, s.f = t.f → s = t := by
    rintro ⟨_, _⟩ ⟨_, _⟩ rfl
    rfl
  exact key _ _ (funext h)

def secPwOne (s : LB.Sec H) : LB.Sec (pw H 1) where
  f := s.f
  compat i j := (s.compat i j).trans (by
    change _ = (H.g i j ^ (1 : ℤ)).val * _
    rw [zpow_one]
    rfl)

theorem exists_restrict_ne_zero (s : LB.Sec H) {t₀ : ℤ} (a : SecOn (tw M H t₀) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus s ≤ ⊤) a ≠ 0) (t : ℤ) (ht : t₀ ≤ t) :
    ∃ b : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : nonzeroLocus s ≤ ⊤) b ≠ 0 := by
  induction t, ht using Int.leInduction with
  | base => exact ⟨a, ha⟩
  | succ n _ ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨SecOn.mulSec M n s ⊤ b, fun h => hb ?_⟩
    rw [← SecOn.mulSec_restrict] at h
    exact (SecOn.mulSec_bijective s le_rfl).1 (h.trans (map_zero _).symm)

end GlobalTheory.AbLaw.HighTwist

namespace GlobalTheory.AbLaw

open HighTwist

theorem exists_sec_tw_ne_zero : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (σ : LB.Sec (tw M H t)) (i : (tw M H t).ι), σ.f i ≠ 0 := by
  intro R _ Y f hY H m s M hH hM hs
  obtain ⟨x⟩ := hY
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := hs.1 ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have : Nonempty (nonzeroLocus (s i)) := ⟨⟨x, hi⟩⟩
  have := SecOn.invertible (isLB_tw hM hH 0) (hs.2 i).1
  have := nontrivial_of_invertible Γ(Y, nonzeroLocus (s i))
    (SecOn (tw M H 0) (nonzeroLocus (s i)))
  obtain ⟨y, hy⟩ := exists_ne (0 : SecOn (tw M H 0) (nonzeroLocus (s i)))
  obtain ⟨hc, hq, -⟩ := VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hs
  obtain ⟨k, a, ha⟩ := exists_tw_extend_pow_mul Y H M 1 (secPwOne (s i)) (nonzeroLocus (s i)) 0
    hH hM rfl hc hq y
  have hne : SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a ≠ 0 := by
    refine fun h => hy (SecOn.tw_ext fun p l => ?_)
    have e := ha p l
    have h0 : SecOn.twCoord (SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a) p l = 0 := by
      rw [h]; rfl
    rw [SecOn.twCoord_restrict] at h0
    have hu := (SecOn.isUnit_rs_of_le_nonzeroLocus (s i) l
      (inf_le_right.trans inf_le_right : nonzeroLocus (s i) ⊓ (M.U p ⊓ H.U l) ≤ H.U l)
      inf_le_left).pow k
    exact hu.mul_right_eq_zero.1 (e.symm.trans h0)
  refine ⟨0 + k * 1, fun t ht => ?_⟩
  obtain ⟨b, hb⟩ := exists_restrict_ne_zero (s i) a hne t ht
  by_contra hn
  push Not at hn
  have h0 : SecOn.topEquiv _ b = 0 := sec_eq_zero _ (hn _)
  rw [(SecOn.topEquiv _).map_eq_zero_iff.1 h0] at hb
  exact hb (map_zero _)

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.exists_high_twist_section_ne_zero : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (σ : LB.Sec (tw M H t)) (i : (tw M H t).ι), σ.f i ≠ 0 := by
  first | exact @GlobalTheory.AbLaw.exists_sec_tw_ne_zero | exact GlobalTheory.AbLaw.exists_sec_tw_ne_zero | (intros; apply GlobalTheory.AbLaw.exists_sec_tw_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNhdsPowMulTwCoordEqZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_nhds_pow_mul_twCoord_eq_zero {Y : Scheme.{0}} {H M : LB Y} {d : ℤ}
    (σ : LB.Sec (pw H d)) {t : ℤ} (hH : H.IsLB) (hM : M.IsLB) (a : SecOn (tw M H t) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus σ ≤ ⊤) a = 0) (x : Y) :
    ∃ (W : Y.Opens) (n : ℕ), x ∈ W ∧ ∀ (p : M.ι) (l : H.ι) (O : Y.Opens) (_ : O ≤ W)
      (h : O ≤ ⊤ ⊓ (M.U p ⊓ H.U l)),
      rs Y (h.trans (inf_le_right.trans inf_le_right) : O ≤ H.U l) (σ.f l) ^ n *
        rs Y h (SecOn.twCoord a p l) = 0 := by
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
  have hx : x ∈ (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens) := ⟨trivial, hq, hk⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens).2
  have hWU' : W ≤ ⊤ ⊓ (M.U q ⊓ H.U k) := hWU
  have hWk : W ≤ H.U k := hWU'.trans (inf_le_right.trans inf_le_right)
  have hb : Y.basicOpen (rs Y hWk (σ.f k)) ≤ nonzeroLocus σ ⊓ (M.U q ⊓ H.U k) := by
    refine le_inf ?_ ((Y.basicOpen_le _).trans (hWU'.trans inf_le_right))
    refine le_trans ?_ (le_iSup (fun j => Y.basicOpen (σ.f j)) k)
    exact (Scheme.basicOpen_res Y (σ.f k) (homOfLE hWk).op).le.trans inf_le_right
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hW
    (rs Y hWU' (SecOn.twCoord a q k)) (rs Y hWk (σ.f k)) (by
      have e := congrArg (fun y => rs Y hb (SecOn.twCoord y q k)) ha
      simp only [SecOn.twCoord_restrict, rs_rs] at e
      exact (rs_rs _ (Y.basicOpen_le _) _).trans (e.trans (map_zero _)))
  refine ⟨W, n, hxW, fun p l O hO h => ?_⟩
  have e := congrArg (rs Y hO) hn
  rw [map_mul, map_pow, rs_rs, rs_rs (U := H.U k) hWk hO (σ.f k), map_zero] at e
  have hl : O ≤ H.U l := h.trans (inf_le_right.trans inf_le_right)
  have hp : O ≤ M.U p := h.trans (inf_le_right.trans inf_le_left)
  have hq' : O ≤ M.U q := hO.trans (hWU'.trans (inf_le_right.trans inf_le_left))
  have e₁ : rs Y hl (σ.f l) = rs Y (le_inf hl (hO.trans hWk)) ((pw H d).g l k).val *
      rs Y (hO.trans hWk) (σ.f k) :=
    GlobalTheory.LB.sec_rel σ l k hl (hO.trans hWk) (le_inf hl (hO.trans hWk))
  rw [SecOn.twCoord_compat a p q l k h (hO.trans hWU') (le_inf hp hq') (le_inf hl (hO.trans hWk)),
    e₁, mul_pow, mul_mul_mul_comm, e, mul_zero]

theorem exists_pow_mul_twCoord_eq_zero : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → ∀ a : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : V ≤ ⊤) a = 0 → ∃ k : ℕ, ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_right.trans inf_le_right : ⊤ ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord a p l = 0 := by
  rintro Y H M d σ V t hH hM rfl hY a ha
  choose W n hxW hn using exists_nhds_pow_mul_twCoord_eq_zero σ hH hM a ha
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (W x : Set Y))
    (fun x => (W x).2) fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine ⟨s.sup n, fun p l => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun x : s => W x ⊓ (⊤ ⊓ (M.U p ⊓ H.U l)))
    (fun _ => inf_le_right) (fun y hy => ?_) fun x => ?_
  · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy', hy⟩
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) x.2)
    have e := hn x p l _ inf_le_left inf_le_right
    change rs Y _ _ = rs Y _ _
    rw [map_mul, map_pow, rs_rs (U := H.U l) _ _ (σ.f l), map_zero, hm,
      pow_add, _root_.mul_assoc, e, mul_zero]

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToCharts
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem eval₂Hom_xProd_pow {ι : Type} {R B : Type*} [CommRing R] [CommRing B] (c : R →+* B)
    (b : ι → B) (I : Finset ι) (k : ℕ) :
    MvPolynomial.eval₂Hom c b (xProd R I ^ k) = (∏ i ∈ I, b i) ^ k := by
  rw [map_pow, map_prod]
  simp only [MvPolynomial.eval₂Hom_X']

theorem twisted_sections_localise : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (I : Finset (Fin (m + 1))), (∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : (⨅ i ∈ I, nonzeroLocus (s i)) ≤ ⊤) a = 0 → ∃ k : ℕ, xProd R I ^ k • GrSum.of (hx ⊤) t a = 0) ∧ ∀ (t : ℤ) (y : SecOnR f (tw M H t) (⨅ i ∈ I, nonzeroLocus (s i))), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤), GrSum.of (hx _) t' (SecOnR.restrict f _ le_top a) = xProd R I ^ k • GrSum.of (hx _) t y := by
  intro R _ Y f H m s M hH hM hv hx I
  obtain ⟨hc, hq, -⟩ := GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hv
  obtain ⟨σ, hσ, hV⟩ := GlobalTheory.exists_prod_sec_nonzeroLocus Y H _ s I hH
  refine ⟨fun t a ha => ?_, fun t y => ?_⟩
  · obtain ⟨k, hk⟩ := exists_pow_mul_twCoord_eq_zero Y H M _ σ _ t hH hM hV.symm hc
      ((SecOnR.of f _ ⊤).symm a) ha
    obtain ⟨y', e, hy'⟩ := exists_smul_of_twCoord R Y f H m s M hx ⊤ _ _ t _
      ((SecOnR.of f _ ⊤).symm a) (xProd_pow_mem R I k) rfl
    have h0 : y' = 0 := SecOn.tw_ext fun p l => by
      rw [hy', eval₂Hom_xProd_pow, map_pow]
      have := hk p l
      rw [hσ] at this
      exact this
    refine ⟨k, e.trans ?_⟩
    rw [h0, map_zero, map_zero]
  · obtain ⟨k, a, hk⟩ := exists_tw_extend_pow_mul Y H M _ σ _ t hH hM hV.symm hc hq
      ((SecOnR.of f _ _).symm y)
    obtain ⟨y', e, hy'⟩ := exists_smul_of_twCoord R Y f H m s M hx _ _ _ t _
      ((SecOnR.of f _ _).symm y) (xProd_pow_mem R I k) rfl
    have h0 : SecOn.restrict _ le_top a = y' := SecOn.tw_ext fun p l => by
      rw [hy', eval₂Hom_xProd_pow, map_pow, SecOn.twCoord_restrict]
      have := hk p l
      rw [hσ] at this
      exact this
    refine ⟨k, _, SecOnR.of f _ ⊤ a, Eq.trans ?_ e.symm⟩
    rw [← h0, SecOnR.restrict_of]

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToChartsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.twistedSections_localise_to_charts : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (I : Finset (Fin (m + 1))), (∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : (⨅ i ∈ I, nonzeroLocus (s i)) ≤ ⊤) a = 0 → ∃ k : ℕ, xProd R I ^ k • GrSum.of (hx ⊤) t a = 0) ∧ ∀ (t : ℤ) (y : SecOnR f (tw M H t) (⨅ i ∈ I, nonzeroLocus (s i))), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤), GrSum.of (hx _) t' (SecOnR.restrict f _ le_top a) = xProd R I ^ k • GrSum.of (hx _) t y := by
  first | exact @GlobalTheory.AbLaw.twisted_sections_localise | exact GlobalTheory.AbLaw.twisted_sections_localise | (intros; apply GlobalTheory.AbLaw.twisted_sections_localise <;> assumption)
end
end

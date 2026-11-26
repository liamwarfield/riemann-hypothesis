module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieFin
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.BlockRationalityField
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddCharIsIntegral
noncomputable section

namespace GlobalTheory.Mem.AwayChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
open scoped TensorProduct

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adelic_ext {n : ℕ} (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g = bc (prV (E := E) v) h) : g = h := by
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub]
  have h1 := congrArg Units.val (H w)
  rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV] at h1
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at this
  rw [this, sub_self]

theorem exists_trivial_on {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ s, bc (prV (E := E) v) k = 1) ∧
      ∀ v ∉ s, bc (prV (E := E) v) k = bc (prV (E := E) v) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨g, hg, by simp, fun _ _ => rfl⟩
  | insert v s hv ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have hne : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 k) = bc (prV (E := E) w) k := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      rfl
    refine ⟨Formalism.UG.P.afsplitU v 1 k, Formalism.UG.P.afsplitU_mem v σ J 1 k (one_mem _) hk, fun w hw => ?_, fun w hw => ?_⟩
    · by_cases h : w = v
      · subst h; exact Formalism.UG.P.afsplit_right1 w 1 k
      · rw [hne w h]; exact h1 w ((Finset.mem_insert.1 hw).resolve_left h)
    · rw [Finset.mem_insert, not_or] at hw
      rw [hne w hw.1]; exact h2 w hw.2

theorem finite_over (p : ℕ) (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem exists_away_mem (S : StepLevel F E σ J T f bad) (p : ℕ) (hp : p ≠ 0)
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hw : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) g ∈ S.Uloc w) :
    ∃ κ : S.U, (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) g := by
  obtain ⟨k, hk, h1, h2⟩ := exists_trivial_on σ J (finite_over (F := F) p hp).toFinset g hg
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h1 h2
  refine ⟨⟨k, (S.U_eq k).2 ⟨hk, fun v => ?_⟩⟩, h1, h2⟩
  by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [h1 v hv]; exact one_mem _
  · rw [h2 v hv]; exact hw v hv

theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A ℂ) (x : A) : IsIntegral ℤ (ψ x) := by
  have h : ψ x ^ Nat.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact IsIntegral.of_pow Nat.card_pos (by rw [h]; exact isIntegral_one)

theorem chi_isIntegral {gp : Fin 2 → ℕ} {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t skip fc : ℕ} {zl : Bool}
    (X : GLev S G a t 0 skip fc zl) (κ : S.U) : IsIntegral ℤ ((S.chi κ : ℂˣ) : ℂ) := by
  rw [X.chi_eq κ]
  refine IsIntegral.prod _ fun i _ => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun h => ?_
  haveI : Finite (kv F v) := Formalism.UG.P.glint_finite_residueField v
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one, ← AddChar.map_neg_eq_inv]
  exact addChar_isIntegral _ _

end Adelic

theorem exists_inv_char {U LL O Kf : Type} [Group U] [Field LL] [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (χ : U →* ℂˣ) (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ c : U →* Oˣ, ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ algebraMap O Kf ((c κ : Oˣ) : O) * e r = 1 := by
  choose r hr o ho using h
  have r1 : r 1 = 1 := embLL.injective (by rw [hr]; simp)
  have rm : ∀ a b, r (a * b) = r a * r b := fun a b => embLL.injective (by rw [map_mul, hr, hr, hr]; simp)
  let o' : U →* O :=
    { toFun := o
      map_one' := hinj (by rw [ho, r1, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, ho, ho, ho, rm, map_mul]) }
  refine ⟨o'.toHomUnits⁻¹, fun κ => ⟨r κ, hr κ, ?_⟩⟩
  rw [← ho κ, ← map_mul]
  have : o κ = ((o'.toHomUnits κ : Oˣ) : O) := rfl
  rw [this, MonoidHom.inv_apply, Units.inv_mul, map_one]

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem exists_psiTied {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E sp.cm.sig J T f bad) (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (hp : p ≠ 0) (hk : R.k = n)
    (hJ : ∀ x y, J x y = sp.gram0 (Fin.cast hk.symm x) (Fin.cast hk.symm y))
    (hU : ∀ v, S.Uloc v = (L.Uloc v).map (reGL hk _).toMonoidHom)
    {LL O Kf : Type} [Field LL] [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ, PsiTied S L p hk embLL e ψ := by
  obtain ⟨c, hc⟩ := exists_inv_char hinj S.chi embLL e h
  have hex : ∀ a : Formalism.L2.Herm.awayFrom₂ L p, ∃ κ : S.U,
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) (reGL hk _ a.1) := by
    intro a
    obtain ⟨h2, h3⟩ := (mem_awayP_iff L p a.1).1 a.2
    refine exists_away_mem S p hp _ (reGL_mem_UPts hk sp.cm.sig sp.gram0 J hJ _ _ h2) fun w hw => ?_
    rw [bc_reGL, hU w]
    exact Subgroup.mem_map.2 ⟨_, h3 w hw, rfl⟩
  choose κ h1 h2 using hex
  have huniq : ∀ (a : Formalism.L2.Herm.awayFrom₂ L p) (k : S.U),
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k.1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) k.1 = bc (prV (E := E) w) (reGL hk _ a.1)) → κ a = k := by
    intro a k k1 k2
    refine Subtype.ext (adelic_ext _ _ fun v => ?_)
    by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
    · rw [h1 a v hv, k1 v hv]
    · rw [h2 a v hv, k2 v hv]
  let K : Formalism.L2.Herm.awayFrom₂ L p →* S.U := MonoidHom.mk' κ fun a b => by
    refine huniq _ _ (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.coe_mul, map_mul, h1 a v hv, h1 b v hv, mul_one]
    · rw [Subgroup.coe_mul, map_mul, h2 a v hv, h2 b v hv, Subgroup.coe_mul, map_mul, map_mul]
  refine ⟨c.comp K, fun a k k1 k2 => ?_⟩
  obtain rfl := huniq a k k1 k2
  exact hc (κ a)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar


set_option maxHeartbeats 4000000 in
theorem exists_psi : ∀ (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u), (∀ u, Joint0 L0 u (T u)) → (∀ u, LevelZeroCharacterRational T u) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →*
        (ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))ˣ,
      PsiTied (LL := D.what₂.LL) (O := ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))
        (Kf := KfRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ((T u).cls0).lev (L0 u)
        (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ψ := by
  intro D L0 T hJ hψ u w _
  refine exists_psiTied ((T u).cls0).lev (L0 u) _ (D.what₂.places.resChar_prime w).ne_zero (rank_eq_first_level D.R) (Formalism.L2.G.Cmp.gramN_zero D)
    (hJ u).Uloc_eq Subtype.val_injective _ _ fun κ => ?_
  obtain ⟨r, hr⟩ := chiRatAll_rec T u (hψ u) κ
  refine ⟨r, hr, (embRec_int D w _ r).1 ((val_nonneg_iff D w r).2 ?_)⟩
  have h1 : IsIntegral ℤ (D.what₂.embLL r) := hr ▸ chi_isIntegral ((T u).glev0) κ
  have h2 : IsIntegral ℤ r := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 h1
  exact (D.plEq w).valuation_le_one (K := D.what₂.LL) (⟨r, h2⟩ : 𝓞 D.what₂.LL)

end GlobalTheory.Mem.AwayChar
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsEmbeddingOfRingTie
section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TieEmbeddingCastLevelTie
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Ext

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

end Ext

section Ties

abbrev RingTie := @Formalism.L2.G.RingCompatibleAt

abbrev LocalIs := @Formalism.L2.G.GatIs

alias standardSub_of_ringTie := Formalism.L2.G.stdSubAt_of_ring

alias localIs_of_hyperspecial := Formalism.L2.G.gatIs_recG

alias ringTie_record := Formalism.L2.G.ringTied_recC

end Ties

section Bridge

theorem pack_eq (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
    (he : Even (nFr D (D.what₂.places.resChar w)))
    (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ) :
    pack D u Lc w h5 h2 he I ψ = locPackC D u Lc w h5 h2 he I ψ := by
  first
    | with_reducible rfl
    | (delta pack locPackC frobOrder nFr; with_reducible rfl)

end Bridge

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

end Record

abbrev IsConcrete := @Formalism.L2.G.IsRecC

end GlobalTheory.Mem.LocalPack
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack.Test

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar


section Reduction

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem block_rational : Formalism.L2.G.BlockRationalityField := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G M embLL lam hW hM
  exact blockRatReal P.lam0 h pos G M embLL (fun τ => (lam τ).w) (fun τ => (lam τ).anti) hW hM

variable (D : D7) (sc : Scale)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc 1 Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc 1 Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc 1 Lc I ψ hd) B)
  (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
  (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
  (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
  (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
    lamV (lam u w hg) (D.what₂.embLL z))
  (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))


set_option maxHeartbeats 32000000 in
include hK hPos in
theorem comparison_statements (hJ : ∀ u, Joint0 H0.lev0 u (T u))
    (h0 : ∀ u, LevelZeroCharacterRational (D := recC D sc 1 Lc I ψ hd) T u)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    CmpHyp0P T (gatTiesC D sc 1 Lc I ψ hd) (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) := by
  have hpos := fun u w hg v s x => pos_C D sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hs : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u :=
    fun u => sameUloc_of_joint (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u (hJ u)
  have N : CmpLeft D sc 1 Lc I ψ hd H0 hL T B hBs hB :=
    { same := hs
      blk := fun u w hg => blkRatRec_of_stmt block_rational _ _ u w hg B
      psi0 := h0
      chi := chi_C D sc 1 Lc I ψ hd H0 hL T B hBs hB hψ
      valInt := valIntRec_of weylLatticeDescent_holds
        (fun u w hg => ex_C_blk D sc 1 Lc I ψ hd H0 hL T B hBs hB u (hs u) w hg
          (blkRatRec_of_stmt block_rational _ _ u w hg B) (h0 u))
        (fun u w hg => frac_of_gatIs _ u w hg (gatIs_recC D sc 1 Lc I ψ hd H0 hL
          (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg))
        (restExB _)
        (restLatO_of hpos (restLatW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) (fun u => hJ u))
          (restGramW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB)))
        (restChi_of (D := recC D sc 1 Lc I ψ hd) T h0) }
  exact N.toHyp0P hpos


end Reduction


end GlobalTheory.Mem.LocalPack.Test
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcrete
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TiePlace

theorem iota_sigma_mem_range {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (S : HidaSetting p n' W Qq O Kf ι σ j w) (s : ℕ) (y : Qq) :
    ι ((σ ^ s) y) ∈ Set.range (algebraMap O Kf) ↔ y ∈ Set.range (algebraMap W Qq) := by
  haveI := S.frac_alt
  haveI := S.frac_O

  have h1 : ∀ z : Qq, z ∈ Set.range (algebraMap W Qq) → σ z ∈ Set.range (algebraMap W Qq) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := S.frob t
    exact ⟨_, ht'.symm⟩
  have hk : ∀ (k : ℕ) (z : Qq), z ∈ Set.range (algebraMap W Qq) → (σ ^ k) z ∈ Set.range (algebraMap W Qq) := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      rw [pow_succ]
      exact ih _ (h1 z hz)
  have hs : ∀ z : Qq, (σ ^ s) z ∈ Set.range (algebraMap W Qq) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, hk s z⟩
    have hn : 1 ≤ n' := le_trans (by norm_num) S.two_le
    have e : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = z := by
      have em : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = (σ ^ (s * (n' - 1)) * σ ^ s) z := rfl
      rw [em, ← pow_add]
      have : s * (n' - 1) + s = n' * s := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [this, pow_mul, S.period, one_pow]
      rfl
    rw [← e]
    exact hk _ _ h

  have hj : Function.Injective j := by
    intro a b h
    apply IsFractionRing.injective W Qq
    apply ι.injective
    rw [S.ι_comp, S.ι_comp, h]
  have hnu : ¬ IsUnit (p : O) := by
    letI := j.toAlgebra
    haveI : Module.Finite W O := S.finite
    haveI : FaithfulSMul W O := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    intro h
    exact S.p_unif.not_isUnit ((isUnit_map_iff (algebraMap W O) _).1 (by simpa using h))
  have hι : ∀ z : Qq, ι z ∈ Set.range (algebraMap O Kf) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, ?_⟩
    · by_contra hz
      obtain ⟨o, ho⟩ := h
      have hz0 : z ≠ 0 := fun h0 => hz ⟨0, by rw [h0, map_zero]⟩
      obtain ⟨t, ht⟩ := (ValuationRing.isInteger_or_isInteger W z).resolve_left hz
      have htu : ¬ IsUnit t := by
        rintro ⟨u, rfl⟩
        apply hz
        refine ⟨(u⁻¹ : Wˣ), ?_⟩
        rw [← inv_inv z, ← ht]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      have htm : t ∈ Ideal.span {(p : W)} := by
        rw [← S.p_unif.maximalIdeal_eq]
        exact htu
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 htm
      have e1 : algebraMap O Kf (o * j (t' * p)) = 1 := by
        rw [map_mul, ho, ← S.ι_comp, ht, ← map_mul, mul_inv_cancel₀ hz0, map_one]
      have e2 : o * j (t' * p) = 1 := by
        apply IsFractionRing.injective O Kf
        rw [e1, map_one]
      apply hnu
      have : IsUnit (j (t' * p)) := IsUnit.of_mul_eq_one o (by rw [mul_comm]; exact e2)
      rw [map_mul, map_natCast] at this
      exact isUnit_of_mul_isUnit_right this
    · rintro ⟨t, rfl⟩
      exact ⟨j t, (S.ι_comp t).symm⟩
  rw [hι, hs]

theorem val_pos_iff {K : Type} [Field K] (val : AddValuation K (WithTop ℤ)) (z : K) :
    (0 : WithTop ℤ) < val z ↔ z = 0 ∨ ¬ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, false_or, AddValuation.map_inv, not_le]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, val z = n := WithTop.ne_top_iff_exists.1 (fun h => hz ((AddValuation.top_iff val).1 h)) |>.imp fun _ h => h.symm
    rw [hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    norm_cast
    omega

theorem mem_asIdeal_iff_inv {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (x : R) :
    x ∈ v.asIdeal ↔ x = 0 ∨ (algebraMap K (v.adicCompletion K) (algebraMap R K x))⁻¹ ∉ v.adicCompletionIntegers K := by
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx, false_or, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, not_le]
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
    have h1 : (algebraMap K (v.adicCompletion K) (algebraMap R K x)) = ((algebraMap R K x : K) : v.adicCompletion K) := rfl
    rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have h0 : v.valuation K (algebraMap R K x) ≠ 0 := by
      simpa using hx
    rw [one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem inv_int_iff {p : ℕ} {G : GAtP p} (v : Fin G.P.nV) (s : ℕ) {LL : Type} [Field LL]
    (val : AddValuation LL (WithTop ℤ)) (emb : LL →+* G.Kf)
    (hint : ∀ z, (0 : WithTop ℤ) ≤ val z ↔ emb z ∈ Set.range (algebraMap G.O G.Kf)) (z : LL) (y : G.P.Qq v)
    (hk : emb z = G.P.ι v ((G.P.σ v ^ s) y)) :
    y⁻¹ ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  rw [hint, map_inv₀, hk, ← map_inv₀, ← map_inv₀]
  exact (iota_sigma_mem_range (G.P.setting v) s y⁻¹).symm

section Comparison₂

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem tie_mem_iff {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) (v : Fin G.P.nV) (x : 𝓞 F) :
    x ∈ (t.pl v).1.asIdeal ↔ x = 0 ∨
      ((t.eQ v _ rfl).symm ((t.spl _ (t.pl v).2 (inclE (F := F) ((t.pl v).1.adicCompletion F) (algebraMap F E (x : F)))).1))⁻¹ ∉
        Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
  rw [t.spl_F, mem_asIdeal_iff_inv (K := F), t.completion_integers_iff v _ rfl, map_inv₀, RingEquiv.apply_symm_apply]

end Comparison₂

theorem int_map_eq_zero_iff {F E L : Type} [Field F] [Field E] [Field L] (g : F →+* E) (f : E →+* L)
    (x : 𝓞 F) : f (g (x : F)) = 0 ↔ x = 0 := by
  rw [map_eq_zero_iff f f.injective, map_eq_zero_iff g g.injective]
  exact RingOfIntegers.coe_eq_zero_iff


set_option maxHeartbeats 4000000 in
theorem place_of_tie : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  intro D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hpos := pos_C D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s
    (algebraMap D.host.F D.host.E (x : D.host.F))
  have hsig : sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F)) =
      algebraMap D.host.F D.host.E (x : D.host.F) := AlgHom.commutes _ _
  have key : (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
      (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) =
      ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v (algebraMap D.host.F D.host.E (x : D.host.F)))) := by
    have e : tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F)) = Cmp.tEL (recC D sc Ce Lc I ψ hd)
          ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩) (if Even s.val then algebraMap D.host.F D.host.E (x : D.host.F)
            else sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F))) := by
      by_cases he : Even s.val
      · simp only [he, if_true, ite_true, ↓reduceIte]; rfl
      · simp only [he, if_false, ite_false, ↓reduceIte, hsig]; rfl
    rw [e]
    exact hpos
  refine (tie_mem_iff ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) v x).trans ?_
  have hz : x = 0 ↔ tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)) = 0 := by
    exact (int_map_eq_zero_iff (algebraMap D.host.F D.host.E) (Cmp.tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)) x).symm
  refine Iff.trans ?_ (val_pos_iff (D.what₂.places.val w) (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)))).symm
  exact or_congr hz (not_congr (inv_int_iff v s.val (D.what₂.places.val w) ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg)
    ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW_int u w hg) _ _ key))

end GlobalTheory.TiePlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  first | exact @GlobalTheory.TiePlace.place_of_tie | exact GlobalTheory.TiePlace.place_of_tie | (intros; apply GlobalTheory.TiePlace.place_of_tie <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack

namespace GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable (D : D7) (L0 : LevelData D)

def Companion : Prop :=
  ∀ u, ∃ 𝔞 : Ideal (𝓞 D.host.E), (L0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
    (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (L0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0

def stdBasis (hS : Formalism.L2.Herm.StdTied D) : GL (Fin D.R.k) D.host.E := Classical.choose (exists_stdB_of_tied D hS)

theorem stdBasis_std (hS : Formalism.L2.Herm.StdTied D) : Cmp.StdB D (stdBasis D hS) := Classical.choose_spec (exists_stdB_of_tied D hS)

def placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  locIdStd D u w hg (Classical.choose (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)) (stdBasis D hS) (stdBasis_std D hS)
    (Classical.choose (hC u)) (Classical.choose_spec (hC u))

def embK (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg))

def embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))

theorem embK_embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (z : D.what₂.LL) : embK D L0 u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) = lamV (embAlg D L0 u w hg) (D.what₂.embLL z) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).1 z

def awayChar (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ :=
  Classical.choose (GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ u w hg)

def gatOf (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (sc : Scale) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    GAtP (D.what₂.places.resChar w) :=
  (packC D (fun u => L0 u) I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc 1 (D.what₂.places.resChar w))

set_option maxHeartbeats 4000000 in
theorem gatOf_d (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (I) (ψ) (sc : Scale) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (gatOf D L0 I ψ sc u w h).d = Module.finrank ℂ (D.mem u).A.Mu0 := by
  have e := GlobalTheory.ClassRank.pack_d_eq D L0 T hJ u w h (I u w h) (ψ u w h) (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))
  rw [pack_eq] at e
  exact e

section Main

variable {D L0}

set_option maxHeartbeats 4000000 in
theorem posOK_placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0)
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (packC D (fun u => L0 u) (placeId D L0 hS hC) ψ u w hg).posOK (embK D L0 u w hg) (embAlg D L0 u w hg) := by
  have e := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).2 (ψ u w hg)
  unfold LocPack.posOK at e ⊢
  exact e

end Main

section Main2

variable {D L0}

end Main2

theorem gPlTiedS_of {X : D7} {Gt : GatTies X} (H0 : Formalism.L2.Herm.Herm0 X)
    (hpl : ∀ u w hg (v : Fin (X.gat u w hg).P.nV) (s : Fin ((X.gat u w hg).P.n' v)) (x : 𝓞 X.host.F),
      x ∈ ((H0.g u w hg).pl v).1.asIdeal ↔
        (0 : WithTop ℤ) < X.what₂.places.val w (tauLL X (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap X.host.F X.host.E (x : X.host.F))))
    (B : Formalism.L2.Herm.HermColsCh X) (gS : Formalism.L2.Herm.SymmetricGroupCompatibility X B) (hB : B.lev0 = H0.lev0) (hg : HEq gS H0.g) :
    Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces X B gS Gt := by
  obtain ⟨l, g⟩ := H0
  dsimp only at hB hg hpl
  subst hB
  obtain rfl := eq_of_heq hg
  exact hpl

end GlobalTheory.Mem.ConcreteRecord
end
end

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

def IsLocalFamily (sc : Scale) (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (g : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w)) : Prop :=
  ∃ (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (B : GL (Fin D.R.k) D.host.E)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]),
    Cmp.StdB D B ∧
    (∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B) ∧
    (∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z)) ∧
    (∀ u w hg, (packC D (fun u => L0 u) I ψ u w hg).posOK (iK u w hg) (lam u w hg)) ∧
    (∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (L0 u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (nFr D (D.what₂.places.resChar w))) (ψ u w hg)) ∧
    g = gatOf D L0 I ψ sc


set_option maxHeartbeats 4000000 in
theorem exists_isLocalFamily (sc : Scale) {D : D7} {L0 : LevelData D} (T : ∀ u : D.what₂.Word, Forms0 D u)
    (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) :
    ∃ g, (∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0) ∧ IsLocalFamily sc D L0 T g :=
  ⟨gatOf D L0 (placeId D L0 hS hC) (awayChar D L0 T hJ hψ) sc, gatOf_d D L0 T hJ _ _ sc,
    placeId D L0 hS hC, awayChar D L0 T hJ hψ, stdBasis D hS, embK D L0, embAlg D L0, stdBasis_std D hS, fun _ _ _ _ _ => rfl,
    embK_embAlg D L0, posOK_placeId hS hC _,
    fun u w hg => Classical.choose_spec (GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ u w hg), rfl⟩


set_option maxHeartbeats 32000000 in
theorem isRecG_of_isLocalFamily {sc : Scale} {D : D7} {L0 : LevelData D} {T : ∀ u : D.what₂.Word, Forms0 D u}
    (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) {g} (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (h : IsLocalFamily sc D L0 T g) :
    ∃ (Gt : GatTies (setGat D g hd)) (c : LatCmp (setGat D g hd)) (G : GroupCompatibilityAll (setGat D g hd) Gt c),
      IsRecG sc (setGat D g hd) Gt c G.herm G.forms ∧ (∀ u, G.herm.lev0 u = L0 u) ∧ (∀ u, G.forms u = forms0Set D g hd (T u)) ∧
      ∀ u w hg (v : Fin ((setGat D g hd).gat u w hg).P.nV) (s : Fin (((setGat D g hd).gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
        x ∈ ((G.herm.g u w hg).pl v).1.asIdeal ↔
          (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (setGat D g hd) (Gt.gat_pos u w hg ⟨v, s⟩)
            (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  obtain ⟨I, ψ, B, iK, lam, hBs, hB, hK, hPos, hψ', rfl⟩ := h
  let H0 : Formalism.L2.Herm.Herm0 (recC D sc 1 (fun u => L0 u) I ψ hd) :=
    ⟨fun u => L0 u, levTieG D sc 1 (fun u => L0 u) (packC D (fun u => L0 u) I ψ) hd⟩
  let T' : ∀ u, Forms0 (recC D sc 1 (fun u => L0 u) I ψ hd) u := fun u => forms0Set D (gatOf D L0 I ψ sc) hd (T u)
  have CH := Test.comparison_statements D sc (fun u => L0 u) I ψ hd H0 (fun _ => rfl) T' B hBs hB iK lam hK hPos hJ hψ hψ'
  have hpos := fun u w hg v s x => pos_C D sc 1 (fun u => L0 u) I ψ hd H0 (fun _ => rfl) B hBs hB iK lam hK hPos u w hg v s x
  exact ⟨gatTiesC D sc 1 (fun u => L0 u) I ψ hd, _,
    groupCompatibilityOfRecursion D sc 1 (fun u => L0 u) I ψ hd H0 (fun _ => rfl) T' B hBs hB (CH.toHyp0 hpos).toHyp
      (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)),
    LayerTwoModel.isRecG_retie ⟨D, fun u => L0 u, I, ψ, hd, H0, fun _ => rfl, T', B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩ _,
    fun _ => rfl, fun _ => rfl,
    fun u w hg v s x => GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos D sc 1 (fun u => L0 u) I ψ hd H0 (fun _ => rfl) B hBs hB iK lam hK hPos u w hg v s x⟩

end GlobalTheory.Mem.Top.Bl.TrueLocal

end

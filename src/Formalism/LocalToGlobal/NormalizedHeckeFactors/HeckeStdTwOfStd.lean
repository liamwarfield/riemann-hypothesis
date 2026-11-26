module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg

@[expose] public section

section -- merged from Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2

def placesS (D : D7) (l : ℕ) : Set (PlE D.host) :=
  {v | (v ∈ placesOver D.host.E (D.host.g 0) ∨ v ∈ placesOver D.host.E (D.host.g 1) ∨
      v ∈ placesOver D.host.E (if l = D.host.pde then D.host.pde' else D.host.pde)) ∧
    v ∉ placesOver D.host.E l}

def GenAt (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (v : PlE D.host) (k : ℕ) : Prop :=
  IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q ∧ 1 ≤ k ∧ k ≤ D.R.nV

theorem mtL_eq (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    D.what₂.MtL (D.nd.mu i) (D.nd.j i) = D.what₂.MtL (D.what₂.muTw w) j := by
  obtain ⟨h1, h2⟩ := (D.nd.locs_mem j w i).1 h
  rw [D.nd.mu_w i, h1, h2]

def castMt (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)) : D.what₂.MtL (D.what₂.muTw w) j :=
  cast (mtL_eq D h) x

def castMtInv (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) : D.what₂.MtL (D.nd.mu i) (D.nd.j i) :=
  cast (mtL_eq D h).symm y

theorem castMt_castMtInv (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) : castMt D h (castMtInv D h y) = y := by
  unfold castMt castMtInv
  exact cast_cast _ _ y


set_option synthInstance.maxHeartbeats 400000 in
structure NLocBase (D : D7) (M : MtFam D) where

  Oc : ℕ → D.what₂.places.Pl → Type
  [ringOc : ∀ j w, CommRing (Oc j w)]
  [domOc : ∀ j w, IsDomain (Oc j w)]
  [dvrOc : ∀ j w, IsDiscreteValuationRing (Oc j w)]

  ec : ∀ j w, D.what₂.LL →+* FractionRing (Oc j w)

  ec_w : ∀ j w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    ec j w x ∈ (algebraMap (Oc j w) (FractionRing (Oc j w))).range

  V : ℕ → D.what₂.places.Pl → Type
  [acgV : ∀ j w, AddCommGroup (V j w)]
  [modV : ∀ j w, Module (FractionRing (Oc j w)) (V j w)]
  [modVO : ∀ j w, Module (Oc j w) (V j w)]
  [towV : ∀ j w, IsScalarTower (Oc j w) (FractionRing (Oc j w)) (V j w)]
  iV : ∀ j w, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[ec j w] V j w

  iV_basis : ∀ j w (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)),
    LinearIndependent (FractionRing (Oc j w)) (fun a => iV j w (b a)) ∧
      Submodule.span (FractionRing (Oc j w)) (Set.range fun a => iV j w (b a)) = ⊤

  Qc : ℕ → D.what₂.places.Pl → Finset (PlE D.host)

  hL : ∀ j w, PlE D.host → ℕ → Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)

  hL_def : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    GenAt D (D.what₂.places.resChar w) (Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
    ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (hL j w v k x)) =
      NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x))

  hK : ∀ j w, PlE D.host → ℕ → Module.End (FractionRing (Oc j w)) (V j w)
  hK_def : ∀ j w v k x, hK j w v k (iV j w x) = iV j w (hL j w v k x)

  split : ∀ j w v k, GenAt D (D.what₂.places.resChar w) (Qc j w) v k →
    ⨆ μ, (hK j w v k).maxGenEigenspace μ = ⊤

  Qc_over : ∀ j w (v v' : PlE D.host), v ∈ Qc j w →
    (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ Qc j w

  Qc_conj : ∀ j w (v v' : PlE D.host), v' ∈ Qc j w → IsConjPl D.host v v' → v ∈ Qc j w

attribute [instance] NLocBase.ringOc NLocBase.domOc NLocBase.dvrOc NLocBase.acgV NLocBase.modV
  NLocBase.modVO NLocBase.towV

def heckeGens {D : D7} {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Set (Module.End (FractionRing (B.Oc j w)) (B.V j w)) :=
  {f | ∃ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k ∧ f = B.hK j w v k}

abbrev heckeAlg {D : D7} {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Subalgebra (B.Oc j w) (Module.End (FractionRing (B.Oc j w)) (B.V j w)) :=
  Algebra.adjoin (B.Oc j w) (heckeGens B j w)


set_option synthInstance.maxHeartbeats 400000 in
structure NormalizedLocalCompatibility (D : D7) (M : MtFam D) where
  B : NLocBase D M

  Q_eq : ∀ j w i, i ∈ D.nd.locs j w → D.nd.Q i = B.Qc j w

  mx : ∀ j w, D.nd.Loc → Ideal (heckeAlg B j w)
  mx_max : ∀ j w i, i ∈ D.nd.locs j w → (mx j w i).IsMaximal

  mx_inj : ∀ j w, Set.InjOn (mx j w) (D.nd.locs j w)

  mx_all : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → ∀ I : Ideal (heckeAlg B j w), I.IsMaximal →
    ∃ i ∈ D.nd.locs j w, mx j w i = I

  phO : ∀ j w i, i ∈ D.nd.locs j w → D.nd.O i ≃+* B.Oc j w
  phK : ∀ j w i, i ∈ D.nd.locs j w → FractionRing (D.nd.O i) ≃+* FractionRing (B.Oc j w)
  phK_alg : ∀ j w i (h : i ∈ D.nd.locs j w) (z : D.nd.O i),
    phK j w i h (algebraMap _ _ z) = algebraMap _ _ (phO j w i h z)
  phK_emb : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.what₂.LL), phK j w i h (D.nd.embK i x) = B.ec j w x

  Psi : ∀ j w i (h : i ∈ D.nd.locs j w),
    TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) →ₛₗ[(phK j w i h).toRingHom] B.V j w
  Psi_inj : ∀ j w i (h : i ∈ D.nd.locs j w), Function.Injective (Psi j w i h)
  Psi_range : ∀ j w i (h : i ∈ D.nd.locs j w) (y : B.V j w),
    y ∈ NCov.part (heckeAlg B j w) (mx j w i) ↔ ∃ z, Psi j w i h z = y

  Psi_pr : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    Psi j w i h (D.nd.prMt i x) - B.iV j w (castMt D h x) ∈ NCov.off (heckeAlg B j w) (mx j w i)

  ptX : ∀ j w i (h : i ∈ D.nd.locs j w), D.nd.X i ≃
    {ψ : heckeAlg B j w →ₐ[B.Oc j w] B.Oc j w //
      NCov.cls ψ = mx j w i ∧ NCov.W (heckeAlg B j w) (NCov.pt ψ) ≠ ⊥}

  ptX_hT : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.nd.X i) (v : PlE D.host) (k : ℕ)
    (hvk : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k),
    phO j w i h ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) =
      (ptX j w i h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩

  iotaC : ∀ j w, B.Oc j w →+* ℂ

  iotaC_coh : ∀ j w i (h : i ∈ D.nd.locs j w) (z : D.nd.O i), iotaOC D i z = iotaC j w (phO j w i h z)

def HeckeStd {D : D7} {M : MtFam D} (B : NLocBase D M) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ D.R.m →
    (∀ v k v' k', GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (B.Qc j w) v' k' → Commute (B.hK j w v k) (B.hK j w v' k')) ∧
    (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ μ, (B.hK j w v k).maxGenEigenspace μ ≠ ⊥ →
      μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range)

def LocPl (D : D7) (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.muAt w ≠ D.what₂.mu0 ∨ (D.nd.locs j w).Nonempty

theorem locPl_of_mem (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    LocPl D j w :=
  Or.inr ⟨i, h⟩

def HeckeStdTw {D : D7} {M : MtFam D} (B : NLocBase D M) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ D.R.m → LocPl D j w →
    (∀ v k v' k', GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (B.Qc j w) v' k' → Commute (B.hK j w v k) (B.hK j w v' k')) ∧
    (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ μ, (B.hK j w v k).maxGenEigenspace μ ≠ ⊥ →
      μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range)

theorem heckeStdTw_of_std {D : D7} {M : MtFam D} {B : NLocBase D M} (h : HeckeStd B) : HeckeStdTw B :=
  fun j w h1 h2 _ => h j w h1 h2

end Formalism.L2
end
end

section -- merged from Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.Gal

namespace Formalism.L2

section Points

variable {O X : Type} [CommRing O] [IsDomain O] [Fintype X]

def evPt (T : Subalgebra O (X → O)) (x : X) : T →ₐ[O] O :=
  (Pi.evalAlgHom O (fun _ : X => O) x).comp T.val

@[simp] theorem evPt_apply (T : Subalgebra O (X → O)) (x : X) (f : T) : evPt T x f = (f : X → O) x := rfl

theorem evPt_injective (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : Function.Injective (evPt T) := by
  intro x y hxy
  by_contra hne
  obtain ⟨f, hf, hfxy⟩ := hsep x y hne
  exact hfxy (congrArg (fun φ : T →ₐ[O] O => φ ⟨f, hf⟩) hxy)

theorem exists_delta (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (x : X) :
    ∃ P : T, (P : X → O) x ≠ 0 ∧ ∀ y, y ≠ x → (P : X → O) y = 0 := by
  classical
  have key : ∀ y, y ≠ x → ∃ g ∈ T, g x ≠ 0 ∧ g y = 0 := by
    intro y hy
    obtain ⟨f, hf, hne⟩ := hsep x y (Ne.symm hy)
    refine ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _), ?_, ?_⟩
    · simpa [sub_eq_zero] using hne
    · simp
  choose g hgT hgx hgy using key
  let e : X → T := fun y => if hy : y = x then 1 else ⟨g y hy, hgT y hy⟩
  refine ⟨∏ y, e y, ?_, ?_⟩
  · simp only [SubmonoidClass.coe_finsetProd, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun y _ => ?_
    by_cases hy : y = x
    · simp [e, hy]
    · simp [e, hy, hgx y hy]
  · intro y hy
    simp only [SubmonoidClass.coe_finsetProd, Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [e, hy, hgy y hy])

theorem evPt_surjective (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : Function.Surjective (evPt T) := by
  classical
  intro φ
  choose P hPx hPy using exists_delta T hsep
  set N : O := ∏ y, ((P y : T) : X → O) y with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y _ => hPx y
  let c : X → O := fun x => ∏ y ∈ Finset.univ.erase x, ((P y : T) : X → O) y
  have hsum : (∑ x, c x • P x : T) = algebraMap O T N := by
    apply Subtype.ext
    funext z
    have hR : ((algebraMap O T N : T) : X → O) z = N := by simp
    rw [hR]
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single z (fun x _ hxz => by rw [hPy x z (fun h => hxz h.symm), mul_zero])
      (fun h => absurd (Finset.mem_univ z) h)]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ z)
  have hφ : ∃ x, φ (P x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 := congrArg φ hsum
    rw [AlgHom.commutes] at h1
    exact hN0 (by simpa [hcon] using h1.symm)
  obtain ⟨x0, hx0⟩ := hφ
  refine ⟨x0, AlgHom.ext fun g => ?_⟩
  have hmul : g * P x0 = ((g : X → O) x0) • P x0 := by
    apply Subtype.ext
    funext z
    by_cases hz : z = x0
    · subst hz
      simp
    · simp [hPy x0 z hz]
  have h2 := congrArg φ hmul
  rw [map_mul, map_smul, smul_eq_mul] at h2
  have h3 := mul_right_cancel₀ hx0 h2
  rw [evPt_apply]
  exact h3.symm

def ptsEquiv (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : X ≃ (T →ₐ[O] O) :=
  Equiv.ofBijective (evPt T) ⟨evPt_injective T hsep, evPt_surjective T hsep⟩

end Points

section Record

variable (D : D7)

def ptsNd (i : D.nd.Loc) : D.nd.X i ≃ (D.nd.T i →ₐ[D.nd.O i] D.nd.O i) :=
  ptsEquiv (D.nd.T i) (D.nd.T_sep i)

theorem zgoodSub : D.nd.ZgoodSub := fun i x hx =>
  (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1

theorem s0_eq (i : D.nd.Loc) : D.nd.s0 i = max 1 (D.host.QS.factorization (D.nd.l i)) := by
  by_cases h : D.nd.l i = 2
  · have h1 : 1 ≤ D.host.QS.factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization D.host.QS_pos.ne').1
        ((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd)
    rw [D.nd.restNLevelExponent_of_two i h, h, max_eq_right h1]
  · exact D.nd.restNLevelExponent_of_odd i h

theorem mem_S_iff (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) : v ∈ D.nd.S i ↔
    (v ∈ placesOver D.host.E (D.host.g 0) ∨ v ∈ placesOver D.host.E (D.host.g 1) ∨
      v ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
      v ∉ placesOver D.host.E (D.nd.l i) :=
  D.nd.S_def i v

theorem mem_Q_iff (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    v ∈ D.nd.Q i ↔ ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.ntw.psiL i σ ≠ 1 :=
  (D.ntw.psiL_ram i v (D.nd.plOm.1 v) (D.nd.plOm.2 v)).symm

end Record

section Good

open Polynomial

end Good

section Tame

end Tame

def latRel {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Set (L.gen → O) :=
  {r | ∑ g : L.gen, φ (r g) • (g : V) = 0}

def latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Submodule O (L.gen → O) where
  carrier := latRel L
  zero_mem' := by simp [latRel]
  add_mem' := by
    intro a b ha hb
    simp only [latRel, Set.mem_ofPred_eq, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [latRel, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at ha ⊢
    rw [← Finset.smul_sum, ha, smul_zero]

@[simp] theorem mem_latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Rows.OLat O φ V) (r : L.gen → O) : r ∈ latRelSub L ↔ r ∈ latRel L := Iff.rfl

def plF (D : D7) (k : Fin 2) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal}

theorem embK_OtoLL_mem (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    D.nd.embK i (D.what₂.OtoLL y) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range := by
  rw [← D.nd.embK_w i]
  by_cases h0 : D.what₂.OtoLL y = 0
  · rw [h0, AddValuation.map_zero]; exact le_top
  · rw [D.val_eq _ _ h0]
    have hint := D.O_int y
    set x : 𝓞 D.what₂.LL := ⟨D.what₂.OtoLL y, hint⟩
    have hx : (x : D.what₂.LL) = D.what₂.OtoLL y := rfl
    have hle := (D.plEq (D.nd.w i)).valuation_le_one (K := D.what₂.LL) x
    have hne : (D.plEq (D.nd.w i)).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL x) ≠ 0 := by
      simpa [hx] using h0
    unfold vAdd
    have : WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)) ≤ 0 := by
      have hne' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≠ 0 := by simpa [hx] using hne
      have hle' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≤ 1 := by simpa [hx] using hle
      have h2 : WithZero.exp (WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y))) ≤
          WithZero.exp (0 : ℤ) := by
        rw [WithZero.exp_log hne']; simpa using hle'
      exact WithZero.exp_le_exp.mp h2
    exact_mod_cast (by omega : (0:ℤ) ≤ -WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)))

def fracRangeEquiv (O : Type) [CommRing O] [IsDomain O] :
    O ≃+* (algebraMap O (FractionRing O)).range :=
  RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
     (algebraMap O (FractionRing O)).rangeRestrict_surjective⟩

def sOf (D : D7) (i : D.nd.Loc) : D.what₂.O →+* D.nd.O i :=
  (fracRangeEquiv (D.nd.O i)).symm.toRingHom.comp
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i))

theorem sOf_spec (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (sOf D i y) = D.nd.embK i (D.what₂.OtoLL y) := by
  have h := (fracRangeEquiv (D.nd.O i)).apply_symm_apply
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i) y)
  exact congrArg Subtype.val h

structure NormalizedDataCompatibility (D : D7) where
  bj : ∀ i, (D.what₂.MjLat (D.nd.j i)).gen → D.nd.Bj i
  bj_span : ∀ i, Submodule.span (D.nd.O i) (Set.range (bj i)) = ⊤
  bj_rel : ∀ i (c : (D.what₂.MjLat (D.nd.j i)).gen → D.nd.O i), ∑ g, c g • bj i g = 0 ↔
    c ∈ Submodule.span (D.nd.O i) ((fun r => (sOf D i) ∘ r) '' latRel (D.what₂.MjLat (D.nd.j i)))

end Formalism.L2
end
end

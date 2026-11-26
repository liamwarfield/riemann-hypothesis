module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  apply Units.ext; ext x y; rfl

theorem bc_reGL {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin a) R) :
    bc φ (reGL h R g) = reGL h S (bc φ g) := by
  subst h
  rw [reGL_rfl, reGL_rfl]

theorem isHerm_re {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (σ : R →+* R) (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (hh : IsHerm σ J) :
    IsHerm σ J' := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this]; exact hh

theorem det_re {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (hh : IsUnit J.det) :
    IsUnit J'.det := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this]; exact hh

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_mem_UPts {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin a) (E ⊗[F] R)) (hg : g ∈ UPts σ J R) :
    reGL h _ g ∈ UPts σ J' R := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this, reGL_rfl]; exact hg

theorem comp_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    {ι : Type} (yG : ι → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (K : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hs : Function.Surjective (fun i => (Quotient.mk'' (yG i) : ClassSet
      ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))))))
    (x : UPts σ J' (FiniteAdeleRing (𝓞 F) F)) :
    ∃ (i : ι) (γ : GL (Fin b) E) (k : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), γ ∈ UJ (σ : E →+* E) J' ∧ k ∈ K ∧
      k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * reGL h _ (yG i).1 * reGL h _ k := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  obtain ⟨i, hi⟩ := hs (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ (yG i) x).1 hi
  obtain ⟨γ, hγ, eγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  refine ⟨i, γ, k.1, hγ, Subgroup.mem_subgroupOf.1 hk, k.2, ?_⟩
  rw [reGL_rfl, reGL_rfl, eγ, e]; rfl

end Re

section Away

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem mem_awayP_iff (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (k : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    k ∈ Formalism.L2.Herm.awayFrom₂ L p ↔ k ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) k ∈ L.Uloc w := by
  unfold Formalism.L2.Herm.awayFrom₂
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]

end Away

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D)


set_option maxHeartbeats 4000000 in
theorem locGood_locAt (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) : LocGood (sigD D) (gramN D 0 (Nat.zero_le _)) (locAt X u w hg B) := by
  refine { herm := isHerm_re (rank_eq_first_level D.R) _ D.sp.gram0 _ (gramN_zero D) D.sp.baseGram_isHermitian
           det := det_re (rank_eq_first_level D.R) D.sp.gram0 _ (gramN_zero D) (isUnit_det_gram0 D.sp)
           sig := fun v x => (X.g u w hg).spl_sig _ ((X.g u w hg).pl v).2 x
           yG_mem := fun i => reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ ((X.g u w hg).yG i).2
           yG_p := ?_ }
  intro i v
  have h1 := (X.g u w hg).yG_p i _ ((X.g u w hg).pl v).2
  have h2 := bc_reGL (rank_eq_first_level D.R) (prV (E := D.host.E) ((X.g u w hg).pl v).1) ((X.g u w hg).yG i).1
  rw [h1, map_one] at h2
  exact h2


set_option maxHeartbeats 4000000 in
theorem ptEx_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    PtEx ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) ((T u).cls0).y :=
  ptEx_of (locGood_locAt X u w hg B) _ _ ((T u).cls0).y_bij.2

def SameUloc (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) : Prop :=
  ∀ v, ((T u).cls0).lev.Uloc v = ((X.lev0 u).Uloc v).map (reGL (rank_eq_first_level D.R) _).toMonoidHom

theorem sameUloc_of_joint (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hJ : Joint0 X.lev0 u (T u)) :
    SameUloc X T u := hJ.Uloc_eq


set_option maxHeartbeats 4000000 in
theorem ptAll_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    PtAll ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) ((T u).cls0).y := by
  refine ptAll_of (locGood_locAt X u w hg B) _ _ fun x => ?_
  obtain ⟨i, γ, k, hγ, hk, hkU, e⟩ := comp_re (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) (X.g u w hg).yG
    (Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w)) (X.g u w hg).yG_bij.2 x
  refine ⟨i, γ, reGL (rank_eq_first_level D.R) _ k, hγ, reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ hkU, e,
    fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, ((mem_awayP_iff _ _ k).1 hk).2 w' hw', rfl⟩


set_option maxHeartbeats 4000000 in
theorem awayEx_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)
    (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) :
    ∃ κ : ((T u).cls0).lev.U, (locAt X u w hg B).IsAway i γ κ.1 := by
  refine awayEx_of (locGood_locAt X u w hg B) _ (fun i γ => ?_) i γ
  have h1 : (((X.g u w hg).yG i).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1 ∈ Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w) :=
    (mem_map_conj _ _ _).1 (((X.g u w hg).gamI_range i _).1 ⟨γ, rfl⟩)
  have e : ((locAt X u w hg B).yG i)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((locAt X u w hg B).gamI i γ) * (locAt X u w hg B).yG i = reGL (rank_eq_first_level D.R) _ ((((X.g u w hg).yG i).1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1) := by
    rw [map_mul, map_mul, map_inv, ← bc_reGL]
    rfl
  rw [e]
  obtain ⟨h2, h3⟩ := (mem_awayP_iff _ _ _).1 h1
  refine ⟨reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ h2, fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, h3 w' hw', rfl⟩

end Formalism.L2.G
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CompanionOfBaseTied
section -- merged from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieStd
noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField Matrix

namespace Formalism.L2.G

theorem stdB_core {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (h : V → V → E)
    (c : V ≃ₗ[E] (Fin n → E)) (hc : ∀ x y, h x y = hform σ J (c x) (c y)) (b : Module.Basis (Fin n) E V)
    (hb : ∀ a a', h (b a) (b a') = if a = a' then 1 else 0) (L0 : Submodule (𝓞 E) V)
    (hL : L0 = Submodule.span (𝓞 E) (Set.range b)) :
    ∃ B : GL (Fin n) E, cT σ B.1 * J * B.1 = 1 ∧
      ∀ x : Fin n → E, x ∈ L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
        ∀ a, ((B⁻¹ : GL (Fin n) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  let b' : Module.Basis (Fin n) E (Fin n → E) := b.map c
  let M : Matrix (Fin n) (Fin n) E := (Pi.basisFun E (Fin n)).toMatrix b'
  let M' : Matrix (Fin n) (Fin n) E := b'.toMatrix (Pi.basisFun E (Fin n))
  have h1 : M * M' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : M' * M = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  let B : GL (Fin n) E := ⟨M, M', h1, h2⟩
  have hM : ∀ i a, M i a = c (b a) i := fun i a => by
    simp [M, b', Module.Basis.toMatrix_apply]
  refine ⟨B, ?_, fun x => ?_⟩
  · ext a a'
    have := hb a a'
    rw [hc] at this
    rw [Matrix.one_apply, ← this]
    simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, B, hM, Finset.sum_mul]
    rw [Finset.sum_comm]
  · have e1 : L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = Submodule.span (𝓞 E) (Set.range b') := by
      rw [hL, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [e1, Module.Basis.mem_span_iff_repr_mem]
    have e2 : (B⁻¹ : GL (Fin n) E).1 *ᵥ x = b'.repr x := by
      show M' *ᵥ x = b'.repr x
      have h3 := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun E (Fin n)) b' x
      have h4 : ((Pi.basisFun E (Fin n)).repr x : Fin n → E) = x := funext fun i => Pi.basisFun_repr E (Fin n) x i
      rw [h4] at h3
      exact h3
    rw [e2]
    rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermitian_form_frame_coordinates (D : D7) (x y : (D.sp.X 0).V) :
    (D.sp.X 0).hT x y = hform (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
      (crdN D 0 (Nat.zero_le _) x) (crdN D 0 (Nat.zero_le _) y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm]
  unfold hform
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  rfl

theorem exists_stdB (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B := by
  obtain ⟨b, hb, hL⟩ := h
  obtain ⟨B, h1, h2⟩ := stdB_core (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
    (fun x y => (D.sp.X 0).hT x y) (crdN D 0 (Nat.zero_le _)) (hermitian_form_frame_coordinates D)
    (b.reindex (finCongr (rankN D 0 (Nat.zero_le _))))
    (fun a a' => by
      simp only [Module.Basis.reindex_apply]
      rw [hb]
      simp)
    (D.sp.X 0).L0 (by rw [hL, Module.Basis.range_reindex])
  refine ⟨(reGL (rank_eq_first_level D.R) D.host.E).symm B, ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact h1
  · rw [MulEquiv.apply_symm_apply]
    exact h2

theorem exists_stdB_of_tied (D : D7) (h : Formalism.L2.Herm.StdTied D) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B :=
  exists_stdB D (h.1 0 (Nat.zero_le _))

end Formalism.L2.G
end
end

noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.G

section Re

theorem reGL_mulVec {a b : ℕ} (h : a = b) {E : Type} [Field E] (M : GL (Fin a) E) (x : Fin a → E) (i : Fin b) :
    ((reGL h E M).1 *ᵥ fun j : Fin b => x (Fin.cast h.symm j)) i = (M.1 *ᵥ x) (Fin.cast h.symm i) := by
  subst h
  rw [reGL_rfl]
  rfl

end Re

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdB_mem (D : D7) (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (x : Fin D.R.k → D.host.E) :
    x ∈ D.sp.crdLat0 (D.sp.X 0).L0 ↔
      ∀ a, ((B⁻¹ : GL (Fin D.R.k) D.host.E).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h2 := hB.2 (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j))
  have e1 : (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j)) ∈ selfDualLatticeCoords D 0 (Nat.zero_le _) ↔ x ∈ D.sp.crdLat0 (D.sp.X 0).L0 := by
    constructor
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext a
      have := congrFun e (Fin.cast (rank_eq_first_level D.R) a)
      exact this
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext j
      have := congrFun e (Fin.cast (rank_eq_first_level D.R).symm j)
      exact this
  rw [← e1, h2]
  constructor
  · intro h a
    have := h (Fin.cast (rank_eq_first_level D.R) a)
    rw [← map_inv, reGL_mulVec] at this
    exact this
  · intro h j
    rw [← map_inv, reGL_mulVec]
    exact h _

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem T_smul_mem (L : ColLevel R F E sp gp C A clsLat) (y : Fin R.k → E)
    (hy : y ∈ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)) : (A.T : E) • y ∈ L.Lb := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact L.Lb_dual y hy
  | zero => rw [smul_zero]; exact L.Lb.zero_mem
  | add y z _ _ h1 h2 => rw [smul_add]; exact L.Lb.add_mem h1 h2
  | smul c y _ h => rw [smul_comm]; exact L.Lb.smul_mem c h

theorem companion_le (L : ColLevel R F E sp gp C A clsLat) (𝔞 : Ideal (𝓞 E)) :
    L.Lb ⊔ 𝔞 • Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) ≤
      Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) :=
  sup_le (fun x hx => Submodule.subset_span (L.Lb_int x hx)) Submodule.smul_le_right

def LocId.withFr (I : LocId L p nV W Qq) (B : GL (Fin R.k) E)
    (h1 : ∀ x ∈ L.Lb, ∀ a, ((B⁻¹ : GL (Fin R.k) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range)
    (N : ℕ) (hN : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → (N : 𝓞 F) ∉ w.asIdeal)
    (h2 : ∀ i, (N : E) • (B.1 *ᵥ Pi.single i 1) ∈ L.Lb) : LocId L p nV W Qq :=
  { I with
    fr := fun w h => bc (((RingHom.fst _ _).comp (I.spl w h).toRingHom).comp (inclE (F := F) (w.adicCompletion F))) B
    fr_lat := fun w h t => Formalism.MainNotions.Gaps.Loc.fr_lat_of w (I.spl w h) (I.spl_alg w h) L.Lb B h1 N (hN w h) h2 t }

def locIdStd (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq')
    (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (𝔞 : Ideal (𝓞 D.host.E))
    (hL : Lc.Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 Lc.Lb) =
      D.sp.crdLat0 (D.sp.X 0).L0) : LocId Lc (D.what₂.places.resChar w) nV W' Qq' :=
  I.withFr B (fun x hx => (stdB_mem D B hB x).1 (hL ▸ (le_sup_left : Lc.Lb ≤ _) hx)) (D.mem u).A.T
    (fun w' hw' => natCast_notMem w' hg.1 hw' hg.2.2.2.2.2)
    (fun i => T_smul_mem Lc _ (companion_le Lc 𝔞 (hL ▸ (stdB_mem D B hB _).2 fun a => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : a = i
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩)))

theorem companion_of_baseTied (D : D7) (H : Formalism.L2.Herm.HermCols D) (aT : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u))
    (hb : Formalism.L2.Herm.BaseTied D H aT) (u : D.what₂.Word) :
    ∃ 𝔞 : Ideal (𝓞 D.host.E), (H.lev0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
      (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0 := by
  have hi : IsIntegral ℤ (D.host.conj ((aT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  exact ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (hb u ⟨_, hi⟩ rfl).1⟩

end Formalism.L2.G
end
end

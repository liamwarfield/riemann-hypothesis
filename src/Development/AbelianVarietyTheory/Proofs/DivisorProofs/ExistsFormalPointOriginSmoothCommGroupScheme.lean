module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesInjectiveLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendsTaylorPowerSeriesRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupLocalCoordinatesAtOrigin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderiv
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.TaylorDeriv

theorem foldr_iterate_comm {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι → ℕ) (a : ι) (f : A) (l : List ι) :
    l.foldr (fun i g => (ds i)^[α i] g) (ds a f) = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, ih]
    have : Function.Commute (ds i) (ds a) := fun x => h i a x
    exact (this.iterate_left (α i)) _

theorem foldr_iterate_add_single {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι →₀ ℕ) (a : ι) (f : A) (l : List ι) (hl : l.Nodup) (ha : a ∈ l) :
    l.foldr (fun i g => (ds i)^[(α + Finsupp.single a 1 : ι →₀ ℕ) i] g) f
      = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  classical
  induction l with
  | nil => simp at ha
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    by_cases hi : i = a
    · subst hi
      have : l.foldr (fun j g => (ds j)^[(α + Finsupp.single i 1 : ι →₀ ℕ) j] g) f
          = l.foldr (fun j g => (ds j)^[α j] g) f := by
        apply List.foldr_ext
        intro j hj b
        have : j ≠ i := fun e => hl.1 (e ▸ hj)
        simp [Finsupp.single_apply, this.symm]
      rw [this]
      simp [Function.iterate_succ_apply']
    · have ha' : a ∈ l := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hi
        · exact e
      rw [ih hl.2 ha']
      have e : (α + Finsupp.single a 1 : ι →₀ ℕ) i = α i := by
        simp [Finsupp.single_apply, Ne.symm hi]
      rw [e]
      have : Function.Commute (ds i) (ds a) := fun x => h i a x
      exact (this.iterate_left (α i)) _

theorem iterOp_apply_eq_add_single {A : Type} {n : ℕ} (ds : Fin n → A → A)
    (h : ∀ a b f, ds a (ds b f) = ds b (ds a f)) (α : Fin n →₀ ℕ) (a : Fin n) (f : A) :
    iterOp ds α (ds a f) = iterOp ds (α + Finsupp.single a 1) f := by
  unfold iterOp
  rw [foldr_iterate_comm ds h, foldr_iterate_add_single ds h α a f _ (List.nodup_finRange n) (List.mem_finRange a)]

theorem prod_factorial_add_single {n : ℕ} (α : Fin n →₀ ℕ) (a : Fin n) :
    ∏ i, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = (∏ i, ((α i).factorial : ℚ)) * ((α a : ℚ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ (fun i => ((α i).factorial : ℚ)) (Finset.mem_univ a)]
  have : ∏ i ∈ Finset.univ.erase a, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = ∏ i ∈ Finset.univ.erase a, ((α i).factorial : ℚ) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, this.symm]
  rw [this]
  simp [Nat.factorial_succ]
  ring

theorem taylor_deriv_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv (R := B) a (taylor ev (fun i => ⇑(ds i)) f) := by
  intro A B _ _ _ n ev ds h a f
  ext α
  rw [MvPowerSeries.coeff_pderiv]
  simp only [MvPowerSeries.coeff_apply, taylor]
  rw [prod_factorial_add_single, ← iterOp_apply_eq_add_single (fun i => ⇑(ds i)) h]
  have e : ((α a : B) + 1) = algebraMap ℚ B ((α a : ℚ) + 1) := by simp
  have hp : ((α a : ℚ) + 1) ≠ 0 := by positivity
  rw [e, mul_comm _ (algebraMap ℚ B _), ← Algebra.smul_def, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FormalOrigin.TaylorDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderivStatement
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv (R := B) a (taylor ev (fun i => ⇑(ds i)) f) := by
  first | exact @GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | exact GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | (intros; apply GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherian
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.PowerSeriesComplete

theorem isAdicComplete_map_C : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R))
      (MvPowerSeries (Fin n) R) := by
  intro R _ _ I hI n
  have hfg : I.FG := IsNoetherian.noetherian I
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = algebraMap R (MvPowerSeries (Fin n) R) := rfl
  have hP : IsPrecomplete I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isPrecomplete_pi (M := R) (Fin n →₀ ℕ) hfg
  have hH : IsHausdorff I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isHausdorff_pi (M := R) (Fin n →₀ ℕ) hfg
  rw [hC]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

end GlobalTheory.PowerSeriesComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherianStatement
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  first | exact @GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | exact GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | (intros; apply GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsCommuteOfCommGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsCommuteOfCommGroupScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvFieldComm

section Rings

variable {S : Type} [CommRing S]

def fstH (S : Type) [CommRing S] : DualNumber S →+* S := (TrivSqZeroExt.fstHom S S S).toRingHom

def swap (S : Type) [CommRing S] : DualNumber (DualNumber S) →+* DualNumber (DualNumber S) where
  toFun x := TrivSqZeroExt.inl (TrivSqZeroExt.inl x.fst.fst + TrivSqZeroExt.inr x.snd.fst) +
    TrivSqZeroExt.inr (TrivSqZeroExt.inl x.fst.snd + TrivSqZeroExt.inr x.snd.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp <;> ring
  map_mul' a b := by ext <;> simp <;> ring

theorem swap_snd_snd (x : DualNumber (DualNumber S)) : (swap S x).snd.snd = x.snd.snd := by
  simp [swap]

end Rings

section Rings2

variable {R S : Type} [CommRing R] [CommRing S]

abbrev inc (S : Type) [CommRing S] : S →+* DualNumber S := algebraMap S (DualNumber S)

theorem dualMap_comp_inc (φ : R →+* S) : (dualMap φ).comp (inc R) = (inc S).comp φ := by
  refine RingHom.ext fun x => ?_; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_inc : (fstH S).comp (inc S) = RingHom.id S := by
  refine RingHom.ext fun x => ?_; simp [fstH, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_inc_inc_comp (φ : R →+* S) : (swap S).comp ((inc (DualNumber S)).comp ((inc S).comp φ)) =
    (inc (DualNumber S)).comp ((inc S).comp φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_inc_dualMap (φ : R →+* S) : (swap S).comp ((inc (DualNumber S)).comp (dualMap φ)) = dualMap ((inc S).comp φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_dualMap_inc (φ : R →+* S) : (swap S).comp (dualMap ((inc S).comp φ)) = (inc (DualNumber S)).comp (dualMap φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* S) : (fstH S).comp (dualMap φ) = φ.comp (fstH R) := by
  refine RingHom.ext fun x => ?_; simp [fstH, dualMap]

end Rings2

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ψ' : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap ψ' = spMap (ψ.comp ψ') := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem dual_pt {S : Type} [CommRing S] (x : Sp (DualNumber S)) :
    (spMap (fstH S)) ((spMap (algebraMap S (DualNumber S))) x) = x := by
  apply PrimeSpectrum.ext
  ext y
  change algebraMap S (DualNumber S) (fstH S y) ∈ x.asIdeal ↔ y ∈ x.asIdeal
  have hn : (TrivSqZeroExt.inr y.snd : DualNumber S) ∈ x.asIdeal :=
    x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  have hy : y = algebraMap S (DualNumber S) (fstH S y) + TrivSqZeroExt.inr y.snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq y).symm
  constructor
  · intro h; rw [hy]; exact add_mem h hn
  · intro h
    have e : algebraMap S (DualNumber S) (fstH S y) = y - TrivSqZeroExt.inr y.snd := by
      rw [eq_sub_iff_add_eq]; exact hy.symm
    rw [e]; exact sub_mem h hn

section Val

variable {A : Type} [CommRing A] {X : Scheme.{0}}

def evHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq_evHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = evHom x U h f := by
  unfold valR
  rw [dif_pos h]
  rfl

theorem top_le_spMap {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap ψ) y))

theorem valR_spMap_comp {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap ψ ≫ x) U f = ψ (valR x U f) := by
  have h' := top_le_spMap ψ x U h
  rw [valR_eq_evHom _ U h', valR_eq_evHom x U h]
  have e : (spMap ψ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

theorem top_le_fromSpecStalk {x : X} {U : X.Opens} (hU : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
  have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU

theorem valR_fromSpecStalk {x : X} {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (A := X.presheaf.stalk x) (X.fromSpecStalk x) U a = X.presheaf.germ U x hU a := by
  have h := top_le_fromSpecStalk hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans
      (Category.comp_id _))
  unfold valR
  refine (dif_pos h).trans ?_
  change ((X.fromSpecStalk x).appLE U ⊤ h ≫ (Scheme.ΓSpecIso _).hom).hom a = _
  rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Val

section Tr

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem tv_hom (v : TanM (𝟙 (Sp R)) G) : (tv v).left ≫ G.hom = spMap (inc R) := by
  have := Over.w (tv v)
  simpa using this

theorem one_left' {T : Over (Sp R)} : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

theorem fst_tv (v : TanM (𝟙 (Sp R)) G) : spMap (fstH R) ≫ (tv v).left = η[G].left := by
  have h := congrArg (fun k => k.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  simp only [smT, Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, one_left'] at h
  have gen : ∀ ψ : DualNumber R →+* DualNumber R, (∀ x, ψ x = inc R x.fst) →
      spMap ψ ≫ (tv v).left = (overAt (𝟙 (Sp R)) (DualNumber R)).hom ≫ η[G].left →
      spMap ((inc R).comp (fstH R)) ≫ (tv v).left = spMap (inc R) ≫ η[G].left := by
    intro ψ hψ hh
    have : ψ = (inc R).comp (fstH R) := RingHom.ext fun x => hψ x
    subst this
    simpa using hh
  have e2 := gen _ (fun x => by ext <;> simp [tm, TrivSqZeroExt.algebraMap_eq_inl]) h
  have h2 := congrArg (fun k => spMap (fstH R) ≫ k) e2
  simp only [← spMap_comp, ← Category.assoc] at h2
  simp only [spMap_comp, fst_comp_inc, spMap_id] at h2
  simpa using h2

variable {S : Type} [CommRing S]

def gW (g : Sp S ⟶ G.left) : tEpsG (g ≫ G.hom) ⟶ G :=
  Over.homMk (spMap (inc S) ≫ g) (by simp)

def vW (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    tEpsG (g ≫ G.hom) ⟶ G :=
  Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
    simp only [tEpsG, Over.mk_hom, Category.assoc, tv_hom, hg, spMap_comp, dualMap_comp_inc])

def trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    Sp (DualNumber S) ⟶ G.left :=
  (gW G g * vW G φ g hg v).left

theorem isTr_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    GlobalTheory.Heat.IsTr G φ g v (trP G φ g hg v) :=
  ⟨_, _, rfl, rfl, rfl⟩

theorem translateTangent_comp_hom (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    trP G φ g hg v ≫ G.hom = spMap ((inc S).comp φ) := by
  rw [trP, Over.w]
  simp only [tEpsG, Over.mk_hom, hg, spMap_comp]

theorem fst_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    spMap (fstH S) ≫ trP G φ g hg v = g := by
  let E : Over.mk (g ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (fstH S)) (by
      show spMap (fstH S) ≫ spMap (inc S) ≫ g ≫ G.hom = g ≫ G.hom
      rw [← Category.assoc, spMap_comp, fst_comp_inc, spMap_id]; exact Category.id_comp _)
  have e1 : E ≫ gW G g = Over.homMk g rfl := by
    ext
    show spMap (fstH S) ≫ spMap (inc S) ≫ g = g
    rw [← Category.assoc, spMap_comp, fst_comp_inc, spMap_id]; exact Category.id_comp _
  have e2 : E ≫ vW G φ g hg v = 1 := by
    ext
    simp only [E, vW, Over.comp_left, Over.homMk_left, one_left', Over.mk_hom]
    rw [← Category.assoc, spMap_comp, fst_comp_dualMap, ← spMap_comp, Category.assoc, fst_tv, hg]
  have := congrArg (fun k => k.left) (MonObj.comp_mul E (gW G g) (vW G φ g hg v))
  simpa only [e1, e2, _root_.mul_one, Over.comp_left, Over.homMk_left, E, trP] using this

theorem top_le_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G)
    (O : G.left.Opens) (hO : ⊤ ≤ g ⁻¹ᵁ O) : ⊤ ≤ trP G φ g hg v ⁻¹ᵁ O := by
  intro x _
  rw [← dual_pt x]
  show (spMap (fstH S) ≫ trP G φ g hg v) _ ∈ O
  rw [fst_trP]
  exact hO (Set.mem_univ _)

end Tr

section Swap

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]

theorem swap_inc_inc : (swap S).comp ((inc (DualNumber S)).comp (inc S)) = (inc (DualNumber S)).comp (inc S) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v v' : TanM (𝟙 (Sp R)) G) :
    trP G ((inc S).comp φ) (trP G φ g hg v) (translateTangent_comp_hom G φ g hg v) v' =
      spMap (swap S) ≫ trP G ((inc S).comp φ) (trP G φ g hg v') (translateTangent_comp_hom G φ g hg v') v := by
  have hw := translateTangent_comp_hom G φ g hg v'
  have hu := translateTangent_comp_hom G φ g hg v
  let P : tEpsG (trP G φ g hg v' ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (inc (DualNumber S))) (by
      show spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v' ≫ G.hom
      rw [trP, Over.w]; rfl)
  let P' : tEpsG (trP G φ g hg v ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (inc (DualNumber S))) (by
      show spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v ≫ G.hom
      rw [trP, Over.w]; rfl)
  let Q : tEpsG (trP G φ g hg v ≫ G.hom) ⟶ tEpsG (trP G φ g hg v' ≫ G.hom) :=
    Over.homMk (spMap (swap S)) (by
      show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ trP G φ g hg v' ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v ≫ G.hom
      rw [hw, hu, spMap_comp, spMap_comp, swap_inc_inc_comp])
  have e1 : gW G (trP G φ g hg v') = P ≫ (gW G g * vW G φ g hg v') := Over.OverMorphism.ext rfl
  have e2 : gW G (trP G φ g hg v) = P' ≫ (gW G g * vW G φ g hg v) := Over.OverMorphism.ext rfl
  have hx : Q ≫ P ≫ gW G g = P' ≫ gW G g := by
    ext
    show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g =
      spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g
    simp only [← Category.assoc, spMap_comp]
    rw [swap_inc_inc]
  have hb : Q ≫ P ≫ vW G φ g hg v' = vW G ((inc S).comp φ) (trP G φ g hg v) hu v' := by
    ext
    show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ spMap (dualMap φ) ≫ (tv v').left =
      spMap (dualMap ((inc S).comp φ)) ≫ (tv v').left
    simp only [← Category.assoc, spMap_comp]
    rw [swap_inc_dualMap]
  have hc : Q ≫ vW G ((inc S).comp φ) (trP G φ g hg v') hw v = P' ≫ vW G φ g hg v := by
    ext
    show spMap (swap S) ≫ spMap (dualMap ((inc S).comp φ)) ≫ (tv v).left =
      spMap (inc (DualNumber S)) ≫ spMap (dualMap φ) ≫ (tv v).left
    simp only [← Category.assoc, spMap_comp]
    rw [swap_dualMap_inc]
  have key : gW G (trP G φ g hg v) * vW G ((inc S).comp φ) (trP G φ g hg v) hu v' =
      Q ≫ (gW G (trP G φ g hg v') * vW G ((inc S).comp φ) (trP G φ g hg v') hw v) := by
    rw [MonObj.comp_mul, e1, e2, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, hx, hb, hc, mul_right_comm]
  exact congrArg (fun k => k.left) key

end Swap

end GlobalTheory.InvFieldComm

open GlobalTheory.InvFieldComm in
theorem GlobalTheory.InvFieldComm.invField_comm : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v v' : TanM (𝟙 (Sp R)) G) (dd dd' : Fld G.left), IsInv G v dd → IsInv G v' dd' → ∀ O f, dd O (dd' O f) = dd' O (dd O f) := by
  intro R _ G _ _ v v' dd dd' hv hv' O f
  have key : ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ),
      ⊤ ≤ g ⁻¹ᵁ O → valR g O (dd O (dd' O f)) = valR g O (dd' O (dd O f)) := by
    intro S _ φ g hg hO
    have hw1 := top_le_trP G φ g hg v' O hO
    have hu1 := top_le_trP G φ g hg v O hO
    have hw2 := top_le_trP G _ _ (translateTangent_comp_hom G φ g hg v') v O hw1
    have A1 := hv'.2 S φ g _ O (dd O f) hg hO (isTr_trP G φ g hg v')
    have A2 := hv.2 (DualNumber S) _ _ _ O f (translateTangent_comp_hom G φ g hg v') hw1 (isTr_trP G _ _ (translateTangent_comp_hom G φ g hg v') v)
    have B1 := hv.2 S φ g _ O (dd' O f) hg hO (isTr_trP G φ g hg v)
    have B2 := hv'.2 (DualNumber S) _ _ _ O f (translateTangent_comp_hom G φ g hg v) hu1 (isTr_trP G _ _ (translateTangent_comp_hom G φ g hg v) v')
    rw [← B1, ← B2, swap_trP, valR_spMap_comp _ _ _ hw2, swap_snd_snd, A2, A1]
  have hsub : ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left), g ≫ G.hom = spMap φ →
      ⊤ ≤ g ⁻¹ᵁ O → valR g O (dd O (dd' O f) - dd' O (dd O f)) = 0 := by
    intro S _ φ g hg hO
    rw [valR_eq_evHom g O hO, map_sub, ← valR_eq_evHom g O hO, ← valR_eq_evHom g O hO, key S φ g hg hO, sub_self]
  refine sub_eq_zero.1 (TopCat.Presheaf.section_ext G.left.sheaf O _ 0 fun y hy => ?_)
  have h0 := hsub (G.left.presheaf.stalk y) (Spec.preimage (G.left.fromSpecStalk y ≫ G.hom)).hom
    (G.left.fromSpecStalk y) (Spec.map_preimage _).symm (top_le_fromSpecStalk hy)
  exact ((valR_fromSpecStalk hy _).symm.trans h0).trans (map_zero (G.left.presheaf.germ O y hy).hom).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsCommuteOfCommGroupSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorFields_commute_of_commGroupScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v v' : TanM (𝟙 (Sp R)) G) (dd dd' : Fld G.left), IsInv G v dd → IsInv G v' dd' → ∀ O f, dd O (dd' O f) = dd' O (dd O f) := by
  first | exact @GlobalTheory.InvFieldComm.invField_comm | exact GlobalTheory.InvFieldComm.invField_comm | (intros; apply GlobalTheory.InvFieldComm.invField_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationOfVectorFieldLiftNearUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationOfVectorFieldLiftNearUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem scheme_constantSection_add {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a + b) = constFn p U a + constFn p U b := by
  simp [constFn, map_add (f := _)]

theorem constFn_mul_on_open {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a * b) = constFn p U a * constFn p U b := by
  simp [constFn, map_mul]

theorem gammaSpecIso_appLE_of_eq_id_apply {R : Type} [CommRing R] (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (e : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ ⊤) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((f.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = r := by
  subst hf
  simp only [Scheme.Hom.appLE]
  erw [show (homOfLE e) = 𝟙 _ from Subsingleton.elim _ _]
  simp

theorem gammaSpecIso_appLE_section_constantSection_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (e : Sp R ⟶ X) (he : e ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ e ⁻¹ᵁ U) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r)) = r := by
  have hc := Scheme.Hom.appLE_comp_appLE e p ⊤ U ⊤ (fun _ _ => trivial) h
  calc (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((p.appLE ⊤ U (fun _ _ => trivial) ≫ e.appLE U ⊤ h).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl
    _ = _ := by rw [hc]
    _ = r := gammaSpecIso_appLE_of_eq_id_apply _ he _ r

end GlobalTheory.Heat

namespace GlobalTheory.Heat

theorem liftDer_isDerivation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens)
    (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  intro R _ G _ D W d hL hW
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  let ev : Γ(G.left, W) →+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (((η[G]).left.appLE W ⊤ hW).hom)
  have hev : ∀ r, ev (constFn G.hom W r) = r := fun r => gammaSpecIso_appLE_section_constantSection_eq G.hom _ he W hW r
  have hc : ∀ r, d W (constFn G.hom W r) = constFn G.hom W (D r) := hL.2 W le_rfl
  have hadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    have := congrArg ev (hc (a + b))
    rw [scheme_constantSection_add, hL.1.1 W le_rfl, hc, hc, map_add (f := _), hev, hev, hev] at this
    exact this.symm
  have hmul : ∀ a b, D (a * b) = a * D b + b * D a := by
    intro a b
    have := congrArg ev (hc (a * b))
    rw [constFn_mul_on_open, hL.1.2.1 W le_rfl, hc, hc, map_add (f := _), map_mul, map_mul, hev, hev, hev, hev, hev] at this
    exact this.symm
  let L : R →ₗ[ℤ] R := (AddMonoidHom.mk' D hadd).toIntLinearMap
  exact ⟨Derivation.mk' L (fun a b => by simpa [L, smul_eq_mul] using hmul a b), fun r => rfl⟩

end GlobalTheory.Heat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationOfVectorFieldLiftNearUnitStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  first | exact @GlobalTheory.Heat.liftDer_isDerivation | exact GlobalTheory.Heat.liftDer_isDerivation | (intros; apply GlobalTheory.Heat.liftDer_isDerivation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfVectorFieldOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfVectorFieldOnOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerField

variable {X : Scheme.{0}} {W : X.Opens} {d : Fld X} {x : X}

theorem germ_field_congr (hd : IsField W d) {O O' : X.Opens} (hO : x ∈ O) (hO' : x ∈ O')
    (hOW : O ≤ W) (hO'W : O' ≤ W) (f : Γ(X, O)) (f' : Γ(X, O'))
    (h : (X.presheaf.germ O x hO).hom f = (X.presheaf.germ O' x hO').hom f') :
    (X.presheaf.germ O x hO).hom (d O f) = (X.presheaf.germ O' x hO').hom (d O' f') := by
  obtain ⟨V, hV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hO hO' f f' h
  have h1 : (X.presheaf.germ O x hO).hom (d O f) =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iU) f)) := by
    rw [hd.2.2 O V (leOfHom iU) hOW f]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iU x hV _).symm
  have h2 : (X.presheaf.germ O' x hO').hom (d O' f') =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iV) f')) := by
    rw [hd.2.2 O' V (leOfHom iV) hO'W f']
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iV x hV _).symm
  have e' : resG X (leOfHom iU) f = resG X (leOfHom iV) f' := e
  rw [h1, h2, e']

theorem exists_rep (hxW : x ∈ W) (t : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f : Γ(X, O)), (X.presheaf.germ O x hO).hom f = t := by
  obtain ⟨U, m, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
  refine ⟨U ⊓ W, ⟨m, hxW⟩, inf_le_right, resG X (inf_le_left : U ⊓ W ≤ U) s, ?_⟩
  rw [← hs]
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨m, hxW⟩ s

theorem exists_rep₂ (hxW : x ∈ W) (t t' : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f f' : Γ(X, O)),
      (X.presheaf.germ O x hO).hom f = t ∧ (X.presheaf.germ O x hO).hom f' = t' := by
  obtain ⟨O₁, h₁, hW₁, f₁, e₁⟩ := exists_rep hxW t
  obtain ⟨O₂, h₂, hW₂, f₂, e₂⟩ := exists_rep hxW t'
  refine ⟨O₁ ⊓ O₂, ⟨h₁, h₂⟩, inf_le_left.trans hW₁, resG X (inf_le_left : O₁ ⊓ O₂ ≤ O₁) f₁,
    resG X (inf_le_right : O₁ ⊓ O₂ ≤ O₂) f₂, ?_, ?_⟩
  · rw [← e₁]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨h₁, h₂⟩ f₁
  · rw [← e₂]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x ⟨h₁, h₂⟩ f₂

def germMap (hxW : x ∈ W) (t : X.presheaf.stalk x) : X.presheaf.stalk x :=
  (X.presheaf.germ _ x (exists_rep hxW t).choose_spec.choose).hom
    (d _ (exists_rep hxW t).choose_spec.choose_spec.choose_spec.choose)

theorem germMap_germ (hd : IsField W d) (hxW : x ∈ W) {O : X.Opens} (hO : x ∈ O) (hOW : O ≤ W)
    (f : Γ(X, O)) :
    germMap (d := d) hxW ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  have hs := (exists_rep hxW ((X.presheaf.germ O x hO).hom f)).choose_spec.choose_spec
  exact germ_field_congr hd _ hO hs.choose hOW _ f hs.choose_spec.choose_spec

end GlobalTheory.StalkDerField


open GlobalTheory.StalkDerField in
theorem GlobalTheory.StalkDerField.exists_stalk_derivation : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  intro X W d hd x hxW
  let g : X.presheaf.stalk x →+ X.presheaf.stalk x := AddMonoidHom.mk' (germMap (d := d) hxW) (by
    intro t t'
    obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
    rw [← map_add (f := _), germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
      germMap_germ hd hxW hO hOW, hd.1 O hOW f f', map_add])
  refine ⟨Derivation.mk' g.toIntLinearMap ?_, fun O hO hOW f => germMap_germ hd hxW hO hOW f⟩
  intro t t'
  obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
  show germMap hxW _ = _ • germMap hxW _ + _ • germMap hxW _
  rw [← map_mul, germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
    germMap_germ hd hxW hO hOW, hd.2.1 O hOW f f', smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfVectorFieldOnOpenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  first | exact @GlobalTheory.StalkDerField.exists_stalk_derivation | exact GlobalTheory.StalkDerField.exists_stalk_derivation | (intros; apply GlobalTheory.StalkDerField.exists_stalk_derivation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFromSpecStalkTopLeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFromSpecStalkTopLeIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem spMap_fromSpecStalk_le_preimage_iff (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω) (hψ : IsLocalHom ψ) (O : X.Opens) :
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O := by
  constructor
  · intro h
    let p : ↥(Sp Ω) := closedPoint Ω
    have hm : (spMap ψ ≫ X.fromSpecStalk x) p ∈ O := h (x := p) trivial
    rw [Scheme.Hom.comp_apply] at hm
    have e : (spMap ψ) p = (closedPoint (X.presheaf.stalk x) : ↥(Spec (X.presheaf.stalk x))) := by
      show PrimeSpectrum.comap ψ (closedPoint Ω) = _
      exact IsLocalRing.comap_closedPoint ψ
    rw [e, Scheme.fromSpecStalk_closedPoint] at hm
    exact hm
  · intro hx w _
    have : X.fromSpecStalk x (spMap ψ w) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    show (spMap ψ ≫ X.fromSpecStalk x) w ∈ O
    rw [Scheme.Hom.comp_apply]
    exact Specializes.mem_open (x := X.fromSpecStalk x (spMap ψ w)) this O.isOpen hx

theorem spMap_fromSpecStalk_top_le_iff : ∀ (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω), IsLocalHom ψ → ∀ O : X.Opens,
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O :=
  fun X x Ω _ _ ψ hψ O => spMap_fromSpecStalk_le_preimage_iff X x Ω ψ hψ O

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFromSpecStalkTopLeIffStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem : ∀ (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (ψ : X.presheaf.stalk x →+* Ω), IsLocalHom ψ → ∀ O : X.Opens, ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O := by
  first | exact @GlobalTheory.spMap_fromSpecStalk_top_le_iff | exact GlobalTheory.spMap_fromSpecStalk_top_le_iff | (intros; apply GlobalTheory.spMap_fromSpecStalk_top_le_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem exists_formalPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  intro R _ _ _ _ _ _ G _ _ hsm hint n v dd hdd D W d hd hW
  have hx0W : origin G ∈ W := hW (show IsLocalRing.closedPoint R ∈ (⊤ : (Sp R).Opens) from trivial)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit R G D W d hd hW
  choose δ hδ using fun a => GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left ⊤ (dd a) (hdd a).1 (origin G) trivial
  obtain ⟨dA, hdA⟩ := GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left W d hd.1 (origin G) hx0W
  have hcomm : ∀ a b s, δ a (δ b s) = δ b (δ a s) := by
    intro a b s
    obtain ⟨O, hO, f, rfl⟩ := TopCat.Presheaf.germ_exist G.left.presheaf s
    rw [hδ b O hO le_top, hδ a O hO le_top, hδ a O hO le_top, hδ b O hO le_top,
      GlobalTheory.T.invariantVectorFields_commute_of_commGroupScheme R G (v a) (v b) (dd a) (dd b) (hdd a) (hdd b)]
  have hconst : ∀ a r, δ a (constO G r) = 0 := by
    intro a r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G ⊤ trivial r, hδ a ⊤ trivial le_top, GlobalTheory.T.invariantVectorField_apply_constant_eq_zero R G (v a) (dd a) (hdd a), map_zero]
  have hdc : ∀ r, dA (constO G r) = constO G (D' r) := by
    intro r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G W hx0W r, hdA W hx0W le_rfl, hd.2 W le_rfl, ← hD', GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants]
  obtain ⟨z, hz0, hz1, hm⟩ := GlobalTheory.T.smooth_commGroup_local_coordinates_at_origin R G hsm n v dd hdd δ (fun a O hO f => hδ a O hO le_top f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor _ R n (evO G) δ
  have hTC : ∀ r, T (constO G r) = MvPowerSeries.C r := by
    intro r
    rw [hT, GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill _ R n (evO G) δ _ (fun i => hconst i r), GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants]
  have hT0 : ∀ s, MvPowerSeries.constantCoeff (T s) = evO G s := by
    intro s
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hT]
    show (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • evO G (iterOp _ 0 s) = _
    rw [iterOp_zero]
    simp
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left
  have : IsLocalHom T := ⟨fun s hs => by
    have h1 : IsUnit (evO G s) := by rw [← hT0]; exact (MvPowerSeries.isUnit_iff_constantCoeff).1 hs
    exact (isUnit_map_iff (evO G) s).1 h1⟩
  obtain ⟨dΩ, hdΩC, hdΩ⟩ := GlobalTheory.T.derivation_extends_taylorPowerSeriesRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm hconst dA D' hdc
  have hval : ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)),
      valR (spMap T ≫ G.left.fromSpecStalk (origin G)) O f = T ((G.left.presheaf.germ O (origin G) hO).hom f) :=
    fun O hO f => GlobalTheory.FlagBundle.valR_spMap_fromSpecStalk T hO f
  have htop : ∀ O : G.left.Opens, ⊤ ≤ (spMap T ≫ G.left.fromSpecStalk (origin G)) ⁻¹ᵁ O → origin G ∈ O :=
    fun O h => (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance O).1 h
  refine ⟨MvPowerSeries (Fin n) R, inferInstance, NoZeroDivisors.to_isDomain _, inferInstance, MvPowerSeries.C,
    spMap T ≫ G.left.fromSpecStalk (origin G), fun a => intDer (MvPowerSeries.pderiv (R := R) a), intDer dΩ,
    GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian R _ ‹_› n, ?_, (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance W).2 hx0W, fun r => ?_, fun a r => ?_,
    fun a O f hO => ?_, fun O f hOW hO => ?_, fun O f hO hf => ?_⟩
  · rw [Category.assoc, GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq R G _ T]
    congr 1
    exact RingHom.ext hTC
  · rw [← hD']; exact hdΩC r
  · exact MvPowerSeries.pderiv_C
  · have h := htop O hO
    rw [hval O h, hval O h, ← hδ a O h le_top, hT, hT, GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv _ R n (evO G) δ hcomm]
    rfl
  · have h := htop O hO
    rw [hval O h, hval O h, ← hdA O h hOW, hT, hT]
    exact (hdΩ _).symm
  · have h := htop O hO
    rw [hval O h, hT] at hf
    have h0 := GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm _ hf
    exact germ_injective_of_isIntegral G.left (origin G) h (h0.trans (map_zero _).symm)

end GlobalTheory.FormalOrigin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  first | exact @GlobalTheory.FormalOrigin.exists_formalPoint | exact GlobalTheory.FormalOrigin.exists_formalPoint | (intros; apply GlobalTheory.FormalOrigin.exists_formalPoint <;> assumption)
end

module

public import Development.EtaleCohomology.TateTwists.EtaleTateTwistLocalGenerationAndRootCompatOfPart

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorRestrictionAndRootChangeH
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op
  have h2 := congrArg (fun f => f.hom x) h
  simp only [ModuleCat.hom_comp] at h2
  exact h2.symm

theorem res_twGen (q : ℕ) (j : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q j) g _).trans ?_
  congr 1
  change Submodule.mapQ _ _ _ (twRel_le q j (Scheme.Hom.appTop g).hom) (Submodule.Quotient.mk _) = _
  rw [Submodule.mapQ_apply]
  simp [Finsupp.mapDomain_single]

theorem twGen_pow (q : ℕ) [NeZero q] (j : ℤ) {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen j ξ = ((a ^ j : (ZMod q)ˣ) : ZMod q).val • twGen j ζ := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(V, ⊤)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q))) := by
    rw [Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have hs : (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q)) : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) =
      ((a ^ j : (ZMod q)ˣ) : ZMod q).val • Finsupp.single ζ 1 := by
    rw [Finsupp.smul_single]
    congr 1
    apply ULift.ext
    simp only [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val _).symm
  have key : ∀ (n : ℕ) (x y : (twF q j).obj Γ(V, ⊤)), x = n • y →
      ofRings.sec (twF q j) V x = n • ofRings.sec (twF q j) V y := by
    rintro n x y rfl
    exact map_nsmul _ _ _
  refine key _ _ _ ?_
  show (Submodule.Quotient.mk (Finsupp.single ξ 1) : (_ ⧸ twRel q j Γ(V, ⊤))) =
    _ • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (_ ⧸ twRel q j Γ(V, ⊤)))
  rw [hrel, hs]
  exact map_nsmul (Submodule.mkQ _) _ _

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

def LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val

open LateralTheory.EtaleFoundations.GenIsoSurjRootPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers
    (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange := by
  intro q _ j
  refine ⟨fun V U g ζ => res_twGen q j g ζ, fun U ζ ξ => ?_⟩
  obtain ⟨S, hS, h⟩ := hp q U ζ ξ
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a, ha⟩ := h V g hg
  exact ⟨_, (res_twGen q j g ξ).trans (twGen_pow q j (ζ.map g.appTop.hom) (ξ.map g.appTop.hom) a ha)⟩

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem alg_prim_pow {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (ζ ξ : A)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0)
    {K : Type} [Field K] (f : A →+* K) : ∃ (a : (ZMod q)ˣ) (s : A), f s ≠ 0 ∧ s * (ξ - ζ ^ (a : ZMod q).val) = 0 := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map f; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have root : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → IsPrimitiveRoot (f x) q := by
    intro x hx
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    have h1 := congrArg f hx
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h1
    rwa [show f.comp (algebraMap ℤ A) = Int.castRingHom K from RingHom.ext_int _ _] at h1
  have pq : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → x ^ q = 1 := by
    intro x hx
    obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (Polynomial.aeval x) hr
    rw [map_mul, hx, zero_mul] at this
    simpa [sub_eq_zero] using this
  obtain ⟨i, hi, he⟩ := (root ζ hζ).eq_pow_of_pow_eq_one (root ξ hξ).pow_eq_one
  have hcop : i.Coprime q := by
    have h2 := root ξ hξ
    rw [← he] at h2
    exact ((root ζ hζ).pow_iff_coprime (NeZero.pos q) i).1 h2
  refine ⟨ZMod.unitOfCoprime i hcop, ∑ m ∈ Finset.range q, ξ ^ m * (ζ ^ i) ^ (q - 1 - m), ?_, ?_⟩
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    intro h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    have : ∀ m ∈ Finset.range q, f (ξ ^ m * (ζ ^ i) ^ (q - 1 - m)) = (f ζ ^ i) ^ (q - 1) := by
      intro m hm
      rw [map_mul, map_pow, map_pow, map_pow, ← he, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hm; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hqK h
    · exact (root ζ hζ).ne_zero (NeZero.ne q) (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h))
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    rw [hv, geom_sum₂_mul]
    rw [pq ξ hξ, ← pow_mul, mul_comm i q, pow_mul, pq ζ hζ, one_pow, sub_self]

theorem unit_res {U : Scheme.{0}} (s : Γ(U, ⊤)) : ∀ (O : U.Opens) (h : O ≤ ⊤), O = U.basicOpen s →
    IsUnit (U.presheaf.map (homOfLE h).op s) := by
  rintro O h rfl
  exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace s

theorem loc_of_points {U : Scheme.{0}} (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ x : U, ∃ s : Γ(U, ⊤), x ∈ U.basicOpen s ∧ P _ (U.basicOpen s).ι) : Loc U P := by
  choose s hs hPs using h
  let S : Sieve U := { arrows := fun V g => P V g, downward_closed := fun hg k => hP _ _ _ k hg }
  refine ⟨S, Scheme.zariskiTopology_le_etaleTopology _ ?_, fun V g hg => hg⟩
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨U.openCoverOfIsOpenCover (fun x => U.basicOpen (s x)) ?_, ?_⟩
  · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hs x⟩
  · rintro V g ⟨x⟩
    exact hPs x

theorem prim_root_loc : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther := by
  intro q _ U ζ ξ
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  refine loc_of_points _ ?_ fun x => ?_
  · rintro V W g k ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_pow]
  · obtain ⟨a, s, hs, hd⟩ := alg_prim_pow q hq ζ.1 ξ.1 ζ.2.2 ξ.2.2 (U.Γevaluation x).hom
    refine ⟨s, (U.evaluation_ne_zero_iff_mem_basicOpen x (show x ∈ (⊤ : U.Opens) from trivial) s).1 hs, a, ?_⟩
    have hu : IsUnit ((U.basicOpen s).ι.appTop.hom s) := unit_res s _ _ (by simp)
    have h0 := congrArg (U.basicOpen s).ι.appTop.hom hd
    rw [map_mul, map_zero, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_restriction_and_root_change_holds : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers LateralTheory.EtaleFoundations.GenIsoSurjRootPf.prim_root_loc
end
end

section -- merged from Development.EtaleCohomology.TateTwists.TwpairTensUnivExdegPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExDeg

variable {R : Type} [CommRing R]

noncomputable def tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) :
    Tens I J V w →ₗ[ULift.{1} R] Tens I' J' V w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op V)).hom ((g.f p.1.2).hom.app (op V)).hom

theorem lift_res {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (k : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res k w x) = Sec.res k (τ.lift U w x) := by
  classical
  have key : τ.lift V w ∘ₗ Tens.res k w = ((K.X w).obj.map k.op).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (τ.nat k p.1.1 p.1.2 w p.2 a b).symm
  exact congrArg (fun m => m x) key

theorem lam_res {I J I' J' K : Cx R} (ν : Pair I' J' K) (f : I ⟶ I') (g : J ⟶ J') {V U : Scheme.{0}} (k : V ⟶ U)
    (w : ℤ) (x : Tens I J U w) :
    ν.lift V w (tmap f g V w (Tens.res k w x)) = Sec.res k (ν.lift U w (tmap f g U w x)) := by
  classical
  have key : (ν.lift V w ∘ₗ tmap f g V w) ∘ₗ Tens.res k w =
      ((K.X w).obj.map k.op).hom ∘ₗ (ν.lift U w ∘ₗ tmap f g U w) := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e := ν.nat k p.1.1 p.1.2 w p.2 (Sec.map (f.f p.1.1) a) (Sec.map (g.f p.1.2) b)
    rw [secmap_res, secmap_res] at e
    exact e.symm
  exact congrArg (fun m => m x) key

theorem lam_zero {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) (hx : τ.lift V w x = 0) :
    ν.lift V w (tmap f g V w x) = 0 := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) V
  refine TensLocbij.loc_mono (hτ.2 V w x hx) ?_
  intro W k hk
  rw [← lam_res, hk, map_zero, map_zero]
  exact (map_zero _).symm

theorem lam_eq {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x x' : Tens I J V w) (hx : τ.lift V w x = τ.lift V w x') :
    ν.lift V w (tmap f g V w x) = ν.lift V w (tmap f g V w x') := by
  have := lam_zero τ hτ ν f g V w (x - x') (by rw [map_sub, hx, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at this
  exact this

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sheafT (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property)

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y :=
  (TensLocbij.map_comp_apply' R F.obj k g y).symm

def sv {I J K : Cx R} (τ : Pair I J K) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sieve U where
  arrows V g := ∃ x, τ.lift V w x = Sec.res g y
  downward_closed := by
    rintro V W g ⟨x, hx⟩ k
    exact ⟨Tens.res k w x, by rw [lift_res, hx, res_comp]⟩

theorem sv_cov {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    sv τ w y ∈ Scheme.etaleTopology.{0} U := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  exact Scheme.etaleTopology.superset_covering (fun V g hg => hP V g hg) hS

noncomputable def fam {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Presieve.FamilyOfElements ((K'.X w).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (sv τ w y).arrows :=
  fun V _ hk => (ν.lift V w (tmap f g V w hk.choose) : Sec (K'.X w) V)

theorem fam_compat {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    (fam τ ν f g w y).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ heq
  show Sec.res g₁ (ν.lift Y₁ w (tmap f g Y₁ w h₁.choose)) = Sec.res g₂ (ν.lift Y₂ w (tmap f g Y₂ w h₂.choose))
  rw [← lam_res, ← lam_res]
  apply lam_eq τ hτ
  rw [lift_res, lift_res, h₁.choose_spec, h₂.choose_spec, res_comp, res_comp, heq]

noncomputable def glue {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sec (K'.X w) U :=
  (sheafT (K'.X w) _ (sv_cov τ hτ w y)).amalgamate _ (fam_compat τ hτ ν f g w y)

theorem glue_spec {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) {V : Scheme.{0}} (k : V ⟶ U)
    (x : Tens I J V w) (hx : τ.lift V w x = Sec.res k y) :
    Sec.res k (glue τ hτ ν f g w y) = ν.lift V w (tmap f g V w x) := by
  have hk : (sv τ w y).arrows k := ⟨x, hx⟩
  have := (sheafT (K'.X w) _ (sv_cov τ hτ w y)).valid_glue (fam_compat τ hτ ν f g w y) k hk
  refine this.trans ?_
  show ν.lift V w (tmap f g V w hk.choose) = _
  exact lam_eq τ hτ ν f g V w _ _ (hk.choose_spec.trans hx.symm)

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sv_loc {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Loc U fun V k => (sv τ w y).arrows k :=
  ⟨sv τ w y, sv_cov τ hτ w y, fun _ _ h => h⟩

theorem glue_add {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y₁ y₂ : Sec (K.X w) U) :
    glue τ hτ ν f g w (y₁ + y₂) = glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂ := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (TensLocbij.loc_and (sv_loc τ hτ w y₁) (sv_loc τ hτ w y₂)) ?_
  rintro V k ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  rw [glue_spec τ hτ ν f g w _ k (x₁ + x₂) (by rw [map_add (f := _), hx₁, hx₂]; exact (map_add _ _ _).symm)]
  have e : Sec.res k (glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂) =
      Sec.res k (glue τ hτ ν f g w y₁) + Sec.res k (glue τ hτ ν f g w y₂) := map_add _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x₁ hx₁, glue_spec τ hτ ν f g w _ k x₂ hx₂, map_add (f := _), map_add (f := _)]

theorem glue_smul {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (c : ULift.{1} R) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (c • y) = c • glue τ hτ ν f g w y := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (sv_loc τ hτ w y) ?_
  rintro V k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k (c • x) (by rw [map_smul, hx]; exact (map_smul _ _ _).symm)]
  have e : Sec.res k (c • glue τ hτ ν f g w y) = c • Sec.res k (glue τ hτ ν f g w y) := map_smul _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x hx, map_smul, map_smul]

theorem glue_res {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U U' : Scheme.{0}} (w : ℤ) (h : U' ⟶ U) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (Sec.res h y) = Sec.res h (glue τ hτ ν f g w y) := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U'
  refine TensLocbij.loc_mono (sv_loc τ hτ w (Sec.res h y)) ?_
  rintro _ k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k x hx, res_comp]
  rw [res_comp] at hx
  rw [glue_spec τ hτ ν f g w _ (k ≫ h) x hx]

noncomputable def phi {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : K.X w ⟶ K'.X w :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun y => glue τ hτ ν f g w (U := U.unop) y
          map_add' := fun y₁ y₂ => glue_add τ hτ ν f g w y₁ y₂
          map_smul' := fun c y => glue_smul τ hτ ν f g w c y }
     naturality := by
       intro U U' h
       ext y
       exact glue_res τ hτ ν f g w h.unop y }⟩

theorem res_id {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.res (𝟙 U) y = y := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations.ExDeg

open LateralTheory.EtaleFoundations.ExDeg in
theorem LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg_of : LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  refine ⟨ExDeg.phi τ hτ ν f g w, ?_⟩
  intro U s t h a b
  classical
  have hx : τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      Sec.res (𝟙 U) (τ.mul U s t w h a b) := by
    rw [res_id]
    simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  have e := glue_spec τ hτ ν f g w _ (𝟙 U) _ hx
  rw [res_id] at e
  refine e.trans ?_
  simp only [tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof,
    TensorProduct.lift.tmul]
end

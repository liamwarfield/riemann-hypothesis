module

public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafLocalizationPropertiesOfComponents
section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafSectionsEqOfLocallyEq
section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafificationSectionsLocallyFromPresheaf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf : Prop :=
  ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ShfLocPf

theorem etale_sheaf_sections_eq_of_locally_eq : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  intro R _ P
  refine ⟨?_, ?_, ?_⟩
  · intro U y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    intro V g hg
    obtain ⟨t, ht⟩ := hg
    exact ⟨t, ht⟩
  · intro U x hx
    have h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x =
        ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by rw [hx, map_zero]
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]
  · intro F φ
    refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology φ F.property), ?_, ?_⟩
    · exact toSheafify_sheafifyLift Scheme.etaleTopology φ F.property
    · intro ψ hψ
      ext1
      exact sheafifyLift_unique Scheme.etaleTopology φ F.property ψ.hom hψ

end LateralTheory.EtaleFoundations.ShfLocPf
end

namespace LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
theorem etale_sheaf_localization_properties_of_components : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  apply LateralTheory.EtaleFoundations.ShfLocPf.etale_sheaf_sections_eq_of_locally_eq
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := etale_sheaf_localization_properties_of_components
end LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
end

section -- merged from Development.EtaleCohomology.TateTwists.TwFGenInjPf
section -- merged from Development.EtaleCohomology.TateTwists.GenConnPf
section -- merged from Development.EtaleCohomology.TateTwists.OfRingsLocalSectionsHolds
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.OfRingsLoc
variable {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))

instance li : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [CommRing R] in
theorem ι_comp_apply {X U : Scheme.{0}} (f : X ⟶ U) (W : X.Opens) (y : X) (h : y ∈ W) :
    (Scheme.Opens.ι W ≫ f) ⟨y, h⟩ = f y :=
  rfl


omit [CommRing R] in
theorem cov_pt {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S.arrows j := by
  obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := (𝒰.X i).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : IsAffine W := hW
  have : Etale (𝒰.f i) := 𝒰.mem₀.2 ⟨i⟩
  refine ⟨W, Scheme.Opens.ι W ≫ 𝒰.f i, ⟨y, hyW⟩, inferInstance, inferInstance, ?_, ?_⟩
  · exact (ι_comp_apply (𝒰.f i) W y hyW).trans hy
  · exact S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) (Scheme.Opens.ι W)

theorem loc_inj {U : Scheme.{0}} (m : M.obj Γ(U, ⊤)) (hm : ofRings.sec M U m = 0) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0 := by
  have h0 : ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) m =
      ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) 0 := by
    rw [map_zero]; exact hm
  obtain ⟨V, j, v, hV, hj, hv, hS⟩ := cov_pt _
    (Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) m 0 h0) u
  refine ⟨V, j, v, hV, hj, hv, ?_⟩
  have h1 : ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) m =
      ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) 0 := hS
  rw [map_zero] at h1
  exact h1
end LateralTheory.EtaleFoundations.OfRingsLoc
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

def LateralTheory.EtaleFoundations.twF_gen_inj : Prop :=
  ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nontrivial B → ∀ (i : ℤ) (ζ : Prim q B),
    Function.Injective (fun c : ZMod q =>
      (c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj (CommRingCat.of B)) :
        (twF q i).obj (CommRingCat.of B)))

namespace LateralTheory.EtaleFoundations.GenConn

theorem twF_map_mk {q : ℕ} (i : ℤ) {B C : CommRingCat.{0}} (f : B ⟶ C) (ζ : Prim q B) :
    ((twF q i).map f).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map f.hom) 1) := by
  show Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]

theorem inj_of (h : LateralTheory.EtaleFoundations.twF_gen_inj) (q : ℕ) [NeZero q] (U : Scheme.{0}) [Nonempty U] (i : ℤ)
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (fun c : ZMod q => c.val • twGen i ζ) := by
  intro c1 c2 hc
  simp only at hc
  let φ := ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom
  let m : (Scheme.Γ ⋙ twF q i).obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have hsec : φ (c1.val • m - c2.val • m) = 0 := by
    rw [map_sub, map_nsmul, map_nsmul]; exact sub_eq_zero.2 hc
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  have hloc : ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ Etale j ∧ j v = u ∧
        ((twF q i).map j.appTop).hom (c1.val • m - c2.val • m) = 0 := by
    have h0 : φ (c1.val • m - c2.val • m) = φ 0 := by
      rw [map_zero]; exact hsec
    obtain ⟨V, j, v, hV, hj, hv, hS⟩ := LateralTheory.EtaleFoundations.OfRingsLoc.cov_pt _
      (Presheaf.equalizerSieve_mem Scheme.etaleTopology
        (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) _ 0 h0) u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h1 : ConcreteCategory.hom ((Scheme.Γ ⋙ twF q i).map j.op) (c1.val • m - c2.val • m) =
        ConcreteCategory.hom ((Scheme.Γ ⋙ twF q i).map j.op) 0 := hS
    rw [map_zero] at h1
    exact h1
  obtain ⟨V, j, v, -, -, -, hV⟩ := hloc
  let ψ := ((twF q i).map j.appTop).hom
  have hV2 : ψ (c1.val • m) = ψ (c2.val • m) := sub_eq_zero.1 ((ψ.map_sub _ _).symm.trans hV)
  erw [map_nsmul, map_nsmul] at hV2
  have hm : ψ m = Submodule.Quotient.mk (Finsupp.single (ζ.map j.appTop.hom) 1) := twF_map_mk i j.appTop ζ
  rw [hm] at hV2
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := AlgebraicGeometry.Scheme.component_nontrivial V ⊤
  exact h q Γ(V, ⊤) inferInstance i (ζ.map j.appTop.hom) hV2

end LateralTheory.EtaleFoundations.GenConn
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwFInj

theorem prim_field {q : ℕ} {k : Type} [Field k] (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int] using h

theorem pow_mod_eq {k : Type} [Field k] {q : ℕ} {z : k} (hz : IsPrimitiveRoot z q) (n : ℕ) :
    z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

theorem unit_unique {k : Type} [Field k] {q : ℕ} [NeZero q] {z : k} (hz : IsPrimitiveRoot z q)
    {u v : (ZMod q)ˣ} (h : z ^ (u : ZMod q).val = z ^ (v : ZMod q).val) : u = v :=
  Units.ext (ZMod.val_injective _ (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_unit {k : Type} [Field k] {q : ℕ} [NeZero q] {z x : k} (hz : IsPrimitiveRoot z q)
    (hx : IsPrimitiveRoot x q) : ∃ u : (ZMod q)ˣ, x = z ^ (u : ZMod q).val := by
  obtain ⟨j, hj, hjx⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : j.Coprime q := (hz.pow_iff_coprime (NeZero.pos q) j).1 (hjx ▸ hx)
  refine ⟨ZMod.unitOfCoprime j hc, ?_⟩
  rw [← hjx]
  congr 1
  simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

end LateralTheory.EtaleFoundations.TwFInj

namespace LateralTheory.EtaleFoundations.TwFInj

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] {k : Type} [Field k] (π : B →+* k) {z : k}
  (hz : IsPrimitiveRoot z q)

noncomputable def ex (ξ : Prim q B) : (ZMod q)ˣ := Classical.choose (exists_unit hz (prim_field (ξ.map π)))

theorem ex_spec (ξ : Prim q B) : π ξ.1 = z ^ (ex π hz ξ : ZMod q).val :=
  Classical.choose_spec (exists_unit hz (prim_field (ξ.map π)))

theorem ex_rel {ζ ξ : Prim q B} {a : (ZMod q)ˣ} (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ex π hz ξ = ex π hz ζ * a := by
  apply unit_unique hz
  rw [← ex_spec, h, map_pow, ex_spec π hz ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_mod_eq hz]

noncomputable def L (i : ℤ) : (Prim q B →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ => ULift.up (((ex π hz ξ) ^ i : (ZMod q)ˣ) : ZMod q))

theorem twRel_le_ker (i : ℤ) : twRel q i B ≤ LinearMap.ker (L π hz i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
  apply ULift.ext
  simp [ex_rel π hz h, mul_zpow, mul_comm]

end LateralTheory.EtaleFoundations.TwFInj

theorem LateralTheory.EtaleFoundations.twF_gen_inj_of : LateralTheory.EtaleFoundations.twF_gen_inj := by
  intro q _ B _ hB i ζ c1 c2 hc
  simp only at hc
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  have hz := LateralTheory.EtaleFoundations.TwFInj.prim_field (ζ.map π)
  let Φ := Submodule.liftQ _ (LateralTheory.EtaleFoundations.TwFInj.L π hz i) (LateralTheory.EtaleFoundations.TwFInj.twRel_le_ker π hz i)
  have h2 := congrArg Φ hc
  simp only [Φ, map_nsmul, Submodule.liftQ_apply, LateralTheory.EtaleFoundations.TwFInj.L, Finsupp.linearCombination_single, one_smul] at h2
  have h3 := congrArg ULift.down h2
  have h4 : (c1.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) =
      (c2.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) := by
    simp only [nsmul_eq_mul] at h3
    exact h3
  simpa [ZMod.natCast_zmod_val] using (Units.mul_left_inj _).1 h4
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCutTw

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : M.obj Γ(U, ⊤)) : Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)).symm

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem twF_loc (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun _ h => ∃ c : ℕ, Sec.res h (ofRings.sec (twF q i) V x) = c • twGen i (ζ.map h.appTop.hom) := by
  have L := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  have hZ := (etale_locally_roots_of_unity_structure_of_exists_and_kummer etale_locally_exists_primitive_root_of_unity_of_invertible_order etale_locally_kummer_roots_of_units_of_invertible_order q V).2.1
  have key : Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    induction f using Finsupp.induction with
    | zero =>
      refine L.1 V _ fun W h => ⟨0, ?_⟩
      rw [zero_smul, Submodule.Quotient.mk_zero]
      exact map_zero ((twF q i).map h.appTop).hom
    | single_add ξ b g _ _ ih =>
      refine L.2.1 V _ _ (L.2.2.1 V _ _ (hZ ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
        ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
      rw [Submodule.Quotient.mk_add]
      refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
      rw [hc, twF_map_mk, Finsupp.mapDomain_single,
        twF_single_pow q i _ (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha b, add_smul]
      rfl
  refine L.2.1 V _ _ key fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  rw [sec_res, hc]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

theorem loc_surj (q : ℕ) (i : ℤ) (U : Scheme.{0}) (y : Sec (tw q i) U) :
    Loc U fun V g => ∃ x : (twF q i).obj Γ(V, ⊤), ofRings.sec (twF q i) V x = Sec.res g y :=
  (LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf.intersectionNumber_baseChange (ZMod q) (Scheme.Γ ⋙ twF q i)).1 U y

section Lift
variable {q : ℕ} [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U)
  (hn : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
  (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
    e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ)

def liftL (U : Scheme.{0}) : ((Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)) →ₗ[ULift.{1} (ZMod q)] Sec M U :=
  Submodule.liftQ _ (Finsupp.linearCombination _ (e U)) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    change Finsupp.linearCombination _ (e U) _ = 0
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, hr U ζ ξ a h,
      ulift_smul_eq_nsmul, sub_self])

def liftP : Scheme.Γ ⋙ twF q i ⟶ M.obj where
  app U := ModuleCat.ofHom (liftL i M e hr U.unop)
  naturality U V g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_))
    revert ζ
    intro (ζ : Prim q Γ(U.unop, ⊤))
    change Finsupp.linearCombination _ (e V.unop) (Finsupp.mapDomain (Prim.map g.unop.appTop.hom) (Finsupp.single ζ b)) =
      Sec.res g.unop (Finsupp.linearCombination _ (e U.unop) (Finsupp.single ζ b))
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single, ← hn]
    exact (map_smul _ _ _).symm

include hn hr in
theorem lift_ex : ∃ φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (liftP i M e hn hr) M.property), fun U ζ => ?_⟩
  have key := congrArg (fun η => (η.app (op U)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (liftP i M e hn hr) M.property)
  refine key.trans ?_
  change Finsupp.linearCombination _ (e U) (Finsupp.single ζ 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

end Lift

theorem twSec : EtaleTateTwistSectionsLocallyGenerated := by
  intro q _ i
  have L := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  refine ⟨fun U y => ?_, fun U ζ y => ?_, fun U _ ζ c hc => ?_, fun V U g ζ => ?_, fun U ζ ξ a h => ?_,
    fun M e hn hr => ?_⟩
  · refine L.2.2.2.2.1 U _ (L.2.1 U _ _ (loc_surj q i U y) fun V g ⟨x, hx⟩ => ?_)
    by_cases hne : Nonempty (Prim q Γ(V, ⊤))
    · obtain ⟨ζ⟩ := hne
      refine L.2.1 V _ _ (twF_loc q i V ζ x) fun W h ⟨c, hc⟩ => Or.inr ⟨ζ.map h.appTop.hom, c, ?_⟩
      rw [res_comp, ← hx]
      exact hc
    · refine L.1 V _ fun W h => Or.inl ?_
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have hf : f = 0 := Finsupp.ext fun ζ => absurd ⟨ζ⟩ hne
      have h0 : Sec.res g y = 0 := by
        rw [← hx, hf, Submodule.Quotient.mk_zero]
        unfold ofRings.sec
        exact map_zero _
      rw [res_comp, h0]
      exact map_zero _
  · refine L.2.2.2.2.1 U _ (L.2.1 U _ _ (loc_surj q i U y) fun V g ⟨x, hx⟩ => ?_)
    refine L.2.1 V _ _ (twF_loc q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
    have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
      apply Subtype.ext
      simp [Prim.map]
      rfl
    rw [res_comp, ← hx, ← hp]
    exact hc
  · have h1 : ((c : ZMod q).val • twGen i ζ) = c • twGen i ζ := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) c, ulift_smul_eq_nsmul]
      rfl
    have := GenConn.inj_of twF_gen_inj_of q U i ζ (a₁ := (c : ZMod q)) (a₂ := 0) (by
      simp only [h1, hc, ZMod.val_zero, zero_smul])
    exact (ZMod.natCast_eq_zero_iff c q).1 this
  · refine (sec_res (twF q i) g _).trans ?_
    rw [twF_map_mk, Finsupp.mapDomain_single]
    rfl
  · unfold twGen
    have := twF_single_pow q i Γ(U, ⊤) ζ ξ a h 1
    rw [ULift.one_down, one_mul] at this
    refine (congrArg (ofRings.sec (twF q i) U) this).trans ?_
    unfold ofRings.sec
    exact map_nsmul _ _ _
  · obtain ⟨φ, hφ⟩ := lift_ex i M e hn hr
    exact ⟨φ, hφ, fun ψ hψ => TwResExt.twuniq_pf q i M ψ φ fun U ζ => (hψ U ζ).trans (hφ U ζ).symm⟩

end LateralTheory.CohomologicalPurity.LeafAWCutTw

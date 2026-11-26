module

public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
public import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafNormalModelPf

def intCl (Ω : Type) {L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : Subalgebra Ω L :=
  (integralClosure (Algebra.adjoin Ω {u}) L).restrictScalars Ω

theorem intCl_subset {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) (hu : u ∈ V) : (intCl Ω u : Set L) ⊆ V := by
  intro x hx
  let V' : Subalgebra Ω L := { V.toSubring with algebraMap_mem' := hΩ }
  have hle : Algebra.adjoin Ω {u} ≤ V' := Algebra.adjoin_le (Set.singleton_subset_iff.2 hu)
  obtain ⟨p, hp, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  let f : Algebra.adjoin Ω {u} →+* V :=
    { toFun := fun y => ⟨y.1, hle y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hint : IsIntegral V x := ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hpx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).1 hint
  exact y.2

theorem valuation_covers {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) : (intCl Ω u : Set L) ⊆ V ∨ (intCl Ω u⁻¹ : Set L) ⊆ V := by
  rcases V.mem_or_inv_mem u with h | h
  · exact Or.inl (intCl_subset V hΩ h)
  · exact Or.inr (intCl_subset V hΩ h)

theorem transcendental_inv {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : Transcendental Ω u⁻¹ := by
  intro h
  apply hu
  simpa using h.inv

theorem adjoin_inv_eq {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) :
    IntermediateField.adjoin Ω {u⁻¹} = IntermediateField.adjoin Ω {u} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self Ω u)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self Ω u⁻¹)

theorem ne_zero_of_transcendental {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : u ≠ 0 := by
  rintro rfl
  exact hu isAlgebraic_zero

theorem self_mem_intCl {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : u ∈ intCl Ω u :=
  isIntegral_algebraMap (x := (⟨u, Algebra.subset_adjoin (Set.mem_singleton u)⟩ : Algebra.adjoin Ω {u}))

def LeafIntClosureAlg : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.FiniteType Ω (intCl Ω u) ∧ IsIntegrallyClosed (intCl Ω u) ∧ ringKrullDim (intCl Ω u) = 1 ∧
      IsFractionRing (intCl Ω u) L

def LeafIntClosureLoc : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u})

def LeafGlueProper : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L),
  u ≠ 0 → u ∈ A → u⁻¹ ∈ B → Algebra.FiniteType Ω A → Algebra.FiniteType Ω B →
  IsIntegrallyClosed A → IsIntegrallyClosed B → ringKrullDim A = 1 → ringKrullDim B = 1 →
  IsFractionRing A L → IsFractionRing B L →
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u}) →
  (∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) → (A : Set L) ⊆ V ∨ (B : Set L) ⊆ V) →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

theorem adjoin_le_of_shift {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0)
    (h : ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹) :
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) ≤ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (hx | hx)
  · obtain ⟨n, hn⟩ := h x hx
    have : x = x * u⁻¹ ^ n * u ^ n := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
    rw [this]
    have h1 : x * u⁻¹ ^ n ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_left _ hn)
    have h2 : u ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_right _ rfl)
    exact mul_mem h1 (pow_mem h2 n)
  · rw [Set.mem_singleton_iff.1 hx]
    exact Algebra.subset_adjoin (Set.mem_union_left _ (self_mem_intCl u⁻¹))

def LeafIntShift : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L), u ≠ 0 →
  ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹

theorem LeafIntClosureLoc_of (h : LeafIntShift) : LeafIntClosureLoc := by
  intro Ω L _ _ _ u hu _
  have hu0 := ne_zero_of_transcendental hu
  apply le_antisymm (adjoin_le_of_shift hu0 (h Ω L u hu0))
  have h' := adjoin_le_of_shift (inv_ne_zero hu0) (by simpa using h Ω L u⁻¹ (inv_ne_zero hu0))
  simpa using h'

theorem shift_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0) (c : L)
    (hc : c ∈ Algebra.adjoin Ω {u}) : ∃ N : ℕ, ∀ m, N ≤ m → c * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} := by
  have hinv : u⁻¹ ∈ Algebra.adjoin Ω {u⁻¹} := Algebra.subset_adjoin (Set.mem_singleton _)
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    exact pow_mem hinv k
  | algebraMap a =>
    exact ⟨0, fun m _ => mul_mem (Subalgebra.algebraMap_mem _ a) (pow_mem hinv m)⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨max N1 N2, fun m hm => ?_⟩
    rw [add_mul]
    exact add_mem (h1 m (le_trans (le_max_left _ _) hm)) (h2 m (le_trans (le_max_right _ _) hm))
  | mul x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨N1 + N2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : x * y * u⁻¹ ^ (N1 + N2 + k) = (x * u⁻¹ ^ N1) * (y * u⁻¹ ^ (N2 + k)) := by ring
    rw [this]
    exact mul_mem (h1 N1 le_rfl) (h2 _ (Nat.le_add_right _ _))

theorem integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure : LeafIntShift := by
  intro Ω L _ _ _ u hu x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  have hN : ∀ c : Algebra.adjoin Ω {u}, ∃ N : ℕ, ∀ m, N ≤ m → (c : L) * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} :=
    fun c => shift_mem hu c c.2
  choose Nf hNf using hN
  set p' := p.map (algebraMap (Algebra.adjoin Ω {u}) L) with hp'
  have hpm' : p'.Monic := hpm.map _
  have hdeg : p'.natDegree = p.natDegree := hpm.natDegree_map _
  set N := (Finset.range (p.natDegree + 1)).sup (fun i => Nf (p.coeff i)) with hNdef
  set r : L := u⁻¹ ^ N
  refine ⟨N, ?_⟩
  show IsIntegral (Algebra.adjoin Ω {u⁻¹}) (x * u⁻¹ ^ N)
  have hroot : (p'.scaleRoots r).eval (r * x) = 0 := by
    have h0 : p'.eval₂ (RingHom.id L) x = 0 := by
      rw [hp', Polynomial.eval₂_map]; exact hpx
    have h := Polynomial.scaleRoots_eval₂_mul (p := p') (RingHom.id L) x r
    rw [h0, mul_zero] at h
    exact h
  have hmon : (p'.scaleRoots r).Monic := (Polynomial.monic_scaleRoots_iff r).2 hpm'
  have hlift : p'.scaleRoots r ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {u⁻¹}) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots, hp', Polynomial.coeff_map]
    rcases lt_or_ge i p.natDegree with hi | hi
    · have hle : Nf (p.coeff i) ≤ N * (p'.natDegree - i) := by
        have h1 : Nf (p.coeff i) ≤ N :=
          Finset.le_sup (f := fun i => Nf (p.coeff i)) (Finset.mem_range.2 (by omega))
        have h2 : 1 ≤ p'.natDegree - i := by omega
        nlinarith
      have := hNf (p.coeff i) _ hle
      rw [← pow_mul] at *
      exact ⟨⟨_, this⟩, rfl⟩
    · have he : p'.natDegree - i = 0 := by omega
      rw [he, pow_zero, mul_one]
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hpm.coeff_natDegree, map_one]; exact ⟨1, map_one _⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, mul_comm]
  exact hroot

theorem LeafNormalModel_of (hA : LeafIntClosureAlg) (hC : LeafGlueProper) :
    LateralTheory.E.LeafModelCurveCut.ExistsNormalProperCurveModel := by
  intro Ω L _ _ _ u hu hfin
  have hu' := transcendental_inv hu
  have hfin' : FiniteDimensional (IntermediateField.adjoin Ω {u⁻¹}) L := by
    rw [adjoin_inv_eq (Ω := Ω) u]; exact hfin
  obtain ⟨a1, a2, a3, a4⟩ := hA Ω L u hu hfin
  obtain ⟨b1, b2, b3, b4⟩ := hA Ω L u⁻¹ hu' hfin'
  exact hC Ω L (intCl Ω u) (intCl Ω u⁻¹) u (ne_zero_of_transcendental hu) (self_mem_intCl u)
    (self_mem_intCl u⁻¹) a1 b1 a2 b2 a3 b3 a4 b4
    (LeafIntClosureLoc_of integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure Ω L u hu hfin) (fun V hΩ => valuation_covers u V hΩ)

end LateralTheory.E.LeafNormalModelPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AugBijPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.AugBijPf

def Sep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (T : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T),
  (∀ i, Etale (g i)) → (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) →
  ∀ x y : Sec F T, (∀ i, Sec.res (g i) x = Sec.res (g i) y) → x = y

def Glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (T : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T),
  (∀ i, Etale (g i)) → (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) →
  ∀ x : ∀ i, Sec F (V i), (∀ i j, Sec.res (pullback.fst (g i) (g j)) (x i) = Sec.res (pullback.snd (g i) (g j)) (x j)) →
  ∃ y : Sec F T, ∀ i, Sec.res (g i) y = x i

def LocSurj : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → ∀ f : LocallyConstant T (ZMod q),
  ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧ (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧
    ∀ i, ∃ y : Sec (tw q 0) (V i), φ (V i) y = f.comap (g i).base.hom

def LocInj : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → ∀ x : Sec (tw q 0) T, φ T x = 0 →
  ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧ (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧
    ∀ i, Sec.res (g i) x = 0

theorem unit_res {q : ℕ} {V T : Scheme.{0}} (g : V ⟶ T) (h : IsUnit (q : Γ(T, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res f (Sec.res g x) = Sec.res (f ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sheafFor {R : Type} [CommRing R] (F : Shv R) {T : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (g : ∀ i, V i ⟶ T)
    (he : ∀ i, Etale (g i)) (hs : ∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) :
    (Presieve.ofArrows V g).IsSheafFor (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  refine Presieve.IsSheaf.isSheafFor_of_mem_precoverage (J := Scheme.precoverage @Etale) h2 ?_
  exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => by obtain ⟨i, v, hv⟩ := hs x; exact ⟨i, v, hv⟩, he⟩

theorem Sep_holds : Sep := by
  intro R _ F T ι V g he hs x y hxy
  have h := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).1 (sheafFor F g he hs) (fun i => Sec.res (g i) y) (by
    intro i j
    change Sec.res _ (Sec.res _ y) = Sec.res _ (Sec.res _ y)
    rw [res_comp, res_comp, pullback.condition])
  exact h.unique (fun i => hxy i) (fun i => rfl)

theorem Glue_holds : Glue := by
  intro R _ F T ι V g he hs x hx
  obtain ⟨y, hy, -⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).1 (sheafFor F g he hs) x hx
  exact ⟨y, hy⟩

def Root : Prop := ∀ (q : ℕ) (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ (W : Scheme.{0}) (h : W ⟶ U), Etale h ∧ (∀ u : U, ∃ w : W, h.base w = u) ∧ Nonempty (Prim q Γ(W, ⊤))

theorem LocSurj_of (hR : Root) : LocSurj := by
  intro q φ hnat hgen T hT f
  let O : ZMod q → T.Opens := fun c => ⟨{t | f t = c}, f.isLocallyConstant.isOpen_fiber c⟩
  choose W h he hs hζ using fun c => hR q (O c) (unit_res (O c).ι hT)
  refine ⟨ZMod q, W, fun c => h c ≫ (O c).ι, fun c => by haveI := he c; infer_instance, ?_, ?_⟩
  · intro t
    have ht : t ∈ Set.range (O (f t)).ι.base := by rw [Scheme.Opens.range_ι]; exact (rfl : f t = f t)
    obtain ⟨u, hu⟩ := ht
    obtain ⟨w, hw⟩ := hs (f t) u
    exact ⟨f t, w, by rw [Scheme.Hom.comp_apply, hw, hu]⟩
  · intro c
    refine ⟨((c.cast : ℤ)) • twGen 0 (hζ c).some, ?_⟩
    rw [map_zsmul, hgen]
    ext w
    have hm : ((O c).ι.base (h c w)) ∈ O c := by
      have hr : ((O c).ι.base (h c w)) ∈ Set.range (O c).ι.base := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at hr; exact hr
    have hm' : f ((O c).ι.base (h c w)) = c := hm
    have e1 : ((c.cast : ℤ) • (1 : LocallyConstant (W c) (ZMod q))) w = c := by
      change (c.cast : ℤ) • (1 : ZMod q) = c
      rw [zsmul_eq_mul, mul_one, ZMod.intCast_cast, ZMod.cast_id', id_eq]
    rw [e1, LocallyConstant.coe_comap, Function.comp_apply]
    erw [Scheme.Hom.comp_apply]
    exact hm'.symm

theorem AugBij_of_loc (hS : Sep) (hG : Glue) (hSu : LocSurj) (hI : LocInj) : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij := by
  intro q φ hnat hgen
  have inj : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Injective (φ T) := by
    intro T hT
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨ι, V, g, he, hs, h0⟩ := hI q φ hnat hgen T hT x hx
    exact hS _ _ T ι V g he hs x 0 (fun i => by rw [h0 i]; exact (map_zero ((tw q 0).obj.map (g i).op).hom).symm)
  intro T hT
  refine ⟨inj T hT, fun f => ?_⟩
  obtain ⟨ι, V, g, he, hs, hy⟩ := hSu q φ hnat hgen T hT f
  choose y hy using hy
  obtain ⟨z, hz⟩ := hG _ _ T ι V g he hs y (fun i j => by
    apply inj _ (unit_res (pullback.fst (g i) (g j) ≫ g i) hT)
    rw [hnat, hnat, hy i, hy j]
    ext t
    simp only [LocallyConstant.coe_comap, Function.comp_apply]
    erw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rfl)
  refine ⟨z, ?_⟩
  ext t
  obtain ⟨i, v, rfl⟩ := hs t
  have := congrArg (fun k : LocallyConstant (V i) (ZMod q) => k v) ((hnat (g i) z).symm.trans ((congrArg (φ (V i)) (hz i)).trans (hy i)))
  simpa using this

def SecLoc : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (T : Scheme.{0})
  (x : Sec (ofRings R M) T), ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧
    (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧ ∀ i, ∃ a : M.obj Γ(V i, ⊤), Sec.res (g i) x = ofRings.sec M (V i) a

def GenEq : Prop := ∀ (q : ℕ) (U : Scheme.{0}) (ξ ζ : Prim q Γ(U, ⊤)), twGen 0 ξ = twGen 0 ζ

theorem secEq (hE : GenEq) {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : (twF q 0).obj Γ(U, ⊤)) :
    ∃ m : ℤ, ofRings.sec (twF q 0) U a = m • twGen 0 ζ := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨0, by rw [zero_smul]; exact map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom⟩
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    rw [add_smul, ← hm, ← hn, Submodule.Quotient.mk_add]
    exact map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom _ _
  | single ξ c =>
    refine ⟨(c.down.cast : ℤ), ?_⟩
    have h1 : Finsupp.single ξ c = c • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, Submodule.Quotient.mk_smul]
    have h2 : ofRings.sec (twF q 0) U (c • Submodule.Quotient.mk (Finsupp.single ξ 1)) =
        c • twGen 0 ξ := map_smul ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom _ _
    refine h2.trans ?_
    rw [hE q U ξ ζ, ← Int.cast_smul_eq_zsmul (ULift.{1} (ZMod q))]
    congr 1
    apply ULift.ext
    rw [ULift.down_intCast, ZMod.intCast_cast, ZMod.cast_id', id_eq]

theorem LocInj_of (hR : Root) (hL : SecLoc) (hE : GenEq) : LocInj := by
  intro q φ hnat hgen T hT x hx
  obtain ⟨W, h, he, hs, ⟨ζ⟩⟩ := hR q T hT
  obtain ⟨ι, V, g, hge, hgs, ha⟩ := hL (ZMod q) (twF q 0) W (Sec.res h x)
  choose a ha using ha
  refine ⟨{i // Nonempty (V i)}, fun i => V i.1, fun i => g i.1 ≫ h, fun i => by haveI := hge i.1; haveI := he; infer_instance,
    ?_, ?_⟩
  · intro t
    obtain ⟨w, rfl⟩ := hs t
    obtain ⟨i, v, rfl⟩ := hgs w
    exact ⟨⟨i, ⟨v⟩⟩, v, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨i, ⟨v⟩⟩
    obtain ⟨m, hm⟩ := secEq hE (ζ.map (g i).appTop.hom) (a i)
    have hx' : Sec.res (g i ≫ h) x = m • twGen 0 (ζ.map (g i).appTop.hom) :=
      (res_comp (g i) h x).symm.trans ((ha i).trans hm)
    have h0 : φ (V i) (Sec.res (g i ≫ h) x) = 0 := by rw [hnat, hx]; rfl
    rw [hx', map_zsmul, hgen] at h0
    have h3 : (m : ZMod q) = 0 := by
      have := congrArg (fun k : LocallyConstant (V i) (ZMod q) => k v) h0
      change m • (1 : ZMod q) = 0 at this
      rwa [zsmul_eq_mul, mul_one] at this
    show Sec.res (g i ≫ h) x = 0
    rw [hx', ← Int.cast_smul_eq_zsmul (ULift.{1} (ZMod q))]
    have h4 : ((m : ULift.{1} (ZMod q))) = 0 := by apply ULift.ext; simpa using h3
    rw [h4, zero_smul]

theorem secLoc' : SecLoc := by
  intro R _ M T x
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ M)) (U := Opposite.op T) x
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hmem
  have hc := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).1 𝒰.mem₀
  refine ⟨𝒰.I₀, 𝒰.X, 𝒰.f, hc.2, fun t => ?_, fun i => ?_⟩
  · obtain ⟨i, v, hv⟩ := hc.1 t; exact ⟨i, v, hv⟩
  · obtain ⟨a, ha⟩ := @h𝒰 _ (𝒰.f i) (by exact Presieve.ofArrows.mk i)
    exact ⟨a, ha.symm⟩

theorem twGen_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen 0 ζ) = twGen 0 (ζ.map g.appTop.hom) := by
  have h := congrArg (fun k => (ModuleCat.Hom.hom k) (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)).naturality g.op)
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ξ ζ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  apply (Submodule.Quotient.eq _).2
  apply Submodule.subset_span
  refine ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

def ZarPow : Prop := ∀ (q : ℕ) (U : Scheme.{0}) (ξ ζ : Prim q Γ(U, ⊤)) (u : U),
  ∃ (O : U.Opens) (a : (ZMod q)ˣ), u ∈ O ∧ (ξ.map O.ι.appTop.hom).1 = (ζ.map O.ι.appTop.hom).1 ^ (a : ZMod q).val

theorem GenEq_of (hZ : ZarPow) : GenEq := by
  intro q U ξ ζ
  choose O a hu ha using hZ q U ξ ζ
  refine Sep_holds (ZMod q) (tw q 0) U U (fun u => (O u : Scheme.{0})) (fun u => (O u).ι) (fun u => inferInstance) ?_ _ _ ?_
  · intro t
    have ht : t ∈ Set.range (O t).ι.base := by rw [Scheme.Opens.range_ι]; exact hu t
    obtain ⟨v, hv⟩ := ht
    exact ⟨t, v, hv⟩
  · intro u
    rw [twGen_res, twGen_res]
    exact twGen_eq_of_pow _ _ (a u) (ha u)

def LocPow : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (ξ ζ : Prim q A),
  ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val

theorem ZarPow_of (hL : LocPow) : ZarPow := by
  intro q U ξ ζ u
  obtain ⟨a, ha⟩ := hL q (U.presheaf.stalk u) (ξ.map (U.presheaf.germ ⊤ u trivial).hom) (ζ.map (U.presheaf.germ ⊤ u trivial).hom)
  have h : U.presheaf.germ ⊤ u trivial ξ.1 = U.presheaf.germ ⊤ u trivial (ζ.1 ^ (a : ZMod q).val) := by
    rw [map_pow]; exact ha
  obtain ⟨W, hW, i1, i2, he⟩ := U.presheaf.germ_eq (U := ⊤) (V := ⊤) u trivial trivial _ _ h
  refine ⟨W, a, hW, ?_⟩
  show (Scheme.Opens.ι (X := U) W).appTop.hom ξ.1 = ((Scheme.Opens.ι (X := U) W).appTop.hom ζ.1) ^ _
  rw [← map_pow, Scheme.Opens.ι_appTop]
  have hle : (Scheme.Opens.ι (X := U) W) ''ᵁ ⊤ ≤ W := by simp
  have := congrArg (U.presheaf.map (homOfLE hle).op).hom he
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp] at this
  exact (congrArg (fun k => (U.presheaf.map (Quiver.Hom.op k)).hom ξ.1) (Subsingleton.elim _ _)).trans
    (this.trans (congrArg (fun k => (U.presheaf.map (Quiver.Hom.op k)).hom (ζ.1 ^ (a : ZMod q).val)) (Subsingleton.elim _ _)))

end LateralTheory.E.AugBijPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafNegPf
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNegPf

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  change IsZero ((((chainsN R).obj E).extend ComplexShape.embeddingDownNat).X n)
  apply HomologicalComplex.isZero_extend_X
  intro i
  change -(i : ℤ) ≠ n
  omega

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) :
    IsZero ((res R F).X n) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

theorem cone_isZero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (p : ℤ) (hp : 0 < p) :
    IsZero ((mappingCone ((chains R).map f)).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply mappingCone.ext_from _ (p + 1) p rfl
  · exact (chains_isZero R U (p + 1) (by omega)).eq_of_src _ _
  · exact (chains_isZero R E p hp).eq_of_src _ _

theorem cochain_eq_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain (mappingCone ((chains R).map f)) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (res_isZero R F q hq).eq_of_tgt _ _
  · exact (cone_isZero R f p (by omega)).eq_of_src _ _

theorem LeafNeg_of : LateralTheory.E.LeafDegCut.LeafNeg := by
  intro R _ U E f F m hm
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  have hx : x = y := by
    ext1
    rw [cochain_eq_zero R f F m hm (x : Cochain _ _ m), cochain_eq_zero R f F m hm (y : Cochain _ _ m)]
  rw [hx]

end LateralTheory.E.LeafNegPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) :
    pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s := pullback.fst _ _

abbrev tY {Y B S : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) (t : S ⟶ U.left) : pullback p (t ≫ U.hom) ⟶ YU p U :=
  pullback.map p (t ≫ U.hom) p U.hom (𝟙 Y) t (𝟙 B) (by simp) (by simp)

abbrev tW {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) :
    pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (tY p U t) (𝟙 W) (𝟙 B) (by simp only [tY, pullback.lift_snd_assoc, Category.assoc]; erw [Category.comp_id]) (by simp)

abbrev rT (q : ℕ) (i : ℤ) {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) (m : ℤ) :=
  rpl q i (prU p ι U) (prS p ι (t ≫ U.hom)) (tW p ι U t) (tY p U t) (pullback.lift_fst _ _ _).symm m

def LeafKillPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → rT q i p ι U t m z = 0) →
  Cov U (fun _ a => rY q i p ι a m z = 0)

def LeafPtW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B), IsProper p → ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → ¬ (Set.range s ⊆ V) →
  ∀ m, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafPtV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y Y' : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B) (g : Y' ⟶ Y), IsProper p → IsProper (g ≫ p) → ∀ (U : B.Etale) (A : Type) [CommRing A]
  (t : Sp A ⟶ U.left), SH A → Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B) → ∀ (m : ℤ), pl q i (fibMap g p (t ≫ U.hom)) m = 0 →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, rT q i (g ≫ p) ι U t m (gY q i p g ι U m y) = 0

theorem LeafKill2_of (hPt : LeafKillPt) (hW : LeafPtW) (hV : LeafPtV) : LeafKill2 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 toK ι _ V hVW p g1 g2 hp hp1 hp2 hS U y
  refine hPt hH q k hq i toK ι (g1 ≫ p) hp1 U 2 _ ?_
  intro A _ t hA
  by_cases hc : Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B)
  · exact hV hH q k hq i toK ι V hVW p g1 hp hp1 U A t hA hc 2 (hS A (t ≫ U.hom) hA hc).2.1 y
  · have := hW hH q k hq i toK ι V hVW (g1 ≫ p) hp1 A (t ≫ U.hom) hA hc 2
    exact Subsingleton.elim _ _

end LateralTheory.E.SecondDegreeKilling
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FiltrationLevelInjectivity
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelInjectivity

def gN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') : cech (Spec.map u) ⟶ cech (Spec.map e) :=
  Arrow.mapCechNerve (f := Arrow.mk (yoneda.map (Spec.map u))) (g := Arrow.mk (yoneda.map (Spec.map e)))
    ⟨yoneda.map (Spec.map φ''), yoneda.map (Spec.map φ'), by
      simp only [Arrow.mk_hom, Functor.id_map, Functor.id_obj, Arrow.mk_left, Arrow.mk_right,
        ← Functor.map_comp, ← Spec.map_comp, h]⟩

def iN {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app _ := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro x y θ
    apply WidePullback.hom_ext
    · intro j
      erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, WidePullback.lift_π]
      exact Category.id_comp _
    · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, WidePullback.lift_base]
      exact Category.id_comp _

theorem iN_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : iN f ≫ cechAug f = sch.map f := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem iN_app_zero_iso {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((iN f).app (op ⦋0⦌)) := by
  refine ⟨⟨WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0, ?_, ?_⟩⟩
  · erw [WidePullback.lift_π]
  · apply WidePullback.hom_ext
    · intro j
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      erw [Category.assoc, WidePullback.lift_π, Category.id_comp]
      exact Category.comp_id _
    · erw [Category.assoc, WidePullback.lift_base, Category.id_comp]
      exact WidePullback.π_arrow _ _

theorem gN_aug {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    gN φ' e u φ'' h ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem gN_iN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    sch.map (Spec.map φ'') ≫ iN (Spec.map e) = iN (Spec.map u) ≫ gN φ' e u φ'' h := by
  have hw : yoneda.map (Spec.map φ'') ≫ yoneda.map (Spec.map e) = yoneda.map (Spec.map u) ≫ yoneda.map (Spec.map φ') := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h]
  refine NatTrans.ext (funext fun x => ?_)
  apply WidePullback.hom_ext
  · intro j
    erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, ← Category.assoc,
      WidePullback.lift_π, Category.id_comp]
    exact Category.comp_id _
  · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, ← Category.assoc,
      WidePullback.lift_base]
    exact hw

def Filt : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  (∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n → Function.Injective (pull R (disc.map (g.app (op ⦋p⦌))) F m) ∧
    Function.Surjective (pull R (disc.map (g.app (op ⦋p⦌))) F (m - 1))) →
  Function.Injective (rpull R g (disc.map h) b a comm F n)

def LvlRel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo : IsPushout φ' e u φ'',
  ∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n →
    Function.Injective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) m) ∧
    Function.Surjective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) (m - 1))

theorem LevelInj_of (hF : Filt) (hL : LvlRel) : LateralTheory.E.RelDescPf.LevelInj := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  refine ⟨gN φ' e u φ'' hpo'.w, gN_aug _ _ _ _ _, iN (Spec.map e), iN (Spec.map u), gN_iN _ _ _ _ _,
    iN_aug _, iN_aug _, ?_⟩
  exact hF hH (ZMod q) (tw q i) n (gN φ' e u φ'' hpo'.w) (yoneda.map (Spec.map φ'')) (iN (Spec.map e))
    (iN (Spec.map u)) (gN_iN _ _ _ _ _) (iN_app_zero_iso _) (iN_app_zero_iso _)
    (hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo')

end LateralTheory.E.FiltrationLevelInjectivity
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.TruncPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncPf

def TruncBij : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (n : ℤ),
  (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p)) → ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m)

def TruncData : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧ g ≫ f' = f ≫ h ∧
    (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p) ∧ IsIso (h.f p)) ∧
    (∀ p : ℤ, p < -(n + 1) → IsZero (K'.X p) ∧ IsZero (L'.X p))

variable (R : Type) [CommRing R] (F : Shv R)

theorem toHom_inj {K : Cx R} (m : ℤ) {x y : HK R K F m}
    (h : CohomologyClass.toHom x = CohomologyClass.toHom y) : x = y := by
  apply CohomologyClass.homAddEquiv.injective
  simpa only [CohomologyClass.homAddEquiv_apply] using h

theorem pull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (m : ℤ) (x : HK R M F m) :
    HK.pull R (f ≫ g) F m x = HK.pull R f F m (HK.pull R g F m x) := by
  apply toHom_inj
  simp only [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom, Functor.map_comp, Category.assoc]

theorem pull_id {K : Cx R} (m : ℤ) (x : HK R K F m) : HK.pull R (𝟙 K) F m x = x := by
  apply toHom_inj
  rw [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

theorem pull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (m : ℤ) : Function.Bijective (HK.pull R f F m) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨HK.pull R (inv f) F m y, ?_⟩⟩
  · have := congrArg (HK.pull R (inv f) F m) hxy
    simpa only [← pull_comp, IsIso.inv_hom_id, pull_id] using this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem subsingleton_of_isZero {K : Cx R} (hK : IsZero K) (m : ℤ) : Subsingleton (HK R K F m) := by
  constructor
  intro x y
  apply toHom_inj
  exact (Functor.map_isZero (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)) hK).eq_of_src _ _

theorem relK_of_isZero {K L : Cx R} (f : K ⟶ L) (n : ℤ) (hK : IsZero K) (hL : IsZero L) : RelK R F n f :=
  ⟨fun m _ _ => ⟨0, (subsingleton_of_isZero R F hK m).elim _ _⟩,
    fun _ _ _ => (subsingleton_of_isZero R F hL n).elim _ _⟩

theorem relK_of_square {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L')
    (w : g ≫ f' = f ≫ h) (n : ℤ)
    (hg : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m))
    (hh : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R h F m))
    (hf' : RelK R F n f') : RelK R F n f := by
  have key : ∀ (m : ℤ) (z : HK R L' F m),
      HK.pull R f F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f' F m z) := by
    intro m z
    rw [← pull_comp, ← pull_comp, w]
  refine ⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨y', rfl⟩ := (hg m (by omega)).2 y
    obtain ⟨z, rfl⟩ := hf'.1 m hm y'
    exact ⟨_, key m z⟩
  · obtain ⟨w1, rfl⟩ := (hh n le_rfl).2 x1
    obtain ⟨w2, rfl⟩ := (hh n le_rfl).2 x2
    rw [key, key] at hx
    rw [hf'.2 ((hg n le_rfl).1 hx)]

theorem piece_transfer {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L')
    (w : g ≫ f' = f ≫ h) (n : ℤ) (p : ℕ) (hg : IsIso (g.f (-(p : ℤ)))) (hh : IsIso (h.f (-(p : ℤ))))
    (hp : RelK R F n (pieceC R f p)) : RelK R F n (pieceC R f' p) := by
  refine relK_of_square R F (pieceC R f' p) (pieceC R f p)
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (g.f _)))
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (h.f _))) ?_ n
    (fun m _ => pull_bij_of_iso R F _ m) (fun m _ => pull_bij_of_iso R F _ m) hp
  simp only [pieceC, ← Functor.map_comp]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ (-(p : ℤ))) w
  simp only [HomologicalComplex.comp_f] at this
  exact this.symm

end LateralTheory.E.TruncPf

open LateralTheory.E.TruncPf in
theorem LateralTheory.E.TruncPf.Trunc_of (hB : TruncBij) (hD : TruncData) : LateralTheory.E.FiltPf.Trunc := by
  intro R _ F K L f n hz
  obtain ⟨P, K', L', f', g, h, hb, w, hiso, hzero⟩ := hD R f n hz
  refine ⟨P, K', L', f', hb, fun hp p => ?_, relK_of_square R F f f' g h w n
    (hB R F g n fun q hq => (hiso q hq).1) (hB R F h n fun q hq => (hiso q hq).2)⟩
  by_cases hq : -(n + 1) ≤ -(p : ℤ)
  · exact piece_transfer R F f f' g h w n p (hiso _ hq).1 (hiso _ hq).2 (hp p)
  · exact relK_of_isZero R F _ n
      (Functor.map_isZero _ (hzero _ (by omega)).1) (Functor.map_isZero _ (hzero _ (by omega)).2)
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafLocalExtendPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafLocalExtendPf

lemma specMap_comp_fromSpecStalkOfMem {C : Scheme.{0}} (U : C.Opens) {x y : C} (h : x ⤳ y)
    (hyU : y ∈ U) (hxU : x ∈ U) :
    Spec.map (C.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hyU =
      U.fromSpecStalkOfMem x hxU := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

lemma existence_of_isProper {X S : Scheme.{0}} (p : X ⟶ S) [IsProper p] :
    ValuativeCriterion.Existence p := by
  have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  exact this.1

theorem LeafLocalExtend_of : LateralTheory.E.LeafExtendCut.LeafLocalExtend := by
  intro C X S _ sC p _ x y hx h hv hfr ψ hψ
  have hdom : IsDomain (C.presheaf.stalk y) := inferInstance
  let alg : Algebra (C.presheaf.stalk y) (C.presheaf.stalk x) :=
    (C.presheaf.stalkSpecializes h).hom.toAlgebra
  let fld : Field (C.presheaf.stalk x) := IsFractionRing.toField (C.presheaf.stalk y)
  have hsq : CommSq ψ (Spec.map (C.presheaf.stalkSpecializes h)) p (C.fromSpecStalk y ≫ sC) :=
    ⟨by rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, hψ]⟩
  let sq : ValuativeCommSq p :=
    @ValuativeCommSq.mk _ _ p (C.presheaf.stalk y) _ hdom hv (C.presheaf.stalk x) fld alg hfr
      ψ (C.fromSpecStalk y ≫ sC) hsq
  obtain ⟨⟨l, hl1, hl2⟩⟩ := (existence_of_isProper p sq).exists_lift
  change Spec.map (C.presheaf.stalkSpecializes h) ≫ l = ψ at hl1
  change l ≫ p = C.fromSpecStalk y ≫ sC at hl2
  obtain ⟨U, hyU, f, hf1, hf2⟩ := spread_out_of_isGermInjective' sC p l hl2
  have hxU : x ∈ U := h.mem_open U.2 hyU
  refine ⟨U, hyU, hxU, f, ?_, hf2⟩
  rw [← hl1, hf1, ← Category.assoc, specMap_comp_fromSpecStalkOfMem U h hyU hxU]

end LateralTheory.E.LeafLocalExtendPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PartCPfSplit
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPfSplit

theorem split_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) : LateralTheory.E.PartCPf.Split := by
  intro B _ _ I hB P p hm
  have key : ∀ e : P.1, ∃ g : Fin p.natDegree → Localization (S I e.1),
      p.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) = ∏ l, (X - C (g l)) := by
    intro e
    have h0 : (0:B) ∉ S I e.1 := by
      rintro ⟨t, ht⟩
      apply (P.idem e.1 e.2).2
      simpa using ht.symm
    obtain ⟨hdom, haic⟩ := hLoc B (S I e.1) h0 hB
    have hme := hm.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
    obtain ⟨s, hs⟩ := hMS _ haic _ hme
    have hcard : s.toList.length = p.natDegree := by
      have := congrArg natDegree hs
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hm.natDegree_map] at this
      simp [this]
    refine ⟨fun l => s.toList.get (Fin.cast hcard.symm l), ?_⟩
    rw [hs]
    conv_lhs => rw [← Multiset.coe_toList s]
    rw [Multiset.map_coe, Multiset.prod_coe]
    rw [← Fintype.prod_equiv (finCongr hcard) (fun i : Fin s.toList.length => X - C (s.toList.get i)) _ (fun _ => rfl)]
    rw [← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp
  choose g hg using key
  refine ⟨p.natDegree, fun l e => g e l, ?_⟩
  refine Polynomial.ext fun k => funext fun e => ?_
  have h2 : (∏ l, (X - C (fun e => g e l))).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
      = ∏ l, (X - C (g e l)) := by simp [Polynomial.map_prod]
  have := congrArg (fun q : (Localization (S I e.1))[X] => q.coeff k) ((hg e).trans h2.symm)
  simpa [coeff_map] using this

theorem PartC_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) (hIP : LateralTheory.E.HensCut.IdemPart)
    (hA : LateralTheory.E.PartDiagCut.PartA) (hl : LateralTheory.E.PartCPf.Lift) : LateralTheory.E.PartDiagCut.PartC :=
  LateralTheory.E.PartCPf.PartC_of' (split_of hLoc hMS) hIP hA hl

end LateralTheory.E.PartCPfSplit
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafIrredPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafIrredPf

lemma mem_range {C0 D0 S T : Scheme.{0}} {v0 : C0 ⟶ D0} {c0 : C0 ⟶ T} {q : D0 ⟶ S} {t : T ⟶ S}
    (h : IsPullback v0 c0 q t) (x : D0) (y : T) (hxy : q x = t y) : x ∈ Set.range v0 := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := t) x y hxy
  refine ⟨h.isoPullback.inv z, ?_⟩
  rw [← hz, ← h.isoPullback_inv_fst]
  rfl

lemma spec_gen {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (y : Sp Ω) (p : Sp R) :
    toR R y ⤳ p := by
  apply (PrimeSpectrum.le_iff_specializes (R := R) ((toR R) y) p).mp
  intro a ha
  have hA : (toR R).base y = PrimeSpectrum.comap (algebraMap R Ω) y := by
    rw [Spec.map_base]; rfl
  change a ∈ ((toR R).base y).asIdeal at ha
  rw [hA] at ha
  let y' : PrimeSpectrum Ω := y
  have ha' : algebraMap R Ω a ∈ y'.asIdeal := ha
  rw [Ideal.eq_bot_of_prime y'.asIdeal, Ideal.mem_bot] at ha'
  have ha := ha'
  have : a = 0 := Subtype.ext (by simpa using ha)
  rw [this]; exact p.asIdeal.zero_mem

theorem LeafIrred_of : LeafIrred := by
  intro k _ Ω _ _ R _ C0 D0 c0 q v0 hc hq h
  obtain ⟨hint, -, -⟩ := hc
  have := hint
  have := hq
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : IrreducibleSpace C0 := irreducibleSpace_of_isIntegral C0
  have hirr : IsIrreducible (Set.range v0) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ C0).image v0 v0.continuous.continuousOn
  have hdense : Dense (Set.range v0) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨x, hx⟩
    obtain ⟨c⟩ := (inferInstance : Nonempty C0)
    have hopen : IsOpen (q '' U) := q.isOpenMap U hU
    have hmem : toR R (c0 c) ∈ q '' U := (spec_gen R (c0 c) (q x)).mem_open hopen ⟨x, hx, rfl⟩
    obtain ⟨x', hx'U, hx'⟩ := hmem
    exact ⟨x', hx'U, mem_range h x' (c0 c) hx'⟩
  have : IsIrreducible (Set.univ : Set D0) := by
    rw [← hdense.closure_eq]; exact hirr.closure
  exact { isPreirreducible_univ := this.2, toNonempty := ⟨this.1.some⟩ }

end LateralTheory.E.LeafIrredPf
end
end

module

public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimLocPf

theorem ring_core {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (q : ℕ) [NeZero q]
    (hq : IsUnit (q : R)) (ζ x : R) (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0)
    (hx : x ^ q = 1) :
    ∃ n < q, ∃ s : R, φ s ≠ 0 ∧ s * (x - ζ ^ n) = 0 ∧ IsPrimitiveRoot (φ ζ) q := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map φ; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have hζK : IsPrimitiveRoot (φ ζ) q := by
    rw [← Polynomial.isRoot_cyclotomic_iff]
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ (Polynomial.cyclotomic q ℤ)
    rw [hζ, map_zero] at h
    simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic] using h
  have hζq : ζ ^ q = 1 := by
    obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h := congrArg (Polynomial.aeval ζ) hc
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.mp h
  have hxK : (φ x) ^ q = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨n, hn, hnx⟩ := hζK.eq_pow_of_pow_eq_one hxK
  set t := x * ζ ^ (q - n) with ht
  refine ⟨n, hn, ∑ i ∈ Finset.range q, t ^ i, ?_, ?_, hζK⟩
  · have h1 : φ t = 1 := by
      rw [ht, map_mul, map_pow, ← hnx, ← pow_add, Nat.add_sub_cancel' hn.le, hζK.pow_eq_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_pow, h1, hqK]
  · have hg : (∑ i ∈ Finset.range q, t ^ i) * (t - 1) = 0 := by
      rw [geom_sum_mul, ht, mul_pow, hx, ← pow_mul, mul_comm (q - n) q, pow_mul, hζq, one_pow,
        one_mul, sub_self]
    have : x - ζ ^ n = (t - 1) * ζ ^ n := by
      rw [ht, sub_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hn.le, hζq, mul_one, one_mul]
    rw [this, ← mul_assoc, hg, zero_mul]

theorem isUnit_of_basicOpen_top (X : Scheme.{0}) (f : Γ(X, ⊤)) (h : X.basicOpen f = ⊤) :
    IsUnit f := by
  have key : ∀ (O : X.Opens) (_ : O = ⊤) (hle : O ≤ ⊤),
      IsUnit (X.presheaf.map (homOfLE hle).op f) → IsUnit f := by
    intro O hO; subst hO; intro hle hu; simpa using hu
  exact key _ h (X.basicOpen_le f) (X.toRingedSpace.isUnit_res_basicOpen f)

theorem affine_nbhd (U : Scheme.{0}) (s : Γ(U, ⊤)) (y : U) (hy : y ∈ U.basicOpen s) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      IsUnit (g.appTop.hom s) := by
  obtain ⟨W, hWa, hyW, hW⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ U.basicOpen s :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) hy
  refine ⟨W, Scheme.Opens.ι W, hWa, inferInstance, by simpa using hyW, ?_⟩
  apply isUnit_of_basicOpen_top
  rw [← Scheme.preimage_basicOpen_top]
  ext z
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact hW (by have h := Set.mem_range_self (f := W.ι) z; simpa using h)

theorem cyc_pow_eq_one {R : Type} [CommRing R] (q : ℕ) (ζ : R)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ) hc
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
  exact sub_eq_zero.mp h

theorem mono_pow {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ ^ a) →
    ∃ a : ℕ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ a := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ a
  rw [ha, map_pow]

theorem part3 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤))
    (hx : x ^ q = 1) : Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_pow x ζ.1)]
  intro y
  obtain ⟨n, -, s, hs, hsx, -⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 x ζ.2.2 hx
  have hy : y ∈ U.basicOpen s := (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, n, ?_⟩
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

theorem mono_unit {q : ℕ} {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : (ZMod q)ˣ, g.appTop.hom x = g.appTop.hom ζ ^ (a : ZMod q).val) →
    ∃ a : (ZMod q)ˣ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ (a : ZMod q).val := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ (a : ZMod q).val
  rw [ha, map_pow]

theorem part2 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_unit ξ.1 ζ.1)]
  intro y
  obtain ⟨n, hn, s, hs, hsx, hζK⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 ξ.1 ζ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  obtain ⟨-, -, -, -, -, hξK⟩ := ring_core (U.Γevaluation y).hom q ξ.2.1 ξ.1 ξ.1 ξ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  have hφ : (U.Γevaluation y).hom ξ.1 = (U.Γevaluation y).hom ζ.1 ^ n := by
    have h := congrArg (U.Γevaluation y).hom hsx
    rw [map_mul, map_sub, map_pow, map_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs)
  have hcop : n.Coprime q := (hζK.pow_iff_coprime (Nat.pos_of_neZero q) n).mp (hφ ▸ hξK)
  have hy : y ∈ U.basicOpen s :=
    (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, ZMod.unitOfCoprime n hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

end LateralTheory.EtaleFoundations.PrimLocPf

namespace LateralTheory.EtaleFoundations

def EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

def EtaleLocallyKummerRootsOfUnits : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem etale_locally_roots_of_unity_structure_of_exists_and_kummer (h1 : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder) (h4 : EtaleLocallyKummerRootsOfUnits) :
    EtalePrimitiveRootsExistLocally := by
  intro q _ U
  exact ⟨h1 q U, PrimLocPf.part2 q U, fun ζ x hx => PrimLocPf.part3 q U ζ x hx,
    fun hq u => h4 q U hq u⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable (R : Type) [CommRing R]

noncomputable def psiOf (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift.{1} (P.obj U) => a U.unop x.down)
  naturality := by
    intro U V g
    refine ModuleCat.free_hom_ext (fun x => ?_)
    have := ha V.unop U.unop g.unop x.down
    simp [freeP] at this ⊢
    exact this.symm

theorem free_hom_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let ψ := psiOf R P F a ha
  let φ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj ((freeP R).obj P) ⟶ F :=
    ((sheafificationAdjunction _ _).homEquiv _ _).symm ψ
  have key : toSheafify _ ((freeP R).obj P) ≫ φ.hom = ψ := by
    have := ((sheafificationAdjunction _ _).homEquiv _ _).apply_symm_apply ψ
    rw [Adjunction.homEquiv_unit] at this
    exact this
  refine ⟨φ, fun U x => ?_⟩
  change ((toSheafify _ ((freeP R).obj P)).app (op U) ≫ φ.hom.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.comp_app, key]
  erw [ModuleCat.freeDesc_apply]
  rfl

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  intro R _ E I n a ha
  have hex : ∀ (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s), ∃ φ : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s,
      ∀ U x, Sec.map φ (freeGen R _ U x) = a p s h U x :=
    fun p s h => free_hom_exists R _ _ (a p s h) (fun V U g x => ha p s h V U g x)
  choose φ hφ using hex
  let f : ∀ (p : ℕ) (s : ℤ) (_ : -(p:ℤ) + n = s), (((chains R).obj E).X (-(p:ℤ)) ⟶ I.X s) :=
    fun p s h => (chainsXIso R E p).hom ≫ φ p s h
  let α : Cochain ((chains R).obj E) I n := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫ f (-i).toNat j (by omega)
    else 0)
  refine ⟨α, fun p s h U x => ?_⟩
  have gen : ∀ (q : ℕ) (hq : q = p) (e : -(p:ℤ) = -(q:ℤ)) (h' : -(q:ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
    rintro q rfl e h'
    simp
  have hv : α.v (-(p:ℤ)) s h = f p s h := by
    simp only [α, Cochain.mk_v]
    rw [dite_eq_left (by omega)]
    exact gen _ (by omega) _ _
  simp only [GlobalTheory.EtC.ev]
  rw [hv]
  simp only [f]
  rw [Iso.inv_hom_id_assoc]
  exact hφ p s h U x
end

section -- merged from Development.EtaleCohomology.TateTwists.TPairAssocPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_pa_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (T : Cx R) (τ : Pair I J T), τ.IsTensor

def t_pa_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
    ∀ μ : Pair I J K, ∃ u : T ⟶ K, τ.Compat μ (𝟙 I) (𝟙 J) u

def t_pa_precomp : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J K : Cx R} (u : I ⟶ I') (μ : Pair I' J K),
    ∃ ρ : Pair I J K, ρ.Compat μ u (𝟙 J) (𝟙 K)

def t_pa_cpush_id : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n),
    cpush _ (𝟙 I) n x = x

def t_pa_cpush_htpy : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) {I J : Cx R} (u u' : I ⟶ J), Homotopy u u' →
    ∀ (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n), cpush _ u n x = cpush _ u' n x

theorem pa_sec_map_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

theorem t_pair_assoc_of (htw : EtaleTensorPairTwistResolutionMul) (htri : EtaleTensorPairProductAssociative) (hext : EtaleTwistResolutionUniversalExtension)
    (hcc : EtaleCupProductNaturalInCoefficients) (ha0 : EtaleCochainCupAssociativeOfPairing) (hex : t_pa_tens_ex) (huniv : t_pa_tens_univ)
    (hpre : t_pa_precomp) (hid : t_pa_cpush_id) (hhtpy : t_pa_cpush_htpy) : t_pair_assoc := by
  intro q _ E i j l k₁ k₂ k e1 e2 e3 μ₁ μ₂ ν₁ ν₂ p1 p2 p3 p4 n m p s₁ s₂ s h₁ h₂ h₃ h₄ a b c
  obtain ⟨T, τ, hτ⟩ := hex (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := hex (ZMod q) T (res _ (tw q l))
  obtain ⟨u, hu⟩ := huniv (ZMod q) τ hτ μ₁
  obtain ⟨ρ, hρ⟩ := hpre (ZMod q) u μ₂
  obtain ⟨ν, hν⟩ := htri (ZMod q) τ τ' hτ hτ' ν₁ ν₂
  obtain ⟨w₁, hw₁⟩ := huniv (ZMod q) τ' hτ' ρ
  obtain ⟨w₂, hw₂⟩ := huniv (ZMod q) τ' hτ' ν
  obtain ⟨ri, -, -⟩ := hext q i
  obtain ⟨rj, fj, -⟩ := hext q j
  obtain ⟨rl, fl, -⟩ := hext q l
  have hT := htw q i j k₁ e1 _ _ ri rj fj τ hτ
  have ek : k₁ + l = k := by omega
  have hT3 := htw q k₁ l k ek _ _ hT rl fl τ' hτ'
  obtain ⟨-, -, huniq⟩ := hext q k
  obtain ⟨H⟩ := (huniq _ hT3).2 w₁ w₂ (by
    intro U ζ
    rw [hw₁, hw₂]
    simp only [HomologicalComplex.id_f, pa_sec_map_id]
    rw [hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0)]
    have r1 := hρ U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r1
    have r2 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r2
    erw [r1, r2, p1, p2, p3, p4])
  have L1 : μ₁.cup E h₁ a b = cpush _ u s₁ (τ.cup E h₁ a b) := by
    rw [hcc _ τ μ₁ (𝟙 _) (𝟙 _) u hu E h₁ a b, hid, hid]
  have L2 : ∀ y, μ₂.cup E h₂ (cpush _ u s₁ y) c = ρ.cup E h₂ y c := by
    intro y
    have := hcc _ ρ μ₂ u (𝟙 _) (𝟙 _) hρ E h₂ y c
    rw [hid, hid] at this
    exact this.symm
  have L3 : ∀ y, ρ.cup E h₂ y c = cpush _ w₁ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ρ (𝟙 _) (𝟙 _) w₁ hw₁ E h₂ y c, hid, hid]
  have L4 : ∀ y, ν.cup E h₂ y c = cpush _ w₂ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ν (𝟙 _) (𝟙 _) w₂ hw₂ E h₂ y c, hid, hid]
  rw [← ha0 _ τ ν ν₁ ν₂ hν E h₁ h₂ h₃ h₄ a b c, L1, L2, L3, L4, hhtpy _ E w₁ w₂ H]

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.pp_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (R := R) (α + β) p s h U x = ev (R := R) α p s h U x + ev (R := R) β p s h U x ∧ ev (R := R) (α - β) p s h U x = ev (R := R) α p s h U x - ev (R := R) β p s h U x ∧ ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (R := R) (c • α) p s h U x = c • ev (R := R) α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev (R := R) α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (R := R) (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev (R := R) α p s h U x)

def LateralTheory.EtaleFoundations.pp_ev_mk : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def LateralTheory.EtaleFoundations.pp_ev_delta : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (R := R) (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev (R := R) α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) α p t (by omega) U (x.face i)

namespace LateralTheory.EtaleFoundations.OpPf
variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}

theorem img_ex (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    (α : Cochain ((chains S).obj E) I n) : ∃ β, ρ.IsImage α β := by
  obtain ⟨β, hβ⟩ := hM R (E := E) (I := J) (n := n) (fun p s h U x => ρ.app U s (ev (R := S) α p s h U x)) (by
    intro p s h V U g x
    rw [ρ.nat, (hB S).2.1])
  exact ⟨β, fun p s h U x => hβ p s h U x⟩

theorem img_unique (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    {α : Cochain ((chains S).obj E) I n} {β β' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) (h' : ρ.IsImage α β') : β = β' :=
  (hB R).2.2.1 β β' (fun p s hh U x => by rw [h, h'])

theorem img_delta (hD : LateralTheory.EtaleFoundations.pp_ev_delta) (ρ : SemiMap I J) {E : Spc} {n m : ℤ} (hm : n + 1 = m)
    {α : Cochain ((chains S).obj E) I n} {β : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) : ρ.IsImage (δ n m α) (δ n m β) := by
  intro p t ht U x
  cases p with
  | zero =>
    obtain rfl : t = m := by omega
    rw [(hD R hm β U).1 x, (hD S hm α U).1 x, h, ρ.comm]
  | succ p =>
    rw [(hD R hm β U).2 p _ t rfl ht x, (hD S hm α U).2 p _ t rfl ht x]
    rw [map_add (f := _), ← ρ.comm, ← h]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← h]

theorem img_cocycle (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) :
    ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1 := by
  obtain ⟨β, hβ⟩ := img_ex hB hM ρ α.1
  refine ⟨Cocycle.mk β (n + 1) rfl ?_, hβ⟩
  have h1 := img_delta hD ρ rfl hβ
  rw [Cocycle.δ_eq_zero] at h1
  have h0 : ρ.IsImage (0 : Cochain ((chains S).obj E) I (n + 1)) (0 : Cochain ((chains R).obj E) J (n + 1)) := by
    intro p s h U x
    rw [((hB R).1 0 0 p s h U x).2.2.1, ((hB S).1 0 0 p s h U x).2.2.1, map_zero]
  exact img_unique hB ρ h1 h0

noncomputable def img (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : Cocycle ((chains R).obj E) J n :=
  (img_cocycle hB hM hD ρ α).choose

theorem img_spec (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : ρ.IsImage α.1 (img hB hM hD ρ α).1 :=
  (img_cocycle hB hM hD ρ α).choose_spec

theorem img_eq (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n)
    (h : ρ.IsImage α.1 β.1) : img hB hM hD ρ α = β :=
  Cocycle.ext (img_unique hB ρ (img_spec hB hM hD ρ α) h)

noncomputable def zmap (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) (E : Spc) (n : ℤ) : Cocycle ((chains S).obj E) I n →+ CohomologyClass ((chains R).obj E) J n :=
  AddMonoidHom.mk' (fun α => CohomologyClass.mk (img hB hM hD ρ α)) (fun a b => by
    rw [← CohomologyClass.mk_add]
    congr 1
    apply img_eq
    intro p s h U x
    have ha := img_spec hB hM hD ρ a p s h U x
    have hb := img_spec hB hM hD ρ b p s h U x
    change ev (R := R) ((img hB hM hD ρ a).1 + (img hB hM hD ρ b).1) p s h U x = ρ.app U s (ev (R := S) (a.1 + b.1) p s h U x)
    rw [((hB R).1 _ _ p s h U x).1, ((hB S).1 _ _ p s h U x).1, map_add (f := _), ha, hb])

noncomputable def theOp (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) : NatOp I J where
  app E n := CohomologyClass.descAddMonoidHom (zmap hB hM hD ρ E n) (by
    intro α hα
    obtain ⟨γ, hγ⟩ := (mem_coboundaries_iff α (n - 1) (by omega)).1 hα
    obtain ⟨γ', hγ'⟩ := img_ex hB hM ρ γ
    have h1 := img_delta hD ρ (by omega : n - 1 + 1 = n) hγ'
    rw [hγ] at h1
    have h2 := img_eq hB hM hD ρ α (Cocycle.mk (δ (n - 1) n γ') (n + 1) rfl (δ_δ _ _ _ _)) h1
    change CohomologyClass.mk (img hB hM hD ρ α) = 0
    rw [h2, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨γ', rfl⟩)
  nat := by
    intro E E' f n x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    change CohomologyClass.mk (zcomp _ (img hB hM hD ρ α) (zero_add n)) =
      CohomologyClass.mk (img hB hM hD ρ (zcomp _ α (zero_add n)))
    congr 1
    symm
    apply img_eq
    intro p s h U y
    change ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp (img hB hM hD ρ α).1 (zero_add n)) p s h U y =
      ρ.app U s (ev (R := S) ((Cochain.ofHom ((chains S).map f)).comp α.1 (zero_add n)) p s h U y)
    rw [(hB R).2.2.2.1, (hB S).2.2.2.1, img_spec hB hM hD ρ α]

end LateralTheory.EtaleFoundations.OpPf

open LateralTheory.EtaleFoundations.OpPf in
theorem LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk)
    (hD : LateralTheory.EtaleFoundations.pp_ev_delta) : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  intro S R _ _ I J ρ
  refine ⟨fun E n α => img_cocycle hB hM hD ρ α, fun E n α β h => ?_⟩
  have hc : ∃ c : NatOp I J, ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) β.1 p s h U x = ρ.app U s (ev (R := S) α.1 p s h U x)) →
      c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β := by
    refine ⟨theOp hB hM hD ρ, fun E n α β h => ?_⟩
    change CohomologyClass.mk (img hB hM hD ρ α) = CohomologyClass.mk β
    rw [img_eq hB hM hD ρ α β h]
  exact pick_spec hc E n α β h
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem sec_glue_forget_isSheaf (R : Type) [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
  have : PreservesLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} R))) :=
    preservesLimitsOfSize_shrink.{1, 0, 0, 1} _
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf Scheme.etaleTopology.{0} F.obj
      (forget (ModuleCat.{1} (ULift.{1} R))) F.property)

theorem etale_sheaf_sections_glue_of_forget_isSheaf : EtaleSheafSectionsSeparatedAndGlue := by
  intro R _ F U
  have hT := sec_glue_forget_isSheaf R F
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨S, hS, h⟩ := hab
    exact (hT S hS).isSeparatedFor.ext (fun V g hg => h V g hg)
  · intro S hS s hs
    let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows :=
      fun V g hg => s V g hg
    have hc : x.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W g k hg
      exact (hs V W g k hg).symm
    obtain ⟨t, ht, -⟩ := hT S hS x hc
    exact ⟨t, fun V g hg => ht g hg⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tt_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

def tt_tens_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → μ.IsTensor →
    K.IsStrictlyGE 0

def tt_twist_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {J M : Cx (ZMod q)}
    (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q j J e' → (∀ t, FlatS (J.X t)) →
    ∀ σ : Pair (sgl (tw q i)) J M, σ.IsTensor →
      IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ)

def tt_res_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) {I J M T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U),
    IsTwRes q i I e → J.IsStrictlyGE 0 → (∀ t, FlatS (J.X t)) →
    ∀ (σ : Pair (sgl (tw q i)) J M) (τ : Pair I J T), σ.IsTensor → τ.IsTensor →
      ∃ m : M ⟶ T, QuasiIso m ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec (J.X 0) U),
        Sec.map (m.f 0) (σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) b) =
          τ.mul U 0 0 0 (add_zero 0) (e U ζ) b

theorem etale_tensor_twisted_resolution_of_existence_bound_and_sides (hex : tt_tens_ex) (hge : tt_tens_ge) (htw : tt_twist_side) (hres : tt_res_side) :
    EtaleTensorPairTwistResolutionMul := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨M, σ, hσ⟩ := hex (ZMod q) (sgl (tw q i)) J
  obtain ⟨-, ε₁, hε₁, hgen₁⟩ := htw q i j k hk e' hJ hflat σ hσ
  obtain ⟨m, hm, hgen⟩ := hres q i e hI hJ.1 hflat σ τ hσ hτ
  refine ⟨hge (ZMod q) τ hI.1 hJ.1 hτ, ε₁ ≫ m, inferInstance, fun U ζ => ?_⟩
  refine Eq.trans ?_ (hgen U ζ (e' U ζ))
  refine Eq.trans ?_ (congrArg (Sec.map (m.f 0)) (hgen₁ U ζ))
  rfl

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.LocBasicPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

theorem loc_pull (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, (Scheme.etaleTopology).pullback_stable k hS,
    fun V g hg => hSP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hSP⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := by
        intro Y Z f hf g W' k
        simpa [Category.assoc] using hf W' (k ≫ g) }
  refine ⟨R, ?_, fun W h hR => by simpa using hR W (𝟙 W)⟩
  refine (Scheme.etaleTopology).transitive hS R ?_
  intro Y f hf
  obtain ⟨T, hT, hTP⟩ := hSP Y f hf
  refine (Scheme.etaleTopology).superset_covering ?_ hT
  intro Z k hk W' k'
  have := hTP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_finset (U : Scheme.{0}) (ι : Type) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U _ (fun V g i hi => by simp at hi)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  haveI := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U ι P h Finset.univ) (fun V g hg i => hg i (Finset.mem_univ i))

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

end LateralTheory.EtaleFoundations.LocBasicPf

open LateralTheory.EtaleFoundations.LocBasicPf in
theorem LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure :=
  ⟨loc_top, loc_mono, loc_and, loc_pull, loc_trans, fun U ι _ P h => loc_finite U ι P h,
    fun U _ P => loc_empty U P⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy : Prop :=
  ∀ (R : Type) [CommRing R] (K L I : Cx R) [I.IsKInjective] (f : K ⟶ L) [QuasiIso f],
    (∀ a : K ⟶ I, ∃ m : L ⟶ I, Nonempty (Homotopy (f ≫ m) a)) ∧
    ∀ m m' : L ⟶ I, Nonempty (Homotopy (f ≫ m) (f ≫ m')) → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0] (a b : sgl F ⟶ I),
    Nonempty (Homotopy a b) → a = b

theorem LateralTheory.EtaleFoundations.etale_sheaf_ext_hom_injective_resolution_of_lift_and_rigidity (hA : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy)
    (hB : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual) : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m, hm⟩ := (hA R (sgl F) T I ε).1 a
    exact ⟨m, hB R F I _ _ hm⟩
  · exact (hA R (sgl F) T I ε).2 m m' ⟨Homotopy.ofEq h⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiIffSectionsOfSeparation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MonoEpiPf

variable {R : Type} [CommRing R]

theorem sep {F : Shv R} {U : Scheme.{0}} (a : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = 0) : a = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  have key := Presheaf.IsSheaf.hom_ext F.property ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a)) 0 (by
      intro I
      ext
      have := hP _ I.f I.hf
      simp only [Sec.res] at this
      simp [LinearMap.toSpanSingleton_apply, this])
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) key
  simpa using this

theorem mono_iff_inj {F G : Shv R} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U)) := by
  constructor
  · intro h U
    have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
    have : Mono (φ.hom.app (op U)) := (NatTrans.mono_iff_mono_app _).1 this _
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro h
    have : Mono φ.hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      induction U using Opposite.rec with | op U => ?_
      exact (ModuleCat.mono_iff_injective _).2 (h U)
    exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem inj_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    (∀ U, Function.Injective (Sec.map φ (U := U))) ↔
      ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  constructor
  · intro h U a ha
    have : a = 0 := h U (by rw [ha]; simp [Sec.map])
    subst this
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => by simp [Sec.res]⟩
  · intro h U
    have hk : ∀ a : Sec F U, Sec.map φ a = 0 → a = 0 := fun a ha => sep a (h U a ha)
    intro a b hab
    have : Sec.map φ (a - b) = 0 := by simp only [Sec.map] at hab ⊢; rw [map_sub, hab, sub_self]
    exact sub_eq_zero.1 (hk _ this)

theorem epi_iff {F G : Shv R} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b := by
  rw [← Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} (ULift.{1} R))]
  constructor
  · intro h U b
    refine ⟨Presheaf.imageSieve φ.hom b, h.imageSieve_mem b, fun V g hg => ?_⟩
    rw [Presheaf.imageSieve_apply] at hg
    exact hg
  · intro h
    refine ⟨fun {U} b => ?_⟩
    obtain ⟨S, hS, hP⟩ := h U b
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    rw [Presheaf.imageSieve_apply]
    exact hP V g hg

theorem ext_sec {F G : Shv R} (φ ψ : F ⟶ G)
    (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  induction U using Opposite.rec with | op U => ?_
  exact h U a

end LateralTheory.EtaleFoundations.MonoEpiPf

open LateralTheory.EtaleFoundations.MonoEpiPf in
theorem LateralTheory.EtaleFoundations.etale_sheaf_mono_epi_iff_sections_of_separation : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria := by
  intro R _ F G φ
  exact ⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff φ,
    fun ψ h => ext_sec φ ψ h⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapIsIsoOfInjSurj
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (b : Sec T U), Loc U fun V g => ∃ a : Sec (tw q k) V, Sec.map φ a = Sec.res g b

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_isIso_of_inj_surj (hme : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hs : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective) (hi : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso := by
  intro q _ i j k T μ hμ hk φ hφ
  have h := hme (ZMod q) φ
  have hm : Mono φ := h.2.1.2 (hi q i j k T μ hμ hk φ hφ)
  have he : Epi φ := h.2.2.1.2 (hs q i j k T μ hμ hk φ hφ)
  exact isIso_of_mono_of_epi φ
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsInjectiveResolutionHomE
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafRestrictScalarsInjectiveResolutionHomExists : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ m : ∀ n : ℤ, (restr φ).obj ((res S F).X n) ⟶ (res R ((restr φ).obj F)).X n,
      (∀ i j : ℤ, (restr φ).map ((res S F).d i j) ≫ m j = m i ≫ (res R ((restr φ).obj F)).d i j) ∧
      (restr φ).map (resι S F) ≫ m 0 = resι R ((restr φ).obj F)

namespace LateralTheory.EtaleFoundations

theorem etaleSheaf_restrictScalars_resolution_comparison_of_hom (hH : EtaleSheafRestrictScalarsInjectiveResolutionHomExists) : EtaleRestrictScalarsResolutionCompatible := by
  intro R S _ _ φ F U a
  obtain ⟨m, hc, h0⟩ := hH R S φ F
  have hex : ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
    refine ⟨⟨fun U s => ((m s).hom.app (op U)).hom.toAddMonoidHom, ?_, ?_⟩, ?_⟩
    · intro V U g s x
      have h := (m s).hom.naturality g.op
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x).symm
    · intro U s t x
      have h := congrArg (fun f : (restr φ).obj ((res S F).X s) ⟶ (res R ((restr φ).obj F)).X t => (f.hom.app (op U)).hom x) (hc s t)
      exact h.symm
    · intro U x
      exact congrArg (fun f : (restr φ).obj F ⟶ (res R ((restr φ).obj F)).X 0 => (f.hom.app (op U)).hom x) h0
  exact pick_spec hex U a

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.acycPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.acyc

def LocAcyc {R : Type} [CommRing R] (C : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (n : ℤ) (z : Sec (C.X n) U), Sec.map (C.d n (n + 1)) z = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) y = Sec.res g z

def ColExact {R : Type} [CommRing R] (C J : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (s t : ℤ) (x : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id x = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (s - 1)) V ⊗[ULift.{1} R] Sec (J.X t) V,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op V)).hom LinearMap.id y =
        TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom x

def acycIff : Prop := ∀ (R : Type) [CommRing R] (C : Cx R), C.Acyclic ↔ LocAcyc C

def column : Prop := ∀ (R : Type) [CommRing R] (C J : Cx R), (∀ t, FlatS (J.X t)) → LocAcyc C → ColExact C J

def stair : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → ColExact C J → LocAcyc T

end LateralTheory.EtaleFoundations.acyc

open LateralTheory.EtaleFoundations.acyc in
theorem LateralTheory.EtaleFoundations.tqis.acyc_of (hI : acycIff) (hC : column) (hS : stair) : LateralTheory.EtaleFoundations.tqis.acyc := by
  intro R _ C J T a b _ _ τ hτ hJ hCa
  exact (hI R T).2 (hS R a b τ hτ (hC R C J hJ ((hI R C).1 hCa)))
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvDeltaPf

variable {R : Type} [CommRing R]

def secHom {F G : Shv R} (U : Scheme.{0}) (x : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := Sec.map φ x
  map_zero' := by simp [Sec.map]
  map_add' f g := by simp [Sec.map]

lemma sec_zsmul {F G : Shv R} (f : F ⟶ G) (c : ℤ) (U : Scheme.{0}) (x : Sec F U) : Sec.map (c • f) x = c • Sec.map f x :=
  map_zsmul (secHom (G := G) U x) c f

lemma sec_sum {ι : Type} (s : Finset ι) {F G : Shv R} (f : ι → (F ⟶ G)) (U : Scheme.{0}) (x : Sec F U) : Sec.map (∑ i ∈ s, f i) x = ∑ i ∈ s, Sec.map (f i) x :=
  map_sum (secHom (G := G) U x) f s

variable (R) in
lemma freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) : Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  calc _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := rfl
    _ = (((freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := by rw [toSheafify_naturality]
    _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) := rfl
    _ = _ := by
      unfold freeGen
      congr 1
      simp [freeP, ModuleCat.freeMk]
      exact Finsupp.mapDomain_single

variable (R) in
lemma chains_d (E : Spc) (p : ℕ) : (chainsXIso R E (p+1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (chainsXIso R E (p+1)).hom ≫ ((chainsN R).obj E).d (p+1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq _ _ rfl rfl
  have h2 : ((chainsN R).obj E).d (p+1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
    simp [chainsN]
  rw [h1, h2, Iso.inv_hom_id_assoc]
  rfl

variable (R) in
lemma etale_simplicial_chains_isZero_of_positive_degree (E : Spc) (k : ℤ) (hk : 0 < k) : IsZero (((chains R).obj E).X k) :=
  HomologicalComplex.isZero_extend_X _ _ _ (by rintro i (h : -(i:ℤ) = k); omega)

lemma sec_add {F G : Shv R} (f g : F ⟶ G) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
  map_add (secHom (G := G) U x) f g

lemma sec_comp {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem part0 {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (x : Sx E 0 U) : ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
  have hz : ((chains R).obj E).d (-((0:ℕ):ℤ)) (-((0:ℕ):ℤ) + 1) = 0 := (etale_simplicial_chains_isZero_of_positive_degree R E _ (by omega)).eq_of_tgt _ _
  have key : (chainsXIso R E 0).inv ≫ (δ n m α).v (-((0:ℕ):ℤ)) m (by simp) = ((chainsXIso R E 0).inv ≫ α.v (-((0:ℕ):ℤ)) n (by simp)) ≫ I.d n m := by
    rw [δ_v n m hm α _ _ (by simp) n (-((0:ℕ):ℤ) + 1) (by omega) rfl, hz]
    simp
  show Sec.map (_ ≫ _) _ = _
  rw [key]
  rfl

theorem partS {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) : ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  have key : (chainsXIso R E (p+1)).inv ≫ (δ n m α).v _ t ht = ((chainsXIso R E (p+1)).inv ≫ α.v _ s hs) ≫ I.d s t + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((free R).map (E.δ i) ≫ ((chainsXIso R E p).inv ≫ α.v (-(p:ℤ)) t (by omega))) := by
    rw [δ_v n m hm α _ _ ht s (-(p:ℤ)) (by omega) (by push_cast; ring), Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ← Category.assoc, chains_d]
    simp only [Category.assoc, Preadditive.sum_comp, Linear.smul_comp]
  show Sec.map (_ ≫ _) _ = _
  rw [key, Units.smul_def, Units.smul_def, sec_add, sec_zsmul, sec_sum]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [sec_zsmul, sec_comp, freeGen_map]
  rfl

end LateralTheory.EtaleFoundations.EvDeltaPf

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds : LateralTheory.EtaleFoundations.EtaleCochainEvaluationCoboundaryFormula := by
  intro R _ E I n m hm α U
  exact ⟨fun x => LateralTheory.EtaleFoundations.EvDeltaPf.part0 hm α U x,
    fun p s t hs ht x => LateralTheory.EtaleFoundations.EvDeltaPf.partS hm α U p s t hs ht x⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductOfFamilyAndLeibniz
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L),
    ∃ m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U,
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) ∧
      ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U),
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) →
      (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
      ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.map (L.d w (w + 1)) (m U s t w h a b) = m U (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) a) b +
          s.negOnePow • m U s (t + 1) (w + 1) (by omega) a (Sec.map (K.d t (t + 1)) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_of_family_and_leibniz (hfam : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists)
    (hleib : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz) : LateralTheory.EtaleFoundations.EtaleTensorPairProductAssociative := by
  intro R _ I J K T T3 τ τ' hτ _ M L μ' ν'
  obtain ⟨m, hnat, heq⟩ := hfam R τ hτ μ' ν'
  refine ⟨⟨m, hnat, hleib R τ hτ μ' ν' m hnat heq⟩, ?_⟩
  intro U s t u st tu w h1 h2 h3 h4 a b c
  exact heq U s t u st tu w h1 h2 h3 h4 a b c
end

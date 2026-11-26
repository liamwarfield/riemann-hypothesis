module

public import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeTwoValueOfRootsKum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V2

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def KumTEx : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def SecGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h⟩ := hP
  obtain ⟨T, hT, h'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h V g hg.1, h' V g hg.2⟩⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, h'⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h' V g hg)⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp]; rfl

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

theorem umap_id {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : Units.map (Scheme.Hom.appTop (𝟙 U)).hom.toMonoidHom u = u := by
  ext; simp

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (h : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  have := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
  simpa using this

theorem glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) = Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem det_gmap {V U : Scheme.{0}} (g : V ⟶ U) (m : GL (Fin 1) Γ(U, ⊤)) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom m) = Units.map g.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  simp [Matrix.GeneralLinearGroup.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  have := ConcreteCategory.congr_hom ((L.app (op (SimplexCategory.mk 1))).naturality g.op) x
  simp only [ConcreteCategory.comp_apply] at this
  rw [this, glMat_res, det_gmap]

noncomputable def fv (q : ℕ) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  kumT q U v + kumT q U w - kumT q U (v * w)

theorem kumT_pow (hK : KumTEx) (q : ℕ) [NeZero q] {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    ∀ (a : ℕ) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 ^ a * v → kumT q U w = kumT q U v + a • resGen 1 ζ := by
  intro a
  induction a with
  | zero => intro v w h; have : w = v := Units.ext (by simpa using h); subst this; simp
  | succ a ih =>
    intro v w h
    have hu : IsUnit (ζ.1 ^ (a + 1)) := by
      rw [show ζ.1 ^ (a + 1) = (w : Γ(U, ⊤)) * ((v⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) by rw [h, mul_assoc]; simp]
      exact (w * v⁻¹).isUnit
    have hz : IsUnit ζ.1 := (isUnit_pow_iff (Nat.succ_ne_zero a)).1 hu
    let m : (Γ(U, ⊤))ˣ := hz.unit ^ a * v
    have hm : kumT q U m = kumT q U v + a • resGen 1 ζ := ih v m (by simp [m])
    have hw : kumT q U w = kumT q U m + resGen 1 ζ := (hK q).2 U ζ m w (by rw [h]; simp [m, pow_succ']; ring)
    rw [hw, hm, succ_nsmul, add_assoc]

theorem res_fv (hK : KumTEx) (q : ℕ) [NeZero q] {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v w : (Γ(U, ⊤))ˣ) :
    Sec.res g (fv q U v w) = fv q V (Units.map g.appTop.hom.toMonoidHom v) (Units.map g.appTop.hom.toMonoidHom w) := by
  have e : ∀ a b c : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (a + b - c) = Sec.res g a + Sec.res g b - Sec.res g c := by
    intro a b c; simp [Sec.res]
  unfold fv
  rw [e, (hK q).1 V U g v hq, (hK q).1 V U g w hq, (hK q).1 V U g (v * w) hq, map_mul]

theorem umap_root {q : ℕ} {W V : Scheme.{0}} (h : W ⟶ V) (ζ : Prim q Γ(V, ⊤)) (v v' : (Γ(V, ⊤))ˣ) (a : ℕ)
    (ha : h.appTop.hom ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a) :
    ((Units.map h.appTop.hom.toMonoidHom v' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ a * Units.map h.appTop.hom.toMonoidHom v := by
  have : (v' : Γ(V, ⊤)) = ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) * v := by simp
  show h.appTop.hom (v' : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a * h.appTop.hom v
  rw [this, map_mul, ha]

theorem indepA (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤))
    (hq : IsUnit (q : Γ(V, ⊤))) (v v' w w' : (Γ(V, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q V v w = fv q V v' w' := by
  have hx : (((v' * v⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hv, inv_pow, mul_inv_cancel]; rfl
  have hy : (((w' * w⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hw, inv_pow, mul_inv_cancel]; rfl
  apply (hG _ _ V).1
  refine loc_mono (loc_and ((hP q V).2.2.1 ζ _ hx) ((hP q V).2.2.1 ζ _ hy)) ?_
  rintro W h ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [res_fv hK q h hq, res_fv hK q h hq]
  have h1 := umap_root h ζ v v' a ha
  have h2 := umap_root h ζ w w' b hb
  have h3 : ((Units.map h.appTop.hom.toMonoidHom v' * Units.map h.appTop.hom.toMonoidHom w' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ (a + b) * ((Units.map h.appTop.hom.toMonoidHom v * Units.map h.appTop.hom.toMonoidHom w : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) := by
    rw [Units.val_mul, h1, h2, Units.val_mul, pow_add]; ring
  unfold fv
  rw [kumT_pow hK q _ a _ _ h1, kumT_pow hK q _ b _ _ h2, kumT_pow hK q _ (a + b) _ _ h3, add_nsmul]
  abel

theorem indepB (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (v v' w w' : (Γ(U, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q U v w = fv q U v' w' := by
  apply (hG _ _ U).1
  refine loc_mono ((hP q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  rw [res_fv hK q g hq, res_fv hK q g hq]
  exact indepA hP hK hG q ζ (unit_res g hq) _ _ _ _ (by rw [← map_pow, ← map_pow, hv]) (by rw [← map_pow, ← map_pow, hw])

def Good (q : ℕ) (U : Scheme.{0}) (u1 u2 : (Γ(U, ⊤))ˣ) (a : Sec ((res _ (tw q 1)).X 0) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u1 →
    w ^ q = Units.map g.appTop.hom.toMonoidHom u2 → Sec.res g a = fv q V v w

theorem good_exists (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (u1 u2 : (Γ(U, ⊤))ˣ) : ∃ a, Good q U u1 u2 a := by
  obtain ⟨S, hS, hS'⟩ := loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => fv q V (hS' V g hg).1.choose (hS' V g hg).2.choose
  obtain ⟨a, ha⟩ := (hG _ _ U).2 S hS s (by
    intro V W g k hg
    simp only [s]
    rw [res_fv hK q k (unit_res g hq)]
    apply indepB hP hK hG q (unit_res (k ≫ g) hq)
    · rw [← map_pow, (hS' V g hg).1.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).1.choose_spec]
    · rw [← map_pow, (hS' V g hg).2.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).2.choose_spec])
  refine ⟨a, fun V g v w hv hw => ?_⟩
  apply (hG _ _ V).1
  refine ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩
  show Sec.res k (Sec.res g a) = Sec.res k (fv q V v w)
  rw [res_comp, ha W (k ≫ g) hk, res_fv hK q k (unit_res g hq)]
  apply indepB hP hK hG q (unit_res (k ≫ g) hq)
  · rw [(hS' W (k ≫ g) hk).1.choose_spec, ← map_pow, hv, umap_comp]
  · rw [(hS' W (k ≫ g) hk).2.choose_spec, ← map_pow, hw, umap_comp]

theorem good_unique (hP : PrimLoc) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) {u1 u2 : (Γ(U, ⊤))ˣ} {a b : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) (hb : Good q U u1 u2 b) : a = b := by
  apply (hG _ _ U).1
  refine loc_mono (loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  rw [ha V g v w hv hw, hb V g v w hv hw]

theorem good_res (q : ℕ) {V U : Scheme.{0}} (g : V ⟶ U) {u1 u2 : (Γ(U, ⊤))ˣ} {a : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) :
    Good q V (Units.map g.appTop.hom.toMonoidHom u1) (Units.map g.appTop.hom.toMonoidHom u2) (Sec.res g a) := by
  intro W k v w hv hw
  rw [res_comp]
  exact ha W (k ≫ g) v w (by rw [hv, umap_comp]) (by rw [hw, umap_comp])

end LateralTheory.EtaleFoundations.V2

open LateralTheory.EtaleFoundations.V2 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeTwoValue := by
  intro q _ E L hi
  have hq : ∀ (U : Scheme.{0}) (x : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.sub 0 0 (by omega)⟩
  refine ⟨fun U x => pick (Good q U (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))), ?_, ?_⟩
  · intro V U g x
    have e1 : lineUnit L ((x.res g).sub 0 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 0 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have e2 : lineUnit L ((x.res g).sub 1 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 1 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have h1 := good_res q g (pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))))
    rw [← e1, ← e2] at h1
    exact good_unique hP hG q (hq V (x.res g)) h1 (pick_spec (good_exists hP hK hG q (hq V (x.res g)) _ _))
  · intro U x v w hv hw
    have := pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega))))
      U (𝟙 U) v w (by rw [umap_id]; exact hv) (by rw [umap_id]; exact hw)
    rwa [res_id] at this
end

section -- merged from Development.EtaleCohomology.TateTwists.CupflipEtaDeltaPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib

namespace LateralTheory.EtaleFoundations.EtaDelta
variable {R : Type} [CommRing R]

theorem along_face {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E M U)
    (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk M) (i : Fin (p + 2)) :
    (x.along a).face i = x.along (SimplexCategory.δ i ≫ a) :=
  along_comp x a (SimplexCategory.δ i)

theorem face_along {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E (M + 1) U) (i : Fin (M + 2))
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk M) :
    (x.face i).along a = x.along (a ≫ SimplexCategory.δ i) :=
  along_comp x (SimplexCategory.δ i) a

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem phi_eq {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) :
    phi μ hk α β x w c = Finsupp.linearCombination ℤ (phiT μ hk α β x w) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem phiT_face {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (i : Fin (M + 2)) (w : ℤ) (z : Pr M) :
    phiT μ hk α β (x.face i) w z =
      phiT μ hk α β x w ⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ i, z.2.2.2 ≫ SimplexCategory.δ i⟩ := by
  simp only [phiT, face_along]

theorem phi_bd {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (w : ℤ) (c : Pr M →₀ ℤ) :
    ∑ i : Fin (M + 2), (-1 : ℤ) ^ (i : ℕ) • phi μ hk α β (x.face i) w c = phi μ hk α β x w (Pr.bd c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [phi_eq, Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact congrArg _ (funext fun z => phiT_face μ hk α β x i w z)

theorem phiT_Fm {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phiT μ hk α β x w ⟨p, r, a, b⟩ = ((m * (p : ℤ)).negOnePow : ℤ) • Fm μ α β U w p r (x.along a) (x.along b) := by
  dsimp only [phiT, Fm]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rw [smul_zero]

end

theorem ev_zero' {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have := ev_sub' (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rwa [sub_self, sub_self] at this

theorem d_ev {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (hst : s + 1 = t) (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s t) (ev α.1 p s hs U y) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q z => if hh : -(q : ℤ) + n = t then ev α.1 q t hh U z else 0) p y := by
  have h := ev_delta_bd (n := n) (m := n + 1) rfl α.1 p s t hs (by omega) U y
  rw [Cocycle.δ_eq_zero, ev_zero', Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul] at h
  exact add_neg_eq_zero.mp h.symm

theorem bd_zero' {E : Spc} {U : Scheme.{0}} {G : Type*} [AddCommGroup G] (p : ℕ) (y : Sx E p U) :
    bd (E := E) (U := U) (fun _ _ => (0 : G)) p y = 0 := by
  cases p <;> simp [bd]

theorem mul_zsmul_left {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h (c • a) b = c • μ.mul U s t w h a b := by
  rw [map_zsmul]; rfl

theorem mul_zsmul_right {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h a (c • b) = c • μ.mul U s t w h a b :=
  map_zsmul _ c b

theorem d_Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cocycle ((chains R).obj E) I n)
    (β : Cocycle ((chains R).obj E) J m) (U : Scheme.{0}) (s t : ℤ) (hst : s + 1 = t) (p r : ℕ)
    (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d s t) (Fm μ α.1 β.1 U s p r y z) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q y' => Fm μ α.1 β.1 U t q r y' z) p y +
      ((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) • bd (fun q z' => Fm μ α.1 β.1 U t p q y z') r z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = s
  · have e : Fm μ α.1 β.1 U s p r y z = μ.mul U _ _ s h (ev α.1 p _ rfl U y) (ev β.1 r _ rfl U z) := by
      unfold Fm; rw [dite_eq_left h]
    rw [e, leib' μ U _ _ s (-(p : ℤ) + n + 1) (-(r : ℤ) + m + 1) t h rfl rfl hst,
      d_ev α p _ _ rfl rfl, d_ev β r _ _ rfl rfl, mul_zsmul_left, mul_zsmul_right, mul_bd_left, mul_bd_right,
      Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    · refine bd_congr (fun q y' hq => ?_) y
      unfold Fm
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · refine bd_congr (fun q z' hq => ?_) z
      unfold Fm
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · have e : Fm μ α.1 β.1 U s p r y z = 0 := by unfold Fm; rw [dite_eq_right h]
    have h0 := secmap_zsmul (K.d s t) (0 : ℤ) (0 : Sec (K.X s) U)
    rw [zero_smul, zero_smul] at h0
    rw [e, h0]
    rw [bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q y' hq => by unfold Fm; rw [dite_eq_right (by omega)]) y,
      bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q z' hq => by unfold Fm; rw [dite_eq_right (by omega)]) z,
      bd_zero', bd_zero', smul_zero, smul_zero, add_zero]

theorem secmap_add' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add ((φ.hom.app (op U)).hom) a b

theorem secmap_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero ((φ.hom.app (op U)).hom)

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)

theorem part1 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((n.negOnePow : ℤˣ) : ℤ) •
      bd (fun q y' => Fm μ α.1 β.1 U t q r y' (x.along b)) p (x.along a)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t) (Pr.d₁ (⟨p, r, a, b⟩ : Pr N)) := by
  cases p with
  | zero => simp [bd, Pr.d₁]
  | succ p =>
    show _ = _ • Finsupp.linearCombination ℤ _
      (∑ i : Fin (p + 2), Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) ((-1 : ℤ) ^ (i : ℕ)))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by push_cast; ring⟩

theorem part2 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) •
      bd (fun q z' => Fm μ α.1 β.1 U t p q (x.along a) z') r (x.along b)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
      ((-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N)) := by
  cases r with
  | zero => simp [bd, Pr.d₂]
  | succ r =>
    show _ = _ • Finsupp.linearCombination ℤ _ ((-1 : ℤ) ^ p •
      ∑ j : Fin (r + 2), Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) ((-1 : ℤ) ^ (j : ℕ)))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, map_zsmul, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-(p : ℤ), by push_cast; ring⟩

theorem d_phiT {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (z : Pr N) :
    Sec.map (K.d s t) (phiT μ hk α.1 β.1 x s z) =
      ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
        (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [phiT_Fm, secmap_zsmul, d_Fm μ α β U s t hst, smul_add, map_add (f := _), smul_add, part1 μ hk α β, part2 μ hk α β]

theorem d_phi {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (c : Pr N →₀ ℤ) :
    Sec.map (K.d s t) (phi μ hk α.1 β.1 x s c) = ((k.negOnePow : ℤˣ) : ℤ) • phi μ hk α.1 β.1 x t (Pr.d N c) := by
  rw [phi_eq, phi_eq]
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp only [map_zero, secmap_zero', smul_zero]
  · intro f g hf hg
    rw [map_add (f := _), map_add (f := _), map_add (f := _), secmap_add', hf, hg, smul_add]
  · intro z a
    rw [Finsupp.linearCombination_single, secmap_zsmul, d_phiT μ hk α β x s t hst]
    unfold Pr.d
    rw [Finsupp.linearCombination_single, map_zsmul, smul_comm]

theorem phi_add {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c + d) = phi μ hk α.1 β.1 x w c + phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_add (f := _)]

theorem phi_sub {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c - d) = phi μ hk α.1 β.1 x w c - phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_sub]

end

end LateralTheory.EtaleFoundations.EtaDelta


open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.EtaDelta in
theorem LateralTheory.EtaleFoundations.cupflip_eta_delta_of : LateralTheory.EtaleFoundations.cupflip_eta_delta := by
  intro h hs R _ I J K μ E n m k hk α β η hη N t ht U x
  cases N with
  | zero =>
    rw [ev_delta_zero (n := k - 1) (by omega) η (-((0 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη 0 _ _ U x,
      d_phi μ hk α β x _ t (by omega), hs.2.1, phi_sub]
  | succ M =>
    rw [ev_delta_succ (n := k - 1) (by omega) η M (-((M + 1 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη (M + 1) _ _ U x]
    simp only [hη]
    rw [Units.smul_def, phi_bd, d_phi μ hk α β x _ t (by omega), ← smul_add, ← phi_add, hs.2.2 M, phi_sub]
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductFamilyOfGluing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensTriFamPf

def SecGlue : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

variable {R : Type} [CommRing R]

lemma res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

lemma res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

lemma res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ _ _

lemma res_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift.{1} R) (a : Sec F U) :
    Sec.res g (r • a) = r • Sec.res g a := map_smul _ _ _

lemma loc_inter {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨S', hS', hSQ⟩ := hQ
  exact ⟨S ⊓ S', Scheme.etaleTopology.intersection_covering hS hS', fun V g hg => ⟨hSP V g hg.1, hSQ V g hg.2⟩⟩

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

lemma loc_pull {U V : Scheme.{0}} (k : V ⟶ U) {P : ∀ W : Scheme.{0}, (W ⟶ U) → Prop} (hP : Loc U P) :
    Loc V fun W h => P W (h ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, Scheme.etaleTopology.pullback_stable k hS, fun W h hh => hSP W _ hh⟩

section
variable {I J K T M L : Cx R}

lemma lift_res (τ : Pair I J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res g w x) = Sec.res g (τ.lift U w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.map_tmul,
        TensorProduct.lift.tmul]
      exact (τ.nat g _ _ _ _ a b).symm
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
  | add x x' hx hx' => simp only [map_add (f := _), hx, hx']

lemma lift_single (τ : Pair I J T) (U : Scheme.{0}) (s t st : ℤ) (h1 : s + t = st) (a : Sec (I.X s) U)
    (b : Sec (J.X t) U) :
    τ.lift U st (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b)) =
      τ.mul U s t st h1 a b := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

noncomputable def Bp (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w)
    (p : {p : ℤ × ℤ // p.1 + p.2 = st}) :
    Sec (I.X p.1.1) V →ₗ[ULift.{1} R] Sec (J.X p.1.2) V →ₗ[ULift.{1} R] (Sec (K.X u) V →ₗ[ULift.{1} R] Sec (L.X w) V) :=
  LinearMap.mk₂ (ULift.{1} R)
    (fun a b => (ν'.mul V p.1.1 (p.1.2 + u) w (by have := p.2; omega) a) ∘ₗ (μ'.mul V p.1.2 u (p.1.2 + u) rfl b))
    (fun a a' b => LinearMap.ext fun c => by simp)
    (fun r a b => LinearMap.ext fun c => by simp)
    (fun a b b' => LinearMap.ext fun c => by simp)
    (fun r a b => LinearMap.ext fun c => by simp)

noncomputable def B (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) :
    Tens I J V st →ₗ[ULift.{1} R] (Sec (K.X u) V →ₗ[ULift.{1} R] Sec (L.X w) V) :=
  DirectSum.toModule _ _ _ fun p => TensorProduct.lift (Bp μ' ν' V st u w h2 p)

lemma B_single (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (s t st u w : ℤ) (h1 : s + t = st)
    (h2 : st + u = w) (a : Sec (I.X s) V) (b : Sec (J.X t) V) (c : Sec (K.X u) V) :
    B μ' ν' V st u w h2 (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b)) c =
      ν'.mul V s (t + u) w (by omega) a (μ'.mul V t u (t + u) rfl b c) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [B, Bp, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.mk₂_apply, LinearMap.comp_apply]

lemma B_res (μ' : Pair J K M) (ν' : Pair I M L) {W V : Scheme.{0}} (k : W ⟶ V) (st u w : ℤ) (h2 : st + u = w)
    (x : Tens I J V st) (c : Sec (K.X u) V) :
    Sec.res k (B μ' ν' V st u w h2 x c) = B μ' ν' W st u w h2 (Tens.res k st x) (Sec.res k c) := by
  induction x using DirectSum.induction_on with
  | zero => simp [Sec.res]
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp [Sec.res]
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [B, Bp, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.map_tmul,
        TensorProduct.lift.tmul, LinearMap.mk₂_apply, LinearMap.comp_apply]
      rw [ν'.nat, μ'.nat]
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']
  | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx']

end

section
variable {I J K T M L : Cx R}

lemma B_wd (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    {V : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} {x y : Tens I J V st} (c : Sec (K.X u) V)
    (h : τ.lift V st x = τ.lift V st y) : B μ' ν' V st u w h2 x c = B μ' ν' V st u w h2 y c := by
  have h0 : τ.lift V st (x - y) = 0 := by rw [map_sub, h, sub_self]
  refine (hg R (L.X w) V).1 _ _ (loc_mono (hτ.2 V st (x - y) h0) fun W k hk => ?_)
  rw [map_sub, sub_eq_zero] at hk
  rw [B_res, B_res, hk]

lemma exists_m (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    ∃ m0 : Sec (L.X w) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : Tens I J V st), τ.lift V st x = Sec.res g a →
      Sec.res g m0 = B μ' ν' V st u w h2 x (Sec.res g c) := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U st a
  obtain ⟨m0, hm0⟩ := (hg R (L.X w) U).2 S hS
    (fun V g hg' => B μ' ν' V st u w h2 (hP V g hg').choose (Sec.res g c)) (by
      intro V W g k hg'
      rw [B_res, res_comp k g c]
      apply B_wd hg τ hτ μ' ν'
      rw [lift_res, (hP V g hg').choose_spec, (hP W (k ≫ g) (S.downward_closed hg' k)).choose_spec, res_comp])
  refine ⟨m0, fun V g x hx => ?_⟩
  apply (hg R (L.X w) V).1
  refine loc_mono (loc_pull g (P := fun W h => S.arrows h) ⟨S, hS, fun _ _ h => h⟩) fun W k hk => ?_
  rw [← res_comp, hm0 W (k ≫ g) hk, B_res, ← res_comp]
  apply B_wd hg τ hτ μ' ν'
  rw [lift_res, (hP W (k ≫ g) hk).choose_spec, hx, res_comp]

noncomputable def mraw (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) (a : Sec (T.X st) U) (c : Sec (K.X u) U) : Sec (L.X w) U :=
  (exists_m hg τ hτ μ' ν' U st u w h2 a c).choose

variable (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)

lemma res_mraw_eq_of_lift {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c : Sec (K.X u) U)
    {V : Scheme.{0}} (g : V ⟶ U) (x : Tens I J V st) (hx : τ.lift V st x = Sec.res g a) :
    Sec.res g (mraw hg τ hτ μ' ν' U st u w h2 a c) = B μ' ν' V st u w h2 x (Sec.res g c) :=
  (exists_m hg τ hτ μ' ν' U st u w h2 a c).choose_spec V g x hx

lemma mraw_add_a {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a a' : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (a + a') c = mraw hg τ hτ μ' ν' U st u w h2 a c + mraw hg τ hτ μ' ν' U st u w h2 a' c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (loc_inter (hτ.1 U st a) (hτ.1 U st a')) fun V g hV => ?_
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := hV
  rw [res_add, res_mraw_eq_of_lift hg τ hτ μ' ν' (a + a') c g (x + x') (by rw [map_add (f := _), hx, hx', res_add]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a' c g x' hx', map_add, LinearMap.add_apply]

lemma mraw_smul_a {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (r : ULift.{1} R) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (r • a) c = r • mraw hg τ hτ μ' ν' U st u w h2 a c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_smul, res_mraw_eq_of_lift hg τ hτ μ' ν' (r • a) c g (r • x) (by rw [map_smul, hx, res_smul]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, map_smul, LinearMap.smul_apply]

lemma mraw_add_c {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c c' : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 a (c + c') = mraw hg τ hτ μ' ν' U st u w h2 a c + mraw hg τ hτ μ' ν' U st u w h2 a c' := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_add, res_mraw_eq_of_lift hg τ hτ μ' ν' a (c + c') g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx,
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c' g x hx, res_add, map_add]

lemma mraw_smul_c {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (r : ULift.{1} R) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 a (r • c) = r • mraw hg τ hτ μ' ν' U st u w h2 a c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_smul, res_mraw_eq_of_lift hg τ hτ μ' ν' a (r • c) g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, res_smul, map_smul]

lemma mraw_nat {V U : Scheme.{0}} (g' : V ⟶ U) {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    Sec.res g' (mraw hg τ hτ μ' ν' U st u w h2 a c) = mraw hg τ hτ μ' ν' V st u w h2 (Sec.res g' a) (Sec.res g' c) := by
  apply (hg R (L.X w) V).1
  refine loc_mono (hτ.1 V st (Sec.res g' a)) fun W k hW => ?_
  obtain ⟨x, hx⟩ := hW
  rw [← res_comp, res_mraw_eq_of_lift hg τ hτ μ' ν' a c (k ≫ g') x (by rw [hx, res_comp]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' (Sec.res g' a) (Sec.res g' c) k x hx, res_comp]

lemma mraw_eq (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu)
    (h4 : s + tu = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c) := by
  subst h3
  have h := res_mraw_eq_of_lift hg τ hτ μ' ν' (h2 := h2) (τ.mul U s t st h1 a b) c (𝟙 U)
    (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b))
    (by rw [lift_single, res_id])
  rw [res_id, res_id] at h
  rw [h, B_single]

noncomputable def mfam (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) :
    Sec (T.X st) U →ₗ[ULift.{1} R] Sec (K.X u) U →ₗ[ULift.{1} R] Sec (L.X w) U :=
  LinearMap.mk₂ (ULift.{1} R) (mraw hg τ hτ μ' ν' U st u w h2)
    (mraw_add_a hg τ hτ μ' ν') (mraw_smul_a hg τ hτ μ' ν') (mraw_add_c hg τ hτ μ' ν') (mraw_smul_c hg τ hτ μ' ν')

end

end LateralTheory.EtaleFoundations.TensTriFamPf


open LateralTheory.EtaleFoundations.TensTriFamPf in
theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_family_of_gluing (hglue : SecGlue) : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists := by
  intro R _ I J K T τ hτ M L μ' ν'
  refine ⟨fun U st u w h2 => mfam hglue τ hτ μ' ν' U st u w h2, ?_, ?_⟩
  · intro V U g s t w h a b
    exact mraw_nat hglue τ hτ μ' ν' g a b
  · intro U s t u st tu w h1 h2 h3 h4 a b c
    exact mraw_eq hglue τ hτ μ' ν' U s t u st tu w h1 h2 h3 h4 a b c
end

module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionEndomorphismGraphOfTorsionAction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftOfUniqueOfSimilitude
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.ZV GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.GraphCut

abbrev graphLB {X : Scheme.{0}} (L : LB X) (f : X ⟶ X) (N : ℕ) : LB X :=
  LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]

theorem cls_graphLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : X ⟶ X) (N : ℕ) (h : (graphLB L f N).IsLB) :
    cls _ h = N • cls L hL + N • pull f (cls L hL) := by
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp [pull_id]

theorem unitS_spMap {o K : Type} [CommRing o] [CommRing K] (β : o →+* K) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  exact (congrArg (fun φ => φ.hom (u : o)) h).symm

theorem vol_inv (H1 : Out.Laws) (H2 : Out.Laws2) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ)
    (hN : 1 ≤ N) :
    SymB (graphLB P.L ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left N) ∧
      ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (graphLB P.L ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left N) e) ((N * 2) ^ P.g * e ^ P.g) := by
  have hi : ((𝟙 P.A)⁻¹ : P.A ⟶ P.A) = GrpObj.inv := by rw [Hom.inv_def, Category.id_comp]
  rw [hi]
  have hs : cls P.L P.isLB = pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) :=
    (cls_eq_iff P.isLB (pull_isLB P.isLB _)).2 (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample H1 H2 K P).2.2.1
  have hB : (graphLB P.L (GrpObj.inv : P.A ⟶ P.A).left N).IsLB := LB.isLB_linComb P.isLB _ _
  have hc := cls_graphLB P.isLB _ N hB
  rw [← hs] at hc
  refine ⟨(cls_eq_iff hB (pull_isLB hB _)).1 ?_, fun e he => ?_⟩
  · rw [cls_pull hB, hc, map_add (f := _), map_nsmul, ← hs]
  · have h0 : SectionsHaveFiniteDimension P.A.hom (lbPow P.L (N * 2 * e)) ((N * 2 * e) ^ P.g) :=
      GlobalTheory.PowSec.exists_basis_sections H1.globalSectionsRank K P (N * 2 * e) (Nat.succ_le_of_lt (by positivity))
    rw [← mul_pow]
    have h1 : (lbPow P.L (N * 2 * e)).IsLB := LB.isLB_linComb P.isLB _ _
    have h2 : (lbPow (graphLB P.L (GrpObj.inv : P.A ⟶ P.A).left N) e).IsLB := LB.isLB_linComb hB _ _
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ h1).2.1 _ h2 ((cls_eq_iff h1 h2).1 ?_)).1 _ h0
    rw [cls_lbPow P.isLB, cls_lbPow hB, hc, ← add_nsmul, smul_smul]
    congr 1
    ring

theorem exists_vol (H1 : Out.Laws) (H2 : Out.Laws2) (g : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (κ N l m k : ℕ) (hk : k = l ^ m) (hm : m ≠ 0) (hN : 1 ≤ N) (hl : l.Prime) (hlt : (N * (1 + κ)) ^ (2 * g) < k)
    (o : Type) [CommRing o] (b : TBase o k) (i : Option J) :
    ∃ δ ≤ (N * (2 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g k J b (spMap β))
      (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → TorsBasis t.A k t.pt →
      SymB (graphLB t.L f.left N) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension t.A.hom (lbPow (graphLB t.L f.left N) e) (δ * e ^ g) := by
  subst hk
  cases i with
  | none =>
    refine ⟨(N * 2) ^ g, Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _, ?_⟩
    intro K _ _ β t f _ hf _
    subst hf
    exact vol_inv H1 H2 K t.pol N hN
  | some i =>
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.T.hilbertFunction_endomorphismGraph_of_torsionAction H1 H2 g N κ l m ((Mat i).map (Int.cast : ℤ → ZMod (l ^ m))) hN hl hlt
    refine ⟨δ, hδ.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) _), ?_⟩
    intro K _ _ β t f hS hf hT
    subst hf
    have hl0 : (l : K) ≠ 0 := by
      have := (b.unit.map β).ne_zero
      rw [map_natCast, Nat.cast_pow] at this
      exact fun h => this (by rw [h, zero_pow hm])
    refine H K t.pol t.pt (Units.map β.toMonoidHom b.ζ) (t.act i) rfl hl0
      (IsPrimitiveRoot.coe_units_iff.1 (b.prim K β)) hT (fun a a' => ?_) (t.hom i) ⟨hT.pos, (hS i).1⟩ (hS i).2
    have := t.pairing a a'
    rw [unitS_spMap] at this
    have e : unitOn ((Units.map β.toMonoidHom b.ζ) ^ Out.stdSymp g a a') =
      unitOn (Units.map β.toMonoidHom b.ζ) ^ Out.stdSymp g a a' := map_zpow (Units.map _) _ _
    rw [e]
    exact this

theorem lift_left_eq {S : Scheme.{0}} {A : Over S} [IsIso (snd (Over.mk (𝟙 S)) A).left] (y : Over.mk (𝟙 S) ⟶ A) :
    y.left ≫ inv (snd (Over.mk (𝟙 S)) A).left = (lift (𝟙 (Over.mk (𝟙 S))) y).left := by
  rw [IsIso.comp_inv_eq, ← Over.comp_left, lift_snd]

theorem pow_comp_graph {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Option J) {T : Over S} (x : T ⟶ t.A) (m : ℕ) :
    (x ^ m) ≫ i.elim (𝟙 t.A)⁻¹ t.act = (x ≫ i.elim (𝟙 t.A)⁻¹ t.act) ^ m := by
  cases i with
  | none => simp only [Option.elim_none, GrpObj.comp_inv, Category.comp_id, inv_pow]
  | some i =>
    haveI := t.hom i
    exact MonObj.pow_comp x m (t.act i)

theorem cutBy_graphIdeal : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (i : Option J), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p q : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) ∧ SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left (q h)) → CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2) := by
  intro H1 H2 g J _ Mat κ n hn hodd
  have hn2 : 2 ≤ n := hn.two_le
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, Hc⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion H1 H2 g ((n ^ 2) ^ 2 * (2 + κ)) (Ix g ((n ^ 2) ^ 2) × Ix g ((n ^ 2) ^ 2))
  refine ⟨2 + k₀ + ((n ^ 2) ^ 2 * (1 + κ)) ^ (2 * g), fun j hj o _ b i => ?_⟩
  have hjn : j < n ^ j := Nat.lt_pow_self hn2
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (by omega)
  have hdvd2 : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  obtain ⟨δ, hδ, Hv⟩ := exists_vol H1 H2 g J Mat κ ((n ^ 2) ^ 2) n (j * 2) ((n ^ j) ^ 2) (pow_mul n j 2).symm (by omega)
    (Nat.succ_le_of_lt (by positivity)) hn
    (lt_of_lt_of_le (lt_of_le_of_lt (by omega) hjn) (Nat.le_self_pow two_ne_zero _)) o b i
  let c : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ 2) ^ 2) := fun a u => ZMod.castHom hdvd2 (ZMod ((n ^ 2) ^ 2)) (a u)
  have hc : Function.Surjective c := fun a => by
    choose a' ha' using fun u => ZMod.castHom_surjective hdvd2 (a u)
    exact ⟨a', funext ha'⟩
  have hc' : ∀ a a', c a = c a' → ∀ u, (a u).val ≡ (a' u).val [MOD (n ^ 2) ^ 2] := fun a a' h u => by
    have := congrFun h u
    simp only [c, ZMod.castHom_apply, ZMod.cast_eq_val] at this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 this
  obtain ⟨Q, HQ⟩ := Hc δ hδ (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Prod.map c c) (hc.prodMap hc)
  refine ⟨Q, d, fun K _ _ β t σ p q f hS hf hE hpq => ?_⟩
  obtain ⟨hiso, hLB, hVA, hpow, hper, hT, hsurj⟩ := GlobalTheory.T.thetaSections_veryAmple_periodic H1 H2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdvd
    (hn2.trans (Nat.le_self_pow two_ne_zero n)) hE
  obtain ⟨hsym, hH⟩ := Hv K β t f hS hf hT
  have ha₂ : (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left ≫ (fst (Over.mk (𝟙 (Sp K))) t.A).left =
      (fst (Over.mk (𝟙 (Sp K))) t.A).left := by rw [← Over.comp_left, lift_fst]
  have ha₂' : (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left =
      (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ f.left := by rw [← Over.comp_left, lift_snd, Over.comp_left]
  obtain ⟨M, th, hM, hMVA, hMiso, hid, hco, hMper⟩ := GlobalTheory.ZV.GraphSystem.exists_product_system K _ _ _ _ _ (fst (Over.mk (𝟙 (Sp K))) t.A).left _ _ _ _ σ σ
    (𝟙 _) (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left hLB hLB hVA hVA inferInstance (Category.id_comp _) ha₂
  let e : (Over.mk (𝟙 (Sp K)) ⊗ t.A).left ≅ t.A.left := asIso (snd (Over.mk (𝟙 (Sp K))) t.A).left
  have he : e.hom ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    ((Over.w (snd (Over.mk (𝟙 (Sp K))) t.A)).trans (Over.w (fst (Over.mk (𝟙 (Sp K))) t.A)).symm).trans (Category.comp_id _)
  have hB : (graphLB t.L f.left ((n ^ 2) ^ 2)).IsLB := LB.isLB_linComb t.isLB _ _
  have hP : (lbPow t.L ((n ^ 2) ^ 2)).IsLB := LB.isLB_linComb t.isLB _ _
  have c₁ := (cls_eq_iff hLB (pull_isLB hP _)).2 hpow
  rw [cls_pull hP, cls_lbPow t.isLB] at c₁
  have c₂ := (cls_eq_iff (LB.isLB_div hM (pull_isLB hLB _)) (pull_isLB hLB _)).2 hMiso
  rw [cls_div hM (pull_isLB hLB _), cls_pull hLB, cls_pull hLB, pull_id, c₁, ← pull_comp, ha₂', pull_comp,
    sub_eq_iff_eq_add', ← map_add, map_nsmul, ← cls_graphLB t.isLB _ _ hB] at c₂
  have c₃ : cls (M.pull e.inv) (pull_isLB hM _) = cls _ hB := by
    rw [cls_pull hM, c₂, ← pull_comp]
    exact (congrArg (fun φ => pull φ (cls _ hB)) e.inv_hom_id).trans (pull_id _)
  rw [hid, ← he]
  refine HQ K t.pol rfl _ e M th (n ^ j) _ (fun h => t.lab h ^ n ^ j) _ hM ?_ (he ▸ hMVA) ?_ ?_ (by omega) ?_ hsurj ?_
  · refine (cls_eq_iff (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)).1 ?_
    rw [cls_pull (pull_isLB hM _)]
    exact c₃.trans (((cls_eq_iff hB (pull_isLB hB _)).2 hsym).trans (congrArg (pull (GrpObj.inv : t.A ⟶ t.A).left) c₃.symm))
  · intro a a' h
    exact hMper a a' (hper _ _ (hc' _ _ (congrArg Prod.fst h))) (hper _ _ (hc' _ _ (congrArg Prod.snd h)))
  · intro m hm
    have h1 : (lbPow (graphLB t.L f.left ((n ^ 2) ^ 2)) m).IsLB := LB.isLB_linComb hB _ _
    have h2 : (lbPow M m).IsLB := LB.isLB_linComb hM _ _
    have h3 := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ t.A.hom _ h1).2.2.2.2.2 _ e _).1 (hH m hm)
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ (pull_isLB h1 e.hom)).2.1 _ h2 ((cls_eq_iff (pull_isLB h1 _) h2).1 ?_)).1 _ h3
    rw [cls_pull h1, cls_lbPow hB, cls_lbPow hM, map_nsmul, c₂]
    rfl
  · have := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow] at this
    exact fun h => this (by rw [h, zero_pow two_ne_zero])
  · intro h
    have hy : (t.lab h ^ n ^ j).left ≫ e.inv = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left := lift_left_eq _
    have hy' : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left ≫
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left =
        (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hf, pow_comp_graph]
    have := hco K (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) (q h)
      (by rw [Category.comp_id]; exact (hpq h).1) (by rw [hy']; exact (hpq h).2)
    rw [← hy] at this
    exact this

end GlobalTheory.GraphCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (i : Option J), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p q : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) ∧ SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left (q h)) → CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2) := by
  first | exact @GlobalTheory.GraphCut.cutBy_graphIdeal | exact GlobalTheory.GraphCut.cutBy_graphIdeal | (intros; apply GlobalTheory.GraphCut.cutBy_graphIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.StabTame

theorem act_natCast {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) (n : ℕ) :
    a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

theorem exists_geomPoint (S : Scheme.{0}) [Nonempty S] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k), Nonempty (Sp k ⟶ S) := by
  obtain ⟨z⟩ : Nonempty S := inferInstance
  exact ⟨AlgebraicClosure (S.residueField z), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom (algebraMap (S.residueField z) _)) ≫ S.fromSpecResidueField z⟩⟩

theorem iterate_modN {V : Type} [AddCommGroup V] (N : ℕ) (e : LinearMap.BilinForm ℤ V) (P : V → Prop) (g : V →+ V)
    (hg : ∀ v w, (N : ℤ) ∣ e (g v) (g w) - e v w) (hP : ∀ v, P v → ∃ c, g v - v = N • c)
    (hco : ∀ v, (∀ w, P w → (N : ℤ) ∣ e v w) → P v) (v : V) : ∃ c, g^[N] v - v = N • c := by
  have h1 : P (g v - v) := by
    refine hco _ fun w hw => ?_
    obtain ⟨c, hc⟩ := hP w hw
    have e1 : e (g v - v) w = (e (g v) (g w) - e v w) - (N : ℤ) * e (g v) c := by
      have : g w = w + N • c := by rw [← hc]; abel
      rw [this]
      simp only [map_sub, map_add (f := _), map_nsmul, LinearMap.sub_apply, nsmul_eq_mul]
      ring
    rw [e1]
    exact dvd_sub (hg v w) (dvd_mul_right _ _)
  obtain ⟨d, hd⟩ := hP _ h1
  have key : ∀ n : ℕ, ∃ c, g^[n] v = v + n • (g v - v) + N • c := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨g c + n • d, ?_⟩
      have : g (g v - v) = (g v - v) + N • d := by rw [← hd]; abel
      rw [Function.iterate_succ_apply', hc, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, this]
      simp only [nsmul_add, succ_nsmul, smul_comm N n d]
      abel
  obtain ⟨c, hc⟩ := key N
  exact ⟨g v - v + c, by rw [hc, nsmul_add]; abel⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section

variable {B : Type} [CommRing B] {b : Base l B} {U : Scheme.{0}} {s : U ⟶ Sp B}

theorem modN_of_point_eq (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) {a a' : D.La}
    (h : u ≫ (o.etaA a').left = u ≫ (o.etaA a).left) : ∃ c, a' - a = l.A • c := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, -, hA, -⟩ := o.geom k u β.hom hβ.symm
  have h1 : I.ev l.A a' = I.ev l.A a := by
    rw [← hA, ← hA]
    exact Over.OverMorphism.ext h
  have h2 := I.add l.A (a' - a) a
  rw [sub_add_cancel, h1] at h2
  exact (I.ker l.A l.A_pos _).1 (right_eq_mul.1 h2)

theorem isometry_modN (o : Obj D l b s) [Nonempty U] (r : U ⟶ U) (ν : SABMap o.t o.t r) (hr : r ≫ s = s)
    {a a' c c' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    (hc : (o.etaA c').left ≫ ν.φ = r ≫ (o.etaA c).left) : (l.A : ℤ) ∣ D.EF a' c' - D.EF a c := by
  obtain ⟨k, _, _, ⟨u⟩⟩ := exists_geomPoint U
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, hζ, hA, -⟩ := o.geom k u β.hom hβ.symm
  obtain ⟨-, J, hζ', hA', -⟩ := o.geom k (u ≫ r) β.hom (by rw [Category.assoc, hr]; exact hβ.symm)
  have hz : I.ζ l.A = J.ζ l.A := Units.ext (hζ.trans hζ'.symm)
  have hL : LBIso o.t.PP.L (o.t.PP.L.pull ν.φ) := ν.lin.imp fun _ h => h.1
  have mv : ∀ {x x' : D.La}, (o.etaA x').left ≫ ν.φ = r ≫ (o.etaA x).left →
      (J.ev l.A x).left = (I.ev l.A x').left ≫ ν.φ := by
    intro x x' h
    rw [← hA, ← hA']
    show (u ≫ r) ≫ (o.etaA x).left = (u ≫ (o.etaA x').left) ≫ ν.φ
    rw [Category.assoc, Category.assoc, h]
  have w := (weilIs_grpPullback_of_comm U U o.t.G o.t.G r ν.φ o.t.PP.L o.t.PP.L o.t.PP.isLB o.t.PP.isLB ν.cart hL
    (Over.mk u) l.A _ _ (J.ev l.A a) (J.ev l.A c) _ (mv ha) (mv hc)).1 (I.isom l.A l.A_pos a' c')
  have e := weilIs_unique_fieldPoint U o.t.G o.t.PP.L o.t.PP.isLB k (u ≫ r) l.A _ _ _ _ w (J.isom l.A l.A_pos a c)
  rw [hz] at e
  rw [← (J.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, e, mul_inv_cancel]

end

theorem modN_of_extends {B : Type} [CommRing B] {b : Base l B} {X U : Scheme.{0}} [IsReduced X] {s : U ⟶ Sp B}
    (j : U ⟶ X) [IsDominant j] (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j) (hN : IsUnit (l.A : Γ(X, ⊤)))
    (r : U ⟶ U) (ν : SABMap o.t o.t r) (ρ : X ⟶ X) (mu : SABMap t t ρ) (hj : j ≫ ρ = r ≫ j)
    (hφ : μ₀.φ ≫ mu.φ = ν.φ ≫ μ₀.φ) {a a' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    {k : Type} [Field k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x)
    (hfib : pullback.fst t.G.hom x ≫ mu.φ = pullback.fst t.G.hom x)
    (W : X.Opens) (σ : W.toScheme ⟶ t.G.left) (hxW : Set.range x ⊆ W) (hσ : σ ≫ t.G.hom = W.ι)
    (hσj : pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) : ∃ c, a' - a = l.A • c := by
  have pn : IsPullback μ₀.φ o.t.G.hom t.G.hom j := μ₀.cart.1
  have pm : IsPullback mu.φ t.G.hom t.G.hom ρ := mu.cart.1
  have sec : ∀ y : 𝟙_ (Over U) ⟶ o.t.G, y.left ≫ o.t.G.hom = 𝟙 U := fun y => Over.w y
  have ext : ∀ {Z : Scheme.{0}} (w : Z ⟶ W.toScheme) (u : Z ⟶ U), w ≫ W.ι = u ≫ j →
      w ≫ σ = u ≫ (o.etaA a).left ≫ μ₀.φ := by
    intro Z w u h
    have := pullback.lift w u h ≫= hσj
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  let T := pullback W.ι (W.ι ≫ ρ)
  let p₁ : T ⟶ W.toScheme := pullback.fst _ _
  let p₂ : T ⟶ W.toScheme := pullback.snd _ _
  have hp : p₁ ≫ W.ι = p₂ ≫ W.ι ≫ ρ := pullback.condition
  have : IsOpenImmersion p₂ := inferInstanceAs (IsOpenImmersion (pullback.snd W.ι (W.ι ≫ ρ)))
  let i : T ⟶ X := p₂ ≫ W.ι
  have : IsReduced T := isReduced_of_isOpenImmersion i
  have w₂ : (p₁ ≫ σ) ≫ t.G.hom = i ≫ ρ := by rw [Category.assoc, hσ, hp, Category.assoc]
  let σ₁ : T ⟶ t.G.left := p₂ ≫ σ
  let σ₂ : T ⟶ t.G.left := pm.lift (p₁ ≫ σ) i w₂
  have s₁ : σ₁ ≫ t.G.hom = i := by rw [Category.assoc, hσ]
  have s₂ : σ₂ ≫ t.G.hom = i := pm.lift_snd _ _ _
  have s₃ : σ₂ ≫ mu.φ = p₁ ≫ σ := pm.lift_fst _ _ _
  let x₀ : Sp k ⟶ W.toScheme := IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι])
  have hx₀ : x₀ ≫ W.ι = x := IsOpenImmersion.lift_fac _ _ _
  let xT : Sp k ⟶ T := pullback.lift x₀ x₀ (by rw [← Category.assoc, hx₀, hx])
  have x₁ : xT ≫ p₁ = x₀ := pullback.lift_fst _ _ _
  have x₂ : xT ≫ p₂ = x₀ := pullback.lift_snd _ _ _
  have hxT : xT ≫ σ₁ = xT ≫ σ₂ := by
    have w : (xT ≫ σ₂) ≫ t.G.hom = 𝟙 _ ≫ x := by
      rw [Category.assoc, s₂, ← Category.assoc, x₂, hx₀, Category.id_comp]
    have h := pullback.lift (xT ≫ σ₂) (𝟙 _) w ≫= hfib
    rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, s₃, ← Category.assoc, x₁] at h
    rw [← h, ← Category.assoc, x₂]
  let q₁ := pullback.fst i j
  let q₂ := pullback.snd i j
  have hq : q₁ ≫ i = q₂ ≫ j := pullback.condition
  have : IsDominant q₁ := isDominant_pullback_fst_of_isOpenMap j i i.isOpenEmbedding.isOpenMap
  have v₁ : q₁ ≫ σ₁ = q₂ ≫ (o.etaA a).left ≫ μ₀.φ := by
    rw [← Category.assoc]
    exact ext _ _ (by rw [Category.assoc]; exact hq)
  have v₂ : q₁ ≫ σ₂ = q₂ ≫ (o.etaA a').left ≫ μ₀.φ := by
    refine pm.hom_ext ?_ ?_
    · rw [Category.assoc, s₃, Category.assoc, Category.assoc, hφ, reassoc_of% ha, ← Category.assoc,
        ← Category.assoc q₂ r]
      refine ext _ _ ?_
      rw [Category.assoc, hp, Category.assoc, ← hj, ← Category.assoc q₂, ← hq, Category.assoc, Category.assoc]
    · rw [Category.assoc, s₂, hq, Category.assoc, Category.assoc, pn.w, ← Category.assoc (o.etaA a').left, sec]
      exact congrArg (q₂ ≫ ·) (Category.id_comp j).symm
  have tor : ∀ y : D.La, (o.etaA y).left ≫ μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left =
      (1 : 𝟙_ (Over U) ⟶ o.t.G).left ≫ μ₀.φ := by
    intro y
    have h : μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left = (o.t.act.act (l.A : 𝓞 E)).left ≫ μ₀.φ := (μ₀.act _).symm
    rw [h, ← Category.assoc, ← Over.comp_left, act_natCast, MonObj.comp_pow, Category.comp_id,
      ← LiftAut.etaA_nsmul, o.etaA_ker]
  have := t.semi.separated
  have := t.semi.smooth
  have : Etale (t.act.act (l.A : 𝓞 E)).left := by
    rw [act_natCast]
    exact GrpTangent.etale_id_pow t.G hN
  have hmul : σ₁ ≫ (t.act.act (l.A : 𝓞 E)).left = σ₂ ≫ (t.act.act (l.A : 𝓞 E)).left := by
    refine ext_of_isDominant_of_isSeparated t.G.hom ?_ q₁ ?_
    · rw [Category.assoc σ₁, Category.assoc σ₂, Over.w, s₁, s₂]
    · rw [reassoc_of% v₁, reassoc_of% v₂, tor, tor]
  have := isOpenImmersion_equalizer_ι_of_unramified _ hmul
  let e := equalizer.ι σ₁ σ₂
  have he : e ≫ σ₁ = e ≫ σ₂ := equalizer.condition _ _
  have : IsDominant (pullback.fst e q₁) := isDominant_pullback_fst_of_isOpenMap q₁ e e.isOpenEmbedding.isOpenMap
  have : Nonempty ↑(equalizer σ₁ σ₂) := ⟨equalizer.lift xT hxT (⊥ : PrimeSpectrum k)⟩
  have : Nonempty ↑(pullback e q₁) := (pullback.fst e q₁).denseRange.nonempty
  obtain ⟨K, _, _, ⟨y⟩⟩ := exists_geomPoint (pullback e q₁)
  refine modN_of_point_eq o (y ≫ pullback.snd e q₁ ≫ q₂) (pn.hom_ext ?_ ?_)
  · simp only [Category.assoc]
    rw [← v₁, ← v₂, ← pullback.condition_assoc, ← pullback.condition_assoc, he]
  · simp only [Category.assoc]
    rw [sec, sec]

theorem exists_sabMap_iterate (Xo : Moduli D l) (r : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r)
    (hr : r ≫ Xo.s = Xo.s) (h : ∀ x, (Xo.univ.eta x).left ≫ ν.φ = r ≫ (Xo.univ.eta x).left) (g : D.La → D.La)
    (hg : ∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r ≫ (Xo.univ.etaA x).left) (n : ℕ) :
    ∃ (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f), f = (fun f : Xo.X ⟶ Xo.X => f ≫ r)^[n] (𝟙 _) ∧
      f ≫ Xo.s = Xo.s ∧ (∀ x, (Xo.univ.eta x).left ≫ m.φ = f ≫ (Xo.univ.eta x).left) ∧
      ∀ x, (Xo.univ.etaA (g^[n] x)).left ≫ m.φ = f ≫ (Xo.univ.etaA x).left := by
  induction n with
  | zero =>
    obtain ⟨m, hm⟩ := ObjMaps.exists_sab_id Xo.univ.t
    exact ⟨𝟙 _, m, rfl, Category.id_comp _, fun _ => by rw [hm, Category.comp_id, Category.id_comp],
      fun _ => by rw [hm, Category.comp_id, Category.id_comp]; rfl⟩
  | succ n ih =>
    obtain ⟨f, m, hf, hs, h₁, h₂⟩ := ih
    obtain ⟨m', hm⟩ := ObjMaps.exists_sab_comp ν m
    refine ⟨f ≫ r, m', by rw [Function.iterate_succ_apply', ← hf], by rw [Category.assoc, hr, hs], fun x => ?_,
      fun x => ?_⟩
    · rw [hm, reassoc_of% (h₁ x), h, Category.assoc]
    · rw [hm, Function.iterate_succ_apply, reassoc_of% (h₂ (g x)), hg, Category.assoc]

theorem iterate_eq_id_of_fixes_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  intro h₁ h₂ h₃ E _ _ _ H D l Xo S β C r ν ρ mu hinc hS ⟨e, he⟩ hj hφ hr hη g hg k _ _ x hx hfib
  obtain ⟨⟨_, hded⟩, -, hfrac⟩ := (BaseRing.isDedFrac_RZ E H l S e hS he).2.2 β hinc
  letI := β.toAlgebra
  obtain ⟨hnoeth, -, -, hpre, hflat, hdom, hqc⟩ := genericPart_dense_proOpen (RZ H S l.A) (KA l) C.X Xo.X C.s C.jQ
    C.flat C.proj C.jQ_open C.jQ_dense
  have hd : IsDominant C.j := hdom
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  have hN : IsUnit (l.A : Γ(C.X, ⊤)) := by
    have := (hAu.map (Scheme.ΓSpecIso (CommRingCat.of (RZ H S l.A))).inv.hom).map C.s.appTop.hom
    rwa [map_natCast, map_natCast] at this
  have : Nonempty C.X := ⟨x (⊥ : PrimeSpectrum k)⟩
  have : Nonempty Xo.X := C.j.denseRange.nonempty
  have hmod := iterate_modN l.A D.EF _ g.toAddMonoidHom
    (fun v w => isometry_modN Xo.univ r.hom ν hr (hg v) (hg w))
    (fun v ⟨W, σ, hW, hσ, hσj⟩ =>
      modN_of_extends C.j Xo.univ C.t C.m hN r.hom ν ρ.hom mu hj hφ (hg v) x hx hfib W σ hW hσ hσj)
    (GlobalTheory.T.levelLabel_extends_of_orthogonal_to_extended h₁ h₂ h₃ E H D l (KA l) (baseKA l) C.X Xo.X C.j Xo.s Xo.univ C.t C.m C.normal hpre hflat hdom hqc
      hN k x)
  obtain ⟨f, m, hf, hs, e₁, e₂⟩ := exists_sabMap_iterate Xo r.hom ν hr hη g.toAddMonoidHom hg l.A
  rw [← hf]
  refine LiftAut.eq_id Xo f m hs e₁ fun a => ?_
  rw [← e₂, LiftAut.etaA_congr Xo.univ (hmod a)]

end GlobalTheory.StabTame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  first | exact @GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | exact GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | (intros; apply GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre <;> assumption)
end
end

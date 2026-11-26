module

public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvB
variable {R : Type} [CommRing R]

theorem ev_add {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev]

noncomputable def evHom {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (fun α β => ev_add α β p s h U x)

theorem ev_compHom {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp [ev, Cochain.comp_v _ _ (add_zero n) _ s s h (add_zero s)]

theorem isZero_pos {E : Spc} (a : ℤ) (ha : 0 < a) : IsZero (((chains R).obj E).X a) := by
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  change -(j : ℤ) = a at hj
  omega

theorem free_ext {P : PSh} {F : Shv R} (φ ψ : (free R).obj P ⟶ F)
    (hφ : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := hφ U.unop x
  simp only [freeGen] at this
  exact this

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => ModuleCat.Hom.hom f y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) x :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom f y)
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) U x :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) y)
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem chainsXIso_nat {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp [chainsXIso, chains, chainsN, HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f p = -(p:ℤ) from rfl)]
  erw [Iso.inv_hom_id_assoc]
  try rfl

theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have := sec_nat ((chainsXIso R E p).inv ≫ α.v _ _ h) g (freeGen R _ U x)
  rw [freeGen_res] at this
  exact this

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hαβ : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  apply Cochain.ext
  intro a b hab
  by_cases ha : 0 < a
  · exact (isZero_pos a ha).eq_of_src _ _
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k : ℤ) := ⟨(-a).toNat, by omega⟩
  rw [← cancel_epi (chainsXIso R E k).inv]
  exact free_ext _ _ (fun U x => hαβ k b hab U x)

theorem ev_pull {E E' : Spc} {I : Cx R} {n : ℤ} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  have e1 : ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v (-(p:ℤ)) s h =
      ((chains R).map f).f (-(p:ℤ)) ≫ α.v (-(p:ℤ)) s h := by
    rw [Cochain.comp_v _ _ (zero_add n) (-(p:ℤ)) (-(p:ℤ)) s (add_zero _) h, Cochain.ofHom_v]
  unfold ev
  rw [e1, ← Category.assoc, chainsXIso_nat, Category.assoc]
  have := freeGen_map (R := R) (f.app (op (SimplexCategory.mk p))) U x
  simp only [Sec.map] at this
  simp [this, Sx.map]

end LateralTheory.EtaleFoundations.EvB

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleCochainEvaluationLinear := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ?_, fun α p s h V U g x => LateralTheory.EtaleFoundations.EvB.ev_res α p s h V U g x,
    fun α β hαβ => LateralTheory.EtaleFoundations.EvB.ev_ext α β hαβ, fun f α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_pull f α p s h U x,
    fun m α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_compHom m α p s h U x⟩
  have H := LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) (E := E) p s h U x
  exact ⟨map_add (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β, map_sub (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β,
    map_zero (LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) p s h U x), fun c => map_zsmul (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) c α⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.CupflipHomotopyPf
section -- merged from Development.EtaleCohomology.TateTwists.CupflipAwFlipPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def CupflipSteen (h : ∀ N, Pr N →₀ ℤ) : Prop :=
  (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
    ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1)

def cupflip_steen : Prop := ∃ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h

def cupflip_homotopy : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → ν.IsAW hk' β.1 α.1 γ'.1 →
        ∃ η : Cochain ((chains R).obj E) K (k - 1), δ (k - 1) k η = γ.1 - (n * m).negOnePow • γ'.1

theorem cupflip_aw_flip_of (hst : cupflip_steen) (hho : cupflip_homotopy) : cupflip_aw_flip := by
  intro R _ I J K μ ν hflip E n m k h h' α β γ γ' hγ hγ'
  obtain ⟨s, hs⟩ := hst
  obtain ⟨η, hη⟩ := hho s hs R μ ν hflip E h h' α β γ γ' hγ hγ'
  rcases Int.units_eq_one_or ((n * m).negOnePow) with he | he
  · rw [he, one_smul] at hη ⊢
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, hη⟩
  · rw [he, Units.neg_smul, one_smul] at hη ⊢
    rw [← sub_eq_zero, sub_neg_eq_add, ← CohomologyClass.mk_add, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, by rw [hη, sub_neg_eq_add]; rfl⟩

end LateralTheory.EtaleFoundations
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations

def phiT {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (z : Pr N) : Sec (K.X w) U :=
  if h : -((z.1 : ℤ) + (z.2.1 : ℤ)) + k = w then
    ((m * (z.1 : ℤ)).negOnePow : ℤ) • μ.mul U (-(z.1 : ℤ) + n) (-(z.2.1 : ℤ) + m) w (by omega)
      (ev (R := R) α z.1 _ rfl U (x.along z.2.2.1)) (ev (R := R) β z.2.1 _ rfl U (x.along z.2.2.2))
  else 0

def phi {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) : Sec (K.X w) U :=
  c.sum fun z a => a • phiT μ hk α β x w z

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (R := R) (α - β) p s h U x = ev (R := R) α p s h U x - ev (R := R) β p s h U x := by
  simp [ev, Cochain.sub_v, Preadditive.comp_sub]
  rfl

theorem ev_zsmul' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x
    (c : ℤ) : ev (R := R) (c • α) p s h U x = c • ev (R := R) α p s h U x := by
  simp [ev, Cochain.smul_v, Linear.comp_smul]
  rfl

def cupflip_ev_ext : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) → α = β

def cupflip_eta_mk : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), ∀ N s hs U x, ev (R := R) η N s hs U x = phi μ hk α β x s (h N)

def cupflip_eta_delta : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (η : Cochain ((chains R).obj E) K (k - 1)),
    (∀ N s hs U x, ev (R := R) η N s hs U x = phi μ hk α.1 β.1 x s (h N)) →
    ∀ N t ht U x, ev (R := R) (δ (k - 1) k η) N t ht U x =
      (k.negOnePow : ℤ) • (phi μ hk α.1 β.1 x t (Pr.aw N) - phi μ hk α.1 β.1 x t (Pr.wa N))

theorem phi_aw {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (hγ : μ.IsAW hk α β γ) (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U) :
    phi μ hk α β x t (Pr.aw N) = ev (R := R) γ N t ht U x := by
  rw [hγ N t ht U x, phi, Pr.aw, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), one_smul, phiT, dite_eq_left (by have := p.2; push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [Units.smul_def]
  rfl

def cupflip_phi_diag : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)
      (γ' : Cochain ((chains R).obj E) K k), ν.IsAW hk' β α γ' →
      ∀ (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U),
        phi μ hk α β x t (Pr.wa N) = ((n * m).negOnePow : ℤ) • ev (R := R) γ' N t ht U x

theorem cupflip_phi_diag_pf : cupflip_phi_diag := by
  intro R _ I J K μ ν hflip E n m k hk hk' α β γ' hγ' N t ht U x
  rw [hγ' N t ht U x, phi, Pr.wa, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), phiT,
    dite_eq_left (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [hflip U _ _ t (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  simp only [Units.smul_def, smul_smul]
  congr 1
  have e : ((-1 : ℤ) ^ ((p : ℕ) * (N - p))) = (((p : ℕ) : ℤ) * ((N - p : ℕ) : ℤ)).negOnePow := by
    rw [Int.negOnePow_def, ← Nat.cast_mul, zpow_natCast]; simp
  rw [e]
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨m * ((N - p : ℕ) : ℤ) - n * m, by ring⟩

theorem cupflip_homotopy_of (hext : cupflip_ev_ext) (hmk : cupflip_eta_mk) (hdl : cupflip_eta_delta) :
    cupflip_homotopy := by
  intro h hs R _ I J K μ ν hflip E n m k hk hk' α β γ γ' hγ hγ'
  obtain ⟨η, hη⟩ := hmk h hs.1 R μ E hk α.1 β.1
  have hd := hdl h hs R μ E hk α β η hη
  refine ⟨((k.negOnePow : ℤˣ) : ℤ) • η, ?_⟩
  rw [show δ (k - 1) k (((k.negOnePow : ℤˣ) : ℤ) • η) = ((k.negOnePow : ℤˣ) : ℤ) • δ (k - 1) k η from
    (δ_hom ℤ _ _ (k - 1) k).map_smul _ _]
  apply hext R
  intro N t ht U x
  have h1 := phi_aw μ hk α.1 β.1 γ.1 hγ N t ht U x
  have h2 := cupflip_phi_diag_pf R μ ν hflip E hk hk' α.1 β.1 γ'.1 hγ' N t ht U x
  rw [ev_zsmul', hd N t ht U x, h1, h2, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul, Units.smul_def, ev_sub', ev_zsmul']

end LateralTheory.EtaleFoundations
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε],
    (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F

def LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (φ ψ : tw q i ⟶ M),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) → φ = ψ

def LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M], FlatS M

def LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) [Injective M] (U : Scheme.{0}), Module.Injective (ULift.{1} R) (Sec M U)

def LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (N : Type 1) [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N],
    Module.Injective (ULift.{1} (ZMod q)) N → Module.Flat (ULift.{1} (ZMod q)) N

theorem LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective)
    (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) : LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat := by
  intro q _ M _
  refine ⟨M.obj, 𝟙 _, fun U y => ?_, fun U x hx => ?_, fun U _ => hQ q _ (hS _ M U)⟩
  · exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g y, rfl⟩⟩
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩
    have hx0 : x = 0 := hx
    subst hx0
    exact map_zero _

namespace LateralTheory.EtaleFoundations.TwResExt

variable {C : Type*} [Category C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard in
theorem qh_iso {S T : CochainComplex C ℤ} (ε : S ⟶ T) [QuasiIso ε] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ε)) := by
  have : IsIso (DerivedCategory.Q.map ε) := inferInstance
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) ε).2 this

attribute [local instance] HasDerivedCategory.standard in
theorem kinj_lift {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ I) :
    ∃ m : T ⟶ I, Nonempty (Homotopy (ε ≫ m) a) := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).2
    (inv (DerivedCategory.Qh.map (qt.map ε)) ≫ DerivedCategory.Qh.map (qt.map a))
  obtain ⟨m, rfl⟩ := qt.map_surjective g
  refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) I).1
  rw [Functor.map_comp, Functor.map_comp]
  erw [hg]
  exact IsIso.hom_inv_id_assoc _ _

attribute [local instance] HasDerivedCategory.standard in
theorem kinj_uniq {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (m m' : T ⟶ I)
    (h : ε ≫ m = ε ≫ m') : Nonempty (Homotopy m m') := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).1
  rw [← cancel_epi (DerivedCategory.Qh.map (qt.map ε)), ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, h]

theorem homotopy_single_eq {F : C} {I : CochainComplex C ℤ} [I.IsStrictlyGE 0]
    (f g : (CochainComplex.singleFunctor C 0).obj F ⟶ I) (h : Homotopy f g) : f = g := by
  have hz : ∀ i j, h.hom i j = 0 := by
    intro i j
    by_cases hi : i = 0
    · subst hi
      by_cases hr : (ComplexShape.up ℤ).Rel j 0
      · have hj : j < 0 := by simp [ComplexShape.up_Rel] at hr; omega
        exact (I.isZero_of_isStrictlyGE 0 j hj).eq_of_tgt _ _
      · exact h.zero _ _ hr
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  apply HomologicalComplex.hom_ext
  intro n
  rw [h.comm n]
  have : h.hom = 0 := by funext i j; exact hz i j
  simp [this]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem ext_hom_pf : LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => kinj_uniq ε m m' h⟩
  obtain ⟨m, ⟨hm⟩⟩ := kinj_lift ε a
  exact ⟨m, homotopy_single_eq _ _ hm⟩

theorem res_pf : LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties := by
  intro R _ F
  refine ⟨?_, fun n => ?_, ?_, ?_, rfl⟩
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)
  · exact inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  · exact inferInstanceAs (QuasiIso (injectiveResolution F).ι')

end LateralTheory.EtaleFoundations.TwResExt

theorem LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq {S A B C : Type*} [Ring S] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C] (t : A →ₗ[S] B) (f g : B →ₗ[S] C) (x : A) (b : S)
    (h : f (t x) = g (t x)) : f (t (b • x)) = g (t (b • x)) := by
  rw [map_smul, map_smul, map_smul, h]

theorem LateralTheory.EtaleFoundations.TwResExt.twuniq_pf : LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators := by
  intro q _ i M φ ψ h
  apply Sheaf.hom_ext
  refine CategoryTheory.sheafify_hom_ext (J := Scheme.etaleTopology) (P := Scheme.Γ ⋙ twF q i) φ.hom ψ.hom M.property ?_
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_)))
  have h1 := h (unop U) ζ
  change (φ.hom.app U).hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i) |>.app U).hom
      (Submodule.Quotient.mk (Finsupp.single ζ b))) = (ψ.hom.app U).hom ((toSheafify Scheme.etaleTopology
      (Scheme.Γ ⋙ twF q i) |>.app U).hom (Submodule.Quotient.mk (Finsupp.single ζ b)))
  rw [← Finsupp.smul_single_one, Submodule.Quotient.mk_smul]
  exact LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq _ _ _ _ b h1

open LateralTheory.EtaleFoundations.TwResExt in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective) (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) :
    LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  have hF := LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat hS hQ
  have hE := ext_hom_pf
  have hR := res_pf
  have hU := twuniq_pf
  intro q _ i
  obtain ⟨hK, hInj, hGE, hQ, hι⟩ := hR (ZMod q) (tw q i)
  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map ((resAug (tw q i)).f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = resGen i ζ := by
    intro U ζ
    rw [← sec_map_comp, hι]
    rfl
  refine ⟨⟨hGE, resAug _, hQ, hgen⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact hF q _
  · intro T e hT
    obtain ⟨_, ε, hε, he⟩ := hT
    have := hε
    have := hK
    have := hGE
    obtain ⟨hex, huniq⟩ := hE (ZMod q) (tw q i) T (res _ (tw q i)) ε
    refine ⟨?_, ?_⟩
    · obtain ⟨m, hm⟩ := hex (resAug _)
      refine ⟨m, fun U ζ => ?_⟩
      rw [← he, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
      exact hgen U ζ
    · intro u u' h
      apply huniq
      apply HomologicalComplex.from_single_hom_ext
      have hφ : sglι (tw q i) ≫ (ε ≫ u).f 0 = sglι (tw q i) ≫ (ε ≫ u').f 0 := by
        apply hU q i
        intro U ζ
        simp only [sec_map_comp, HomologicalComplex.comp_f]
        have h1 := h U ζ
        rw [← he] at h1
        exact h1
      have hiso : IsIso (sglι (tw q i)) := Iso.isIso_inv _
      exact (cancel_epi (sglι (tw q i))).1 hφ
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKernel
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations

abbrev secF (R : Type) [CommRing R] (U : Scheme.{0}) : Shv R ⥤ Type 1 :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U) ⋙ forget _

lemma etale_sheaf_sections_map_comp_hom {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

lemma etale_sheaf_sections_map_zero_hom {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  simpa [Sec.map, Sec.res] using (NatTrans.naturality_apply φ.hom g.op x).symm

lemma kernel_sec {R : Type} [CommRing R] {F G : Shv R} (g : F ⟶ G) (U : Scheme.{0}) :
    Function.Injective (fun k : Sec (kernel g) U => Sec.map (kernel.ι g) k) ∧
    ∀ b : Sec F U, Sec.map g b = 0 → ∃ k, Sec.map (kernel.ι g) k = b := by
  have w : (secF R U).map (kernel.ι g) ≫ (secF R U).map g = (secF R U).map (kernel.ι g) ≫ (secF R U).map 0 := by
    rw [← (secF R U).map_comp, ← (secF R U).map_comp, kernel.condition, comp_zero]
  have hl : IsLimit (Fork.ofι _ w) := isLimitForkMapOfIsLimit (secF R U) _ (kernelIsKernel g)
  have hu := Types.unique_of_type_equalizer _ _ hl
  have hc : ∀ k : Sec (kernel g) U, Sec.map g (Sec.map (kernel.ι g) k) = 0 := by
    intro k; rw [← etale_sheaf_sections_map_comp_hom, kernel.condition]; rfl
  refine ⟨fun k₁ k₂ h => ?_, fun b hb => ?_⟩
  · obtain ⟨x, -, hx⟩ := hu (Sec.map (kernel.ι g) k₁) ((hc k₁).trans (etale_sheaf_sections_map_zero_hom (G := G) _).symm)
    exact (hx k₁ rfl).trans (hx k₂ h.symm).symm
  · obtain ⟨x, hx, -⟩ := hu b (hb.trans (etale_sheaf_sections_map_zero_hom (G := G) b).symm)
    exact ⟨x, hx⟩

theorem etale_short_complex_exact_iff_locally_surjective_on_kernel : EtaleShortComplexExactIffLocallySurjectiveOnKernel := by
  intro R _ S
  rw [S.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi']
  have hl : ∀ {V : Scheme.{0}} (a : Sec S.X₁ V),
      Sec.map (kernel.ι S.g) (Sec.map (kernel.lift S.g S.f S.zero) a) = Sec.map S.f a := by
    intro V a; rw [← etale_sheaf_sections_map_comp_hom, kernel.lift_ι]
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := (kernel_sec S.g U).2 b hb
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (kernel.lift S.g S.f S.zero).hom (U := op U) k, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hl t, show Sec.map (kernel.lift S.g S.f S.zero) t = Sec.res g k from ht, sec_map_res]
  · intro h
    constructor
    intro U k
    obtain ⟨T, hT, hTa⟩ := h U (Sec.map (kernel.ι S.g) k)
      (by rw [← etale_sheaf_sections_map_comp_hom, kernel.condition]; rfl)
    refine Scheme.etaleTopology.superset_covering ?_ hT
    intro V g hg
    obtain ⟨a, ha⟩ := hTa V g hg
    refine ⟨a, (kernel_sec S.g V).1 ?_⟩
    exact (hl a).trans (ha.trans (sec_map_res _ _ _).symm)

end LateralTheory.EtaleFoundations
end
end

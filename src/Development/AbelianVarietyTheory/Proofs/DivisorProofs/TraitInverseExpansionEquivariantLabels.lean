module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTrait
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitTransport
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.SecMove

section General

variable {X X' B : Scheme.{0}} {L : LB X} {L' : LB X'} {I : Type}

def Intertwine (L : LB X) (L' : LB X') (a : B ⟶ X) (a' : B ⟶ X') (pj : I → L.ι) (pk : I → L'.ι) (V : I → B.Opens)
    (u : ∀ i, Γ(B, V i)ˣ) : Prop :=
  (∀ i b, b ∈ V i → a b ∈ L.U (pj i) ∧ a' b ∈ L'.U (pk i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i i', r z ∈ V i → r z ∈ V i' →
      gm r z (V i) (u i) = gm (r ≫ a) z (L.U (pj i) ⊓ L.U (pj i')) (L.g (pj i) (pj i')) *
        (gm (r ≫ a') z (L'.U (pk i) ⊓ L'.U (pk i')) (L'.g (pk i) (pk i')))⁻¹ * gm r z (V i') (u i')

theorem Intertwine.symm {a : B ⟶ X} {a' : B ⟶ X'} {pj : I → L.ι} {pk : I → L'.ι} {V : I → B.Opens}
    {u : ∀ i, Γ(B, V i)ˣ} (H : Intertwine L L' a a' pj pk V u) : Intertwine L' L a' a pk pj V (fun i => (u i)⁻¹) := by
  refine ⟨fun i b hb => (H.1 i b hb).symm, fun Z r z i i' hi hi' => ?_⟩
  rw [map_inv, map_inv, H.2 Z r z i i' hi hi']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem mem_one {Y : Scheme.{0}} {φ : Y ⟶ X} {y : Y} {j : Fin 1 → L.ι} :
    y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ↔ φ y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by rw [Subsingleton.elim k 0]; exact h⟩

theorem trF_one {Y Z : Scheme.{0}} (φ : Y ⟶ X) (N : ℕ) (r : Z ⟶ Y) (z : Z) (j j' : Fin 1 → L.ι) :
    trF (fun _ : Fin 1 => φ) (fun _ => (N : ℤ)) r z j j' =
      gm (r ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ N := by
  rw [trF, Fin.prod_univ_one, zpow_natCast]

theorem exists_move (hL : L.IsLB) {a : B ⟶ X} {a' : B ⟶ X'} {pj : I → L.ι} {pk : I → L'.ι} {V : I → B.Opens}
    {u : ∀ i, Γ(B, V i)ˣ} (H : Intertwine L L' a a' pj pk V u) (cov : ∀ b, ∃ i, b ∈ V i)
    {T S : Scheme.{0}} (m : T ⟶ B) (k : T ⟶ S) {ψ : T ⟶ X} {ψ' : S ⟶ X'} (hψ : m ≫ a = ψ) (hψ' : m ≫ a' = k ≫ ψ')
    (N : ℕ) (s : SecK L' ψ' N) : ∃ t : SecK L ψ N, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i, m (r z) ∈ V i →
      gs r z (LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => pj i)) (t.f (fun _ => pj i)) =
        (gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i)) := by
  have m₁ : ∀ i (y : T), m y ∈ V i → y ∈ LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => pj i) := fun i y hy => by
    rw [mem_one, ← hψ]; exact (H.1 i _ hy).1
  have m₂ : ∀ i (y : T), m y ∈ V i → k y ∈ LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i) := fun i y hy => by
    rw [mem_one]
    have := (H.1 i _ hy).2
    rwa [show a' (m y) = ψ' (k y) from congrArg (fun q => q y) hψ'] at this
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i i', m (r z) ∈ V i → m (r z) ∈ V i' →
      (gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i)) =
      (trF (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ)) r z (fun _ => pj i) (fun _ => pj i')).val *
        ((gm (r ≫ m) z (V i') (u i') ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i')) (s.f (fun _ => pk i'))) := by
    intro Z r z i i' hi hi'
    rw [sec_trans s (r ≫ k) z (m₂ i _ hi) (m₂ i' _ hi'), trF_one, trF_one, H.2 Z (r ≫ m) z i i' hi hi',
      Category.assoc, Category.assoc, Category.assoc, hψ, hψ', ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul, ← mul_pow, ← mul_pow, mul_right_comm, inv_mul_cancel_right]
  have glue : ∀ p : Fin 1 → L.ι, ∃ t : Γ(T, LB.wchart L (fun _ : Fin 1 => ψ) p), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i,
      r z ∈ LB.wchart L (fun _ : Fin 1 => ψ) p → m (r z) ∈ V i →
      gs r z _ t = (trF (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ)) r z p (fun _ => pj i)).val *
        ((gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i))) := by
    intro p
    let W : I → T.Opens := fun i => LB.wchart L (fun _ : Fin 1 => ψ) p ⊓ m ⁻¹ᵁ V i
    have l₁ : ∀ i, W i ≤ LB.wchart L (fun _ : Fin 1 => ψ) p ⊓ LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => pj i) :=
      fun i y hy => ⟨hy.1, m₁ i y hy.2⟩
    have l₂ : ∀ i, W i ≤ k ⁻¹ᵁ LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i) := fun i y hy => m₂ i y hy.2
    obtain ⟨v, hv⟩ : ∃ v : ∀ i, Γ(T, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i, r z ∈ W i →
        gs r z (W i) (v i) = (trF (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ)) r z p (fun _ => pj i)).val *
        ((gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i))) :=
      ⟨fun i => (res (l₁ i) ((LB.LinComb L (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ))).g p (fun _ => pj i))).val *
          ((res (inf_le_right : W i ≤ m ⁻¹ᵁ V i) (pullU m _ (u i)) ^ N).val *
            (T.presheaf.map (homOfLE (l₂ i)).op).hom ((k.app _).hom (s.f (fun _ => pk i)))),
        fun Z r z i hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val ((gm_res r z _ hz _).trans
            (gm_linComb L _ _ r z _ _ (l₁ i hz).1 (l₁ i hz).2))))
          ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
            ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_pow _ _ _).trans (congrArg (· ^ N)
              ((gm_res r z _ hz _).trans (gm_pull r m z _ hz.2 _))))))
            ((gs_res r z (l₂ i) hz _).trans (gs_pull r k z _ (l₂ i hz) _)))))⟩
    obtain ⟨t, ht, -⟩ := T.sheaf.existsUnique_gluing' W (LB.wchart L (fun _ : Fin 1 => ψ) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := cov (m y)
        exact Opens.mem_iSup.2 ⟨i, hy, hi⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 T) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 T) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, key _ (𝟙 T) y q q' hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          trF_trans hL _ _ (𝟙 T) y hy.1.1 (l₁ q hy.1).2 (l₁ q' hy.2).2])
    refine ⟨t, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz t).symm.trans ((congrArg (gs r z (W q)) (ht q)).trans (hv Z r z q hz))
  choose t ht using glue
  refine ⟨⟨t, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i hi => ?_⟩
  · obtain ⟨i, hi⟩ := cov (m y)
    refine (gs_res (𝟙 T) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 T) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 T) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 T) y j j' hy.1 hy.2)))
      (gs_res (𝟙 T) y _ hy _))).symm)
    refine (ht j _ (𝟙 T) y i hy.1 hi).trans (Eq.trans ?_ (congrArg _ (ht j' _ (𝟙 T) y i hy.2 hi)).symm)
    rw [← trF_trans hL _ _ (𝟙 T) y hy.1 hy.2 (m₁ i y hi), Units.val_mul, _root_.mul_assoc]; rfl
  · refine (ht _ Z r z i (m₁ i _ hi) hi).trans ?_
    rw [trF_self hL _ _ r z (m₁ i _ hi), Units.val_one, _root_.one_mul]

theorem exists_transport (hL : L.IsLB) (hL' : L'.IsLB) {Y : Scheme.{0}} (f : B ⟶ Y) [IsIso f] {φ : Y ⟶ X} {φ' : B ⟶ X'}
    {pj : I → L.ι} {pk : I → L'.ι} {V : I → B.Opens} {u : ∀ i, Γ(B, V i)ˣ} (H : Intertwine L L' (f ≫ φ) φ' pj pk V u)
    (cov : ∀ b j k, φ (f b) ∈ L.U j → φ' b ∈ L'.U k → ∃ i, pj i = j ∧ pk i = k ∧ b ∈ V i) (N : ℕ) :
    ∃ Tr : SecK L' φ' N → SecK L φ N, Function.Bijective Tr ∧
      (∀ σ σ' σ'' : SecK L' φ' N, (∀ i, σ''.f i = σ.f i + σ'.f i) → ∀ i, (Tr σ'').f i = (Tr σ).f i + (Tr σ').f i) ∧
      (∀ (e : Γ(Y, ⊤)) (σ σ' : SecK L' φ' N),
        (∀ i, σ'.f i = (B.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom e) * σ.f i) →
        ∀ i, (Tr σ').f i = (Y.presheaf.map (homOfLE le_top).op).hom e * (Tr σ).f i) ∧
      ∀ (σ : SecK L' φ' N) (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i →
        gs (r ≫ f) z (LB.wchart L (fun _ : Fin 1 => φ) (fun _ => pj i)) ((Tr σ).f (fun _ => pj i)) =
          (gm r z (V i) (u i) ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => φ') (fun _ => pk i)) (σ.f (fun _ => pk i)) := by
  have cov₀ : ∀ b, ∃ i, b ∈ V i := fun b => by
    obtain ⟨j, hj⟩ := exists_chart hL (φ (f b))
    obtain ⟨k, hk⟩ := exists_chart hL' (φ' b)
    obtain ⟨i, -, -, hi⟩ := cov b j k hj hk
    exact ⟨i, hi⟩
  have fi : ∀ b : B, (inv f) (f b) = b := fun b => congrArg (fun q => q b) (IsIso.hom_inv_id f)
  have fi' : ∀ y : Y, f ((inv f) y) = y := fun b => congrArg (fun q => q b) (IsIso.inv_hom_id f)
  choose Tr hT using fun σ : SecK L' φ' N => exists_move hL H cov₀ (inv f) (inv f) (ψ := φ) (ψ' := φ')
    (IsIso.inv_hom_id_assoc f φ) rfl N σ
  have hT' : ∀ (σ : SecK L' φ' N) (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i →
        gs (r ≫ f) z (LB.wchart L (fun _ : Fin 1 => φ) (fun _ => pj i)) ((Tr σ).f (fun _ => pj i)) =
          (gm r z (V i) (u i) ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => φ') (fun _ => pk i)) (σ.f (fun _ => pk i)) := by
    intro σ Z r z i hi
    have := hT σ Z (r ≫ f) z i (by show (inv f) (f (r z)) ∈ V i; rw [fi]; exact hi)
    rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this
  have ext : ∀ (J : Fin 1 → L.ι) (s t : Γ(Y, LB.wchart L (fun _ : Fin 1 => φ) J)),
      (∀ (y : Y) i, (fun _ => pj i) = J → (inv f) y ∈ V i → gs (inv f ≫ f) y _ s = gs (inv f ≫ f) y _ t) → s = t := by
    intro J s t h
    refine fn_ext fun y hy => ?_
    obtain ⟨k, hk⟩ := exists_chart hL' (φ' (inv f y))
    obtain ⟨i, e, -, hi⟩ := cov (inv f y) (J 0) k (by rw [fi']; exact mem_one.1 hy) hk
    have := h y i (funext fun a => by rw [e, Subsingleton.elim a 0]) hi
    rwa [IsIso.inv_hom_id] at this
  have m₁ : ∀ i (y : Y), (inv f) y ∈ V i → (inv f ≫ f) y ∈ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => pj i) :=
    fun i y hy => mem_one.2 (H.1 i _ hy).1
  have m₂ : ∀ i (b : B), b ∈ V i → b ∈ LB.wchart L' (fun _ : Fin 1 => φ') (fun _ => pk i) :=
    fun i y hy => mem_one.2 (H.1 i _ hy).2
  have sx : ∀ {T : Scheme.{0}} {M : LB T} (s t : LB.Sec M), s.f = t.f → s = t := by
    rintro T M ⟨s, _⟩ ⟨t, _⟩ h
    cases h; rfl
  refine ⟨Tr, ⟨fun σ σ' e => sx _ _ (funext fun J => fn_ext fun b hb => ?_), fun τ => ?_⟩,
    fun σ σ' σ'' h J => ext J _ _ ?_, fun e σ σ' h J => ext J _ _ ?_, hT'⟩
  · obtain ⟨j, hj⟩ := exists_chart hL (φ (f b))
    obtain ⟨i, -, ek, hi⟩ := cov b j (J 0) hj (mem_one.1 hb)
    obtain rfl : (fun _ => pk i) = J := funext fun a => by rw [ek, Subsingleton.elim a 0]
    have h₁ := hT' σ _ (𝟙 B) b i hi
    rw [e, hT' σ' _ (𝟙 B) b i hi] at h₁
    exact ((Units.mul_right_inj _).1 h₁).symm
  · obtain ⟨σ, hσ⟩ := exists_move hL' H.symm cov₀ (𝟙 B) f (ψ := φ') (ψ' := φ) (Category.id_comp _)
      (Category.id_comp _) N τ
    refine ⟨σ, sx _ _ (funext fun J => ext J _ _ ?_)⟩
    rintro y i rfl hi
    refine (hT' σ _ (inv f) y i hi).trans ?_
    rw [hσ _ (inv f) y i hi, Category.comp_id, map_inv, inv_pow, Units.mul_inv_cancel_left]
  · rintro y i rfl hi
    refine (hT' σ'' _ (inv f) y i hi).trans (Eq.trans ?_ (gs_add _ y _ (m₁ i y hi) _ _).symm)
    rw [hT' σ _ (inv f) y i hi, hT' σ' _ (inv f) y i hi, ← mul_add]
    exact congrArg _ ((congrArg _ (h _)).trans (gs_add _ y _ (m₂ i _ hi) _ _))
  · rintro y i rfl hi
    refine (hT' σ' _ (inv f) y i hi).trans (Eq.trans ?_ (gs_mul _ y _ (m₁ i y hi) _ _).symm)
    rw [hT' σ _ (inv f) y i hi, mul_left_comm]
    refine congrArg _ ((congrArg _ (h _)).trans ((gs_mul _ y _ (m₂ i _ hi) _ _).trans (congrArg₂ (· * ·) ?_ rfl)))
    exact (gs_res _ y _ (m₂ i _ hi) _).trans ((gs_pull (inv f) f y ⊤ trivial e).trans (gs_res _ y _ (m₁ i y hi) _).symm)

theorem exists_chain {XA XP XG XK Xt : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {Lt : LB Xt}
    {α : XA ⟶ XP} {β : XG ⟶ XP} {π : XK ⟶ XG} {gn : XK ⟶ Xt} {wA : LB.Iso LA (LP.pull α)} {ℓ : LB.Iso LG (LP.pull β)}
    {w₀ : LB.Iso (Lt.pull gn) (LG.pull π)} (hA : PGen wA) (hℓ : PGen ℓ) (h₀ : PGen w₀) (a : B ⟶ XA) (g : B ⟶ XK)
    (a' : B ⟶ Xt) (hgn : g ≫ gn = a') (hc : a ≫ α = g ≫ π ≫ β) :
    ∃ (V : LA.ι × LP.ι × LG.ι × Lt.ι → B.Opens) (u : ∀ i, Γ(B, V i)ˣ),
      Intertwine LA Lt a a' (fun i => i.1) (fun i => i.2.2.2) V u ∧
      (∀ i b, b ∈ V i ↔ a b ∈ LA.U i.1 ∧ α (a b) ∈ LP.U i.2.1 ∧ π (g b) ∈ LG.U i.2.2.1 ∧ a' b ∈ Lt.U i.2.2.2) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i → gm r z (V i) (u i) =
        (gw wA (r ≫ a) z i.2.1 i.1)⁻¹ * (gw ℓ (r ≫ g ≫ π) z i.2.1 i.2.2.1 * gw w₀ (r ≫ g) z i.2.2.1 (fun _ => i.2.2.2)) := by
  subst hgn
  have pc : ∀ b, α (a b) = β (π (g b)) := fun b => congrArg (fun q => q b) hc
  obtain ⟨V, hV⟩ : ∃ V : LA.ι × LP.ι × LG.ι × Lt.ι → B.Opens, ∀ i b,
      b ∈ V i ↔ a b ∈ LA.U i.1 ∧ α (a b) ∈ LP.U i.2.1 ∧ π (g b) ∈ LG.U i.2.2.1 ∧ (g ≫ gn) b ∈ Lt.U i.2.2.2 :=
    ⟨fun i => a ⁻¹ᵁ LA.U i.1 ⊓ (a ⁻¹ᵁ (α ⁻¹ᵁ LP.U i.2.1) ⊓ (g ⁻¹ᵁ (π ⁻¹ᵁ LG.U i.2.2.1) ⊓ (g ≫ gn) ⁻¹ᵁ Lt.U i.2.2.2)),
      fun _ _ => Iff.rfl⟩
  have l₁ : ∀ i, V i ≤ a ⁻¹ᵁ ((LP.pull α).U (fun _ => i.2.1) ⊓ LA.U i.1) := fun i x hx =>
    ⟨mem_pull.2 ((hV i x).1 hx).2.1, ((hV i x).1 hx).1⟩
  have l₂ : ∀ i, V i ≤ (g ≫ π) ⁻¹ᵁ ((LP.pull β).U (fun _ => i.2.1) ⊓ LG.U i.2.2.1) := fun i x hx =>
    ⟨mem_pull.2 (by have := ((hV i x).1 hx).2.1; rw [pc] at this; exact this), ((hV i x).1 hx).2.2.1⟩
  have l₃ : ∀ i, V i ≤ g ⁻¹ᵁ ((LG.pull π).U (fun _ => i.2.2.1) ⊓ (Lt.pull gn).U (fun _ => i.2.2.2)) := fun i x hx =>
    ⟨mem_pull.2 ((hV i x).1 hx).2.2.1, mem_pull.2 ((hV i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(B, V i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i → gm r z (V i) (u i) =
      (gw wA (r ≫ a) z i.2.1 i.1)⁻¹ * (gw ℓ (r ≫ g ≫ π) z i.2.1 i.2.2.1 * gw w₀ (r ≫ g) z i.2.2.1 (fun _ => i.2.2.2)) :=
    ⟨fun i => (res (l₁ i) (pullU a _ (wA.s (fun _ => i.2.1, i.1))))⁻¹ *
        (res (l₂ i) (pullU (g ≫ π) _ (ℓ.s (fun _ => i.2.1, i.2.2.1))) *
          res (l₃ i) (pullU g _ (w₀.s (fun _ => i.2.2.1, fun _ => i.2.2.2)))),
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z (l₁ i) hz _).trans (gm_pull r a z _ (l₁ i hz) _))))
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z (l₂ i) hz _).trans (gm_pull r (g ≫ π) z _ (l₂ i hz) _))
          ((gm_res r z (l₃ i) hz _).trans (gm_pull r g z _ (l₃ i hz) _)))))⟩
  refine ⟨V, u, ⟨fun i b hb => ⟨((hV i b).1 hb).1, ((hV i b).1 hb).2.2.2⟩, fun Z r z i i' hi hi' => ?_⟩, hV, hu⟩
  have e₁ := hA Z (r ≫ a) z i.2.1 i'.2.1 i.1 i'.1 (mem_pull.1 (l₁ i hi).1) (mem_pull.1 (l₁ i' hi').1) (l₁ i hi).2 (l₁ i' hi').2
  have e₂ := hℓ Z (r ≫ g ≫ π) z i.2.1 i'.2.1 i.2.2.1 i'.2.2.1 (mem_pull.1 (l₂ i hi).1) (mem_pull.1 (l₂ i' hi').1)
    (l₂ i hi).2 (l₂ i' hi').2
  have e₃ := h₀ Z (r ≫ g) z i.2.2.1 i'.2.2.1 (fun _ => i.2.2.2) (fun _ => i'.2.2.2) (mem_pull.1 (l₃ i hi).1)
    (mem_pull.1 (l₃ i' hi').1) (l₃ i hi).2 (l₃ i' hi').2
  have e₄ := gm_linComb Lt (fun _ : PUnit => gn) (fun _ => 1) (r ≫ g) z (fun _ => i.2.2.2) (fun _ => i'.2.2.2)
    (l₃ i hi).2 (l₃ i' hi').2
  rw [Fintype.prod_unique, zpow_one, Category.assoc] at e₄
  replace e₃ := e₃.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (congrArg (·⁻¹) e₄)) rfl)
  simp only [Category.assoc] at e₁ e₂ e₃
  rw [hc] at e₁
  rw [hu Z r z i hi, hu Z r z i' hi', e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end General

theorem exists_trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∃ Tr : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j), Function.Bijective Tr ∧ (∀ σ σ' σ'' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ i, σ''.f i = σ.f i + σ'.f i) → ∀ i, (Tr σ'').f i = (Tr σ).f i + (Tr σ').f i) ∧ (∀ (c : F) (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)), (∀ i, σ'.f i = liftFun T.A.A _ (fnF (R := W) F c) * σ.f i) → ∀ i, (Tr σ').f i = liftFun C.A.A _ (fnF (R := R) F c) * (Tr σ).f i) ∧ ∀ σ : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (Tr σ) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) := by
  intro R _ _ _ _ D C j wA hwA W _ _ _ T F _ _ _ _ _ f _ hf hc w₀ hw₀
  have hg : ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) ≫ T.U.gen.hom.left = (snd (TFK (R := W) F) T.A.A).left := by
    rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id]; exact Category.comp_id _
  obtain ⟨V, u, H, hV, hu⟩ := exists_chain ((isGen_iff _).1 hwA) ((isGen_iff _).1 T.ℓ_gen) ((isGen_iff _).1 hw₀)
    (f ≫ (snd (TFK (R := R) F) C.A.A).left) ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) _ hg
    ((Category.assoc _ _ _).trans (hc.trans (Category.assoc _ _ _).symm))
  obtain ⟨Tr, h₁, h₂, h₃, h₄⟩ := exists_transport C.A.isLB T.A.isLB f H (fun b a t ha ht => by
    obtain ⟨p, hp⟩ := exists_chart C.P.L.isLB (C.α ((f ≫ (snd (TFK (R := R) F) C.A.A).left) b))
    obtain ⟨g, hg⟩ := exists_chart T.U.LG.isLB
      (pullback.fst T.G.hom (jK W) (((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) b))
    exact ⟨(a, p, g, t), rfl, rfl, (hV _ b).2 ⟨ha, hp, hg, ht⟩⟩) (C.n ^ j)
  refine ⟨Tr, h₁, h₂, fun c σ σ' h => h₃ ((fst (TFK (R := R) F) C.A.A).left.appTop.hom (fnF (R := R) F c)) σ σ' (fun i => ?_), ?_⟩
  · refine (h i).trans (congrArg₂ (· * ·) ?_ rfl)
    exact (congrArg (fun q => ((TFK (R := W) F ⊗ T.A.A).left.presheaf.map (homOfLE le_top).op).hom
      (q.appTop.hom (fnF (R := W) F c))) hf).symm
  rintro σ Z p _ q rfl hp hq z JP JA JG Jt hP hA hG ht
  have e₀ : p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β :=
    hp.trans ((Category.assoc _ _ _).trans (congrArg (q ≫ ·) hc))
  obtain rfl : p = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) := by
    refine T.cart.1.hom_ext (by simpa only [Category.assoc] using e₀) (hq.trans ?_)
    have c₁ : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have c₂ : (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F = (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom :=
      pullback.condition
    have c₃ : pullback.fst T.G.hom (jK W) ≫ T.G.hom = pullback.snd T.G.hom (jK W) ≫ jK W := pullback.condition
    simp only [Category.assoc]
    rw [spMap_comp, c₃, reassoc_of% c₁, reassoc_of% c₂]
  have k₁ : (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β =
      q ≫ (f ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α := by
    rw [hp]; simp only [Category.assoc]
  have hi := (hV (JA ((q ≫ f) ≫ (snd (TFK (R := R) F) C.A.A).left), JP ((q ≫ (snd (TFK (R := W) F) T.A.A).left ≫
    T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β), JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫
    T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)), Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) (q z)).2
    ⟨hA _, by rw [k₁]; exact hP _, hG _, ht _⟩
  have e := h₄ σ Z q z _ hi
  rw [hu Z q z _ hi] at e
  refine (congrArg _ e).trans ?_
  simp only [Category.assoc, mul_pow, inv_pow, Units.val_mul]
  rw [_root_.mul_assoc, Units.mul_inv_cancel_left]
  rfl

end GlobalTheory.Mum.SecMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquivPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabMove

theorem exists_mulEquiv_points {S K K' X : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over K} [GrpObj A] {A' : Over K'}
    [GrpObj A'] {g : K ⟶ S} {g' : K' ⟶ S} {α : A.left ⟶ G.left} {α' : A'.left ⟶ G.left}
    (h : IsGrpPullback A G g α) (h' : IsGrpPullback A' G g' α') (t : X ⟶ K) (t' : X ⟶ K')
    (f : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left)
    (hf₁ : f ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left)
    (hf₂ : f ≫ (snd (Over.mk t) A).left ≫ α = (snd (Over.mk t') A').left ≫ α') :
    ∃ e : (Over.mk t' ⟶ A') ≃* (Over.mk t ⟶ A), ∀ x', (e x').left ≫ α = x'.left ≫ α' ∧
      (ptSecT A' x').left ≫ f = (ptSecT A (e x')).left := by
  have s₁ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (fst T Y).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have s₂ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (snd T Y).left = x.left := fun x => by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have w : (snd (Over.mk t) A).left ≫ A.hom = (fst (Over.mk t) A).left ≫ t :=
    (Over.w (snd (Over.mk t) A)).trans (Over.w (fst (Over.mk t) A)).symm
  have w' : (snd (Over.mk t') A').left ≫ A'.hom = (fst (Over.mk t') A').left ≫ t' :=
    (Over.w (snd (Over.mk t') A')).trans (Over.w (fst (Over.mk t') A')).symm
  have hu : t' ≫ g' = t ≫ g := by
    have e := congrArg (fun q => (ptSecT A' (1 : Over.mk t' ⟶ A')).left ≫ q ≫ G.hom) hf₂
    simp only [Category.assoc] at e
    rw [h.1.w, h'.1.w, reassoc_of% w, reassoc_of% w', reassoc_of% hf₁, reassoc_of% (s₁ (1 : Over.mk t' ⟶ A')),
      reassoc_of% (s₁ (1 : Over.mk t' ⟶ A'))] at e
    exact e.symm
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h t (t ≫ g) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h' t' (t ≫ g) hu
  have key : ∀ x', ((e'.trans e.symm) x').left ≫ α = x'.left ≫ α' := fun x' => by
    rw [← he, ← he', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  refine ⟨e'.trans e.symm, fun x' => ⟨key x', ?_⟩⟩
  have a₁ : ((ptSecT A' x').left ≫ f) ≫ (fst (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (fst (Over.mk t) A).left := by
    rw [Category.assoc, hf₁, s₁, s₁]; rfl
  have a₂ : ((ptSecT A' x').left ≫ f) ≫ (snd (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (snd (Over.mk t) A).left := by
    refine h.1.hom_ext ?_ ?_
    · rw [s₂, key, Category.assoc, Category.assoc, hf₂, reassoc_of% (s₂ x')]
    · rw [Category.assoc, w, Category.assoc _ _ A.hom, w, ← Category.assoc, a₁, Category.assoc]
  exact pullback.hom_ext a₁ a₂

end GlobalTheory.Mum.LabMove

namespace GlobalTheory.Mum

theorem Trait.exists_lab_push : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → (∀ x : TFK (R := W) F ⟶ T.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p', lab' p' = x) → ∃ lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A), LabExt em (C.lab j) lab ∧ (∀ x : TFK (R := R) F ⟶ C.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p, lab p = x) ∧ ∀ (p : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), p'.y = T.hD.xe.symm p.y → IsPullGtF T.φ T.hD F p.g p'.g → (ptSecT T.A.A (lab' p')).left ≫ f = (ptSecT C.A.A (lab p)).left := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ _ em hF f _ hf₁ hf₂ lab' hext honto
  have := T.U.gen_hom
  have : IsMonHom T.U.gen.symm.hom := by show IsMonHom T.U.gen.inv; infer_instance
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ) (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((isGrpPullback_of_iso T.U.gen.symm).comp ((isGrpPullback_pullback T.G (jK W)).comp T.cart)).congr
      (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := LabMove.exists_mulEquiv_points C.α_cart gT (jFK (R := R) F) (jFK (R := W) F) f hf₁ hf₂
  let P : QkPt D.toPre F (C.n ^ j) → QkPt T.D'.toPre F (C.n ^ j) :=
    GlobalTheory.ArcPull.pullQk T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hP : ∀ p p', p' = P p ↔ p'.y = T.hD.xe.symm p.y ∧ IsPullGtF T.φ T.hD F p.g p'.g :=
    GlobalTheory.ArcPull.eq_pullQk_iff T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hs : Function.Surjective P :=
    GlobalTheory.ArcPull.pullQk_surjective T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  refine ⟨fun p => e (lab' (P p)), fun p p₁ hp => ?_, fun x => ?_, fun p p' hy hg => ?_⟩
  · refine C.α_cart.1.hom_ext ?_ ?_
    · rw [Category.assoc]
      exact (he _).1.trans (hext p p₁ (P p₁) hp ((hP _ _).1 rfl).1 ((hP _ _).1 rfl).2)
    · rw [Category.assoc, Over.w, Over.w]
      simp only [TFK, Over.mk_hom, jFK]
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
  · obtain ⟨x', rfl⟩ := e.surjective x
    rw [← map_pow, MulEquiv.map_eq_one_iff, honto, hs.exists]
    exact exists_congr fun p => e.injective.eq_iff.symm
  · obtain rfl := (hP p p').2 ⟨hy, hg⟩
    exact (he _).2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hc f hf hfst hα w₀ hw₀ lab' hlab' E' hE'
  obtain ⟨Φ, hΦb, hΦa, hΦs, hΦP, hΦp, hΦf⟩ := GlobalTheory.FamPull.fam_transport R D W T.φ T.D' T.hD F hc (C.n ^ j)
  obtain ⟨lab, hLE, hon, hlr⟩ := GlobalTheory.Mum.Trait.exists_lab_push R hR D C j W T F em hc f hf hfst hα lab' hlab' hE'.onto
  obtain ⟨Tr, hTb, hTa, hTs, hTv⟩ := GlobalTheory.Mum.SecMove.exists_trait_transport R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  have hC2 := GlobalTheory.T.transport_symmetric_lifts_theta_group_trait R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  refine ⟨lab, fun s => Tr (E' (Φ s)), Φ, hLE, ⟨?_, ?_, ?_, hon, ?_, ?_, ?_⟩, hΦP, fun s => hTv (E' (Φ s))⟩
  · exact hTb.comp (hE'.bij.comp hΦb)
  · intro s s' s'' h i
    exact hTa _ _ _ (hE'.add _ _ _ (hΦa s s' s'' h)) i
  · intro c s s' h i
    exact hTs c _ _ (hE'.smul c _ _ (hΦs c s s' h)) i
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hΦf p p' hy hg).1 (hE'.frame p')
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).1 (hE'.lift p')
  · intro p w θ s s' hw hθ hr
    obtain ⟨p', hy, hg⟩ := hΦp p
    obtain ⟨w', hw', hr'⟩ := (hΦf p p' hy hg).2 w hw
    obtain ⟨θ', hθ', hact⟩ := (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).2 θ hθ
    exact hact _ _ _ _ (hTv _) (hTv _) (hE'.act p' w' θ' _ _ hw' hθ' (hr' s s' hr))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_equivariant_bijection_transport_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  first | exact @GlobalTheory.Mum.trait_transport | exact GlobalTheory.Mum.trait_transport | (intros; apply GlobalTheory.Mum.trait_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_comp_tfk {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    spMap em.toRingHom ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := by
  simp only [TFK, Over.mk_hom, jFK]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem Trait.exists_lab_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  intro R _ _ _ hR D C j W _ _ _ T F _ _ _ _ em hF f hfi hf1 hf2
  have : CharZero R := hR.2
  have hN : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have hbij := qkPt_algClosure_bijective R D.toPre F em (C.n ^ j) hN
  have hpull : ∀ p' : QkPt T.D'.toPre F (C.n ^ j), ∃ p₁ : QkPt D.toPre F (C.n ^ j),
      p'.y = T.hD.xe.symm p₁.y ∧ IsPullGtF T.φ T.hD F p₁.g p'.g := fun p' =>
    qkPullExists GlobalTheory.globalFns_holds R W T.φ D.toPre T.D'.toPre T.hD F hF (C.n ^ j) p'
  have huniq : ∀ (p' : QkPt T.D'.toPre F (C.n ^ j)) (p₁ p₂ : QkPt D.toPre F (C.n ^ j)),
      p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g →
      p'.y = T.hD.xe.symm p₂.y → IsPullGtF T.φ T.hD F p₂.g p'.g → p₁ = p₂ :=
    fun p' p₁ p₂ h₁ g₁ h₂ g₂ => GlobalTheory.TorusExt.qk_ext (T.hD.xe.symm.injective (h₁.symm.trans h₂))
      (GlobalTheory.ArcPull.pullGt_unique' T.hD g₁ g₂)
  choose P₁ hP₁ using hpull
  choose P hP using fun p' => (hbij.2 (P₁ p')).exists

  let y : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A) := fun p =>
    Over.homMk (spMap em.toRingHom ≫ (C.lab j p).left) (by
      rw [Category.assoc, Over.w, spMap_comp_tfk])
  let g : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ TFK (R := R) F ⊗ C.A.A) := fun p => lift (𝟙 _) (y p)
  have hg1 : ∀ p, (g p).left ≫ (fst (TFK (R := R) F) C.A.A).left = 𝟙 _ := fun p => by
    rw [← Over.comp_left, lift_fst]; rfl
  have hg2 : ∀ p, (g p).left ≫ (snd (TFK (R := R) F) C.A.A).left = spMap em.toRingHom ≫ (C.lab j p).left := fun p => by
    rw [← Over.comp_left, lift_snd]; rfl
  have hfst : inv f ≫ (fst (TFK (R := W) F) T.A.A).left = (fst (TFK (R := R) F) C.A.A).left := by
    rw [← hf1, IsIso.inv_hom_id_assoc]
  let lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A) := fun p' =>
    Over.homMk ((g (P p')).left ≫ inv f ≫ (snd (TFK (R := W) F) T.A.A).left) (by
      rw [Category.assoc, Category.assoc, Over.w (snd (TFK (R := W) F) T.A.A), ← Over.w (fst (TFK (R := W) F) T.A.A),
        reassoc_of% hfst, reassoc_of% (hg1 (P p'))])
  have heq : ∀ p', (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β =
      spMap em.toRingHom ≫ (C.lab j (P p')).left ≫ C.α := fun p' => by
    simp only [lab', Over.homMk_left, Category.assoc]
    rw [← hf2, IsIso.inv_hom_id_assoc, reassoc_of% (hg2 (P p'))]
  refine ⟨lab', fun p' => T.lab F em hF j (P p') (P₁ p') p' (lab' p') (hP p') (hP₁ p').1 (hP₁ p').2 (heq p'), ?_⟩
  intro p p₁ p' hE hy hgp
  obtain rfl : p₁ = P₁ p' := huniq p' p₁ (P₁ p') hy hgp (hP₁ p').1 (hP₁ p').2
  obtain rfl : p = P p' := (hbij.2 (P₁ p')).unique hE (hP p')
  exact heq p'

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionLabels_genericFibre_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  first | exact @GlobalTheory.Mum.Trait.exists_lab_pull | exact GlobalTheory.Mum.Trait.exists_lab_pull | (intros; apply GlobalTheory.Mum.Trait.exists_lab_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreIsoGenericFibreCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreIsoGenericFibreCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_fibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  intro R _ _ _ _ D C W _ _ _ T F _ _ _ hF

  have hρ : Function.Injective ((algebraMap (FractionRing W) F).comp ((algebraMap W (FractionRing W)).comp T.φ)) :=
    (algebraMap (FractionRing W) F).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
  obtain ⟨ga, hga, hy⟩ := Modif.factor_gp R C.toModif F _ (jFK (R := W) F ≫ jK W ≫ T.ξ) hρ (by
    rw [Category.assoc, Category.assoc, T.ξ_π]
    simp only [jK, jFK, spMap, ← Spec.map_comp]
    rfl)
  have hga' : ga = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (hga r).trans (hF r).symm)
  subst hga'
  have hu : jFK (R := W) F ≫ jK W ≫ T.ξ = jFK (R := R) F ≫ C.gp := hy

  have s₁ : IsPullback (pullback.snd (jFK (R := W) F) T.A.A.hom) (pullback.fst (jFK (R := W) F) T.A.A.hom)
      T.A.A.hom (jFK (R := W) F) := (IsPullback.of_hasPullback _ _).flip
  haveI : IsIso T.U.gen.inv.left := ⟨⟨T.U.gen.hom.left, by rw [← Over.comp_left, T.U.gen.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, T.U.gen.hom_inv_id, Over.id_left]⟩⟩
  have s₂ : IsPullback T.U.gen.inv.left T.A.A.hom (pullback.snd T.G.hom (jK W)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w T.U.gen.inv⟩
  have s₃ : IsPullback (pullback.fst T.G.hom (jK W)) (pullback.snd T.G.hom (jK W)) T.G.hom (jK W) :=
    IsPullback.of_hasPullback _ _
  have hW : IsPullback ((pullback.snd (jFK (R := W) F) T.A.A.hom) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β)
      (pullback.fst (jFK (R := W) F) T.A.A.hom) C.G.hom (jFK (R := R) F ≫ C.gp) := by
    have := ((s₁.paste_horiz s₂).paste_horiz s₃).paste_horiz T.cart.1
    rw [← hu]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using this

  have t₁ : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.A.A.hom (jFK (R := R) F) := (IsPullback.of_hasPullback _ _).flip
  have hR : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom ≫ C.α) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.G.hom (jFK (R := R) F ≫ C.gp) := t₁.paste_horiz C.α_cart.1
  refine ⟨(hW.isoIsPullback _ _ hR).hom, inferInstance, hW.isoIsPullback_hom_snd _ _ hR, ?_⟩
  exact hW.isoIsPullback_hom_fst _ _ hR

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreIsoGenericFibreCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_iso_genericFibre_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  first | exact @GlobalTheory.Mum.Trait.exists_fibre_iso | exact GlobalTheory.Mum.Trait.exists_fibre_iso | (intros; apply GlobalTheory.Mum.Trait.exists_fibre_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantInverseThetaExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantInverseThetaExpansion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_expandsF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  intro R _ _ I hI hC D A G _ _ U hG F _ _ _ N hN w₀ hw₀ lab hlab
  haveI := hC
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have gf : GlobalFnsSt := hL.1.globalFns
  have hN1 : 1 ≤ N := hN.pos
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨b₁, b₂⟩ := hbij F N hN1 w₀ hw₀
  choose E hE using fun s => (b₂ s).exists
  obtain ⟨f, hf, hfN⟩ := GlobalTheory.TorsionIso.torsion_clause R I hI D A G hG U F N hN1
  have hlabf : ∀ p, lab p = f p := fun p => (hf.1 p (lab p)).1 (hlab p)
  have hSF := GlobalTheory.SymFrameClause.symFrame_clause R I hI D A G hG U F N hN
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hE⟩
  · refine ⟨fun s s' h => ?_, fun t => ?_⟩
    · have h1 := hE s
      rw [h] at h1
      exact (b₁ (E s')).unique h1 (hE s')
    · obtain ⟨s, hs, -⟩ := b₁ t
      exact ⟨s, (b₂ s).unique (hE s) hs⟩
  · intro s s' s'' h j
    have hT := hlin F N w₀ (E s) (E s') (SecOps.secAdd (E s) (E s')) s s' 1 (hE s) (hE s') (fun j => by
      simp [SecOps.secAdd, liftFun])
    have e : (1 : F) • s + s' = s'' := fam_ext fun α j => by rw [h]; simp
    rw [e] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ s'').unique (hE s'') hT)
  · intro c s s' hs j
    obtain rfl := (isSmul_iff c s s').1 hs
    obtain ⟨z, hz, -⟩ := b₁ SecOps.secZero
    have hz0 : z = 0 := by
      have h2 := hlin F N w₀ _ _ SecOps.secZero z z 1 hz hz (fun j => by simp [SecOps.secZero])
      have h3 := (b₁ _).unique hz h2
      rw [one_smul] at h3
      exact left_eq_add.1 h3
    have hT := hlin F N w₀ (E s) SecOps.secZero
      (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F c)) (E s)) s z c (hE s) hz (fun j => by
        show _ = _ + 0
        rw [add_zero]
        rfl)
    rw [hz0, add_zero] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ _).unique (hE _) hT)
  · intro x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := hf.2.1 x hx
      exact ⟨p, (hlabf p).trans hp⟩
    · rintro ⟨p, rfl⟩
      rw [hlabf]
      exact hfN p
  · intro p
    exact (hSF p).1.1
  · intro p
    exact ((hSF p).2 (lab p) (hlab p)).1
  · intro p w θ s s' hw hθ hrel
    obtain ⟨t', ht'⟩ := GlobalTheory.RootShift.exists_isActOf A.isLB θ (E s)
    obtain ⟨s'', hs'', -⟩ := b₁ t'
    have h1 := ((hSF p).2 (lab p) (hlab p)).2 θ hθ w₀ hw₀ w hw (E s) t' s s'' (hE s) hs'' ht'
    obtain rfl := GlobalTheory.ThetaTranslate.phiRel_unique gf p hw.1 hrel h1
    have e := (b₂ s').unique (hE s') hs''
    rw [← e] at ht'
    exact ht'

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantInverseThetaExpansionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_inverse_thetaExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  first | exact @GlobalTheory.Mum.exists_eqv_expandsF | exact GlobalTheory.Mum.exists_eqv_expandsF | (intros; apply GlobalTheory.Mum.exists_eqv_expandsF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitSectionIntegralExpansionMemRangeInverseExpa
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitSectionIntegralExpansionMemRangeInverseExpa
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Mum.TraitValue

theorem value_of_expands {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (F : Type) [Field F] [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK W))))
    (t : SecK A.L (snd (TFK (R := W) F) A.A).left k) (s : Fam D.toPre F k) (h : U.ExpandsF F k w t s)
    (σ : H0 U.LG.L k) (f : ∀ x, D.toPre.SecB k x) (hσ : ∀ e, U.ExpandsAt e k σ f)
    (hs : ∀ x, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F x) (DegPre.famε k) (s.s x) (D.toPre.famφB x)
      (DegPre.famε k) (f x) (DegPre.prB D.toPre F).left 1)
    (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ A.A).left) (z : Z) JG Jt (hG : Good U.LG.L z JG) (ht : Good A.L z Jt) :
    sval σ (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)) z JG =
      (gw w (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left) z
        (JG (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)))
        (fun _ => Jt (q ≫ (snd (TFK (R := W) F) A.A).left)) ^ k).val * sval t q z Jt := by
  obtain ⟨σ', h₁, h₂⟩ := h
  have h₃ : U.ExpandsG F k (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) s := by
    refine (expandsG_iff U.toUnifPre F k _ s).2 ⟨1, fun _ => 1, fun _ => (σ, f), fun _ => hσ, ?_, fun α => ?_⟩
    · rw [Fin.sum_univ_one, one_smul]
    · rw [Fin.sum_univ_one, one_smul]
      refine sec_ext' D.toPre.P.isLB fun y J hJ => ?_
      have a := (secScal_iff_val D.toPre.P.isLB _ _ _ _).1 (hs α) y J hJ
      rw [gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at a
      exact a.symm.trans ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing W) F))))))).symm
  obtain rfl : σ' = _ :=
    ((expandsG_bijective U.toUnifPre F GlobalTheory.allSixLaws.1.globalFns hk (U.expand k hk)).2 s).unique h₂ h₃
  let n : TFK (R := W) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have e₁ : (q ≫ n.left) ≫ (U.genF F).left = q := by
    rw [Category.assoc, ← Over.comp_left, hn, Over.id_left, Category.comp_id]
  have e₂ : (q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left]
  have e₃ : (q ≫ n.left) ≫ UnifPre.gFK (G := G) F =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W) := by
    rw [← Category.assoc, e₂, Category.assoc, Category.assoc]
  have e₄ : ((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left =
      q ≫ (snd (TFK (R := W) F) A.A).left := by
    rw [e₂, Category.assoc, Category.assoc, ← Over.comp_left _ _ _ U.gen.inv, Iso.inv_hom_id, Over.id_left,
      Category.comp_id]
  have key := (isoRelM_iff w _ k _ h₁.1 _ h₁.2.1 _ _).1 h₁ Z (q ≫ n.left) z
    (JG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (Jt (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
    (hG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (ht (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
  rw [Category.comp_id, e₁, e₄, zpow_natCast] at key
  have v : sval (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) (q ≫ n.left) z JG =
      sval σ (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫
        pullback.fst G.hom (jK W)) z JG :=
    (sval_pullOver _ _ _ _ hG).trans (sval_pullOver _ _ _ _ hG)
  have key' := v.symm.trans key
  rw [e₂, e₃, Category.assoc, Category.assoc] at key'
  exact key'

theorem value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ w₀ _ E' hE F₀ s' σ hs ⟨σ'', f'', hc, hp, he⟩ Z p q h₁ h₂ z JP JG Jt gP gG gt
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have ep : p = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) := by
    refine T.cart.1.hom_ext (by rw [h₁]; simp only [Category.assoc]) ?_
    have a₁ : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have a₂ : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom =
        (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have a₃ : spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) = jFK (R := W) F ≫ jK W :=
      Spec.map_comp (CommRingCat.ofHom (algebraMap W (FractionRing W))) (CommRingCat.ofHom (algebraMap (FractionRing W) F))
    rw [h₂, a₃, Category.assoc, Category.assoc, Category.assoc, pullback.condition, reassoc_of% a₁, reassoc_of% a₂]
  have c := hc Z p z JP JG gP gG
  have h1 : Out.scal T.G.hom (1 : W) = 1 := by unfold Out.scal; rw [map_one, map_one]
  rw [h1, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul] at c
  have v := value_of_expands T.U F hk w₀ (E' s') s' (hE s') σ'' f'' he (hs f'' hp) Z q z JG Jt gG gt
  rw [c, _root_.mul_assoc, ← v, ← ep]

end GlobalTheory.Mum.TraitValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitSectionIntegralExpansionMemRangeInverseExpaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  first | exact @GlobalTheory.Mum.TraitValue.value | exact GlobalTheory.Mum.TraitValue.value | (intros; apply GlobalTheory.Mum.TraitValue.value <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabels
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem traitInv_eqv_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hem
  obtain ⟨f, hfi, hf1, hf2⟩ := GlobalTheory.T.exists_fibre_iso_genericFibre_cover R hR D C W T F hem
  obtain ⟨lab', hq, hm⟩ := GlobalTheory.T.exists_torsionLabels_genericFibre_trait R hR D C j W T F em hem f hfi hf1 hf2
  have hW := T.cdvr
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have : CharZero R := hR.2
  have hcW : CharZero W := charZero_of_injective_ringHom T.inj
  have hsemi : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨w₀, hw₀⟩ := T.U.ext
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hx⟩ := GlobalTheory.T.exists_equivariant_inverse_thetaExpansion W (maximalIdeal W) hW' hcW T.D' T.A T.G T.U hsemi F (C.n ^ j) hodd w₀ hw₀ lab' hq
  obtain ⟨lab, E, Φ, hlab, hE, hΦ, hrel⟩ := GlobalTheory.T.trait_equivariant_bijection_transport_cover R hR D C j wA hwA W T F em hem f hfi hf1 hf2 w₀ hw₀ lab' hm E' hE'
  refine ⟨lab, E, hlab, hE, ?_⟩
  intro F₀ s σ hs hσ Z p p' hβ hG z J J' hJ hJ'
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt T.U.LG.isLB z
  obtain ⟨Jt, hJt⟩ := GlobalTheory.UU.exists_good_pt T.A.isLB z
  have hq1 : (p' ≫ inv f) ≫ f = p' := by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hG' : p ≫ T.G.hom = (p' ≫ inv f) ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [hG, ← hf1]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hβ' : p ≫ T.β = (p' ≫ inv f) ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    rw [hβ, ← hf2, Category.assoc, IsIso.inv_hom_id_assoc]
  exact (GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion R hR D C j W T F w₀ hw₀ E' hx F₀ (Φ s) σ (hΦ s F₀ hs) hσ Z p (p' ≫ inv f) hβ' hG' z J JG Jt hJ hJG hJt).trans
    (hrel s Z p p' (p' ≫ inv f) hq1 hβ hG' z J J' JG Jt hJ hJ' hJG hJt).symm

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_inverse_expansion_equivariant_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  first | exact @GlobalTheory.Mum.traitInv_eqv_value | exact GlobalTheory.Mum.traitInv_eqv_value | (intros; apply GlobalTheory.Mum.traitInv_eqv_value <;> assumption)
end

module ROmega.Examples.Section-3 where

open import Agda.Primitive
open import Level

open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)
  hiding (Σ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)

open import Data.String
open import Data.Unit.Polymorphic
open import Data.Fin renaming (zero to fzero ; suc to fsuc)

open import ROmega.Kinds
open import ROmega.Entailment -- extensionality
open import ROmega.Entailment.Reasoning
open import ROmega.Types hiding (U)
open import ROmega.Types.Substitution
open import ROmega.Types.Substitution.Properties -- extensionality
open import ROmega.Equivalence.Syntax
open import ROmega.Terms -- extensionality

--------------------------------------------------------------------------------
-- We work in the simple row theory.

open SimpleRowSyntax
open SimpleRowSemantics
open TermSyntax Ent
open TermSemantics Ent ⟦_⟧n

--------------------------------------------------------------------------------
-- idω : ★ → ★ at all levels.

idω : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ ((★ ℓ) `→ (★ ℓ))
idω {ℓ} = `λ (★ ℓ) (tvar Z)

-- #############################################################################
-- 3.1 First-Class Labels.
-- #############################################################################

--------------------------------------------------------------------------------
-- Select (sel).
--
-- We have:
--  sel : ∀ Ł : L, T : ★, ζ : R[ ★ ]. (Ł R▹ T) ≲ ζ ⇒ Π ζ → ⌊ Ł ⌋ → T
--  sel = Λ Ł : L. Λ T : ★. Λ ζ : R[ ★ ]. ƛ p : (Ł R▹ T) ≲ ζ ⇒ Π ζ.
--           λ r : Π ζ. λ l : ⌊ Ł ⌋. (prj r) / l
--
--------------------------------------------------------------------------------

selT : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ (lsuc ℓ))
selT {ℓ} =
  `∀ (L {lzero}) (`∀ (★ ℓ) (`∀ R[ ★ ℓ ]
    ((Ł R▹ T) ≲ ζ ⇒ Π ζ `→ ⌊_⌋ {ι = lzero} Ł `→ T)))
    where
      ζ = tvar Z
      T = tvar (S Z)
      Ł = tvar (S (S Z))
 

sel : ∀ {ℓ ℓΔ ℓφ ℓΓ} {Δ : KEnv ℓΔ} {φ : PEnv Δ ℓφ}  {Γ : Env Δ ℓΓ} → Term Δ φ Γ (selT {ℓ})
sel {ℓ} = `Λ L (`Λ (★ ℓ) (`Λ R[ (★ ℓ) ]
        (`ƛ ((Ł R▹ T) ≲ ζ) (`λ (Π ζ) (`λ ⌊ Ł ⌋ body)))))
  where
    ζ = tvar Z
    T = tvar (S Z)
    Ł = tvar (S (S Z))
      
    body = (prj▹ (var (S Z)) (n-var Z)) / (var Z)

--------------------------------------------------------------------------------
-- Construct (con).

conT : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ (lsuc ℓ))
conT {ℓ} =
  `∀ (L {lzero}) (`∀ (★ ℓ) (`∀ R[ (★ ℓ) ]
    ((l R▹ t) ≲ z ⇒ ⌊_⌋ {ι = lzero} l `→ t `→ Σ z)))
    where
      z = tvar Z
      t = tvar (S Z)
      l = tvar (S (S Z))

con : ∀ {ℓ ℓΔ ℓφ ℓΓ} {Δ : KEnv ℓΔ} {φ : PEnv Δ ℓφ}  {Γ : Env Δ ℓΓ} → Term Δ φ Γ (conT {ℓ})
con {ℓ} = `Λ L (`Λ (★ ℓ) (`Λ R[ (★ ℓ) ]
        (`ƛ ((l R▹ t) ≲ z) ((`λ (⌊ l ⌋) (`λ t Σz))))))
  where
    z = tvar Z 
    t = tvar (S Z)
    l = tvar (S (S Z))

    x = var Z
    l'  = var (S Z)
    Σz = inj▹ (l' ▹ x) (n-var Z)
    

-- Some assertions about con.
con₁ con₂ : ∀ {ℓ} → ⟦ conT {ℓ} ⟧t tt
con₁ _ t z π ρ x with π fzero
... | n , eq rewrite eq = n , x
con₂ = ⟦ con ⟧ tt tt tt

con-ext-eq : ∀ {ℓ} u X z π ρ u' → con₁ {ℓ} u X z π ρ u' ≡ con₂ {ℓ} u X z π ρ u'
con-ext-eq _ X row π r _ with π fzero 
... | m , eq rewrite eq = refl

--------------------------------------------------------------------------------
-- Case (case).

caseT : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ (lsuc ℓ))
caseT {ℓ} =
  `∀ (L {lzero}) (`∀ (★ ℓ) (`∀ (★ ℓ)
    (⌊_⌋ {ι = lzero} l `→ (t `→ u) `→ Σ (l R▹ t) `→ u)))
    where
      l = tvar (S (S Z))
      t = tvar (S Z)
      u = tvar Z

case : ∀ {ℓ ℓΔ ℓΦ ℓΓ} {Δ : KEnv ℓΔ} {Φ : PEnv Δ ℓΦ}  {Γ : Env Δ ℓΓ} →
       Term Δ Φ Γ (caseT {ℓ})
case {ℓ} = `Λ L (`Λ (★ ℓ) (`Λ (★ ℓ)
       (`λ ⌊ Ł ⌋ (`λ (T `→ U) (`λ (Σ (Ł R▹ T)) (f · ((Σ⁻¹ x) / l)))))))
  where
    Ł = tvar (S (S Z))
    T = tvar (S Z)
    U = tvar Z

    l = var (S (S Z))
    f = var (S Z)
    x = var Z

--------------------------------------------------------------------------------
-- If Then Else (ifte).

Tru Fls : ∀ {ℓΔ} {Δ : KEnv ℓΔ} →
          Type Δ (L {lzero})
Tru = lab "True"
Fls = lab "False"

BoolP : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Pred (Δ , R[ ★ ℓ ]) (★ ℓ)
BoolP = (Tru R▹ ∅) · Fls R▹ ∅ ~ tvar Z

Bool : ∀ {ℓ} {ℓΔ} {Δ : KEnv ℓΔ} →
       Type Δ (★ (lsuc ℓ))
Bool {ℓ} = `∀ (R[ ★ ℓ ]) (BoolP ⇒ Σ (tvar Z))

ifteT : ∀ {ℓ} {ℓΔ} {Δ : KEnv ℓΔ} →
        Type Δ (★ (lsuc ℓ))
ifteT {ℓ} = `∀ (★ ℓ) (`∀ R[ ★ ℓ ]
  (BoolP {ℓ} ⇒ Bool {ℓ} `→ tvar (S Z) `→ tvar (S Z) `→ tvar (S Z)))

ifte : ∀ {ℓ ℓΔ ℓφ ℓΓ} {Δ : KEnv ℓΔ} {φ : PEnv Δ ℓφ}  {Γ : Env Δ ℓΓ} →
       Term Δ φ Γ (ifteT {ℓ})
ifte =
  `Λ (★ _)
  (`Λ R[ ★ _ ]
  (`ƛ _
  (`λ Bool
  (`λ (tvar (S Z))
  (`λ (tvar (S Z))
  ((((((((case ·[ Tru ]) ·[ ∅ ]) ·[ _ ]) · lab Tru) · `λ _ (var (S (S Z)))))
  ▿
  ((((((case ·[ Fls ]) ·[ ∅ ]) ·[ _ ]) · lab Fls) · `λ _ (var (S Z)))))
  (n-var Z) · (((var (S (S Z))) ·[ tvar Z ]) ·⟨ n-var Z ⟩)  ))))))
    

-- #############################################################################
-- 3.2 The Duality of Records.
-- #############################################################################

--------------------------------------------------------------------------------
-- Reification (reify).

reifyT : Type ε ★₁
reifyT = `∀ R[ ★₀ ] (`∀ ★₀ (((Σ z) `→ t) `→ Π (⌈ (`λ ★₀ ((tvar Z) `→ (tvar (S Z)))) ⌉· z)))
  where
    t = tvar Z
    z = tvar (S Z)

reify : Term ε ε ε reifyT
reify = `Λ R[ ★₀ ] (`Λ ★₀ (`λ (((Σ z) `→ t)) (syn z (`λ ★₀ ((tvar Z) `→ (tvar (S Z)))) sbod)))
  where
    t = tvar Z
    z = tvar (S Z)
        
    sbod = `Λ (L {lzero}) (`Λ ★₀ (`Λ R[ ★₀ ] (`ƛ ((l R▹ u) · y ~ z')
      (`λ ⌊ l ⌋
        (t-≡
          (`λ u
            (f ·
              ((((((con ·[ l ]) ·[ u ]) ·[ z' ])
              ·⟨ n-·≲L (n-var Z) ⟩)
              · (var (S Z)))
              · (var Z))))
          (teq-sym teq-β))))))
      where
        y  = tvar Z
        u  = tvar (S Z)
        l  = tvar (S (S Z))
        z' = tvar (S (S (S (S Z))))
        f  = var (S (S Z))

⟦reify⟧ : ⟦ reifyT ⟧t tt
⟦reify⟧ = ⟦ reify ⟧ tt tt tt

--------------------------------------------------------------------------------
-- Reflection (reflect).

-- We have:
--  ana :   (ρ : Row κ) (φ : κ → ★) (T : ★) →
--          (∀ Ł : L, U : κ, Y : R[ κ ]. (Ł R▹ U) · Y ~ ρ ⇒ ⌊ Ł ⌋ → φ U → T) →
--          Σ ρ → T             
--
--  reflect : ∀ ζ : R[ ★ ], T : ★.
--            Π (lift₂ (λ (X : ★). X → T) ζ) →
--            Σ ζ → T
--  reflect = Λ ζ : R[ ★ ]. Λ T : ★.
--              λ r : Π (lift₂ (λ (X : ★). X → T) ζ).
--              ana ★ ζ (λ X : ★. X) T (
--                Λ Ł : L. Λ U : ★. Λ Y : R[ κ ].
--                ƛ p : (Ł R▹ U) · Y ~ ρ.
--                λ l : ⌊ Ł ⌋. λ u : (λ X. X) U.
--                sel ·[ Ł ] ·[ ((λ X. X) U) → T ] ·[ lift₂ (λ (X : ★). X → T) ζ ]
--                    ·⟨ ? ⟩ ·( r ) ·( l ) ·( u ))

reflectT : Type ε ★₁
reflectT = `∀ R[ ★₀ ] (`∀ ★₀
              (Π (⌈ (`λ ★₀ ((tvar Z) `→ (tvar (S Z)))) ⌉· z) `→
              ((Σ (⌈ idω ⌉· z)) `→ t)))
         where
           t = tvar Z
           z = tvar (S Z)

reflect : Term ε ε ε reflectT
reflect =
--     Λ ζ : R[ ★ ].
      `Λ R[ ★₀ ]
--     Λ T : ★.      
     (`Λ ★₀
--     λ r : Π (ζ → T).    
     (`λ (Π (⌈ (`λ ★₀ (tvar Z `→ tvar (S Z))) ⌉· (tvar (S Z))))
      (ana (tvar (S Z)) idω (tvar Z) M)))
  where
    M =
--     Λ Ł : L.
      `Λ L
--     Λ U : ★
     (`Λ ★₀
--     Λ Y : R[ κ ].     
     (`Λ R[ ★₀ ]
--     ƛ p : (Ł R▹ U) · Y ~ Ζ
     (`ƛ ((tvar (S (S Z)) R▹ tvar (S Z)) · (tvar Z) ~ (tvar (S (S (S (S Z))))))
--     λ l : ⌊ Ł ⌋
     (`λ ⌊ (tvar (S (S Z))) ⌋
--     λ u : (idω ·U).
     (`λ (idω ·[ tvar (S Z) ])
--   (sel body)
     body)))))
       where
         body =
           ((((((sel
--           ·[ Ł ]
             ·[ tvar (S (S Z)) ])
--           ·[ ((λ X. X) U) → T ] 
             ·[ idω ·[ tvar (S Z) ] `→ (tvar (S (S (S Z)))) ])
--           ·[ lift₂ (λ (X : ★). X → T) ζ ]
             ·[ (⌈ (`λ ★₀ (tvar Z `→ tvar (S (S (S (S Z)))))) ⌉· (tvar (S (S (S (S Z)))))) ])
--           ·⟨  evidence ⟩
            ·⟨ evidence ⟩) 
--           · r
             · var (S (S Z)))
--           · l
             · (var (S Z )))
--           · u
             · (var Z)
             where
               Ł = tvar (S (S Z))
               T = (tvar (S (S (S Z))))
               T' = (tvar (S (S (S (S Z)))))
               Uu = tvar (S Z)
               Y = tvar Z
               ζ = tvar (S (S (S (S Z))))

               evidence :  Ent _ _ ((Ł R▹ ((idω ·[ Uu ]) `→ T)) ≲ ⌈ (`λ ★₀ (tvar Z `→ T')) ⌉· ζ)               
               evidence = 
                  (((Ł R▹ Uu) · Y ~ ζ)
                 ⊩⟨ n-·≲L ⟩
                   ((Ł R▹ Uu) ≲ ζ)
                 ⊩⟨ n-≡ (peq-≲ (teq-sing teq-refl (teq-sym teq-β)) teq-refl) ⟩
                   ((Ł R▹ (idω ·[ Uu ])) ≲ ζ)
                 ⊩⟨ n-≲lift₂ ⟩
                   ((⌈ (`λ ★₀ (tvar Z `→ T')) ⌉· (Ł R▹ (idω ·[ Uu ])) ≲ ⌈ (`λ ★₀ (tvar Z `→ T')) ⌉· ζ))
                 ⊩⟨ n-≡ (peq-≲ teq-lift₂ teq-refl) ⟩
                   (((Ł R▹ ((`λ ★₀ (tvar Z `→ T')) ·[ (idω ·[ Uu ]) ])) ≲ ⌈ (`λ ★₀ (tvar Z `→ T')) ⌉· ζ))
                 ⊩⟨ n-≡ (peq-≲ (teq-sing teq-refl teq-β) teq-refl) ⟩
                   ∎)
                 (n-var Z)


-- #############################################################################
-- 3.3 Transformations.
-- #############################################################################

--------------------------------------------------------------------------------
-- Iterators (Iter).

Iter :  ∀ {Δ : KEnv lzero} →
        (κ : Kind lzero) →
        Type Δ (κ `→ ★₀) →
        Type Δ (κ `→ ★₀) →
        Type Δ (R[ κ ]) →
        Type Δ ★₁
Iter κ f g z =
  `∀ (L {lzero}) (`∀ κ (`∀ R[ κ ]
    ((Ł R▹ U) · Y ~ z' ⇒ ⌊_⌋ {ι = lzero} Ł `→ f' ·[ U ] `→ g' ·[ U ])))
    where
      z' = weaken (weaken (weaken z))
      f' = weaken (weaken (weaken f))
      g' = weaken (weaken (weaken g))
      Ł = tvar (S (S Z))
      U = tvar (S Z)
      Y = tvar Z

--------------------------------------------------------------------------------
-- mapping over records (map-π).

map-ΠT : ∀ {Δ : KEnv lzero} →
         (κ : Kind lzero) →
         Type Δ ★₁
map-ΠT κ =
  `∀ R[ κ ] (`∀ (κ `→ ★₀) (`∀ (κ `→ ★₀)
  (Iter κ f g z `→ (Π (⌈ f ⌉· z)) `→ Π (⌈ g ⌉· z) )))
  where
    g = tvar Z
    f = tvar (S Z)
    z = tvar (S (S Z))

map-Π : ∀ {Δ : KEnv lzero} {Φ : PEnv Δ lzero}  {Γ : Env Δ lzero} →
        (κ : Kind lzero) →
        Term Δ Φ Γ (map-ΠT κ)
map-Π κ =
   `Λ {- z -} R[ κ ]
  (`Λ {- f -} (κ `→ ★₀)
  (`Λ {- g -} (κ `→ ★₀)
  (`λ {- i -} (Iter κ (tvar (S Z)) (tvar Z) (tvar (S (S Z))))
  (`λ {- r -} (Π (⌈ f ⌉· tvar (S (S Z)))) 
      (syn (tvar (S (S Z))) (tvar Z)
       (`Λ {- Ł -} L
       (`Λ {- U -} κ 
       (`Λ {- Y -} R[ κ ]
       (`ƛ {- _ -} ((tvar (S (S Z)) R▹ tvar (S Z)) · (tvar Z) ~ tvar (S (S (S (S (S Z))))))
       (`λ {- l -} ⌊ tvar (S (S Z)) ⌋
       ((i' · l) · ((sel' · r) · l)))
       )))))))))
  where
    f = tvar (S Z)

    l  = var Z
    r = var (S Z)

    i' = let
            Ł = tvar (S (S Z))
            U = tvar (S Z)
            Y = tvar Z
       in ((((var (S (S Z))) ·[ Ł ]) ·[ U ]) ·[ Y ]) ·⟨ n-var Z ⟩
    sel' = let
            Ł = tvar (S (S Z))
            U = tvar (S Z)
            -- Y = tvar Z
            z' = tvar (S (S (S (S (S Z)))))
            f' = tvar (S (S (S (S Z))))
         in
       (((sel
       ·[ Ł ])
       ·[ f' ·[ U ] ])
       ·[ (⌈ f' ⌉· z') ])
      ·⟨ evidence ⟩
        where
          evidence : let
              Ł = tvar (S (S Z))
              U = tvar (S Z)
              z' = tvar (S (S (S (S (S Z)))))
              f' = tvar (S (S (S (S Z))))
            in Ent _ _ ((Ł R▹ (f' ·[ U ]) ) ≲ (⌈ f' ⌉· z'))
          evidence = let
              Ł = tvar (S (S Z))
              U = tvar (S Z)
              Y = tvar Z
              z' = tvar (S (S (S (S (S Z)))))
              f' = tvar (S (S (S (S Z))))
            in
              ((((Ł R▹ U) · Y ~ z')
              ⊩⟨ n-·≲L ⟩
                ((Ł R▹ U) ≲ z'
              ⊩⟨ n-≲lift₂ ⟩
                 ⌈ f' ⌉· (Ł R▹ U ) ≲ ⌈ f' ⌉· z'
              ⊩⟨ n-≡ (peq-≲ teq-lift₂ teq-refl) ⟩
              ∎)) (n-var Z))

--------------------------------------------------------------------------------
-- Mapping over Variants.

map-ΣT : ∀ {Δ : KEnv lzero} →
         (κ : Kind lzero) →
         Type Δ ★₁
map-ΣT κ =
  `∀ R[ κ ] (`∀ (κ `→ ★₀) (`∀ (κ `→ ★₀)
  (Iter κ f g z `→ (Σ (⌈ f ⌉· z)) `→ Σ (⌈ g ⌉· z) )))
  where
    g = tvar Z
    f = tvar (S Z)
    z = tvar (S (S Z))

map-Σ : ∀ {Δ : KEnv lzero} {Φ : PEnv Δ lzero}  {Γ : Env Δ lzero} →
        (κ : Kind lzero) →
        Term Δ Φ Γ (map-ΣT κ)
map-Σ κ =
   `Λ {- z -} R[ κ ]
  (`Λ {- f -} (κ `→ ★₀)
  (`Λ {- g -} (κ `→ ★₀)
  (`λ {- i -} (Iter κ (tvar (S Z)) (tvar Z) (tvar (S (S Z))))
  (`λ {- v -} (Σ (⌈ f ⌉· tvar (S (S Z)))) 
      ((ana (tvar (S (S Z))) (tvar (S Z)) (Σ (⌈ tvar Z ⌉· (tvar (S (S Z)))))
       (`Λ {- Ł -} L
       (`Λ {- U -} κ 
       (`Λ {- Y -} R[ κ ]
       (`ƛ {- _ -} ((tvar (S (S Z)) R▹ tvar (S Z)) · (tvar Z) ~ tvar (S (S (S (S (S Z))))))
       (`λ {- l -} ⌊ tvar (S (S Z)) ⌋
       (`λ {- x -} (tvar (S (S (S (S Z))))  ·[ (tvar (S Z)) ])
       (((con' · l) · ((i' · l) · x)
       ))))))))) · (var Z))))))
  where
    f = tvar (S Z)
    x  = var Z
    l = var (S Z)
    i' =
      let
        Ł = tvar (S (S Z))
        U = tvar (S Z)
        Y = tvar Z
      in ((((var (S (S (S Z)))) ·[ Ł ]) ·[ U ]) ·[ Y ]) ·⟨ n-var Z ⟩
    
    con' =
      let

        Ł = tvar (S (S Z))
        U = tvar (S Z)
        -- Y = tvar Z
        z' = tvar (S (S (S (S (S Z)))))
        g' = tvar (S (S (S Z)))        
      in (((con
        ·[ Ł ])
        ·[ g' ·[ U ] ])
        ·[ ⌈ g' ⌉· z' ])
        ·⟨ evidence ⟩
        where
          evidence : let
              Ł = tvar (S (S Z))
              U = tvar (S Z)
              z' = tvar (S (S (S (S (S Z)))))
              g' = tvar (S (S (S Z)))
            in Ent _ _ ((Ł R▹ (g' ·[ U ]) ) ≲ (⌈ g' ⌉· z'))
          evidence = let
              Ł = tvar (S (S Z))
              U = tvar (S Z)
              Y = tvar Z
              z' = tvar (S (S (S (S (S Z)))))
              g' = tvar (S (S (S Z)))
            in
              ((((Ł R▹ U) · Y ~ z')
              ⊩⟨ n-·≲L ⟩
                ((Ł R▹ U) ≲ z'
              ⊩⟨ n-≲lift₂ ⟩
                 ⌈ g' ⌉· (Ł R▹ U ) ≲ ⌈ g' ⌉· z'
              ⊩⟨ n-≡ (peq-≲ teq-lift₂ teq-refl) ⟩
              ∎)) (n-var Z))

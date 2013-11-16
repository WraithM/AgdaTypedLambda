module TypedLambda where

open import Data.Nat using (ℕ; zero; _+_; _≤?_; _≥_; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Data.List hiding ([_])
open import Data.Maybe
open import Function using (_∘_;_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import Data.String hiding (_≟_)

-- For compiling --
-- open import Data.Unit using ( ⊤ )
-- open import IO

infixr 30 _⇒_

data Type : Set where
  nat : Type
  bool : Type
  _⇒_ : Type → Type → Type

Ctx : ℕ → Set
Ctx = Vec Type

data AST (A : Set) : Set where
  var : A → AST A
  lit : ℕ → AST A
  bool : Bool → AST A
  _⊕_ : AST A → AST A → AST A -- Addition
  _∙_ : AST A → AST A → AST A -- Application
  lam : Type → AST A → AST A

DebruijnEnv : Set
DebruijnEnv = List (String × ℕ)

find : String → DebruijnEnv → Maybe ℕ
find _ [] = nothing
find s ((x , n) ∷ Γ) with x == s
... | true  = just n
... | false = find s Γ

Syntax = AST ℕ

debruijnize' : DebruijnEnv → AST String → (Syntax × DebruijnEnv)
debruijnize' Γ (var x) with find x Γ 
... | just n = (var n , Γ)
... | nothing = let n' = length Γ in (var n' , (x , n') ∷ Γ)
debruijnize' Γ (lit x) = (lit x , Γ)
debruijnize' Γ (bool x) = (bool x , Γ)
debruijnize' Γ (x ⊕ y) = let (x' , _) = debruijnize' Γ x
                             (y' , _) = debruijnize' Γ y
                         in (x' ⊕ y' , Γ)
debruijnize' Γ (x ∙ y) = let (x' , Γ') = debruijnize' Γ x
                             (y' , Γ'') = debruijnize' Γ' y
                         in (x' ∙ y' , Γ'')
debruijnize' Γ (lam t x) = let (x' , Γ') = debruijnize' Γ x
                           in (lam t x' , Γ')

debruijnize : AST String → Syntax
debruijnize = proj₁ ∘ debruijnize' []

testast : Syntax
testast = debruijnize ((lam (nat ⇒ (nat ⇒ nat)) (var "x") ∙ (lam (nat ⇒ nat) (var "y") ∙ var "x")) ⊕ (var "y"))

data Term {n} (Γ : Ctx n) : Type → Set where
  var : ∀ {τ} (v : Fin n) → τ ≡ lookup v Γ → Term Γ τ
  lit : ℕ → Term Γ nat
  bool : Bool → Term Γ bool
  _⊕_ : Term Γ nat → Term Γ nat → Term Γ nat
  _∙_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

erase : ∀ {n} {Γ : Ctx n} {τ} → Term Γ τ → Syntax
erase (var x _) = var (toℕ x)
erase (lit n) = lit n
erase (bool b) = bool b
erase (t ⊕ u) = erase t ⊕ erase u
erase (t ∙ u) = erase t ∙ erase u
erase (lam σ t) = lam σ (erase t)

data Fromℕ (n : ℕ) : ℕ → Set where
  yes : (m : Fin n) → Fromℕ n (toℕ m)
  no : (m : ℕ) → Fromℕ n (n + m)

fromℕ : ∀ n m → Fromℕ n m
fromℕ zero m = no m
fromℕ (suc _) zero = yes Data.Fin.zero
fromℕ (suc n) (suc m) with fromℕ n m
fromℕ (suc n) (suc .(toℕ m)) | yes m = yes (suc m)
fromℕ (suc n) (suc .(n + m)) | no m = no m

≡⇒₁ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → σ ≡ σ′
≡⇒₁ refl = refl
≡⇒₂ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → τ ≡ τ′
≡⇒₂ refl = refl

_≟_ : (τ σ : Type) → Dec (τ ≡ σ)
nat ≟ nat = yes refl
nat ≟ bool = no λ()
nat ≟ _ ⇒ _ = no λ()
bool ≟ bool = yes refl
bool ≟ nat = no λ ()
bool ≟ _ ⇒ _ = no λ ()
_ ⇒ _ ≟ nat = no λ ()
_ ⇒ _ ≟ bool = no λ ()
σ ⇒ τ ≟ σ' ⇒ τ' with σ ≟ σ' | τ ≟ τ'
σ ⇒ τ ≟ .σ ⇒ .τ | yes refl | yes refl = yes refl
σ ⇒ τ ≟ σ' ⇒ τ' | no σ≢σ' | _ = no (σ≢σ' ∘ ≡⇒₁)
σ ⇒ τ ≟ σ' ⇒ τ' | _ | no τ≢τ' = no (τ≢τ' ∘ ≡⇒₂)

data Check {n} (Γ : Ctx n) : Syntax → Set where
  yes : (τ : Type) (t : Term Γ τ) → Check Γ (erase t)
  no  : {e : Syntax} → Check Γ e

check : ∀ {n} (Γ : Ctx n) (t : Syntax) → Check Γ t
check {n} Γ (var v) with fromℕ n v
check {n} Γ (var .(toℕ v)) | yes v = yes (lookup v Γ) (var v refl)
check {n} Γ (var .(n + m)) | no m = no
check Γ (lit n) = yes nat (lit n)
check Γ (bool x) = yes bool (bool x)
check Γ (t ⊕ u) with check Γ t | check Γ u  
check Γ (.(erase t) ⊕ .(erase u)) | yes nat t | yes nat u = yes nat (t ⊕ u)
check Γ (_ ⊕ _) | _ | _ = no
check Γ (t ∙ u) with check Γ t | check Γ u
check Γ (.(erase t) ∙ .(erase u)) | yes (σ ⇒ τ) t | yes σ' u with σ ≟ σ'
check Γ (.(erase t) ∙ .(erase u)) | yes (σ ⇒ τ) t | yes .σ u | yes refl = yes τ (t ∙ u)
check Γ (.(erase t) ∙ .(erase u)) | yes (σ ⇒ τ) t | yes σ' u | no _ = no
check Γ (t ∙ u) | _ | _ = no
check Γ (lam σ t) with check (σ ∷ Γ) t
check Γ (lam σ .(erase t)) | yes τ t = yes (σ ⇒ τ) (lam σ t)
check Γ (lam σ t) | no = no

-- Interpret types
⟦_⟧ : Type → Set
⟦ nat ⟧ = ℕ
⟦ bool ⟧ = Bool
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _∷_
data Env : ∀ {n} → Ctx n → Set where
  [] : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)
  
lookupEnv : ∀ {n} {Γ : Ctx n} (m : Fin n) → Env Γ → ⟦ lookup m Γ ⟧
lookupEnv zero (x ∷ _) = x
lookupEnv (suc n) (_ ∷ Γ) = lookupEnv n Γ

-- eval terms in a context Γ
_[_] : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧
Γ [ var v refl ] = lookupEnv v Γ
Γ [ lit x ] = x
Γ [ bool x ] = x
Γ [ t ⊕ u ] = Γ [ t ] + Γ [ u ]
Γ [ t ∙ u ] = (Γ [ t ]) (Γ [ u ])
Γ [ lam _ t ] = λ x → (x ∷ Γ) [ t ]

lookupSyntax : ℕ → List Syntax → Maybe Syntax
lookupSyntax zero [] = nothing
lookupSyntax zero (x ∷ _) = just x
lookupSyntax (suc n) [] = nothing
lookupSyntax (suc n) (x ∷ Γ) = lookupSyntax n Γ

eval : List Syntax → Syntax → Syntax
eval Γ (var x) with lookupSyntax x Γ
eval Γ (var x) | just y = y
eval Γ (var x) | nothing = var x
eval Γ (lit x) = lit x
eval Γ (bool x) = bool x
eval Γ (x ⊕ y) with eval Γ x | eval Γ y
eval Γ (x ⊕ y) | lit x' | lit y' = lit (x' + y')
eval Γ (x ⊕ y) | x' | y' = (x' ⊕ y')
eval Γ ((lam _ e) ∙ arg) = eval (arg ∷ Γ) e
eval Γ (lam t y) = lam t y
eval Γ (_ ∙ _) = bool false

testast2 = eval [] (lam nat (var 0 ⊕ var 1) ∙ lit 3)

-- For compiling --
-- main' : IO ⊤
-- main' = putStrLn "Hello"

-- main = run main'

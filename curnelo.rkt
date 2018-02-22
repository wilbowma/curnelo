#lang racket/base
(require
 "mk/mk.scm"
 rnrs/base-6
 rnrs/lists-6
 "chko.rkt"
 chk)

(provide
 typeo
 evalo)

(define (varo e)
  (conde
   [(symbolo e)
    (=/= e 'Sigma)
    (=/= e 'pair)
    (=/= e 'fst)
    (=/= e 'snd)
    (=/= e 'Type)
    (=/= e 'closure)
    (=/= e 'lambda)
    (=/= e 'Pi)]))

(define deltao
  (lambda (x gamma term)
    (conde
      [(== '() gamma) (== x term)]
      [(fresh (y t gamma^)
         (== `((,y . ,t) . ,gamma^) gamma)
         (conde
           [(== x y) (== t term)]
           [(=/= x y) (deltao x gamma^ term)]))])))

(define ext-envo
  (lambda (gamma x e gamma^)
    (== `((,x . ,e) . ,gamma) gamma^)))

;; Universe levels:
;; lz : Level
;; lsucc : Level -> Level
(define (levelo e)
  (conde
   [(== 'lz e)]
   [(fresh (e^)
      (== `(lsucc ,e^) e)
      (levelo e^))]))

(define (max-levelo i j k)
  (conde
   [(== 'lz i)
    (== j k)]
   [(== 'lz j)
    (== i k)]
   [(fresh (i^ j^ k^)
      (== i `(lsucc ,i^))
      (== j `(lsucc ,j^))
      (== k `(lsucc ,k^))
      (max-levelo i^ j^ k^))]))

(define (constanto e)
  (conde
   [(varo e)]
   [(fresh (e1 e2)
      (== `(,e1 . ,e2) e)
      (=/= 'closure e1))]))

(define evalo
  (lambda (gamma e e^)
    (conde
      [(varo e) (deltao e gamma e^)]
      [(fresh (A A^ B B^ gamma^ x)
         (== `(Pi (,x : ,A) ,B) e)
         (ext-envo gamma x x gamma^)
         (== `(Pi (,x : ,A^) ,B^) e^)
         (evalo gamma A A^)
         (evalo gamma^ B B^))]
      [(fresh (x A ebody ebody^)
         (== `(lambda (,x : ,A) ,ebody) e)
         (== `(closure ,gamma (,x : ,A) ,ebody^) e^)
         (evalo gamma ebody ebody^))]
      [(fresh (ep ep^ e1 e2 e1^)
         (== `(fst ,ep) e)
         (== `(pair ,e1 ,e2) ep^)
         (== e1^ e^)
         (evalo gamma ep ep^)
         (evalo gamma e1 e1^))]
      [(fresh (ep ep^ e1 e2 e2^)
         (== `(snd ,ep) e)
         (== `(pair ,e1 ,e2) ep^)
         (== e2^ e^)
         (evalo gamma ep ep^)
         (evalo gamma e2 e2^))]
      [(fresh (e1 e2 e2^)
         (== `(,e1 ,e2) e)
         (conde
           [(fresh (e1^)
              (constanto e1^)
              (evalo gamma e1 e1^)
              (== `(,e1^ ,e2^) e^))]
           [(fresh (gamma^ x A ebody env)
              (evalo gamma e1 `(closure ,env (,x : ,A) ,ebody))
              (ext-envo env x e2^ gamma^)
              (evalo gamma^ ebody e^))])
         (evalo gamma e2 e2^))]
      [(fresh (i)
         (== `(Type ,i) e)
         (== `(Type ,i) e^))]
      [(fresh (gamma x A B gamma^ A^ B^)
         (== `(Sigma (,x : ,A) ,B) e)
         (ext-envo gamma x x gamma^)
         (== `(Sigma (,x : ,A^) ,B^) e^)
         (evalo gamma A A^)
         (evalo gamma^ B B^))]
      [(fresh (e1 e2 e1^ e2^)
         (== `(pair ,e1 ,e2) e)
         (== `(pair ,e1^ ,e2^) e^)
         (evalo gamma e1 e1^)
         (evalo gamma e2 e2^))])))

(chko
 #:out #:!c (q) '(Type lz)
 (evalo '() '((lambda (x : (Type (lsucc lz))) x) (Type lz)) q)

 #:out #:!c (q) 'x
 (evalo '() 'x q)

 #:out #:!c (q) '(closure () (x : (Type lz)) x)
 (evalo '()
        '((lambda (f : (Pi (x : (Type lz)) (Type lz))) f)
          (lambda (x : (Type lz)) x))
        q)

 ; NB: Fragile set
 #:subset #:n 30 #:!c (q)
 '(x
   (fst (pair x _.0))
   ((lambda (_.0 : _.1) _.0) x)
   ((lambda (_.0 : _.1) x) _.2)
   (snd (pair _.0 x))
   ((lambda (_.0 : _.1) x) (lambda (_.2 : _.3) _.4))
   ((lambda (_.0 : _.1) x) (Type _.2)))
 (evalo '() q 'x)

 ; NB: Fragile set
 #:subset #:n 30 #:!c (q)
 '((Type _.0)
   _.0
   (Pi (_.0 : (Type _.1)) (Type _.2))
   (Pi (_.0 : _.1) (Type _.2))
   (Pi (_.0 : (Type _.1)) _.0))
 (evalo '() q q)

 #:= #:!c (q) '(x)
 (evalo '() '(fst (pair x y)) q)

 #:= #:!c (q) '(y)
 (evalo '() '(snd (pair x y)) q))

(define typeo
  (lambda (Gamma e gamma A)
    (conde
      [(varo e) ;; T-Var
       (lookupo e Gamma A)]
      [(fresh (x A^ B Gamma^ gamma^ i) ;; T-Pi-Prop
         (== `(Pi (,x : ,A^) ,B) e)
         (ext-envo Gamma x A^ Gamma^)
         (ext-envo gamma x x gamma^)
         (== A `(Type lz))
         (typeo Gamma A^ gamma `(Type ,i))
         (typeo Gamma^ B gamma^ `(Type lz)))]
      [(fresh (x A^ B Gamma^ gamma^ i j k) ;; T-Pi-Type
         (== `(Pi (,x : ,A^) ,B) e)
         (ext-envo Gamma x A^ Gamma^)
         (ext-envo gamma x x gamma^)
         (== A `(Type ,k))
         (max-levelo i j k)
         (typeo Gamma A^ gamma `(Type ,i))
         (typeo Gamma^ B gamma^ `(Type ,j)))]
      [(fresh (x A^ body B Gamma^ gamma^ i) ;; T-Lam
         (== `(lambda (,x : ,A^) ,body) e)
         (== `(Pi (,x : ,A^) ,B) A)
         (ext-envo Gamma x A^ Gamma^)
         (ext-envo gamma x x gamma^)
         (typeo Gamma A^ gamma `(Type ,i))
         (typeo Gamma^ body gamma^ B))]
      [(fresh (e1 e2 A^ B gamma^ x) ;; T-App
         ;; I suspect this could use more constraints to allow typeo to return different subgammas
         ;; from type-checko, but I'll sort that out later.
         ;; Unification might just do the right thing
         (== `(,e1 ,e2) e)
         (== A B)
         (ext-envo gamma^ x e2 gamma)
         (type-checko Gamma e2 gamma^ A^)
         (typeo Gamma e1 gamma^ `(Pi (,x : ,A^) ,B)))]
      [(fresh (i)
         (== `(Type ,i) e) ;; T-Type
         (levelo i)
         (== `(Type (lsucc ,i)) A))])))

;; Need infer/check distinction for algorithmic interpretation.
(define (type-checko Gamma e gamma A)
  (fresh (B) ;; T-Conv
    (typeo Gamma e gamma B)
    (evalo gamma B A)))

(define lookupo
  (lambda (x gamma term)
    (fresh (y t gamma^)
      (== `((,y . ,t) . ,gamma^) gamma)
      (conde
        [(== x y) (== t term)]
        [(=/= x y) (lookupo x gamma^ term)]))))

(chko
 #:out #:!c (q) '(Type (lsucc lz))
 (typeo '() '(Type lz) '() q)

 #:= (q) '()
 (typeo '() 'z '() q)

 #:out #:!c (q) '(Type lz)
 (typeo '((z . (Type lz))) 'z '() q)

 #:out #:!c (q) '(Pi (x : (Type lz)) (Type lz))
 (typeo '() '(lambda (x : (Type lz)) x) '() q)

 #:= (q gamma) '()
 (typeo '() '((lambda (x : (Type lz)) (Type lz)) (Type lz)) gamma q)

 #:out #:!c (q gamma) '((Type (lsucc lz)) ((x . (Type lz)) . _.0))
 (typeo '() '((lambda (x : (Type (lsucc lz))) (Type lz)) (Type lz)) gamma q)

 #:out #:!c (q gamma) '((Type (lsucc lz)) ((x . (Type lz)) . _.0))
 (typeo '() '((lambda (x : (Type (lsucc lz))) x) (Type lz)) gamma q)

 #:out #:!c (q) '(Pi (A : (Type lz)) (Pi (a : A) A))
 (typeo '() '(lambda (A : (Type lz))
                   (lambda (a : A)
                     a)) '() q)

 ;; Try inferring some types
 #:in #:n 5 #:!c (q ?1 ?2) '((Pi (A : (Type lz)) (Pi (a : A) A)) (Type lz) A)
 (typeo '() `(lambda (A : ,?1)
                   (lambda (a : ,?2)
                     a)) '() q)

 ;; Try inferring some terms
 #:in #:n 2 #:!c (e) '(lambda (A : (Type lz))
                  (lambda (a : A)
                    a))
 (typeo '() e '() `(Pi (A : (Type lz)) (Pi (a : A) A)))

 ;; Check dependent application
 #:in #:n 1 #:!c (q) '(Pi (a : (Type lz)) (Type lz))
 (fresh (gamma ?1 q1)
        (typeo '() `((lambda (A : ,?1)
                           (lambda (a : A)
                             a))
                         (Type lz)) gamma q1)
        (evalo gamma q1 q))

 ;; Check conversion
 #:in #:n 1 #:!c (q) '(Pi (a : (Type lz)) (Type lz))
 (fresh (gamma ?1)
        (type-checko '() `((lambda (A : ,?1)
                                 (lambda (a : A)
                                   a))
                               (Type lz)) gamma q))

 ;; Check False as a concept
 #:out #:n 1 #:!c (q) '(Type lz)
 (type-checko '() `(Pi (α : (Type lz)) α) '() q)

 ;; Prove me some Nats
 #:subset #:n 5 #:!c (e) '(z (s z))
 (fresh (gamma)
        (typeo '((z . Nat) (s . (Pi (x : Nat) Nat)) (Nat . (Type lz)))
               e gamma 'Nat)))

;; Prove False

;; Have been run for 60 seconds
#;(chko
 #:= #:t 60 (e) '((()))
 (typeo '() e '() '(Pi (α : (Type lz)) α))

;; Prove False under some assumptions
 #:= #:t 60 (e) '((()))
 (typeo '((f . (Pi (A : (Type lz))
                   (Pi (B : (Type lz))
                       (Pi (_ : A) B))))
          (z . Nat)
          (s . (Pi (n : Nat) Nat))
          (Nat . (Type lz))) e '() '(Pi (α : (Type lz)) α)))

;; Let's try some lists
(chko
 #:subset #:n 2 #:!c (e) '(nil)
 (fresh (gamma)
        (typeo '((cons . (Pi (a : Nat) (Pi (cdr : NatList) NatList)))
                 (nil . NatList)
                 (NatList . (Type lz))
                 (z . Nat)
                 (s . (Pi (x : Nat) Nat))
                 (Nat . (Type lz)))
               e gamma 'NatList))

 #:subset #:n 50 #:!c (e) '(nil ((cons z) nil))
 (fresh (gamma)
        (typeo '((cons . (Pi (a : Nat) (Pi (cdr : NatList) NatList)))
                 (nil . NatList)
                 (NatList . (Type lz))
                 (z . Nat)
                 (s . (Pi (x : Nat) Nat))
                 (Nat . (Type lz)))
               e gamma 'NatList)))

(define eq-decl
  '((refl . (Pi (A : (Type lz)) (Pi (a : A) (((eq A) a) a))))
    (eq . (Pi (A : (Type lz)) (Pi (a : A) (Pi (b : A) (Type lz)))))))

(define nat-decl
  '((z . Nat)
    (s . (Pi (n : Nat) Nat))
    (Nat . (Type lz))))

(chko
 #:out #:n 2 #:!c (A) '(Type lz)
 (lookupo 'Nat (append eq-decl nat-decl) A)

 #:out #:n 1 #:!c (A gamma) '((Pi (a : A) (((eq A) a) a))

                              ((A . Nat) . _.0))

 (typeo (append eq-decl nat-decl) '(refl Nat) gamma A)

 ;; Infer the type of (refl Nat z)
 #:out #:n 1 #:!c (A gamma) '((((eq A) a) a)

                              ((a . z)
                               (A . Nat)
                               ;; TODO: includes incorrect (Nat . A) binding...
                               . _.0))

 (typeo (append eq-decl nat-decl)
        '((refl Nat) z) gamma A)

 ;; Find some proofs that z = z
 #:in #:n 2 #:!c (e) '((refl Nat) z)
 (fresh (gamma)
        (typeo (append eq-decl nat-decl)
               e `((a . z) (A . Nat) . ,gamma) '(((eq A) a) a))))

;; Let's try polymorphic Lists
(chko
 #:out #:n 1 #:!c (e) '(nil Nat)
 (fresh (gamma)
        (typeo '((cons . (Pi (A : (Type lz)) (Pi (a : A) (Pi (cdr : (List A)) (List A)))))
                 (nil . (Pi (A : (Type lz)) (List A)))
                 (List . (Pi (A : (Type lz)) (Type lz)))
                 (z . Nat)
                 (s . (Pi (x : Nat) Nat))
                 (Nat . (Type lz)))
               e `((A . Nat) . ,gamma) '(List A)))

 #:subset #:n 5 #:!c (e) '((nil Nat)
 ;; NB: Busy eta-expanding things...
                            #;(((cons Nat) z) (nil Nat)))
 (fresh (gamma)
        (typeo '((cons . (Pi (A : (Type lz)) (Pi (a : A) (Pi (cdr : (List A)) (List A)))))
                 (nil . (Pi (A : (Type lz)) (List A)))
                 (List . (Pi (A : (Type lz)) (Type lz)))
                 (z . Nat)
                 (s . (Pi (x : Nat) Nat))
                 (Nat . (Type lz)))
               e `((A . Nat) . ,gamma) '(List A)))

 ;; But it's in there.
 #:= #:n 1 #:!c (e) '()
 (fresh (gamma)
        (typeo '((cons . (Pi (A : (Type lz)) (Pi (a : A) (Pi (cdr : (List A)) (List A)))))
                 (nil . (Pi (A : (Type lz)) (List A)))
                 (List . (Pi (A : (Type lz)) (Type lz)))
                 (z . Nat)
                 (s . (Pi (x : Nat) Nat))
                 (Nat . (Type lz)))
               '(((cons Nat) z) (nil Nat)) `((A . Nat) . ,gamma) '(List A))))

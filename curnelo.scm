#lang racket/base
(require
 "mk/mk.scm"
 rnrs/base-6
 rnrs/lists-6
 chk)

(define (varo e)
  (conde
   [(symbolo e)
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

(define evalo
  (lambda (gamma e e^)
    (conde
      [(fresh (i)
         (== `(Type ,i) e)
         (== `(Type ,i) e^))]
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
      [(fresh (e1 e2 e2^ x A ebody env)
         (== `(,e1 ,e2) e)
         (evalo gamma e1
                `(closure ,env (,x : ,A) ,ebody))
         (evalo gamma e2 e2^)
         (fresh (gamma^)
           (ext-envo gamma
                     x
                     e2^
                     gamma^)
           (evalo gamma^ ebody e^)))])))

(chk
 (run* (q)
       (evalo '() '((lambda (x : (Type (lsucc lz))) x) (Type lz)) q))
 '(((Type lz)))

 (run* (q)
       (evalo '() 'x q))
 '((x))

 (run* (q)
       (evalo '()
              '((lambda (f : (Pi (x : (Type lz)) (Type lz))) f)
                (lambda (x : (Type lz)) x))
              q))
 '(((closure () (x : (Type lz)) x)))

 (run 5 (q)
      (evalo '() q 'x))
 '((x)
   (((lambda (_.0 : _.1) x) (Type _.2))
    (=/= ((_.0 x))))
   (((lambda (_.0 : _.1) _.0) x)
    (=/= ((_.0 Pi)) ((_.0 Type)) ((_.0 closure)) ((_.0 lambda)))
    (sym _.0))
   (((lambda (_.0 : _.1) x) _.2)
    (=/= ((_.0 x)) ((_.2 Pi)) ((_.2 Type)) ((_.2 closure)) ((_.2 lambda)))
    (sym _.2))
   (((lambda (_.0 : _.1) x) (lambda (_.2 : _.3) (Type _.4))) (=/= ((_.0 x)))))

 (run 5 (q)
      (evalo '() q q))
 '(((Type _.0))
   (_.0 (=/= ((_.0 Pi)) ((_.0 Type)) ((_.0 closure)) ((_.0 lambda))) (sym _.0))
   ((Pi (_.0 : (Type _.1)) (Type _.2)))
   ((Pi (_.0 : _.1) (Type _.2))
    (=/= ((_.1 Pi)) ((_.1 Type)) ((_.1 closure)) ((_.1 lambda)))
    (sym _.1))
   ((Pi (_.0 : (Type _.1)) _.0)
    (=/= ((_.0 Pi)) ((_.0 Type)) ((_.0 closure)) ((_.0 lambda)))
    (sym _.0))))

(define typeo
  (lambda (Gamma e gamma A)
    (conde
     [(fresh (i)
        (== `(Type ,i) e) ;; T-Type
        (levelo i)
        (== `(Type (lsucc ,i)) A))]
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
      [(fresh (e1 e2 A^ B gamma^^ gamma^ x)
         ;; I suspect this could use more constraints to allow typeo to return different subgammas
         ;; from type-checko, but I'll sort that out later.
         ;; Unification might just do the right thing
         (== `(,e1 ,e2) e)
         (ext-envo gamma^ x e2 gamma)
         (type-checko Gamma e2 gamma^ A^)
         (typeo Gamma e1 gamma^ `(Pi (,x : ,A^) ,B))
         (== A B))])))

;; Need infer/check distinction for algorithmic interpretation.
(define (type-checko Gamma e gamma A)
  (fresh (B)
    (typeo Gamma e gamma B)
    (evalo gamma B A)))

(define lookupo
  (lambda (x gamma term)
    (fresh (y t gamma^)
      (== `((,y . ,t) . ,gamma^) gamma)
      (conde
        [(== x y) (== t term)]
        [(=/= x y) (lookupo x gamma^ term)]))))

(require racket/function)
(chk
 (run* (q)
       (typeo '() '(Type lz) '() q))
 '(((Type (lsucc lz))))

 (run* (q)
       (typeo '() 'z '() q))
 '()

 (run* (q)
       (typeo '((z . (Type lz))) 'z '() q))
 '(((Type lz)))

 (run* (q) (typeo '() '(lambda (x : (Type lz)) x) '() q))
 '(((Pi (x : (Type lz)) (Type lz))))

 (run* (q gamma)
       (typeo '() '((lambda (x : (Type lz)) (Type lz)) (Type lz)) gamma q))
 '()

 (run* (q gamma)
       (typeo '() '((lambda (x : (Type (lsucc lz))) (Type lz)) (Type lz)) gamma q))
 '((((Type (lsucc lz))
     ((x . (Type lz)) . _.0))))

 (run* (q gamma)
       (typeo '() '((lambda (x : (Type (lsucc lz))) x) (Type lz)) gamma q))
 '((((Type (lsucc lz))
     ((x . (Type lz)) . _.0))))

 (run* (q)
       (typeo '() '(lambda (A : (Type lz))
                      (lambda (a : A)
                        a)) '() q))
 '(((Pi (A : (Type lz))
      (Pi (a : A)
          A))))

 ;; Try inferring some types
 #:? (curry member '(((Pi (A : (Type lz)) (Pi (a : A) A))
                      (Type lz) A)))
 (run 5 (q ?1 ?2)
      (typeo '() `(lambda (A : ,?1)
                    (lambda (a : ,?2)
                      a)) '() q))

 ;; Try inferring some terms
 #:? (curry member '((lambda (A : (Type lz))
                       (lambda (a : A)
                         a))))
 (run 2 (e)
      (typeo '() e '() `(Pi (A : (Type lz)) (Pi (a : A) A))))

 ;; Check dependent application
 #:? (curry member '((Pi (a : (Type lz)) (Type lz))))
 (run 1 (q)
      (fresh (gamma ?1 q1)
             (typeo '() `((lambda (A : ,?1)
                            (lambda (a : A)
                              a))
                          (Type lz)) gamma q1)
             (evalo gamma q1 q)))

 ;; Check conversion
 #:? (curry member '((Pi (a : (Type lz)) (Type lz))))
 (run 1 (q)
      (fresh (gamma ?1)
             (type-checko '() `((lambda (A : ,?1)
                                  (lambda (a : A)
                                    a))
                                (Type lz)) gamma q)))

 )

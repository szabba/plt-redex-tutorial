#lang racket

(require redex)
(require redex/tut-subst)

(define-language L
  [e (e e ...)
     (λ ((x t) ...) e)
     x
     (amb t e ...)
     number
     (+ e ...)
     (if0 e e e)
     (fix e)]
  [t (→ t ... t) num]
  [x variable-not-otherwise-mentioned])

(define-extended-language L+Γ L
  [Γ · (x : t Γ)])

(define-judgment-form
  L+Γ
  #:mode (types I I O)
  #:contract (types Γ e t)
  
  ; application
  [(types Γ e_1 (→ t_2 t_r ... t_out))
   (types Γ e_2 t_2)
   (types Γ e_r t_r) ...
   -----------------------------------
   (types Γ
          (e_1 e_2 e_r ...)
          t_out)]
  
  ; abstraction
  [(types (x : t_1 Γ) e t_2)
   -----------------------------------
   (types Γ (λ ((x t_1)) e) (→ t_1 t_2))]
  
  [(types (x_1 : t_1 Γ)
          (λ ((x_r t_r) ...) e_body)
          (→ t_r ... t_out))
   -----------------------------------------
   (types Γ
          (λ ((x_1 t_1) (x_r t_r) ...) e_body)
          (→ t_1 t_r ... t_out))]
  
  ; fixpoint
  [(types Γ
          e
          (→ (→ t_first t_rest  ... t_out)
             t_first t_rest ... t_out))
   --------------------------------------------
   (types Γ
          (fix e)
          (→ t_first t_rest ... t_out))]
  
  ; lookup
  [---------------------
   (types (x : t Γ) x t)]
  
  ; no-duplicates in type environment
  [(types Γ x_1 t_1)
   (side-condition (different x_1 x_2))
   ------------------------------------
   (types (x_2 : t_2 Γ) x_1 t_1)]
  
  ; plus
  [(types Γ e num) ...
   -----------------------
   (types Γ (+ e ...) num)]
  
  ; number
  [--------------------
   (types Γ number num)]
  
  ; if0
  [(types Γ e_1 num)
   (types Γ e_2 t)
   (types Γ e_3 t)
   -----------------------------
   (types Γ (if0 e_1 e_2 e_3) t)]
  
  ; amb
  [-------------------
   (types Γ (amb t) t)]
  
  [(types Γ e_h t)
   (types Γ (amb t e_t ...) t)
   -------------------------------
   (types Γ (amb t e_h e_t ...) t)])

(define-metafunction L+Γ
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

(test-equal
 (judgment-holds
  (types · (amb num 1) t)
  t)
 (term (num)))

(test-equal
 (judgment-holds
  (types · (amb (→ num num)) t)
  t)
 (term ((→ num num))))

(test-equal
 (judgment-holds
  (types ·
         (amb (→ num num) (λ ((x num)) x))
         t)
  t)
 (term ((→ num num))))

(test-equal
 (judgment-holds
  (types ·
         ((λ ((x num)) x) 3)
         t)
  t)
 (term (num)))

(test-equal
 (judgment-holds
  (types ·
         (λ ((x num)
             (y num))
           (+ x y))
         t)
  t)
 (term ((→ num num num))))

(test-equal
 (judgment-holds
  (types ·
         (λ ((x num)
             (y (→ num num)))
           (y x))
         t)
  t)
 (term ((→ num (→ num num) num))))

(test-equal
 (judgment-holds
  (types ·
         ((λ ((x num)
              (y (→ num num)))
            (y x))
          0
          (λ ((x num)) x))
         t)
  t)
 (term (num)))

(test-equal
 (judgment-holds
  (types ·
         (fix (λ ((f (→ num num)) (x num))
                (if0 x
                     0
                     (if0 (+ x -1)
                          1
                          (+ (f (+ x -2))
                             (f (+ x -1)))))))
         t)
  t)
 (term ((→ num num))))

(test-equal
 (judgment-holds
  (types ·
         (fix (λ ((f (→ num num num)) (x num) (y num))
                (+ (f x y) (f y x))))
         t)
  t)
 (term ((→ num num num))))

(define-extended-language Ev L+Γ
  (p (e ...))
  (P (e ... E e ...))
  (E (v E)
     (E e)
     (+ v ... E e ...)
     (if0 E e e)
     (fix E)
     hole)
  (v (λ ((x t) ...) e)
     (fix v)
     number))

(define-metafunction Ev
  Σ : number ... -> number
  [(Σ number ...)
   ,(apply + (term (number ...)))])

(define-metafunction Ev
  subst : (x v) ... e -> e
  [(subst (x v) ... e)
   ,(subst/proc x?
                (term (x ...))
                (term (v ...))
                (term e))])

(define x? (redex-match Ev x))

(define red
  (reduction-relation
   Ev
   #:domain p
   
   (--> (in-hole P (if0 0 e_1 e_2))
        (in-hole P e_1)
        "if0t")
   
   (--> (in-hole P (if0 v e_1 e_2))
        (in-hole P e_2)
        (side-condition (not (equal? 0 (term v))))
        "if0f")
   
   (--> (in-hole P ((fix (λ ((x t) ...) e)) v ...))
        (in-hole P ((λ ((x t) ...) e)
                    (fix (λ ((x t) ...) e))
                    v ...))
        "fix")
   
   (--> (in-hole P ((λ ((x t) ...) e) v ...))
        (in-hole P (subst (x v) ... e))
        "βv")
   
   (--> (in-hole P (+ number ...))
        (in-hole P (Σ number ...))
        "+")
   
   (--> (e_1 ... (in-hole E (amb t e_2 ...)) e_3 ...)
        (e_1 ... (in-hole E e_2) ... e_3 ...)
        "amb")))


(test-->>
 red
 (term (((λ ((x num)) (+ x 1)) 0)))
 (term (1)))

(test-->>
 red
 (term (((λ ((x num)
             (y num))
           (+ x y))
         1 3)))
 (term (4)))

(test-->>
 red
 (term
  (((fix (λ ((f (→ num num))
             (n num))
           n))
    0)))
 (term (0)))

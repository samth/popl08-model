(module redex-both mzscheme
  (require (planet "require.ss" ("ryanc" "require.plt" 1))           
           (lib "list.ss")
           (lib "trace.ss")
           (lib "match.ss"))
  (define-module redex
    (planet "reduction-semantics.ss" ("robby" "redex.plt" 3 12))
    (planet "gui.ss" ("robby" "redex.plt" 3 12))
    (planet "pict.ss" ("robby" "redex.plt" 3 12))
    (planet "generator.ss" ("robby" "redex.plt" 3 12))
    (planet "subst.ss" ("robby" "redex.plt" 3 12)))
  (require (lib "mrpict.ss" "texpict")
           (lib "class.ss")
           (lib "mred.ss" "mred"))
  (require-redex)
  
  (require (planet "environment.ss" ("cobbe" "environment.plt" 3 0)))
  
  (provide (all-defined-except require-for-template-redex require-for-syntax-redex require-redex))
  
  (define occur-lang
    (language (e (e e)
                 (if e e e)
                 wrong
                 x
                 v)
              (E (E e)
                 (v E)
                 (if E e e)
                 hole)
              (v (lambda (x : t) e) number boolean c)
              (boolean #t #f)
              (t int bool top #t #f (t -> t) (t -> t & t) (U t ...))
              (c add1 number? boolean? zero? not)
              (x (variable-except lambda add1 if number? boolean? zero? not))))
  
  (define occur-subst
    (subst
     [`(lambda (,v : ,t) ,body)
      (all-vars (list v))
      (build (lambda (vars body) `(lambda (,@vars : ,t) ,body)))
      (subterm (list v) body)]
     [`(if ,e1 ,e2 ,e3)
       (all-vars '())
       (build (lambda (vars e1 e2 e3) `(if ,e1 ,e2 ,e3)))
       (subterm '() e1)
       (subterm '() e2)
       (subterm '() e3)]
     [(or (? boolean?) (? (lambda (x) (eq? x 'wrong))) (? number?)) (constant)]
     [(? symbol?) (variable)]
     [`(,fun ,arg)
      (all-vars '())
      (build (lambda (vars fun  arg) `(,fun ,arg)))
      (subterm '() fun)
      (subterm '() arg)]))  
  
  ;; free-vars : e -> (listof x)
  (define-metafunction free-vars
    occur-lang
    [(e_1 e_2) ,(apply append (term ((free-vars e_1) (free-vars e_2))))]
    [x_1 ,(list (term x_1))]
    [(if e_1 e_2 e_3) ,(apply append (term ((free-vars e_1) (free-vars e_2) (free-vars e_3))))]                      
    [(lambda (x_1) e_1)
     ,(remq* (term (x_1)) (term (free-vars (term e_1))))]
    [v_1 ,null])
  
  (define (closed e) (equal? (term (free-vars ,e)) null))
  
  (define value? (test-match occur-lang v))
  
  
  (define-metafunction delta
    occur-lang
    [(add1 v_1) ,(if (number? (term v_1)) (add1 (term v_1))
                     (term wrong))]
    [(zero? v_1) ,(if (number? (term v_1)) (= 0 (term v_1))
                      (term wrong))]
    [(not v_1) ,(if (boolean? (term v_1)) (not (term v_1))
                    (term wrong))]
    [(number? v_1) ,(if (number? (term v_1)) (term #t) (term #f))]
    [(boolean? v_1) ,(if (boolean? (term v_1)) (term #t) (term #f))])

  (define reductions
    (reduction-relation 
     occur-lang
     [==> ((lambda (variable_1 : t_1) e_body) v_arg)
           ,(occur-subst (term variable_1)
                         (term v_arg)
                         (term e_body))
           E-Beta]     
     [==> (if #f e_2 e_3)
          ,(term e_3)
          E-IfFalse]
     [==> (if #f e_2 e_3)
          ,(term #f)
          E-IfFalseBad]
     [==> (if v_1 e_2 e_3)
          ,(term e_2)
          E-IfTrue
          (side-condition (not (eq? (term v_1) #f)))]
     [--> (in-hole E_1
                   (c_op v_arg))
          ,(let ([v (term (delta (c_op v_arg)))])
             (if (equal? v (term wrong))
                 (term wrong)
                 (term (in-hole E_1 ,v))))
          E-Delta]
     where
     [(==> a b) (--> (in-hole E_1 a) (in-hole E_1 b))]
     ))
  
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; typechecking from here ;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  
  (define-struct type () #f)
  (define-struct (top-type type) () #f)
  (define-struct (base-type type) (name) #f)
  (define-struct (proc-type type) (arg result latent) #f)
  (define-struct (union-type type) (elems) #f)
  
  (define-struct effect () #f)
  (define-struct (no-effect effect) () #f)
  (define-struct (latent-type-effect effect) (t) #f)
  (define-struct (type-effect effect) (t v) #f)
  (define-struct (true-effect effect) () #f)
  (define-struct (false-effect effect) () #f)
  (define-struct (var-effect effect) (v) #f)
  
  (define N (make-base-type 'Number))
  (define TT (make-base-type #t))
  (define FF (make-base-type #f))
  
  (define NE (make-no-effect))
  (define Top (make-top-type))
  
  (define-struct  tc-result (type effect) #f)

  

  ;; this does type intersection
  (define (type-restrict old restriction)
    (if (subtype restriction old) restriction
        (match old
          [($ union-type e) (apply Un (map (lambda (x) (type-restrict restriction x)) e))]
          [_ restriction])))
  
  ;; this is set minus on types
  (define (type-minus old remove)
    (if (subtype old remove) (Un)
        (match old
          [($ union-type e) (apply Un (map (lambda (x) (type-minus x remove)) e))]
          [_ old])))
  
  (define (update-env env key f)
    (extend-env (list key) (list (f (lookup env key))) env))
  
  (define ((envop f) env eff)
    (match eff
      [($ type-effect t v) (update-env env v (lambda (old) (f old t)))]
      [_ env]))
  (define env+ (envop type-restrict))
  (define env- (envop type-minus))
  
  (define ret (case-lambda
                [(a) (make-tc-result a NE)]
                [(a b) (make-tc-result a b)]))
  
  (define ->
    (case-lambda
      [(a b) (make-proc-type a b NE)]
      [(a b c) (make-proc-type a b (make-latent-type-effect c))]))
  
  (define (Un . args) 
    (define (make-union/one t) (if (union-type? t) (union-type-elems t) (list t)))    
    (define (union2 a b)     
      (if (subtype a b)
          b
          (if (subtype b a) a
              (make-union-type (append (make-union/one a) (make-union/one b))))))
    (foldl union2 (make-union-type (list)) args))
  #;(define (Un . elems)
    (cond [(= 1 (length elems)) (car elems)]
          [else (let* ([unions (filter union-type? elems)]
                       [not-unions (filter (lambda (x) (not (union-type? x))) elems)]
                       [lists (map union-type-elems unions)]
                       [l (apply append lists)]
                       [l* (append l not-unions)])
                  (if (= 1 (length l*)) (car l*)
                      (make-union-type l*)))]))    
  
  (define-metafunction delta-t
    occur-lang
    [add1 ,(ret (-> N N) (make-true-effect))]
    [not ,(ret (-> Top B) (make-true-effect))]
    [zero? ,(ret (-> N B) (make-true-effect))]
    [number? ,(ret (-> Top B N) (make-true-effect))]
    [boolean? ,(ret (-> Top B B) (make-true-effect))])
  

  (define-struct (exn:tc exn:fail) (stuff) #f)
  (define (fail! . args) (apply error "typechecking failed"  args))
  
  (define (parse-type t)
    (match t
      ['number N]
      ['int N]
      ['boolean B]
      ['bool B]
      [#t TT]
      [#f FF]
      ['top Top]      
      [(a '-> b ) (make-proc-type (parse-type a) (parse-type b) NE)]
      [(a '-> b '& c) (make-proc-type (parse-type a) (parse-type b) (parse-type c))]
      [('U e ...) (make-union-type (map parse-type e))]))
  
  (define (subtype a b)
    (match (list a b)
      [(a a) #t]
      [(_ ($ top-type)) #t]
      [(($ proc-type a b latent) ($ proc-type a* b* latent)) (and (subtype a* a) (subtype b b*))]
      [(($ union-type e) b) (andmap (lambda (x) (subtype x b)) e)]
      [(a ($ union-type e)) (ormap (lambda (x) (subtype a x)) e)]
      [_ #f]))
  
  ;(trace type-minus)
  ;(trace type-restrict)
  ;(trace env+)
  
  (define (null-intersect? a b)
    (match (list a b)
      [(a b) (=> unmatch) (not (or (subtype a b)
                                   (subtype b a)
                                   (unmatch)))]
      [((? base-type?) (? base-type?)) #t]
      [else #f]
      ))
  
  (define B (Un TT FF))
  (define initial-env (symbol-env (number-var N) (boolean-var B)))

  
  )
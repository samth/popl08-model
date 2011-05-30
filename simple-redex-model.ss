(module simple-redex-model mzscheme
  (require (lib "list.ss")
           (lib "trace.ss")
           (lib "match.ss"))
  
  (require (planet "environment.ss" ("cobbe" "environment.plt" 3 0)))
  
  (require "redex-ex.ss" "redex-both.ss")  
  (require (lib "mrpict.ss" "texpict")
           (lib "class.ss")
           (lib "mred.ss" "mred"))
  (dc-for-text-size (new bitmap-dc% [bitmap (make-object bitmap% 1 1)]))
  (require-redex)


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; typechecking from here ;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define enable-T-IfAnd (make-parameter #f))
  (define enable-T-IfOr (make-parameter #f))
  (define enable-T-AbsPred (make-parameter #f))
  (define enable-T-IfTrue (make-parameter #t))
  (define enable-T-IfFalse (make-parameter #t))
  (define enable-T-IfVar (make-parameter #f))
  
  (define (comb-eff tst thn els)
    (match (list tst thn els)
      [(p0 p p) p]
      ;; silly student expansion
      [(p0 ($ true-effect) ($ false-effect)) p0]
      [(($ true-effect) p1 p2) p1]
      [(($ false-effect) p1 p2) p2]
      ;; or
      [(($ type-effect t v) ($ true-effect) ($ type-effect s v)) 
       (if (enable-T-IfOr)
           (make-type-effect (Un t s) v)
           NE)]
      [_ NE]))

 
  (define (typecheck e env)
    (define-metafunction tc/local 
      occur-lang
      [number ,(ret N (make-true-effect))]
      [boolean_1 ,(if (term boolean_1)
                      (ret TT (make-true-effect))
                      (ret FF (make-false-effect)))]
      [c_1 (delta-t c_1)]
      [x_1 ,(ret (lookup env (term x_1) (lambda (x) (fail! "lookup" x))) (make-var-effect (term x_1)))]
      [(if e_test e_then e_else)
       ,(match-let* ([($ tc-result test-ty test-eff) (typecheck (term e_test) env)])          
          (cond
            ;; this is slightly more aggressive in terms of the returned effect than the model
            ;; this is neccessary for typechecking tc7
            [(and (enable-T-IfFalse) (false-effect? test-eff)) (typecheck (term e_else) env)]
            [(and (enable-T-IfTrue) (true-effect? test-eff)) (typecheck (term e_then) env)]
            [(and (enable-T-IfVar) (var-effect? test-eff))
             (let ([v (var-effect-v test-eff)])
               (match-let* ([($ tc-result ty1 eff1) (typecheck (term e_then) (env- env (make-type-effect FF v)))]
                            [($ tc-result ty2 eff2) (typecheck (term e_else) (update-env env v (lambda (old) FF)))]
                            [new-eff (comb-eff test-eff eff1 eff2)])
                 (ret (Un ty1 ty2) new-eff)))]
            [else 
             (match-let* ([($ tc-result ty1 eff1) (typecheck (term e_then) (env+ env test-eff))]
                          [($ tc-result ty2 eff2) (typecheck (term e_else) (env- env test-eff))]
                          [new-eff (comb-eff test-eff eff1 eff2)])
               (ret (Un ty1 ty2) new-eff))]))]
      [(lambda (x_1 : t_1) e_body) 
       ,(match-let* ([in (parse-type (term t_1))]
                     [($ tc-result out out-eff) 
                      (typecheck (term e_body) (extend-env (list (term x_1)) (list in) env))])
          (match out-eff
            [(and (? (lambda _ (enable-T-AbsPred)))                                                   
                  ($ type-effect t v)
                  (= type-effect-v (? (lambda (s) (eq? s (term x_1))))))
             ;(printf "got here~n")
             (ret (-> in out t) (make-true-effect))]
            [_ (ret (-> in out) (make-true-effect))]))]
      [(e_1 e_2) ,(let ()
                    (define (mk-res-eff arg arg-eff latent e2)
                      (cond [(and (latent-type-effect? latent)
                                  (var-effect? arg-eff))
                             (make-type-effect (latent-type-effect-t latent)
                                               (var-effect-v arg-eff))]
                            [(and (latent-type-effect? latent)
                                  (subtype arg (latent-type-effect-t latent)))
                             (make-true-effect)]
                            [(and (latent-type-effect? latent)
                                  (not (subtype arg latent))
                                  (closed e2)
                                  (value? e2))
                             (make-false-effect)]
                            [else NE]))
                    (match (typecheck (term e_1) env)
                      [($ tc-result ($ proc-type in out latent) eff)                      
                       (match-let* ([($ tc-result arg arg-eff) (typecheck (term e_2) env)]
                                    [res-eff (mk-res-eff arg arg-eff latent (term e_2))])
                         (if (subtype arg in)
                             (ret out res-eff)
                             (error "argument not subtype" arg in e)))]
                      [($ tc-result ($ union-type elems) eff)
                       (match-let* ([arr-elems (filter proc-type? elems)]
                                    [($ tc-result arg arg-eff) (typecheck (term e_2) env)]
                                    [matched-arr-elems (filter (lambda (t) (subtype arg (proc-type-arg t))) arr-elems)])
                         (when (null? matched-arr-elems)
                           (fail! "no matching function type in union"))
                         (ret (apply Un (map proc-type-result matched-arr-elems))))]
                      [t (fail! "operator not a procedure" t (term e_1))]))]
      [e_1 ,(fail! "unknown expression" (term e_1))]


      )
    (term (tc/local ,e)))
  
  (define (tc e) (typecheck e initial-env))
  ;; is e1 below e2?
  (define (subeff e1 e2)
    (match (list e1 e2)
      [(p p) #t]
      [(($ false-effect) ($ true-effect)) #f]
      [(($ true-effect) ($ false-effect)) #f]
      [(($ true-effect) p) #t]
      [(($ false-effect) p) #t]
      [(($ no-effect) ($ type-effect _ _)) #t]
      [(($ no-effect) ($ var-effect _)) #t]
      [_ #f]))
  
  (define (check e node)
    (let* ([parents (term-node-parents node)]
           [parent-exprs (map term-node-expr parents)])
    (with-handlers ([exn:fail? (lambda _ #f)])
      (match-let* ([(($ tc-result parent-types parent-effs) ...) 
                    ;; if the parents don't typecheck, just ignore them
                    (with-handlers ([exn:fail? (lambda _ '())])
                      (map tc parent-exprs))]
                   [($ tc-result cur-type cur-eff) (tc e)])
        (and (andmap (lambda (t) (subtype cur-type t)) parent-types)
             (andmap (lambda (t) (subeff cur-eff t)) parent-effs))))))
  
  (define (check* e node)
    (define parents (term-node-parents node))
    (define children (term-node-children node))
    (define val? (value? e))
    (define parent-exprs (map term-node-expr parents))
    (define (check/plain e)
      (with-handlers ([exn:fail? (lambda _ #f)])
        (parameterize ([enable-T-IfTrue #f]
                       [enable-T-IfFalse #f])
          (tc e))))
    (define (check/middle e)
      (with-handlers ([exn:fail? (lambda _ #f)])
        (tc e)))
    (define (check/experimental e)
      (with-handlers ([exn:fail? (lambda _ #f)])
        (parameterize ([enable-T-IfAnd #t]
                       [enable-T-IfOr #t]
                       [enable-T-AbsPred #t]
                       [enable-T-IfVar #t])
          (tc e))))
    ;; check type preservation
    (define parent-types (with-handlers ([exn:fail? (lambda _ '())])
                           (map tc-result-type (map check/experimental parent-exprs))))
    (define cur-type (check/experimental e))
    (define preserve? (if cur-type
                          (let ([cur-type (tc-result-type cur-type)])
                            (andmap (lambda (t) (subtype cur-type t)) parent-types))
                          #t))
    (cond
      [(not preserve?) "purple"]
      ;; if it checks and doesn't reduce, but isn't a value
      [(and (not val?)
            (or (check/plain e)
                (check/middle e)
                (check/experimental e))
            (null? children))
       "blue"]
      ;; if it checks with no additions, then it's fine
      [(check/plain e) #t]
      ;; if we have to use the iftrue/false rules in the middle, that's ok
      [(and (not (null? parents)) (check/middle e)) "yellow"]
      ;; if we use them elsewhere, that's bad
      [(check/middle e) "MediumPurple"]
      ;; experimental rules get their own color
      [(check/experimental e) "green"]
      ;; this term didn't typecheck, but the parent did, which is bad
      [(and preserve? (not (null? parent-types))) "red"]
      ;; otherwise it didn't check at all, nor did the parents
      [else #f]))
  
  (define (r t) (apply-reduction-relation reductions t))
  (define (r* t) (apply-reduction-relation* reductions t))
  
  (define (tr t) (traces/pred occur-lang reductions (list t) check))
  
  (define (tr2 t) (traces occur-lang reductions t))

  
  (define (tr* . t) (traces/pred occur-lang reductions t check*))
  
  (define (trx t)
    (parameterize ([enable-T-IfAnd #t] ;; this rule is unsound
                   [enable-T-IfOr #t]
                   [enable-T-AbsPred #t])
      (tr t)))
  
  (print-struct #t)
  
  (provide tr* terms)

  #;(define t (lang->generator-table occur-lang (list 1 2 3 4 5 6 7 8 9 0) '(a b c x y z w i j k l) (list) (list 'wrong) 0))
  )
(module redex-ex mzscheme
  
  (require (lib "list.ss")
           (lib "trace.ss")
           (lib "match.ss")
           "redex-both.ss")
  
  (require-redex)
  (provide (all-defined))
    
  (define t1 (term ((lambda (x : top) x) 3)))
  (define t2 (term ((lambda (x : int) (add1 x)) 3)))
  
  (define t3 (term ((lambda (x : top) (if (number? x) (add1 x) 0)) #t)))

  (define t4 (term ((lambda (x : (U int bool)) (if (number? x) (add1 x) 0)) #t)))
  (define t5 (term ((lambda (x : (U int bool)) (if (number? x) (zero? x) (not x))) #t)))

  ;; these use the experimental features

  ;; T-AbsPred
  (define t6 (term ((lambda (x : top) (if ((lambda (y : top) (number? y)) x) (add1 x) 0)) #t)))
  ;; T-IfAnd
  (define t7 (term ((lambda (x : top) (if (if (boolean? x) x #f) (not x) #t)) 0)))

  ;; breaks T-IfAnd
  (define t8 (term ((lambda (x : (U int bool)) 
                      (if 
                       (if (boolean? x) ((lambda (y : top) #f) x) #f)
                       3
                       (add1 x)))
                    #f)))
  
  ;; T-IfOr
  (define t10 (term ((lambda (x : top) 
                      (if 
                       (if (boolean? x) #t (number? x))
                       (if (boolean? x) 1 (add1 x))
                       12))
                    9)))
  (define t10* (term ((lambda (x : top) 
                      (if 
                       (if (boolean? x) #t (number? x))
                       (if (boolean? x) 1 (add1 x))
                       12))
                    #f)))
  
  
  
  ;; shows red
  (define t9 (term (if #f (add1 #f) #f)))
  
  (define t11 (term ((lambda (v : (U int bool)) (if (boolean? v) 5 (add1 v))) #f)))
  
  ;; more examples
  
  (define t12 (term ((if 12 (lambda (x : top) 5) (lambda (x : top) 4)) 11)))
  (define t13 (term ((lambda (v : top) ((if v (lambda (x : top) 5) (lambda (x : top) 4)) 11)) #f)))
  
  (define bad 
    (term
     ((((lambda (x : (int -> (U int bool)))
          (lambda (y : bool)
            (if y
                x
                (lambda (z : int) z))))
        (lambda (x : int) #f))
       #f)
      0)))
  
  (define t14
    (term ((lambda (v : (U #f int))
             (if v (add1 v) 6))
           12)))
  (define t15
    (term ((lambda (v : (U #f int))
             (if v (add1 v) ((lambda (x : bool) 7) v)))
           #f)))
  (define t16
    (term ((lambda (v : (U #f int))
             (if v (add1 v) ((lambda (x : bool) 7) v)))
           42)))
  
  (define terms (list t1 t2 t3 t4 t5 t6 #;t7 #;t8 t9 t10 t10* t11 t12 t13 t14 t15 t16 bad))
  
  
  )
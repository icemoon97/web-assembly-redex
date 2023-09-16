#lang racket
(require redex)

;; ==================================================================================
;; SYNTAX
;; ==================================================================================

(define-language WA
  (e ::= (i32.const n) ;; constant
     i32.binop         ;; binary operators
     i32.relop         ;; relational operators
     i32.load          ;; load from memory
     i32.store         ;; store to memory
     memory.size       ;; get memory size
     memory.grow       ;; increase memory size
     (block e ...)     ;; label at end
     (loop e ...)      ;; label at start
     (br n)            ;; branch
     (brif n)          ;; conditional branch
     (getlocal n)      ;; get frame local
     (setlocal n)      ;; set frame local
     (call n)          ;; function call
     trap              ;; trap
     return)           ;; return  
  (n ::= integer)
  (i32.binop ::= add sub mul divs)
  (i32.relop ::= eq lts gts)
  (f ::= ((params n) (locals n) (body e ...)))
  (m ::= (f ...))
  ;; configuration for machine
  (c ::= ((mod m) (locals n ...) (mem n ...) (stack n ...) (instrs e ...)))
  )

;; ==================================================================================
;; MACHINE
;; ==================================================================================

(define-metafunction WA 
  binop : i32.binop n n -> n
  [(binop add n_1 n_2) ,(+ (term n_1) (term n_2))]
  [(binop sub n_1 n_2) ,(- (term n_1) (term n_2))]
  [(binop mul n_1 n_2) ,(* (term n_1) (term n_2))]
  [(binop divs n_1 n_2) ,(/ (term n_1) (term n_2))])

(define-metafunction WA 
  relop : i32.relop n n -> n
  [(relop eq n_1 n_2) ,(if (= (term n_1) (term n_2))
                           1
                           0)]
  [(relop lts n_1 n_2) ,(if (< (term n_1) (term n_2))
                            1
                            0)]
  [(relop gts n_1 n_2) ,(if (> (term n_1) (term n_2))
                            1
                            0)])
(define-metafunction WA
  save : (mem n ...) n n -> (mem n ...)
  [(save (mem n_1 ...) n_2 n_3) ,(list-set (term (mem n_1 ...))
                                           (+ (term n_3) 1)
                                           (term n_2))])

;; check if index is valid for given memory
(define (bounds-check mem index)
  (and (< index (length (rest mem)))
       (>= index 0)))

(define-extended-language WA-admin
  WA
  (e ::= ....
     (label (cont e ...) (n ...) (body e ...))
     (frame c)
     (returning n)))

(define ->machine
  (reduction-relation
   WA-admin
   [--> ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_1 ...) (instrs (i32.const n_2) e ...))
        ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_2 n_1 ...) (instrs e ...))
        D-const]
   
   [--> ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_2 n_1 n_stack ...) (instrs i32.binop e ...))
        ((mod m) (locals n_loc ...) (mem n_mem ...) (stack (binop i32.binop n_2 n_1) n_stack ...) (instrs e ...))
        D-binop]
   
   [--> ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n_2 n_1 n_stack ...) (instrs i32.relop e ...))
        ((mod m)(locals n_loc ...)(mem n_mem ...) (stack (relop i32.relop n_2 n_1) n_stack ...) (instrs e ...))
        D-relop]

   ;; memory rules
   [--> ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n_1 n_2 ...) (instrs i32.load e ...))
        ((mod m)(locals n_loc ...)(mem n_mem ...) (stack ,(list-ref (term (mem n_mem ...)) (+ (term n_1) 1))  n_2 ...) (instrs e ...))
        (side-condition (bounds-check (term (mem n_mem ...))
                                      (term n_1)))
        D-loadvalid]
   
   [--> ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n_1 n_2 ...) (instrs i32.load e ...))
        ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n_1 n_2 ...)(instrs trap))
        (side-condition (not (bounds-check (term (mem n_mem ...))
                                           (term n_1))))
        D-loadinvalid]
   
   [--> ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n_1 n_2 n_3 ...) (instrs i32.store e ...))
        ((mod m)(locals n_loc ...)(save (mem n_mem ...) n_1 n_2) (stack n_3 ...) (instrs e ...))
        (side-condition (bounds-check (term (mem n_mem ...))
                                      (term n_2)))
        D-storevalid]
   
   [--> ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n_1 n_2 n_3 ...) (instrs i32.store e ...))
        ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n_1 n_2 n_3 ...) (instrs trap))
        (side-condition (not (bounds-check (term (mem n_mem ...))
                                           (term n_2))))
        D-storeinvalid]
   
   [--> ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n ...) (instrs memory.size e ...))
        ((mod m)(locals n_loc ...)(mem n_mem ...) (stack ,(- (length (term (mem n_mem ...))) 1) n ...) (instrs e ...))
        D-size]

   [--> ((mod m)(locals n_loc ...)(mem n_mem ...) (stack n ...) (instrs memory.grow e ...))
        ((mod m)(locals n_loc ...) ,(append (term (mem n_mem ...)) (list 0 0)) (stack n ...) (instrs e ...))
        D-grow]

   ;; control flow rules
   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (label (cont e_cont ...) (n_1 ...) (body (br n_2) e_body ...)) e ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (br ,(- (term n_2) 1)) e ...))
        (side-condition (> (term n_2) 0))
        D-breakingcontinue]

   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (label (cont e_cont ...) (n_1 ...) (body (br 0) e_body ...)) e ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs e_cont ... e ...))
        D-breakingdone]

   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (label (cont e_cont ...) (n_1 ...) (body)) e ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs e ...))
        D-labeldone]

   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (label (cont e_cont ...) (n_1 ...) (body e_1 ...)) e ...))
        ((mod m)
         (locals n_loc2 ...)
         (mem n_mem2 ...)
         (stack n_stack ...)
         (instrs (label (cont e_cont ...) (n_2 ...) (body e_2 ...)) e ...))
        ;; checks that reduction relation can actually be applied (messy but works)
        (side-condition (not (empty? (apply-reduction-relation ->machine (term ((mod m)
                                                                                (locals n_loc ...)
                                                                                (mem n_mem ...)
                                                                                (stack n_1 ...)
                                                                                (instrs e_1 ...)))))))
        (where ((mod m)(locals n_loc2 ...)(mem n_mem2 ...) (stack n_2 ...) (instrs e_2 ...))
               ,(first (apply-reduction-relation ->machine (term ((mod m)
                                                                  (locals n_loc ...)
                                                                  (mem n_mem ...)
                                                                  (stack n_1 ...)
                                                                  (instrs e_1 ...))))))
        D-labelstep]
   
                            

   [--> ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_1 ...) (instrs (block e_1 ...) e_2 ...))
        ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_1 ...) (instrs (label (cont) () (body e_1 ...)) e_2 ...))
        D-block]
   
   [--> ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_1 ...) (instrs (loop e_1 ...) e_2 ...))
        ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_1 ...) (instrs (label (cont (loop e_1 ...)) () (body e_1 ...)) e_2 ...))
        D-loop]

   [--> ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_1 n_2 ...) (instrs (brif n_br) e ...))
        ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_2 ...) (instrs e ...))
        (side-condition (= (term n_1) 0))
        D-brif-false]
             
   [--> ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_1 n_2 ...) (instrs (brif n_br) e ...))
        ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_2 ...) (instrs (br n_br) e ...))
        (side-condition (not (= (term n_1) 0)))
        D-brif-true]

   ;; call stack rules
   [--> ((mod m) (locals n_loc ...)
                 (mem n_mem ...)
                 (stack n_1 ...)
                 (instrs (label (cont e_cont ...) (n ...) (trap e_body ...)) e ...))
        ((mod m) (locals n_loc ...)
                 (mem n_mem ...)
                 (stack n_1 ...)
                 (instrs trap))
        D-label-trap]
   
   [--> ((mod m) (locals n_loc ...)
                 (mem n_mem ...)
                 (stack n_1 ...)
                 (instrs (label (cont e_cont ...) (n ...) ((returning n_r) e_body ...)) e ...))
        ((mod m) (locals n_loc ...)
                 (mem n_mem ...)
                 (stack n_1 ...)
                 (instrs (returning n_r)))
        D-label-Returning]
   
   [-->((mod m) (locals n_loc ...)
                (mem n_mem ...)
                (stack n_v n_stack ...)
                (instrs (setlocal n_i) e ...))
       ((mod m) ,(list-set (term (locals n_loc ...))
                           (+ (term n_i) 1)
                           (term n_v))
                (mem n_mem ...)
                (stack n_stack ...)
                (instrs e ...))
       D-SetLocal]
   
   [--> ((mod m) (locals n_loc ...)
                 (mem n_mem ...)
                 (stack n_stack ...)
                 (instrs (getlocal n_i) e ...))
        ((mod m) (locals n_loc ...)
                 (mem n_mem ...)
                 (stack ,(list-ref (rest (term (locals n_loc ...))) (term n_i)) n_stack ...)
                 (instrs e ...))
        D-GetLocal]
   
   [--> ((mod m) (locals n_loc ...) (mem n_mem ...) (stack n_stack ...) (instrs (call n_i) e_inst ... ))
        ((mod m) (locals n_loc ...)
                 (mem n_mem ...)
                 ,(if (> (length (term (stack n_stack ...))) (+ (term n_p) 1))
                      (flatten (term (stack ,(list-tail (rest (term (stack n_stack ...))) (term n_p)))))
                      (term (stack)))
                 (instrs (frame ((mod m)
                                 ,(flatten (term (locals ,(append (reverse (take (rest (term (stack n_stack ...))) (term n_p))) (build-list (term n_l) (const 0))))))
                                 (mem n_mem ...)
                                 (stack)
                                 (instrs e_f ...))) e_inst ...))
        (where ((params n_p) (locals n_l) (body e_f ...))
               ,(list-ref (term m) (term n_i)))
        D-call]
       
   [--> ((mod m) (locals n_loc ...) (mem n_mem1 ...)
                 (stack n_stack ...)
                 (instrs (frame ((mod m)
                                 (locals n_c ...)
                                 (mem n_mem1 ...)
                                 (stack n_cs ...)
                                 (instrs e_c ...))) e ...))
        ((mod m) (locals n_loc ...) (mem n_mem2 ...)
                 (stack n_stack ...)
                 (instrs (frame ((mod m) (locals n_loc2 ...) (mem n_mem2 ...) (stack n_stack2 ...) (instrs e_2 ...))) e ...))
        (side-condition (not (empty? (apply-reduction-relation ->machine (term ((mod m)
                                                                                (locals n_c ...)
                                                                                (mem n_mem1 ...)
                                                                                (stack n_cs ...)
                                                                                (instrs e_c ...)))))))
        (where ((mod m) (locals n_loc2 ...) (mem n_mem2 ...) (stack n_stack2 ...) (instrs e_2 ...))
               ,(first (apply-reduction-relation ->machine (term ((mod m) (locals n_c ...) (mem n_mem1 ...) (stack n_cs ...) (instrs e_c ...))))))
        D-framestep]
   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (frame ((mod m)
                         (locals n_loc2 ...)
                         (mem n_mem2 ...)
                         (stack)
                         (instrs))) e ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem2 ...)
         (stack n_stack ...)
         (instrs e ...))
        D-Frame-Done-Empty]
   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (frame ((mod m)
                         (locals n_loc2 ...)
                         (mem n_mem2 ...)
                         (stack n n_stack2 ...)
                         (instrs))) e ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem2 ...)
         (stack n n_stack ...)
         (instrs e ...))
        D-Frame-Done]
   
 
   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n n_stack ...)
         (instrs return e ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (returning n) e ...))
        D-Return]
   
   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (label (cont e_cont ...) (n_label ...) (body (returning n) e_l ...)) e_i ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (returning n) e_i ...))
        D-Label-Returning]
   
   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (frame ((mod m)
                         (locals n_floc ...)
                         (mem n_fmem ...)
                         (stack n_fstack  ...)
                         (instrs (returning n) e_f ...)))
                 e_i ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (frame ((mod m)
                         (locals n_floc ...)
                         (mem n_fmem ...)
                         (stack  n)
                         (instrs)))
                 e_i ...))
        D-Frame-Returning]
   
   [--> ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs (frame ((mod m)
                         (locals n_floc ...)
                         (mem n_fmem ...)
                         (stack n_fstack  ...)
                         (instrs trap e_f ...)))
                 e_i ...))
        ((mod m)
         (locals n_loc ...)
         (mem n_mem ...)
         (stack n_stack ...)
         (instrs trap))
        D-Frame-trap]
        
   ))



;; ==================================================================================
;; TESTING
;; ==================================================================================

(define (test-WA program-term result-term)
  (test-equal (term ,(first (apply-reduction-relation* ->machine program-term)))
              result-term))

;; testing binop 
(test-WA (term ((mod ()) (locals) (mem) (stack) (instrs (i32.const 5) (i32.const 3) add)))
         (term ((mod ()) (locals) (mem) (stack 8) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 3 2) (instrs sub)))
         (term ((mod ()) (locals) (mem) (stack 1) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 4 3) (instrs mul)))
         (term ((mod ()) (locals) (mem) (stack 12) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 12 3) (instrs divs)))
         (term ((mod ()) (locals) (mem) (stack 4) (instrs))))
;; testing relop
(test-WA (term ((mod ()) (locals) (mem) (stack 5 5) (instrs eq)))
         (term ((mod ()) (locals) (mem) (stack 1) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 4 5) (instrs eq)))
         (term ((mod ()) (locals) (mem) (stack 0) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 5 3) (instrs gts)))
         (term ((mod ()) (locals) (mem) (stack 1) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 3 5) (instrs gts)))
         (term ((mod ()) (locals) (mem) (stack 0) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 3 5) (instrs lts)))
         (term ((mod ()) (locals) (mem) (stack 1) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 5 3) (instrs lts)))
         (term ((mod ()) (locals) (mem) (stack 0) (instrs))))
;; testing memory functions
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack 1 1) (instrs i32.store)))
         (term ((mod ()) (locals) (mem 0 1 0 0) (stack) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack 1 0) (instrs i32.store)))
         (term ((mod ()) (locals) (mem 1 0 0 0) (stack) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack 5 2 8 1) (instrs i32.store i32.store)))
         (term ((mod ()) (locals) (mem 0 8 5 0) (stack) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack 1 100) (instrs i32.store)))
         (term ((mod ()) (locals) (mem 0 0 0 0) (stack 1 100) (instrs trap))))
(test-WA (term ((mod ()) (locals) (mem 2 4 6 8) (stack 1) (instrs i32.load)))
         (term ((mod ()) (locals) (mem 2 4 6 8) (stack 4) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack 100) (instrs i32.load)))
         (term ((mod ()) (locals) (mem 0 0 0 0) (stack 100) (instrs trap))))
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack 1) (instrs memory.size)))
         (term ((mod ()) (locals) (mem 0 0 0 0) (stack 4 1) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack 1) (instrs memory.grow)))
         (term ((mod ()) (locals) (mem 0 0 0 0 0 0) (stack 1) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0 0 0) (stack) (instrs memory.size memory.grow memory.size)))
         (term ((mod ()) (locals) (mem 0 0 0 0 0 0) (stack 6 4) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack) (instrs (block (br 0)))))
         (term ((mod ()) (locals) (mem) (stack) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0) (stack) (instrs (block (i32.const 1) (i32.const 1) i32.store (br 0)))))
         (term ((mod ()) (locals) (mem 0 1) (stack) (instrs))))
;;testing control flow
(test-WA (term ((mod ()) (locals) (mem) (stack) (instrs (label (cont) () (body (br 5))))))
         (term ((mod ()) (locals) (mem) (stack) (instrs (br 4)))))
(test-WA (term ((mod ()) (locals) (mem) (stack) (instrs (label (cont add) () (body (br 0))) sub)))
         (term ((mod ()) (locals) (mem) (stack) (instrs add sub))))
(test-WA (term ((mod ()) (locals) (mem) (stack) (instrs (label (cont add) () (body)) sub)))
         (term ((mod ()) (locals) (mem) (stack) (instrs sub))))
(test-WA (term ((mod ()) (locals)
                         (mem)
                         (stack)
                         (instrs (label (cont (i32.const 2)) (5 4) (body (i32.const 6) add (br 0))))))
         (term ((mod ()) (locals) (mem) (stack 2) (instrs))))
(test-WA (term ((mod ()) (locals) (mem 0 0)
                         (stack)
                         (instrs (label (cont) (5 1) (body i32.store)))))
         (term ((mod ()) (locals) (mem 0 5) (stack) (instrs))))
(define test-nested-control (term ((mod ())
                                   (locals)
                                   (mem)
                                   (stack)
                                   (instrs (label (cont (i32.const 2))
                                                  ()
                                                  (body (label (cont) () (body (br 1)))))))))
(test-WA test-nested-control
         (term ((mod ()) (locals) (mem) (stack 2) (instrs))))

;testing call stack
(test-WA (term ((mod ())
                (locals 1)
                (mem)
                (stack)
                (instrs (getlocal 0))))
         (term ((mod ())
                (locals 1)
                (mem)
                (stack 1)
                (instrs))))
(test-WA (term ((mod ())
                (locals 1 2)
                (mem)
                (stack)
                (instrs (getlocal 1) (getlocal 0) (getlocal 1))))
         (term ((mod ())
                (locals 1 2)
                (mem)
                (stack 2 1 2)
                (instrs))))
(test-WA (term ((mod ())
                (locals 1 2)
                (mem)
                (stack 3)
                (instrs (setlocal 1))))
         (term ((mod ())
                (locals 1 3)
                (mem)
                (stack)
                (instrs))))
(define simple-call (term ((mod (((params 2) (locals 0) (body (getlocal 0)))))
                           (locals)
                           (mem)
                           (stack 1 2)
                           (instrs (call 0)))))
(define simple-call2 (term ((mod (((params 2) (locals 0) (body (getlocal 0)))))
                            (locals)
                            (mem)
                            (stack 2 1)
                            (instrs (call 0)))))
(define add-call (term ((mod (((params 2) (locals 0) (body (getlocal 0) (getlocal 1) add))))
                        (locals)
                        (mem)
                        (stack 2 1)
                        (instrs (call 0)))))
(define trap-call (term ((mod (((params 2) (locals 1) (body (getlocal 0) (getlocal 1) add trap))))
                         (locals)
                         (mem)
                         (stack 2 1)
                         (instrs (call 0)))))
(test-WA simple-call
         (term ((mod (((params 2) (locals 0) (body (getlocal 0)))))
                (locals)
                (mem)
                (stack 2)
                (instrs))))
(test-WA simple-call2
         (term ((mod (((params 2) (locals 0) (body (getlocal 0)))))
                (locals)
                (mem)
                (stack 1)
                (instrs))))
(test-WA add-call
         (term ((mod (((params 2) (locals 0) (body (getlocal 0) (getlocal 1) add))))
                (locals)
                (mem)
                (stack 3)
                (instrs))))
(test-WA trap-call
         (term ((mod (((params 2) (locals 1) (body (getlocal 0) (getlocal 1) add trap))))
                (locals)
                (mem)
                (stack)
                (instrs trap))))

;code block from stanford paper
(define loop-call (term ((mod (((params 0) (locals 1) (body (block (loop
                                                                    (getlocal 0)
                                                                    (i32.const 1)
                                                                    add
                                                                    (setlocal 0)
                                                                    (getlocal 0)
                                                                    (i32.const 10)
                                                                    eq
                                                                    (brif 1)
                                                                    (br 0)
                                                                    ))))))
                         (locals)
                         (mem)
                         (stack 0)
                         (instrs (call 0)))))
(define loop-call-with-return (term ((mod (((params 1) (locals 0) (body (block (loop
                                                                                (getlocal 0)
                                                                                (i32.const 1)
                                                                                add
                                                                                (setlocal 0)
                                                                                (getlocal 0)
                                                                                (i32.const 10)
                                                                                eq
                                                                                (brif 1)
                                                                                (br 0)
                                                                                ))
                                                                        (getlocal 0)
                                                                        return
                                                                        ))))
                                     (locals)
                                     (mem)
                                     (stack 0)
                                     (instrs (call 0)))))
(define no-call (term ((mod ())
                       (locals 0)
                       (mem)
                       (stack)
                       (instrs (block (loop
                                       (getlocal 0)
                                       (i32.const 1)
                                       add
                                       (setlocal 0)
                                       (getlocal 0)
                                       (i32.const 10)
                                       eq
                                       (brif 1)
                                       (br 0)
                                       ))))))
(test-WA no-call
         (term ((mod ())
                (locals 10)
                (mem)
                (stack)
                (instrs))))
(test-WA loop-call
         (term ((mod (((params 0) (locals 1) (body (block (loop
                                                           (getlocal 0)
                                                           (i32.const 1)
                                                           add
                                                           (setlocal 0)
                                                           (getlocal 0)
                                                           (i32.const 10)
                                                           eq
                                                           (brif 1)
                                                           (br 0)
                                                           ))))))
                (locals)
                (mem)
                (stack 0)
                (instrs))))
(test-WA loop-call-with-return
         (term ((mod
                 (((params 1)
                   (locals 0)
                   (body
                    (block
                     (loop
                      (getlocal 0)
                      (i32.const 1)
                      add
                      (setlocal 0)
                      (getlocal 0)
                      (i32.const 10)
                      eq
                      (brif 1)
                      (br 0)))
                    (getlocal 0)
                    return))))
                (locals)
                (mem)
                (stack 10)
                (instrs))))


;; test loop program, increments mem[0] by 7 until it is greater than 10
(define test-loop (term ((mod ())
                         (locals)
                         (mem 1 0 0 0)
                         (stack)
                         (instrs (block (loop (i32.const 0)
                                              (i32.const 0)
                                              i32.load
                                              (i32.const 7)
                                              add
                                              i32.store
                                              (i32.const 0)
                                              i32.load
                                              (i32.const 20)
                                              gts
                                              (brif 0)))))))
(test-WA test-loop
         (term ((mod ()) (locals) (mem 22 0 0 0) (stack) (instrs))))
                                       




(test-results)
(traces ->machine (term ((mod ()) (locals) (mem) (stack) (instrs (i32.const 5) (i32.const 3) add))))
(traces ->machine (term ((mod ()) (locals) (mem 0 0 0 0)
                                  (stack) (instrs memory.size memory.grow memory.size (i32.const 1) (i32.const 1) i32.store (i32.const 1) i32.load))))
(traces ->machine (term ((mod ()) (locals) (mem 0 0 0 0)
                                  (stack) (instrs  (i32.const 17)  i32.load))))
(traces ->machine test-nested-control)
(traces ->machine test-loop)
(traces ->machine add-call)
(traces ->machine (term ((mod (((params 2) (locals 0) (body (getlocal 0) (getlocal 1) add return))))
                        (locals)
                        (mem)
                        (stack 2 1)
                        (instrs (call 0)))))


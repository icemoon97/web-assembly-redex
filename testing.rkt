#lang racket
(require redex
         "web-assembly.rkt")


;; ==================================================================================
;; UTILITIES
;; ==================================================================================

(define (test-WA program-term result-term)
  (test-equal (term ,(first (apply-reduction-relation* ->machine program-term)))
              result-term))

;; ==================================================================================
;; TESTING
;; ==================================================================================

;; Binop
(test-WA (term ((mod ()) (locals) (mem) (stack) (instrs (i32.const 5) (i32.const 3) add)))
         (term ((mod ()) (locals) (mem) (stack 8) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 3 2) (instrs sub)))
         (term ((mod ()) (locals) (mem) (stack 1) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 4 3) (instrs mul)))
         (term ((mod ()) (locals) (mem) (stack 12) (instrs))))
(test-WA (term ((mod ()) (locals) (mem) (stack 12 3) (instrs divs)))
         (term ((mod ()) (locals) (mem) (stack 4) (instrs))))

;; Relop
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

;; Memory
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

;; Control Flow
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

;; Call Stack
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

;; example taken from specification
(define loop-call (term ((mod (((params 0)
                                (locals 1)
                                (body (block (loop
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
         (term ((mod (((params 0)
                       (locals 1)
                       (body (block (loop
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
#;(traces ->machine (term ((mod ()) (locals) (mem) (stack) (instrs (i32.const 5) (i32.const 3) add))))
#;(traces ->machine (term ((mod ()) (locals) (mem 0 0 0 0)
                                    (stack) (instrs memory.size memory.grow memory.size (i32.const 1) (i32.const 1) i32.store (i32.const 1) i32.load))))
#;(traces ->machine (term ((mod ()) (locals) (mem 0 0 0 0)
                                    (stack) (instrs  (i32.const 17)  i32.load))))
#;(traces ->machine test-nested-control)
#;(traces ->machine test-loop)
#;(traces ->machine add-call)
#;(traces ->machine (term ((mod (((params 2) (locals 0) (body (getlocal 0) (getlocal 1) add return))))
                           (locals)
                           (mem)
                           (stack 2 1)
                           (instrs (call 0)))))


#lang br/quicklang
(require bv)

(struct ebpf-state
  (pc            ;; program counter
   code          ;; instructions
   regs-m        ;; registers M[]
   reg-x         ;; register X
   acc-a         ;; accumulator A
   labels)       ;; hash table mapping labels to its line offset in the program
   #:transparent)

(define (initial-state instrs)
  (ebpf-state
   0
   instrs
   (make-vector 16 (bv 0 32))
   (bv 3 32)
   (bv 5 32)
   '#hash()))

;(define (pre-state st)
;  (cons (ebpf-state-pc st) (ebpf-state-acc-a st) (ebpf-state-reg-x) (ebpf-state-regs-m)))


(define (exec st)
  (define current-pc (ebpf-state-pc st))
  (define code-size (length (ebpf-state-code st)))
  (if (>= current-pc code-size)
      st
      (let* ([next-instr (list-ref (ebpf-state-code st) current-pc)]
             [next-state (next-instr st)])
        (exec next-state))))

;General definition for ld operation
;Also addressing mode 4 for ld
(define (ld k st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc) instrs m x k labels))))

(define (ld-add3 k st)
  (ld (vector-ref (ebpf-state-regs-m st) k) st))

(define ldi ld)

;;General definition for ldx
;;Also addressing mode 4 for ldx
(define (ldx k st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc) instrs m k a labels))))

(define (ldx-add3 k st)
  (ldx (vector-ref (ebpf-state-regs-m st) k) st))

;st operation
(define (st-add3 k st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc)
                 instrs
                 (vector-set! m k a)
                 x
                 a
                 labels))))

;stx operation
(define (stx-add3 k st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc)
                 instrs
                 (vector-set! m k x)
                 x
                 a
                 labels))))



;general definition for arithmetic instructions
(define (arith-instr k op st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc) instrs m x (op a k) labels))))


;add operation with addressing mode 0
(define (add-add0 st)
  (arith-instr (ebpf-state-reg-x st) bvadd st))

;add operation with addressing mode 4
(define (add-add4 k st)
  (arith-instr (bv k 32) bvadd st))

;sub operation with addressing mode 0
(define (sub-add0 st)
  (arith-instr (ebpf-state-reg-x st) bvsub st))

;sub operation with addressing mode 4
(define (sub-add4 k st)
  (arith-instr (bv k 32) bvsub st))

;sub operation with addressing mode 0
(define (mul-add0 st)
  (arith-instr (ebpf-state-reg-x st) bvmul st))

;sub operation with addressing mode 4
(define (mul-add4 k st)
  (arith-instr (bv k 32) bvmul st))

;div operation with addressing mode 0
(define (div-add0 st)
  (arith-instr (ebpf-state-reg-x st) bvsdiv st))

;div operation with addressing mode 4
(define (div-add4 k st)
  (arith-instr (bv k 32) bvsdiv st))

;mod operation with addressing mode 0
(define (mod-add0 st)
  (arith-instr (ebpf-state-reg-x st) bvsmod st))

;mod operation with addressing mode 4
(define (mod-add4 k st)
  (arith-instr (bv k 32) bvsmod st))


;nop
(define (nop st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc) instrs m x a labels))))


;general definition for jump operations
(define (jump-to-label st key)
  (define new-pc (hash-ref (ebpf-state-labels st) key))
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state new-pc instrs m x a labels))))

;jmp and ja seem a lot like the general definition for jump operations
(define jmp jump-to-label)
(define ja jump-to-label)

;conditional jumps definitions
;;with literal k
(define (jmp-cond st cond k lt lf)      ;;cond is a logical operator 
  (if (cond (ebpf-state-acc-a st) k)
      (jump-to-label st lt)
      (if (null? lf)
          (nop st)
          (jump-to-label st lf))))

;when addressing reg-x it will be k

;;jeq definitions
;;;addressing mode 7
(define (jeq-add7 k lt lf st)
  (jmp-cond st bveq k lt lf))

;;;addressing mode 8
(define (jeq-add8 lt lf st)
  (jmp-cond st bveq (ebpf-state-reg-x st) lt lf))

;;;addressing mode 9
(define (jeq-add9 k lt st)
  (jmp-cond st bveq k lt null))

;;;addressing mode 10
(define (jeq-add10 lt st)
  (jmp-cond st bveq (ebpf-state-reg-x st) lt null))

;;jneq or jne
;;;helper operator "not equal" for bv 
(define (bvneq x y)
  (not (bveq x y)))

;;;definition
;;;addressing mode 9
(define (jneq-add9 k lt st)
  (jmp-cond st bvneq k lt null))
  
(define jne-add9 jneq-add9)

;;;addressing mode 10
(define (jneq-add10 lt st)
  (jmp-cond  st bvneq (ebpf-state-reg-x st) lt null))

(define jne-add10 jneq-add10)

;;jlt definition
;;;addressing mode 9
(define (jlt-add9 k lt st)
  (jmp-cond st bvslt k lt null))

;;;addressing mode 10
(define (jlt-add10 lt st)
  (jmp-cond  st bvslt (ebpf-state-reg-x st) lt null))

;;jle definition
;;;addressing mode 9
(define (jle-add9 k lt st)
  (jmp-cond st bvsle k lt null))

;;;addressing mode 10
(define (jle-add10 lt st)
  (jmp-cond  st bvsle (ebpf-state-reg-x st) lt null))

;;jgt definitions
;;;addressing mode 7
(define (jgt-add7 k lt lf st)
  (jmp-cond st bvsgt k lt lf))
  
;;;addressing mode 8
(define (jgt-add8 lt lf st)
  (jmp-cond st bvsgt (ebpf-state-reg-x st) lt lf))

;;;addressing mode 9
(define (jgt-add9 k lt st)
  (jmp-cond st bvsgt k lt null))

;;;addressing mode 10
(define (jgt-add10 lt st)
  (jmp-cond st bvsgt (ebpf-state-reg-x st) lt null))

;;jge definitions
;;;addressing mode 7
(define (jge-add7 k lt lf st)
  (jmp-cond st bvsge k lt lf))
  
;;;addressing mode 8
(define (jge-add8 lt lf st)
  (jmp-cond st bvsge (ebpf-state-reg-x st) lt lf))

;;;addressing mode 9
(define (jge-add9 k lt st)
  (jmp-cond st bvsge k lt null))

;;;addressing mode 10
(define (jge-add10 lt st)
  (jmp-cond st bvsge (ebpf-state-reg-x st) lt null))

;;jset definitions
;;;addressing mode 7
(define (jset-add7 k lt lf st)
  (jmp-cond st bvand k lt lf))

;;;addressing mode 8
(define (jset-add8 lt lf st)
  (jmp-cond st bvand (ebpf-state-reg-x st) lt lf))

;;;addressing mode 9
(define (jset-add9 k lt st)
  (jmp-cond st bvand k lt null))

;;;addressing mode 10
(define (jset-add10 lt st)
  (jmp-cond st bvand (ebpf-state-reg-x st) lt null))

;neg
(define (neg st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc) instrs m x (bvnot a) labels))))

;general definition for bitwise operators
(define bitwise-ops arith-instr) 

;;and
;;addressing mode 0
(define (and-add0 st)
    (bitwise-ops (ebpf-state-reg-x st) bvand st))

;;addressing mode 4
(define (and-add4 k st)
    (bitwise-ops k bvand st))

;;or
(define (or-add0 st)
    (bitwise-ops (ebpf-state-reg-x st) bvor st))

(define (or-add4 k st)
    (bitwise-ops k bvor st))

;;xor
(define (xor-add0 st)
    (bitwise-ops (ebpf-state-reg-x st) bvxor st))

(define (xor-add4 k st)
    (bitwise-ops k bvxor st))

;;lsh
(define (lsh-add0 k st)
    (bitwise-ops (ebpf-state-reg-x st) bvshl st))

(define (lsh-add4 k st)
    (bitwise-ops k bvshl st))

;;rsh
(define (rsh-add0 k st)
    (bitwise-ops (ebpf-state-reg-x st) bvlshr st))

(define (rsh-add4 k st)
    (bitwise-ops k bvlshr st))

;tax
(define (tax st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc) instrs m a a labels))))

;txa
(define (txa st)
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state (add1 pc) instrs m x x labels))))

;ret
(define (ret-add4 k st)
  (define code-size (length (ebpf-state-code st)))
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state code-size instrs m x k labels))))

(define (ret-add11 st)
  (define code-size (length (ebpf-state-code st)))
  (match st
    ((ebpf-state pc instrs m x a labels)
     (ebpf-state code-size instrs m x a labels))))
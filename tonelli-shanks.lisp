; Number Theory Library
; Tonelli-Shanks Square Root
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors:
;   Alessandro Coglio (coglio@kestrel.edu),
;   Eric Smith (eric.smith@kestrel.edu),
;   Jagadish Bapanapally (jagadishb285@gmail.com)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(include-book "kestrel/arithmetic-light/mod-expt-fast" :dir :system)
(include-book "kestrel/number-theory/quadratic-residue" :dir :system)
(local (include-book "projects/quadratic-reciprocity/eisenstein" :dir :system))
(local (include-book "kestrel/number-theory/mod-expt-fast" :dir :system))

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;rtl::primep


(in-theory (disable acl2::mod-expt-fast))

(local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; --------------------------------
;; Square root
;; Tonelli-Shanks algorithm.
;; See:
;;   https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm
;; Another reference, not just about "extension fields" but with
;; good explanations of the various modular square root options for various fields:
;;   "Square root computation over even extension fields"
;;   https://eprint.iacr.org/2012/685.pdf

;; ----------------
;; p - 1 = Q.2^S

;; Step 1 of
;; https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm

;; Factors n into the S powers of 2 and the rest Q.
;; If n is a power of 2, Q will be 1.
;; Otherwise Q will be the product of the odd prime factors.
;;
(define Q*2^S ((n natp))
  :returns (mv (q natp) (s natp))
  :verify-guards nil
  (if (or (not (natp n)) (= n 0))
      (mv 0 0)
    (if (oddp n)
        (mv n 0)
      (mv-let (inner-q inner-s)
        (Q*2^S (/ n 2))
        (mv inner-q (+ inner-s 1)))))
  ///
  (verify-guards Q*2^S))

(defthm q2s-q-is-odd
  (implies (and (natp n) (< 0 n))
           (oddp (mv-nth 0 (Q*2^S n))))
  :hints (("Goal" :in-theory (e/d (Q*2^S oddp) ()))))

;; Show that q2s is correct:

(defthm Q*2^S-type-0
  (natp (mv-nth 0 (Q*2^S n)))
  :rule-classes :type-prescription)

(defthm Q*2^S-type-1
  (natp (mv-nth 1 (Q*2^S n)))
  :rule-classes :type-prescription)

(defthm q2s-is-correct
  (implies (natp n)
           (equal (* (mv-nth 0 (q*2^s n))
                     (expt 2 (mv-nth 1 (q*2^s n))))
                  n))
  :hints (("Goal" :in-theory (enable q*2^s acl2::expt-of-+))))

;; if n is even, then, (mv-nth 1 (Q*2^S n)) is a positive integer
(defthm posp-Q*2^S-n-is-even
  (implies (and (> n 1)
                (natp n)
                (evenp n))
           (posp (mv-nth 1 (Q*2^S n))))
  :hints (("Goal"
           :use ((:instance q2s-is-correct (n n))
                 (:instance q2s-q-is-odd (n n)))
           ))
  )

(defun least-repeated-square-aux (i tt^2^i M p)
  (declare (xargs :guard (and (posp i) (natp tt^2^i) (natp M) (natp p)
                              (< 2 p))
                  ))
  (declare (xargs :measure (nfix (- M i))))
  (if (and (posp i) (natp M) (< i M))
      (let ((next-square (mod (* tt^2^i tt^2^i) p)))
        (if (= next-square 1)
            i
          (least-repeated-square-aux (+ i 1) next-square M p)))
    0))

(defthm least-repeated-square-aux-less-than-M
  (implies (< 0 M)
           (< (least-repeated-square-aux i tt M p) M)))

;; This variant is needed for verifying guards on T-S-aux
(defthm least-repeated-square-aux-less-than-M--variant
  (implies (and (natp M) (< 0 M) (natp (least-repeated-square-aux i tt M p)))
           (<= 0 (+ -1 M (- (least-repeated-square-aux i tt M p))))))

(defun least-repeated-square (tt M p)
  (declare (xargs :guard (and (natp tt) (natp M) (natp p) (< 2 p))))
  (if (= (mod tt p) 1)
      0
    (least-repeated-square-aux 1 tt M p)))

(defthm least-repeated-square-less-than-M
  (implies (< 0 M)
           (< (least-repeated-square tt M p) M)))

(defthm least-repeated-square-is-natp
  (natp (least-repeated-square tt M p)))

;; ----------------

;; Squares base n times,
;; i.e., computes base^(2^n)
;; for (natp n) and (natp base) and odd prime p.
(define repeated-square ((base natp) (n natp) (p natp))
  :returns (retval natp)
  :measure (nfix n)
  (declare (xargs :guard (and (natp base) (natp n) (natp p) (< 2 p))))
  (if (or (not (natp base)) (not (natp n)) (not (natp p)) (< p 3))
      0
    (if (zp n)
        base
      (repeated-square (mod (* base base) p) (- n 1) p))))

;; ----------------
;; main T-S loop
;; step 4 of
;; https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm
;; if (least-repeated-square tt m p) returns 0, then return R
;; Otherwise update M, c, tt and R and then go into next loop.

(encapsulate
  ()

  (local
   (defthm T-S-aux-subgoal
     (IMPLIES (NOT (ZP (LEAST-REPEATED-SQUARE TT M P)))
              (O< (NFIX (LEAST-REPEATED-SQUARE TT M P))
                  (NFIX M)))
     :hints (("Goal" :use (:instance
                           least-repeated-square-aux-less-than-M
                           (i 1) (tt tt) (m m) (p p))))
     )
   )

  (defun T-S-aux (M c tt R p)
    (declare (xargs :measure (nfix M)
                    :guard-debug t
                    :guard (and (posp M) (natp c) (natp tt)
                                (natp R)
                                (rtl::primep p) (< 2 p))
                    :hints (("Goal" :use (:instance T-S-aux-subgoal
                                                    (tt tt) (m m) (p p))))
                    ))
    (let ((M2 (least-repeated-square tt M p)))
      (if (zp M2)
          R
        (let ((b (repeated-square c (- (- M M2) 1) p)))
          (let (
                (c2 (mod (* b b) p))
                (tt2 (mod (* tt b b) p))
                (R2 (mod (* R b) p)))
            (T-S-aux M2 c2 tt2 R2 p))))))
  )

(verify-guards T-S-aux)

(defthm integerp-T-S-aux
  (implies  (and (natp M)
                 (natp c)
                 (natp tt)
                 (natp R)
                 (natp p)
                 (< 2 p))
            (natp (T-S-aux M c tt R p)))
  )

(defthm integerp-of-mod-expt-fast-1
  (implies (and (integerp a)
                (natp i)
                (integerp n))
           (integerp (acl2::mod-expt-fast a i n)))
  :hints (("Goal" :in-theory (enable acl2::mod-expt-fast))))

(defthm mod-expt-fast-natp
  (implies (and (integerp n)
                (< 1 n)
                (natp a)
                (natp i))
           (natp (acl2::mod-expt-fast a i n)))
  :hints (("Goal"
           :in-theory (e/d (acl2::mod-expt-fast) ())
           ))
  )

(defthm natp-lemma1
  (implies (and (natp n)
                (oddp q)
                (natp q)
                (rtl::primep p)
                (< n p)
                (> p 2))
           (natp (ACL2::MOD-EXPT-FAST N(+ 1/2 (* 1/2 q)) P)))
  :hints (("Goal"
           :in-theory (enable acl2::not-evenp-when-oddp)
           ))
  )

;; ----------------
;; Tonelli-Shanks modular square root algorithm,
;; with a refinement to always return the lesser of the two square roots.

;; The argument z must be a "quadratic nonresidue", which means a number
;; that has no square root in the prime field.

;; The argument n must be a quadratic reside in the prime field and it can also be equal to 0

;; The function returns the square root of n in the prime field p

(define tonelli-shanks-sqrt-aux ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (has-square-root? n p)
              (not (has-square-root? z p)))
  :guard-debug t
  :short "Tonelli-Shanks modular square root of n in the prime field p"
  :long "Finds the square root of n modulo p. p must be an odd prime. z is a quadratic nonresidue in p. n is a quadratic residue and can also be equal to 0"
  :returns (sqrt natp :hyp :guard)
  :parents (acl2::number-theory)

  (if (= n 0)
      0
    (mv-let (Q S)
      (Q*2^S (- p 1))
      (let (
            (M S)
            (c (acl2::mod-expt-fast z Q p))
            (tt (acl2::mod-expt-fast n Q p))
            (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
        (T-S-aux M c tt R p))))
  :guard-hints (("Goal"
                 :use ((:instance posp-Q*2^S-n-is-even (n (- p 1))))
                 :in-theory (e/d (acl2::integerp-of-*-of-1/2-becomes-evenp
                                  acl2::not-evenp-when-oddp
                                  acl2::mod-expt-fast
                                  rtl::oddp-odd-prime)
                                 (oddp))
                 )))

(defthm natp-tonelli-shanks-sqrt-aux
  (implies  (and (natp n)
                 (natp p)
                 (natp z)
                 (rtl::primep p)
                 (< n p)
                 (has-square-root? n p)
                 (not (has-square-root? z p))
                 (< 2 p))
            (natp (tonelli-shanks-sqrt-aux n p z)))
  :hints (("Goal"
           :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
           )))

;; ----------------
;; Tonelli-Shanks modular square root algorithm.

;; The argument z must be a "quadratic nonresidue", which means a number
;; that has no square root in the prime field.

;; The argument n must be a integer greater than or equal to 0.

;; The argument p must be a prime greater that 2.

;; The function returns the lesser number of the square roots of n modulo p if the square root exists, otherwise returns 0.

;; If the function returns 0, it means either n is 0 or there is no square root

(define tonelli-shanks-lesser-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :guard-debug t
  :short "Tonelli-Shanks modular square root."
  :long "Finds the lesser square root of the two square roots of n modulo p if it exists, otherwise returns 0. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard :hints (("Goal"
                                           :use (:instance natp-tonelli-shanks-sqrt-aux (n n) (p p) (z z))
                                           :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
                                           )))
  :parents (acl2::number-theory)
  (if (has-square-root? n p)
      (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
        (if (> sqrt (/ p 2))
            (mod (- sqrt) p)
          sqrt))
    0)
  :guard-hints (("Goal" :use (:instance natp-tonelli-shanks-sqrt-aux
                                        (n n) (p p) (z z))
                 :in-theory (e/d (tonelli-shanks-sqrt-aux) ()))))

(define tonelli-shanks-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :short "Tonelli-Shanks modular square root."
  :long "Finds the lesser square root of the two square roots of n modulo p if it exists, otherwise returns 0. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard)
  :parents (acl2::number-theory)
  (tonelli-shanks-lesser-sqrt n p z))

(define tonelli-shanks-either-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :guard-debug t
  :short "Tonelli-Shanks modular square root."
  :long "Finds a square root of n modulo p if it exists, else returns 0. p must be an odd prime. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard)
  :parents (acl2::number-theory)
  (if (has-square-root? n p)
      (tonelli-shanks-sqrt-aux n p z)
    0))

(define tonelli-shanks-greater-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :guard-debug t
  :short "Tonelli-Shanks modular square root."
  :long "Finds the greater square root of the two square roots of n modulo p if it exists, otherwise returns 0. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard :hints (("Goal"
                                           :use (:instance natp-tonelli-shanks-sqrt-aux (n n) (p p) (z z))
                                           :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
                                           )))
  :parents (acl2::number-theory)
  (if (has-square-root? n p)
      (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
        (if (> sqrt (/ p 2))
            sqrt
          (mod (- sqrt) p)))
    0)
  :guard-hints (("Goal" :use (:instance natp-tonelli-shanks-sqrt-aux
                                        (n n) (p p) (z z))
                 :in-theory (e/d (tonelli-shanks-sqrt-aux) ()))))

(encapsulate
  ()

  (local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
  (local (include-book "arithmetic/equalities" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm repeated-square-=mod-expt-fast-*1/3
     (implies (posp a)
              (equal (* (expt c (expt 2 (+ -1 a)))
                        (expt c (expt 2 (+ -1 a))))
                     (expt c (expt 2 a))))
     :hints (("goal"
              :use ((:instance acl2::exponents-add-for-nonneg-exponents
                               (r c)
                               (i (expt 2 (+ -1 a)))
                               (j (expt 2 (+ -1 a)))))
              ))))
  
  (defthm repeated-square-equiv
    (implies (and (posp x)
                  (natp c)
                  (natp p)
                  (< 2 p))
             (equal (repeated-square c x p)
                    (acl2::mod-expt-fast c (expt 2 x) p)))
    :hints (("goal"
             :use ((:instance acl2::mod-of-expt-of-mod (i (expt 2 (+ -1 x)))
                              (x (* c c))
                              (y p))
                   (:instance acl2::exponents-add-unrestricted (r c)
                              (i (expt 2 (+ -1 x))) (j (expt 2 (+ -1 x)))))
             :in-theory (enable acl2::mod-expt-fast repeated-square)
             ))))

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
   (local (include-book "kestrel/number-theory/mod-expt-fast" :dir :system))
   (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))
   
   (defthmd hyps-t-s-aux
     (implies (and (natp n)
                   (natp p)
                   (natp z)
                   (not (has-square-root? z p))
                   (< 2 p)
                   (< z p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (< 0 n)
                   (equal (mv-nth 0 (q*2^s (- p 1))) q)
                   (equal (acl2::mod-expt-fast z q p) c)
                   (equal (acl2::mod-expt-fast n (/ (+ q 1) 2) p) r))
              (and (posp c)
                   (posp r)
                   (< c p)
                   (< r p)))
     :hints (("Goal"
              :use ((:instance acl2::<-of-0-and-mod-expt-fast-when-primep (n p) (i q) (a z))
                    (:instance acl2::<-of-0-and-mod-expt-fast-when-primep (n p) (i (/ (+ q 1) 2)) (a n)))
              :in-theory (e/d (acl2::mod-expt-fast) ())
              )))))

(local
 (encapsulate
   ()

   (local (include-book "kestrel/number-theory/mod-expt-fast" :dir :system))

   (local
    (defthm lemma1
      (implies (and (posp m)
                    (natp m2)
                    (< m2 m))
               (<= (+ m2 1) m))))

   (defthm <0<t-s-aux<p
     (implies (and (posp n)
                   (has-square-root? n p)
                   (posp m)
                   (posp c)
                   (< c p)
                   (natp tt)
                   (posp r)
                   (< r p)
                   (natp p)
                   (< n p)
                   (rtl::primep p)
                   (< 2 p)
                   (< 0 (least-repeated-square tt m p)))
              (let ((b (repeated-square c (- (- m (least-repeated-square tt m p)) 1) p)))
                (let ((c2 (mod (* b b) p))
                      (tt2 (mod (* tt b b) p))
                      (r2 (mod (* r b) p)))
                  (declare (ignore tt2))
                  (and (posp r2)
                       (< r2 p)
                       (posp c2)
                       (< c2 p)
                       ))))
     :hints (("Goal"
              :use ((:instance acl2::<-of-0-and-mod-expt-fast-when-primep (n p)
                               (i (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P))))
                               (a c))
                    (:instance lemma1 (m m) (m2 (LEAST-REPEATED-SQUARE TT M P)))
                    (:instance least-repeated-square-less-than-M (m m) (tt tt) (p p))
                    (:instance least-repeated-square-is-natp (tt tt) (m m) (p p))
                    (:instance repeated-square-equiv (c c) (x (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P))))
                               (p p)))
              :in-theory (e/d (acl2::mod-expt-fast repeated-square) (least-repeated-square hyps-t-s-aux))
              )))))

(defthmd t-s-aux-posp<p
  (implies  (and (posp n)
                 (has-square-root? n p)
                 (posp m)
                 (posp c)
                 (< c p)
                 (natp tt)
                 (posp r)
                 (< r p)
                 (natp p)
                 (< n p)
                 (rtl::primep p)
                 (< 2 p))
            (and (posp (t-s-aux m c tt r p))
                 (< (t-s-aux m c tt r p) p)))
  :hints (("Goal"
           :in-theory (e/d (t-s-aux) (least-repeated-square repeated-square))
           :induct (t-s-aux m c tt r p)
           )))

(local
 (defthm tonelli-shanks-sqrt-aux-is-posp<p
   (implies (and (posp n)
                 (natp z)
                 (> p 2)
                 (has-square-root? n p)
                 (< n p)
                 (< z p)
                 (rtl::primep p)
                 (not (has-square-root? z p))
                 (equal (tonelli-shanks-sqrt-aux n p z) y))
            (and (posp y)
                 (< y p)))
   :hints (("Goal"
            :in-theory (e/d (tonelli-shanks-sqrt-aux has-square-root?) ())
            :use ((:instance hyps-t-s-aux
                             (n n)
                             (p p)
                             (z z)
                             (q (mv-nth 0 (q*2^s (- p 1))))
                             (c (acl2::mod-expt-fast z (mv-nth 0 (q*2^s (- p 1))) p))
                             (r (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (q*2^s (- p 1))) 1) 2) p)))
                  (:instance t-s-aux-posp<p
                             (n n)
                             (p p)
                             (m (mv-nth 1 (q*2^s (- p 1))))
                             (c (acl2::mod-expt-fast z (mv-nth 0 (q*2^s (- p 1))) p))
                             (tt (acl2::mod-expt-fast n (mv-nth 0 (q*2^s (- p 1))) p))
                             (r (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (q*2^s (- p 1))) 1) 2) p))
                             )
                  )))))

(defun natp-evenp (x)
  (and (natp x)
       (evenp x)))

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  
  (define tonelli-shanks-even-sqrt ((n natp) (p natp) (z natp))
    :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
    :guard-debug t
    :short "Tonelli-Shanks modular square root."
    :long "Finds the even square root of the two square roots of n modulo p if it exists, otherwise returns 0. z is a quadratic nonresidue in p."
    :returns (sqrt natp-evenp :hyp :guard :hints (("Goal" :cases ((= n 0))
                                                   :use ((:instance tonelli-shanks-sqrt-aux-is-posp<p (n n) (p p) (z z) (y (tonelli-shanks-sqrt-aux n p z))))                                                    
                                                   :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
                                                   )))
    :parents (acl2::number-theory)
    (if (has-square-root? n p)
        (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
          (if (evenp sqrt)
              sqrt
            (mod (- sqrt) p)))
      0)
    :guard-hints (("Goal" :use ((:instance natp-tonelli-shanks-sqrt-aux
                                           (n n) (p p) (z z))
                                (:instance tonelli-shanks-sqrt-aux (n 0) (p p) (z z))
                                (:instance natp-tonelli-shanks-sqrt-aux
                                           (n 0) (p p) (z z)))
                   :in-theory (e/d (tonelli-shanks-sqrt-aux acl2::not-evenp-when-oddp) ())))))

(defun natp-oddp (x)
  (and (natp x)
       (oddp x)))

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  
  (define tonelli-shanks-odd-sqrt ((n posp) (p natp) (z natp))
    :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
    :guard-debug t
    :short "Tonelli-Shanks modular square root."
    :long "Finds the odd square root of the two square roots of n modulo p if it exists, otherwise returns 1. z is a quadratic nonresidue in p."
    :returns (sqrt natp-oddp :hyp :guard :hints (("Goal" :cases ((= n 0))
                                                  :use ((:instance tonelli-shanks-sqrt-aux-is-posp<p (n n) (p p) (z z) (y (tonelli-shanks-sqrt-aux n p z))))                                                    
                                                  :in-theory (e/d (tonelli-shanks-sqrt-aux oddp acl2::not-evenp-when-oddp) ())
                                                  )))
    :parents (acl2::number-theory)
    (if (has-square-root? n p)
        (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
          (if (oddp sqrt)
              sqrt
            (mod (- sqrt) p)))
      1)
    :guard-hints (("Goal" :use ((:instance natp-tonelli-shanks-sqrt-aux
                                           (n n) (p p) (z z))
                                (:instance tonelli-shanks-sqrt-aux (n 0) (p p) (z z))
                                (:instance natp-tonelli-shanks-sqrt-aux
                                           (n 0) (p p) (z z)))
                   :in-theory (e/d (tonelli-shanks-sqrt-aux acl2::not-evenp-when-oddp oddp) ())))))

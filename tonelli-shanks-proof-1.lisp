
(in-package "PRIMES")

(include-book "kestrel/number-theory/tonelli-shanks-test" :dir :system)

(local
 (encapsulate
   ()

   (local (include-book "rtl/rel11/lib/basic" :dir :system))
   (local (include-book "arithmetic/equalities" :dir :system))
   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm mod-*a-b=
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (= c 0)))
              (= (mod (* a b) c)
                 (mod (* (mod a c) (mod b c)) c))))

   (defthm mod-*mod-a*mod-b=
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (= c 0)))
              (= (mod (* (mod a c) (mod b c)) c)
                 (mod (* a b) c)))
     :hints (("Goal"
              :use (:instance mod-*a-b= (a a) (b b) (c c))
              :in-theory nil
              ))
     )
   ))

(local
 (encapsulate
   ()
   (local (include-book "divides"))
   (local (include-book "kestrel/crypto/ecurve/primes" :dir :system))
   
   (defthm primep-implies
     (implies (and (rtl::primep p)
                   (< 2 p))
              (and (oddp p)
                   (integerp p)))
     :hints (("Goal"
              :in-theory (e/d (rtl::primep) (oddp))
              ))
     )
   )
 )

(encapsulate
  ()
  
  (local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm y^2=1modp-lemma1
     (implies (and (integerp a)
                   (integerp b)
                   (rtl::primep p)
                   (rtl::divides p (* a b))
                   (not (rtl::divides p b)))
              (rtl::divides p a))
     :hints (("Goal"
              :use (:instance rtl::euclid (p p) (a a) (b b))
              ))))

  (local
   (defthm y^2=1modp-1
     (implies (and (rtl::primep p)
                   (integerp y)
                   (< 2 p)
                   (equal (mod (* y y) p) 1))
              (or (equal (mod y p) 1)
                  (equal (mod y p) (mod -1 p))))
     :hints (("Goal"
              :cases ((rtl::divides p (- y 1))
                      (rtl::divides p (+ y 1)))
              :use ((:instance rtl::divides-mod-equal (n p) (a (* y y)) (b 1))
                    (:instance y^2=1modp-lemma1 (a (- y 1)) (b (+ y 1)))         
                    (:instance rtl::divides-mod-equal (n p) (a y) (b 1))
                    (:instance rtl::divides-mod-equal (n p) (a y) (b -1)))
              :in-theory (e/d (rtl::primep) ())
              ))
     )
   )

  (local
   (defthm y^2=1modp-2
     (implies (and (rtl::primep p)
                   (integerp y)
                   (< 2 p)
                   (or (equal (mod y p) 1)
                       (equal (mod y p) (mod -1 p))))
              (equal (mod (* y y) p) 1))
     :hints (("Goal"
              :cases ((equal (mod y p) 1)
                      (equal (mod y p) (mod -1 p)))
              :use ((:instance primep-implies (p p))
                    (:instance mod-*a-b= (a y) (b y) (c p))
                    (:instance mod-*mod-a*mod-b= (a y) (b y) (c p)))
              :in-theory (e/d () (mod))
              ))))

  (defthm y^2=1modp
    (implies (and (rtl::primep p)
                  (integerp y)
                  (< 2 p))
             (iff (equal (mod (* y y) p) 1)
                  (or (equal (mod y p) 1)
                      (equal (mod y p) (mod -1 p)))))
    :hints (("Goal"
             :use ((:instance y^2=1modp-1)
                   (:instance y^2=1modp-2))
             ))
    )
  )

(encapsulate
  ()

  (local (include-book "kestrel/arithmetic-light/expt" :dir :system))

  (local
   (encapsulate
     ()
     (local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))

     (defthm mod-of-expt-of-mod
       (implies (and (natp i)
                     (integerp x)
                     (posp y))
                (equal (mod (expt (mod x y) i) y)
                       (mod (expt x i) y))))

     (defthm natp-2^x
       (implies (natp x)
                (natp (expt 2 x)))
       )

     )
   )

  (local
   (encapsulate
     ()
     
     (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
     (local (include-book "arithmetic/equalities" :dir :system))

     (defthm Exponents-add-for-nonneg-exponents
       (implies (and (<= 0 i)
                     (<= 0 j)
                     (integerp i)
                     (integerp j))
                (equal 
                 (* (expt r i)
                    (expt r j)) (expt r (+ i j)))))

     (defthm expt-half-linear
       (implies (natp i)
                (equal (+ (expt 2 (+ -1 i))
                          (expt 2 (+ -1 i)))
                       (expt 2 i)))

       )    
     )
   )

;;   (defun lrs-aux-equiv (i tt M p)
;;     (declare (xargs :guard (and (posp i) (natp tt) (natp M) (natp p) (<= 0 i)
;;                                 (< 2 p))
;;                     ))
;;     (declare (xargs :measure (nfix (- M i))))
;;     (if (and (posp i) (natp M) (< i M))
;;         (let ((next-square (acl2::mod-expt-fast tt (expt 2 i) p)))
;;           (if (= next-square 1)
;;               i
;;             (lrs-aux-equiv (+ i 1) tt M p)))
;;       0))

;;   (defthm least-repeated-square-aux-equiv
;;     (implies (and ;(posp i)
;;                   (natp tt)
;;                   (natp m)
;;                   (natp p)
;;                   ;(<= 0 i)
;;                   (< 2 p))
;;              (equal (least-repeated-square-aux 1 tt m p)
;;                     (lrs-aux-equiv 1 tt m p)))
;;     )
  
;;   )

;; ---

  (local
   (defthmd least-repeated-square-aux-lemma1
     (implies (and (posp i)
                   (< i M)
                   (natp x)
                   (< x i)
                   (natp tt^2^i)
                   (natp M)
                   (natp p)
                   (< 2 p)
                   (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX i
                                                          tt^2^i
                                                          M P)
                               0)))
              (< x (LEAST-REPEATED-SQUARE-AUX i
                                              tt^2^i
                                              M P)))
     :hints (("Goal"
              :in-theory (e/d () (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b=))
              ))
     ))
  
  ;; (local
  ;;  (defthmd least-repeated-square-aux-lemma1
  ;;    (implies (and (natp x)
  ;;                  (integerp tt)
  ;;                  (integerp p)
  ;;                  (< 2 p)
  ;;                  (equal (mod (expt (mod (* tt tt) p)
  ;;                                    (expt 2 x)) p)
  ;;                         1))
  ;;             (equal (mod (expt tt (expt 2 (+ 1 x))) p)
  ;;                    1))
  ;;    :hints (("Goal"
  ;;             :use ((:instance mod-of-expt-of-mod (i (expt 2 x))
  ;;                              (y p) (x (* tt tt)))
  ;;                   (:instance expt-half-linear (i (+ x 1))))
  ;;             :do-not-induct t
  ;;             :in-theory (e/d () (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b=))
  ;;             ))
  ;;    )
  ;;  )
  
  (local
   (defthm least-repeated-square-aux-lemma2
     (IMPLIES
      (AND (INTEGERP I)
           (<= 0 I)
           (INTEGERP M)
           (<= 0 M)
           (< I M)
           (NOT (EQUAL (MOD (* TT TT) P) 1))
           (EQUAL (MOD (EXPT (MOD (* TT TT) P)
                             (EXPT 2
                                   (+ (- I)
                                      (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                                 (MOD (* TT TT) P)
                                                                 M P))))
                       P)
                  1)
           (< (+ 1 I) M)
           (INTEGERP TT)
           (<= 0 TT)
           (< 0 M)
           (INTEGERP P)
           (<= 0 P)
           (< 0 I)
           (< 2 P)
           (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                  (MOD (* TT TT) P)
                                                  M P)
                       0)))
      (EQUAL (MOD (EXPT TT
                        (EXPT 2
                              (+ 1 (- I)
                                 (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                            (MOD (* TT TT) P)
                                                            M P))))
                  P)
             1))
     :hints (("Goal"
              :use (
                    (:instance expt-half-linear (i (+ (- I)
                                                      (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                                                 (MOD (* TT TT) P)
                                                                                 M P) 1)))
                    (:instance least-repeated-square-aux-lemma1 (i (+ i 1)) (x i)
                               (m m) (p p) (tt^2^i (MOD (* TT TT) P))))
              :in-theory (e/d () (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b=))
              ))
     )
   )

  (local
   (defthmd least-repeated-square-aux-not=0-lemma1
     (implies (and (natp tt)
                   (posp M)
                   (natp p)
                   (posp i)
                   (< 2 p)
                   (equal (least-repeated-square-aux i tt m p) lrs)
                   (not (= lrs 0)))
              (and (= (mod (expt tt (expt 2 (+ lrs (- i) 1))) p) 1)
                   (< lrs M)
                   (< i M)))
     :hints (("Goal"
              :use ((:instance least-repeated-square-aux-lemma2))
              :in-theory (e/d (acl2::expt) (y^2=1modp primep-implies
                                                      mod-*a-b= mod-*mod-a*mod-b=))
              ))))
  (local
   (defthmd least-repeated-square-aux-not=0
     (implies (and (natp tt)
                   (natp M)
                   (natp p)
                   (< 2 p)
                   (equal (least-repeated-square-aux 1 tt m p) lrs)
                   (not (= lrs 0)))
              (and (= (mod (expt tt (expt 2 lrs)) p) 1)
                   (< lrs M)
                   (< 0 M)))
     :hints (("Goal"
              :use (:instance least-repeated-square-aux-not=0-lemma1 (i 1) (tt tt) (m m)
                              (p p) (lrs (least-repeated-square-aux 1 tt m p)))
              :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies
                                                               mod-*a-b= mod-*mod-a*mod-b=))))
     )
   )

  (local
   (defthmd least-repeated-square-aux-lemma3
     (implies (and (natp tt)
                   (natp M)
                   (natp p)
                   (posp i)
                   (< 2 p)
                   (natp d)
                   (< d i)
                   (> d 0)
                   (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX I TT M P)
                               0)))
              (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX d TT M P)
                          0)))
     :hints (("Goal"
              :in-theory (e/d () (y^2=1modp primep-implies
                                            mod-*a-b= mod-*mod-a*mod-b=))))
     ))

  (local
   (defthmd least-repeated-square-aux-lemma4
     (implies (and (natp tt)
                   (natp m)
                   (natp p)
                   (posp i)
                   (< i m)
                   (< 2 p)
                   (not (= (least-repeated-square-aux i tt m p) 0))
                   (not (= (mod tt p) 1)))
              (not (= (least-repeated-square-aux 1 tt m p) 0)))
     :hints (("Goal"
              :use (:instance least-repeated-square-aux-lemma3
                              (d 1)
                              (i i)
                              (tt tt)
                              (m m)
                              (p p))
              :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies
                                                               mod-*a-b= mod-*mod-a*mod-b=))
              ))
     )
   )

  (local
   (defthmd least-repeated-square-tt^2^lrs-lemma1
     (implies (and (natp tt)
                   (posp M)
                   (natp p)
                   (posp i)
                   (< i m)
                   (<= 1 x)
                   (<= x (- m i))
                   ;(< (+ i 1) m)
                   (< 2 p)
                   (equal (least-repeated-square-aux i tt m p) 0))
                   ;(= lrs 0))
             ; (not (= (least-repeated-square-aux i tt m p) 0)))
              (not (= (mod (expt tt (expt 2 x)) p) 1)))
     :hints (("Goal"
              :use ((:instance least-repeated-square-aux-not=0-lemma1
                               (tt tt) (m m) (p p) (i i) (lrs (least-repeated-square-aux i tt m p))
                               ))
              :in-theory (e/d (acl2::expt) (y^2=1modp primep-implies
                                            mod-*a-b= mod-*mod-a*mod-b=))
              ))))
  )
--

  (local
   (defthmd least-repeated-square-tt^2^lrs-lemma1
     (implies (and (natp tt)
                   (posp M)
                   (natp p)
                   (posp i)
                   (< 2 p)
                   (equal (least-repeated-square-aux i tt m p) lrs)
                   (= lrs 0))
              (not (= (mod (expt tt (expt 2 (+ lrs (- i) 1))) p) 1)))
     :hints (("Goal"
              ;:use ((:instance least-repeated-square-aux-lemma2))
              :in-theory (e/d () (y^2=1modp primep-implies
                                                      mod-*a-b= mod-*mod-a*mod-b=))
              ))))

  (skip-proofs
   (defthm least-repeated-square-tt^2^lrs=1-1
     (IMPLIES (AND (NOT (EQUAL 0 I))
                   (EQUAL (LEAST-REPEATED-SQUARE-AUX I TT M P)
                          0)
                   (EQUAL (LEAST-REPEATED-SQUARE-AUX 1 TT M P)
                          0)
                   (INTEGERP TT)
                   (<= 0 TT)
                   (INTEGERP M)
                   (<= 0 M)
                   (INTEGERP P)
                   (<= 0 P)
                   (INTEGERP I)
                   (< 0 I)
                   (< I M)
                   (< 2 P)
                   (< 0 M)
                   (NOT (EQUAL (MOD TT P) 1)))
              (NOT (EQUAL (MOD (EXPT TT (EXPT 2 I)) P)
                          1)))
     )
   )

  (defthm least-repeated-square-tt^2^lrs=1
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (posp i)
                  (< i m)
                  (< 2 p)
                  (< 0 m)
                  (not (= (mod tt p) 1))
                  (= (mod (expt tt (expt 2 i)) p) 1))
             (= (mod (expt tt (expt 2 (least-repeated-square tt m p))) p) 1))
    :hints (("Goal"
             :use (
                   (:instance least-repeated-square-aux-not=0-lemma1
                              (tt tt) (m m) (p p) (lrs i) (i i))
                   (:instance least-repeated-square-aux-lemma4
                              (tt tt) (m m) (p p) (i i))
                   (:instance least-repeated-square-aux-not=0
                              (tt tt) (m m) (p p)
                              (lrs (least-repeated-square-aux 1 tt m p)))
                   )
             :do-not-induct t
             :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b=))
             ))
    )
  
  )

---

  (local
   (defthmd least-repeated-square-aux-lemma5
     (implies (and (natp tt)
                   (natp m)
                   (natp p)
                   (posp i)
                   (< i m)
                   ;(< (+ i 1) m)
                   (NOT (EQUAL (MOD (* TT TT) P) 1))
                   (< 2 p)
                   (= (least-repeated-square-aux (+ i 1) (MOD (* TT TT) P) m p) 0))
              (= (least-repeated-square-aux i tt m p) 0))
          :hints (("Goal"
              :in-theory (e/d () (y^2=1modp primep-implies
                                                               mod-*a-b= mod-*mod-a*mod-b=))
              ))
          ))

  (defthm least-repeated-square-tt^2^lrs=1
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (posp i)
                  (< i m)
                  (< 2 p)
                  (< 0 m)
                  (not (= (mod tt p) 1))
                  (= (mod (expt tt (expt 2 i)) p) 1))
             (= (mod (expt tt (expt 2 (least-repeated-square tt m p))) p) 1))
    :hints (("Goal"
             ;; :cases ((= i 0)
             ;;         (> i 0))
             :use (
                   (:instance least-repeated-square-aux-not=0-lemma1
                              (tt tt) (m m) (p p) (lrs i) (i 1))
                   ;; (:instance least-repeated-square-aux-lemma4
                   ;;            (tt tt) (m m) (p p) (i i))
                   (:instance least-repeated-square-aux-not=0
                              (tt tt) (m m) (p p)
                              (lrs (least-repeated-square-aux 1 tt m p)))
                   )
             :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b=))
             ))
    )
  )

---
  :hints (("Goal"
           :in-theory (enable acl2::mod-expt-fast)
           :cases ((= i 0)
                   (> i 0))         
           )
          ("Subgoal 1"
           :use (
                 (:instance least-repeated-square-aux-not=0-1
                            (tt tt) (m m) (p p) (lrs i) (i i))
                 (:instance least-repeated-square-aux-not=0-2
                            (tt tt) (m m) (p p) (i i))
                 (:instance least-repeated-square-aux-not=0
                            (tt tt) (m m) (p p)
                            (lrs (least-repeated-square-aux 0 tt m p)))
                 )
           )
          )
  )
  
  )

----
             ("Subgoal *1/9.1"
              ;; :cases ((= i 0)
              ;;         (= i 1)
              ;;         (= i 2))
              :use (:instance least-repeated-square-aux-not=0-lemma3 (d 2)
                              (i i)
                              (tt tt)
                              (m m)
                              (p p))
              )
             )
     )
   )
  )
             ("Subgoal *1/1"
              :cases ((= i 0)
                      (= i 1)
                      (= i 2))
              :use (:instance least-repeated-square-aux-not=0-2-1 (d 2)
                              (i i)
                              (tt tt)
                              (m m)
                              (p p))
              )
   ;;   )
   ;; )
  
  )

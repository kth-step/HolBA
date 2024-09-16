; memory 32->8 (LE)
; ----------------------
(define-fun loadfun_LE_32_8_8
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)))
  (_ BitVec 8)
  (select a ad)
)
(define-fun loadfun_LE_32_8_16
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)))
  (_ BitVec 16)
  (concat (select a (bvadd ad (_ bv1 32))) (select a (bvadd ad (_ bv0 32))))
)
(define-fun loadfun_LE_32_8_32
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)))
  (_ BitVec 32)
  (concat (select a (bvadd ad (_ bv3 32))) (select a (bvadd ad (_ bv2 32))) (select a (bvadd ad (_ bv1 32))) (select a (bvadd ad (_ bv0 32))))
)
(define-fun loadfun_LE_32_8_64
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)))
  (_ BitVec 64)
  (concat (select a (bvadd ad (_ bv7 32))) (select a (bvadd ad (_ bv6 32))) (select a (bvadd ad (_ bv5 32))) (select a (bvadd ad (_ bv4 32))) (select a (bvadd ad (_ bv3 32))) (select a (bvadd ad (_ bv2 32))) (select a (bvadd ad (_ bv1 32))) (select a (bvadd ad (_ bv0 32))))
)

(define-fun storefun_LE_32_8_8
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)) (v (_ BitVec 8)))
  (Array (_ BitVec 32) (_ BitVec 8))
  (store a ad v)
)
(define-fun storefun_LE_32_8_16
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)) (v (_ BitVec 16)))
  (Array (_ BitVec 32) (_ BitVec 8))
  (store (store a (bvadd ad (_ bv1 32)) ((_ extract 15 8) v)) (bvadd ad (_ bv0 32)) ((_ extract 7 0) v))
)
(define-fun storefun_LE_32_8_32
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)) (v (_ BitVec 32)))
  (Array (_ BitVec 32) (_ BitVec 8))
  (store (store (store (store a (bvadd ad (_ bv3 32)) ((_ extract 31 24) v)) (bvadd ad (_ bv2 32)) ((_ extract 23 16) v)) (bvadd ad (_ bv1 32)) ((_ extract 15 8) v)) (bvadd ad (_ bv0 32)) ((_ extract 7 0) v))
)
(define-fun storefun_LE_32_8_64
  ((a (Array (_ BitVec 32) (_ BitVec 8))) (ad (_ BitVec 32)) (v (_ BitVec 64)))
  (Array (_ BitVec 32) (_ BitVec 8))
  (store (store (store (store (store (store (store (store a (bvadd ad (_ bv7 32)) ((_ extract 63 56) v)) (bvadd ad (_ bv6 32)) ((_ extract 55 48) v)) (bvadd ad (_ bv5 32)) ((_ extract 47 40) v)) (bvadd ad (_ bv4 32)) ((_ extract 39 32) v)) (bvadd ad (_ bv3 32)) ((_ extract 31 24) v)) (bvadd ad (_ bv2 32)) ((_ extract 23 16) v)) (bvadd ad (_ bv1 32)) ((_ extract 15 8) v)) (bvadd ad (_ bv0 32)) ((_ extract 7 0) v))
)

; memory 64->8 (LE)
; ----------------------
(define-fun loadfun_LE_64_8_8
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)))
  (_ BitVec 8)
  (select a ad)
)
(define-fun loadfun_LE_64_8_16
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)))
  (_ BitVec 16)
  (concat (select a (bvadd ad (_ bv1 64))) (select a (bvadd ad (_ bv0 64))))
)
(define-fun loadfun_LE_64_8_32
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)))
  (_ BitVec 32)
  (concat (select a (bvadd ad (_ bv3 64))) (select a (bvadd ad (_ bv2 64))) (select a (bvadd ad (_ bv1 64))) (select a (bvadd ad (_ bv0 64))))
)
(define-fun loadfun_LE_64_8_64
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)))
  (_ BitVec 64)
  (concat (select a (bvadd ad (_ bv7 64))) (select a (bvadd ad (_ bv6 64))) (select a (bvadd ad (_ bv5 64))) (select a (bvadd ad (_ bv4 64))) (select a (bvadd ad (_ bv3 64))) (select a (bvadd ad (_ bv2 64))) (select a (bvadd ad (_ bv1 64))) (select a (bvadd ad (_ bv0 64))))
)

(define-fun storefun_LE_64_8_8
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)) (v (_ BitVec 8)))
  (Array (_ BitVec 64) (_ BitVec 8))
  (store a ad v)
)
(define-fun storefun_LE_64_8_16
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)) (v (_ BitVec 16)))
  (Array (_ BitVec 64) (_ BitVec 8))
  (store (store a (bvadd ad (_ bv1 64)) ((_ extract 15 8) v)) (bvadd ad (_ bv0 64)) ((_ extract 7 0) v))
)
(define-fun storefun_LE_64_8_32
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)) (v (_ BitVec 32)))
  (Array (_ BitVec 64) (_ BitVec 8))
  (store (store (store (store a (bvadd ad (_ bv3 64)) ((_ extract 31 24) v)) (bvadd ad (_ bv2 64)) ((_ extract 23 16) v)) (bvadd ad (_ bv1 64)) ((_ extract 15 8) v)) (bvadd ad (_ bv0 64)) ((_ extract 7 0) v))
)
(define-fun storefun_LE_64_8_64
  ((a (Array (_ BitVec 64) (_ BitVec 8))) (ad (_ BitVec 64)) (v (_ BitVec 64)))
  (Array (_ BitVec 64) (_ BitVec 8))
  (store (store (store (store (store (store (store (store a (bvadd ad (_ bv7 64)) ((_ extract 63 56) v)) (bvadd ad (_ bv6 64)) ((_ extract 55 48) v)) (bvadd ad (_ bv5 64)) ((_ extract 47 40) v)) (bvadd ad (_ bv4 64)) ((_ extract 39 32) v)) (bvadd ad (_ bv3 64)) ((_ extract 31 24) v)) (bvadd ad (_ bv2 64)) ((_ extract 23 16) v)) (bvadd ad (_ bv1 64)) ((_ extract 15 8) v)) (bvadd ad (_ bv0 64)) ((_ extract 7 0) v))
)

; --------------------------------------------------------------------------------------------

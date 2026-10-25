; Differential baseline for docs/impl/identity-extent-test.md.
; Runs on hyperon-experimental revision 3f76dc460da6961f57f69f6c3e550c59c74ada83.
; No custom grounded atom or host-side identity store is used.

; Stable occurrence IDs and intensions are an explicit user protocol.
(entity a (glue (a-left out) (a-right in)))
(entity b (glue (b-left out) (b-right in)))
(entity uses primitive)

; Evidence and dependency edges are also explicit atoms.
(evidence a-build strict)
(evidence b-build strict)
(evidence observation-p strict)
(evidence observation-q strict)
(evidence a-p strict)
(evidence b-p strict)
(evidence a-q strict)
(evidence b-q strict)
(evidence equal-p strict)
(evidence link-a strict)
(evidence link-b strict)
(evidence map-q-p strict)
(evidence refuter-a strict)

(premise a-p a-build)
(premise a-p observation-p)
(premise b-p b-build)
(premise b-p observation-p)
(premise a-q a-build)
(premise a-q observation-q)
(premise b-q b-build)
(premise b-q observation-q)
(premise equal-p a-p)
(premise equal-p b-p)
(premise link-a a-build)
(premise link-b b-build)

; Same context-indexed extent, two distinct entity IDs.
(projection a p diag01 a-p)
(projection b p diag01 b-p)
(projection a q diag012 a-q)
(projection b q diag01 b-q)
(equal-at a b p equal-p)

; Tuple membership makes the q counterexample and restriction observable.
(holds a q 0 0 a-q)
(holds a q 1 1 a-q)
(holds a q 2 2 a-q)
(holds b q 0 0 b-q)
(holds b q 1 1 b-q)
(maps q p 0 0 map-q-p)
(maps q p 1 1 map-q-p)

; Relations are endpoints only because the protocol explicitly uses their IDs.
(metaedge edge-a uses subject a p link-a)
(metaedge edge-b uses subject b p link-b)

; 1–3: identities/intensions remain separate and the extent lookup returns both.
!(assertEqualToResult
  (match &self (entity a $intension) $intension)
  ((glue (a-left out) (a-right in))))
!(assertEqualToResult
  (match &self (entity b $intension) $intension)
  ((glue (b-left out) (b-right in))))
!(assertEqual
  (match &self (projection $entity p diag01 $evidence) $entity)
  (superpose (a b)))

; 4–5: two endpoints and a local EqualAt atom; no equality at q is inferred.
!(assertEqual
  (match &self (metaedge $edge uses subject $entity p $evidence) $edge)
  (superpose (edge-a edge-b)))
!(assertEqualToResult
  (match &self (equal-at a b p $evidence) $evidence)
  (equal-p))
!(assertEqualToResult
  (match &self (equal-at a b q $evidence) $evidence)
  ())

; 6–7: (2,2) distinguishes q; the explicit point map restricts a back to p.
!(assertEqualToResult
  (match &self (holds a q 2 2 $evidence) $evidence)
  (a-q))
!(assertEqualToResult
  (match &self (holds b q 2 2 $evidence) $evidence)
  ())
!(assertEqual
  (match &self
    (, (holds a q $qx $qy $projection-evidence)
       (maps q p $qx $px $map-evidence)
       (maps q p $qy $py $map-evidence))
    (pair $px $py))
  (superpose ((pair 0 0) (pair 1 1))))

; 8: native remove-atom removes exactly one atom. Hyperon does not traverse
; the user-level premise relation, so dependent projection/equality/metaedge
; atoms remain. The assertions record that mismatch rather than hiding it.
!(remove-atom &self (evidence a-build strict))
!(assertEqualToResult
  (match &self (evidence a-build $strength) $strength)
  ())
!(assertEqualToResult
  (match &self (projection a p $extent $evidence) $evidence)
  (a-p))
!(assertEqualToResult
  (match &self (equal-at a b p $evidence) $evidence)
  (equal-p))
!(assertEqualToResult
  (match &self (metaedge edge-a uses subject a p $evidence) $evidence)
  (link-a))

; Retraction history is retained only when the protocol adds it manually.
!(add-atom &self (retracted a-build refuter-a))
!(assertEqualToResult
  (match &self (retracted a-build $reason) $reason)
  (refuter-a))

changequote(<!,!>)
changecom(<!/*!>,<!*/!>)

include(msgs.m4i)
include(crypto.m4i)

theory ODoH begin

builtins: diffie-hellman, hashing, symmetric-encryption, signing

functions: Expand/3, Extract/2, hmac/1, aead/3, decrypt/2, aead_verify/3 

restriction Eq_check_succeed: "All x y #i. Eq(x,y) @ i ==> x = y"
restriction Neq_check_succeed: "All x y #i. Neq(x,y) @ i ==> not (x = y)"


/* The plaintext can be recovered with the key */
equations: decrypt(aead(k, p, a), k) = p
/* The authentication can be checked with the key and AAD */
equations: aead_verify(aead(k, p, a), a, k) = true

rule Starter:
  [ Fr(~kxy) ]
--[ Channel($X, $Y) ]->
  [ KeyExC($X, $Y, ~kxy)
  , KeyExS($X, $Y, ~kxy)
  , KeyExI($X, $Y, ~kxy)
  ]

rule Generate_DH_key_pair:
  [ Fr(~x)
  , Fr(~key_id)
  ]
-->
  [ !Pk($A, ~key_id, 'g'^~x)
  , Out(<~key_id, 'g'^~x>)
  , !Ltk($A,~key_id, ~x)
  ]

rule C_1:
  [ KeyExC($C, $P, ~k)
  , Fr(~q)
  ]
--[]->
  [ C_1($C, $P, ~k, ~q)
  ]

rule C_2:
let
  gx = 'g'^~x
  kem_context = <gx, gy>
  dh = gy^~x
  shared_secret = ExtractAndExpand(dh, kem_context)
  key_id = ~key_id
  msg_type='0x01'
  query = ~q
  resp_seed = ~n
in
  [ C_1($C, $P, ~k, ~q)
  , !Pk($T, ~key_id, gy)
  , Fr(~x)
  , Fr(~n)
  ]
--[ Neq($P, $T)]->
  [ Out(senc(<$T, ODoHMessage>, ~k)) ] 

rule P_1:
  [ KeyExS($C, $P, ~k)
  , In(senc(<$T, <gx, opaque_message>>, ~k))
  ]
--[ Secret(~k) ]->
  [Out(<$T, <gx, opaque_message>>)]

rule T_1:
let
  gy = 'g'^~y
  kem_context = <gx, gy>
  dh = gx^~y
  shared_secret = ExtractAndExpand(dh, kem_context)
  expected_aad = <L, key_id, '0x01'>
in
  [ In(<$T, gx, ODoHMessage>)
  , !Ltk($T, ~key_id, ~y)
  ]
--[ T_1(gy)
  ]->
  [Out('Done')]

rule revSK:
  [ KeyExI($X, $Y, ~kxy) ]
--[ RevSk(~kxy) ]->
  [ Out(~kxy) ]

lemma secret:
  "All x #i #j . K(x)@j & Secret(x)@i ==> Ex #k . RevSk(x)@k"

lemma half_way:
  exists-trace
  "Ex gy #i . T_1(gy)@i"

end

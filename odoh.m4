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

rule C_QueryGeneration:
  [ KeyExC($C, $P, ~k)
  , Fr(~q)
  ]
--[]->
  [ C_QueryGeneration($C, $P, ~k, ~q)
  ]

rule C_QueryEncryption:
let
  gx = 'g'^~x
  kem_context = <gx, gy>
  dh = gy^~x
  shared_secret = ExtractAndExpand(dh, kem_context)
  key_id = ~key_id
  msg_type='0x01'
  query = ~q
in
  [ C_QueryGeneration($C, $P, ~k, ~q)
  , !Pk($T, ~key_id, gy)
  , Fr(~x)
  ]
--[ Neq($P, $T)]->
  [ Out(senc(<$T, ODoHQuery>, ~k)) ] 

rule P_HandleQuery:
  [ KeyExS($C, $P, ~k)
  , In(senc(<$T, <gx, opaque_message>>, ~k))
  ]
--[ Secret(~k) ]->
  [Out(<$T, <gx, opaque_message>>)]

rule T_HandleQuery:
let
  gy = 'g'^~y
  kem_context = <gx, gy>
  dh = gx^~y
  shared_secret = ExtractAndExpand(dh, kem_context)
  response_secret = ExtractAndExpand(shared_secret, 'odoh response')
  expected_aad = <L, key_id, '0x01'>
in
  [ In(<$T, gx, ODoHQuery>)
  , !Ltk($T, ~key_id, ~y)
  ]
--[ T_HandleQuery(gy) ]->
  [ Out('Done')
  , T_ResponseEncryption(msg_id, response_secret)]

rule T_ResponseEncryption:
let
  msg_type='0x02'
  response = ~r
in
  [ T_ResponseEncryption(msg_id, shared_secret)
  , Fr(~r)
  ]
--[  ]->
  [  ]

rule revSK:
  [ KeyExI($X, $Y, ~kxy) ]
--[ RevSk(~kxy) ]->
  [ Out(~kxy) ]

lemma secret:
  "All x #i #j . K(x)@j & Secret(x)@i ==> Ex #k . RevSk(x)@k"

lemma half_way:
  exists-trace
  "Ex gy #i . T_HandleQuery(gy)@i"

end

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
  [ C_QueryGeneration(~q, $C, $P, ~k)
  ]

rule C_QueryEncryption:
let
  gx = 'g'^~x
  kem_context = <gx, gy>
  dh = gy^~x
  shared_secret = ExtractAndExpand(dh, kem_context)
  response_secret = ExtractAndExpand(shared_secret, 'odoh_response')
  key_id = ~key_id
  msg_type='0x01'
  query = ~q
  msg_id = ~msg_id
in
  [ C_QueryGeneration(~q, $C, $P, ~k)
  , !Pk($T, ~key_id, gy)
  , Fr(~x)
  , Fr(~msg_id)
  ]
--[ Neq($P, $T)]->
  [ Out(senc(<$T, ODoHQuery>, ~k))
  , C_ResponseHandler(query, $C, $P, ~k,  $T, response_secret, ~msg_id)
  ] 

rule P_HandleQuery:
  [ KeyExS($C, $P, ~k)
  , In(senc(<$T, <ODoHHeader, <gx, opaque_message>>>, ~k))
  , Fr(~ptid)
  ]
--[ Secret(~k) ]->
  [Out(<$T, <ODoHHeader, <gx, opaque_message>>>)
  , P_ResponseHandler(~ptid, $C, $P, ~k, msg_id)
  ]

rule T_HandleQuery:
let
  gy = 'g'^~y
  kem_context = <gx, gy>
  dh = gx^~y
  shared_secret = ExtractAndExpand(dh, kem_context)
  response_secret = ExtractAndExpand(shared_secret, 'odoh_response')
  expected_aad = <L, key_id, '0x01'>
  key_id = ~key_id
in
  [ In(<$T, ODoHQuery>)
  , !Ltk($T, ~key_id, ~y)
  , Fr(~ttid)
  ]
--[ T_HandleQuery(gy) ]->
  [ T_ResponseEncryption(~ttid, msg_id, ~key_id, response_secret)
  ]

rule T_ResponseEncryption:
let
  msg_type='0x02'
  answer = ~r
  psk = shared_secret
  key_id = ~key_id
in
  [ T_ResponseEncryption(~ttid, msg_id, ~key_id, shared_secret)
  , Fr(~r)
  ]
--[ T_Done(~ttid, msg_id) ]->
  [ Out(ODoHResponse) ]

rule P_HandleResponse:
  [ P_ResponseHandler(~ptid, $C, $P, ~k, msg_id)
  , In(<ODoHHeader, opaque_message>)
  ]
--[ P_Done(~ptid, msg_id)]->
  [ Out(senc(<ODoHHeader, opaque_message>, ~k)) ]

rule C_HandleResponse:
let
  expected_msg_type = '0x02'
  psk = response_secret
  msg_id = ~msg_id
in
  [ C_ResponseHandler(~query, $C, $P, ~k,  $T, response_secret, ~msg_id)
  , In(senc(ODoHResponse, ~k)) ]
--[ Eq(expected_msg_type, msg_type)
  , C_Done(~query, answer)
  ]->
  []

rule revSK:
  [ KeyExI($X, $Y, ~kxy) ]
--[ RevSk(~kxy) ]->
  [ Out(~kxy) ]

lemma secret:
  "All x #i #j . K(x)@j & Secret(x)@i ==> Ex #k . RevSk(x)@k"

lemma half_way:
  exists-trace
  "Ex gy #i . T_HandleQuery(gy)@i"

lemma end_to_end:
  exists-trace
  "Ex q a #i. C_Done(q, a)@i"

end

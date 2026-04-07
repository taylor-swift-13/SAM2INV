int main1(int e){
  int v1q, h6d, q2bn, k44y, c6oa;
  v1q=e*2;
  h6d=0;
  q2bn=e;
  k44y=v1q;
  c6oa=v1q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v1q == e * 2;
  loop invariant 0 <= h6d;
  loop invariant (v1q > 0) ==> (h6d <= v1q);
  loop invariant (v1q > 0 && h6d >= 1) ==> (q2bn == h6d / v1q && k44y == q2bn && c6oa == h6d % v1q);
  loop invariant v1q == \at(e,Pre) * 2;
  loop invariant (h6d == 0 && q2bn == \at(e,Pre) && c6oa == v1q && k44y == v1q)
                   || (v1q > 0 && k44y == q2bn && q2bn * v1q + c6oa == h6d && 0 <= c6oa && c6oa < v1q);
  loop invariant (h6d > 0) ==> q2bn == h6d / v1q;
  loop invariant (h6d > 0) ==> k44y == q2bn;
  loop invariant (h6d == 0) ==> c6oa == v1q;
  loop invariant (h6d > 0) ==> (h6d == (q2bn * v1q + c6oa));
  loop invariant (h6d > 0) ==> (0 <= c6oa && c6oa < v1q);
  loop invariant (h6d == 0 ==> q2bn == e && k44y == v1q && c6oa == v1q)
                   && (h6d > 0 && v1q > 0 ==> q2bn == (h6d / v1q) && k44y == q2bn && c6oa == (h6d % v1q));
  loop assigns h6d, c6oa, q2bn, k44y;
*/
while (v1q > 0 && h6d < v1q) {
      h6d = h6d + 1;
      c6oa = h6d % v1q;
      q2bn = h6d / v1q;
      k44y = q2bn;
  }
}
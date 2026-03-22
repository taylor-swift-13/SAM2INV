int main1(int b){
  int k, c1eo, q6nv, y, s2tw, hj;
  k=b;
  c1eo=0;
  q6nv=1;
  y=c1eo;
  s2tw=6;
  hj=(b%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(b, Pre);
  loop invariant s2tw == 6 || s2tw == k;
  loop invariant y == 0;
  loop invariant b >= \at(b, Pre);
  loop invariant q6nv >= 1;
  loop invariant hj == ((\at(b, Pre) % 6) + 2);
  loop invariant (s2tw == 6) ==> (b == \at(b, Pre) && q6nv == 1 && y == 0);
  loop invariant ((q6nv == 1) ==> (b == \at(b,Pre)));
  loop assigns b, q6nv, y, s2tw;
*/
while (s2tw<=k-1) {
      q6nv = q6nv*hj+4;
      y = y*hj;
      b = b + q6nv;
      s2tw = k;
  }
}
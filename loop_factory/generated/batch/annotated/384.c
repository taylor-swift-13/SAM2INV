int main1(int m,int q){
  int h, s, v, k;

  h=q;
  s=0;
  v=h;
  k=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == q;
  loop invariant s >= 0;
  loop invariant s <= h || h < 0;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (k == 0) ==> (s == 0);
  loop invariant (s == 0) ==> (v == h);

  loop invariant 0 <= s;
  loop invariant v >= h + 4*s;
  loop invariant k >= 4*s;
  loop assigns v, k, s;
*/
while (s<h) {
      v = v*2+4;
      k = k*v+4;
      s = s+1;
  }

}

int main1(int p,int q){
  int y, d, k, v;

  y=p;
  d=0;
  k=q;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == p + 2*d;
  loop invariant k == q + 3*d + 3*((d + 6)/7);
  loop invariant y == p;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= d;

  loop invariant k >= q + 3*d;
  loop invariant k <= q + 6*d;
  loop invariant k == \at(q, Pre) + 3*d + 3*((d+6)/7);
  loop invariant v == \at(p, Pre) + 2*d;
  loop invariant y == \at(p, Pre);


  loop invariant q + 3*d <= k;
  loop assigns d, k, v;
*/
while (d<y) {
      k = k+3;
      v = v+2;
      if ((d%7)==0) {
          k = k-(-3);
      }
      d = d+1;
  }

}

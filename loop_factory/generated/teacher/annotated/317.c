int main1(int a,int m){
  int q, v, d, p;

  q=33;
  v=q;
  d=0;
  p=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == ((33 - v) / 2) * (2*p + 1);

  loop invariant p == m;
  loop invariant p == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v <= 33;
  loop invariant 2*d == (33 - v) * (2*p + 1);
  loop invariant 2*d == (33 - v) * (2*m + 1);
  loop invariant v >= 1;

  loop invariant q == 33;

  loop assigns d, v;
*/
while (v>=2) {
      d = d+p+p;
      d = d+1;
      v = v-2;
  }

}

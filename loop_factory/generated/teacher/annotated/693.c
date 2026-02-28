int main1(int a,int b,int k,int m){
  int d, i, h, q, e, f;

  d=15;
  i=0;
  h=0;
  q=1;
  e=6;
  f=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant e == 6 + 6 * f;
  loop invariant q == 3 * f * f + 3 * f + 1;
  loop invariant h == f * f * f;
  loop invariant f <= d + 1;
  loop invariant d == 15;
  loop invariant f >= 0;
  loop invariant e == 6*(f+1);
  loop assigns f, h, q, e;
*/
while (f<=d) {
      f = f+1;
      h = h+q;
      q = q+e;
      e = e+6;
  }

}

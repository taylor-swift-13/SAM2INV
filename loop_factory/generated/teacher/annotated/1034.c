int main1(int m,int p){
  int n, j, t, q;

  n=m+16;
  j=0;
  t=j;
  q=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (q == \at(p, Pre) && t == 0) || t == q*q;
  loop invariant q >= \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant n == \at(m, Pre) + 16;
  loop invariant t >= 0;
  loop invariant (t == 0 && q == \at(p, Pre)) || t == q * q;
  loop invariant (t == 0 || t == q * q);
  loop invariant t <= q*q;
  loop invariant (t == q*q) || (q == \at(p, Pre) && t == 0);
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant (t == q*q) || (t == 0 && q == \at(p, Pre));
  loop assigns q, t;
*/
while (1) {
      q = q+1;
      t = q*q;
  }

}

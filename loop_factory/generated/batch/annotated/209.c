int main1(int a,int q){
  int h, t, n;

  h=27;
  t=h;
  n=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t >= 0;
  loop invariant t <= 27;
  loop invariant h == 27;
  loop invariant 0 <= t <= 27;
  loop invariant 0 <= t;
  loop invariant t <= h;
  loop invariant (\at(q, Pre) == 0 || \at(q, Pre) == 1) ==> n == \at(q, Pre);
  loop assigns n, t;
*/
while (t>=1) {
      n = n*n;
      t = t-1;
  }

}

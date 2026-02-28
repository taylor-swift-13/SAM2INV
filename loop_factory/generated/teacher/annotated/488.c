int main1(int p,int q){
  int i, f, n;

  i=(q%7)+14;
  f=0;
  n=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == (\at(q, Pre) % 7) + 14;
  loop invariant f <= i;
  loop invariant 0 <= f;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant f >= 0;

  loop invariant i == (q % 7) + 14;
  loop invariant (f > 0) ==> (n % 2 == 0);
  loop invariant (f == 0) ==> (n == p);
  loop invariant (f == 0) || (n % 2 == 0);
  loop assigns f, n;
*/
while (f<i) {
      n = n+1;
      n = n+n;
      f = f+1;
  }

}

int main1(int p,int q){
  int i, f, n;

  i=(q%7)+14;
  f=0;
  n=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == ((\at(q, Pre) % 7) + 14);
  loop invariant 0 <= f;
  loop invariant f <= i;
  loop invariant n >= p;

  loop invariant i == (q % 7) + 14;
  loop invariant f >= 0;
  loop invariant i >= 0;
  loop invariant f >= 0 && f <= i && (f == 0 ==> n == p) && (f > 0 ==> n >= 0);
  loop invariant (f == 0) ==> (n == p);
  loop assigns f, n;
*/
while (f<i) {
      n = n*2;
      n = n*n;
      f = f+1;
  }

}

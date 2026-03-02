int main1(int k,int p){
  int f, j, n;

  f=(p%38)+15;
  j=2;
  n=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 0 || n == 1;
  loop invariant f == (\at(p,Pre) % 38) + 15;
  loop invariant k == \at(k,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant f == \at(p, Pre) % 38 + 15;
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant f == (p % 38) + 15;

  loop invariant (k == \at(k, Pre)) && (p == \at(p, Pre));

  loop invariant n >= 0;
  loop invariant n <= 1;
  loop invariant f == (\at(p, Pre) % 38) + 15;
  loop invariant n*(n-1) == 0;
  loop invariant 0 <= n && n <= 1;
  loop invariant p == \at(p, Pre) && k == \at(k, Pre);
  loop invariant (n == 0 || n == 1);
  loop assigns n;
*/
while (1) {
      n = n+3;
      if (n+1<f) {
          n = n+n;
      }
      n = n-n;
  }

}

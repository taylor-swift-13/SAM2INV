int main1(int x,int r){
  int a, n, ejb, hj;
  a=x;
  n=1;
  ejb=0;
  hj=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == x;
  loop invariant ejb == 4*(n-1);
  loop invariant hj == 4*n;
  loop invariant 1 <= n;
  loop invariant n <= a || a <= 0;
  loop invariant x == \at(x, Pre);
  loop invariant r == \at(r, Pre);
  loop assigns ejb, hj, n;
*/
while (n<a) {
      ejb += 4;
      hj += 4;
      n += 1;
  }
}
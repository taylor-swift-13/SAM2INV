int main1(){
  int k, uf, v, np, l1xk;
  k=1;
  uf=1;
  v=0;
  np=0;
  l1xk=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant np == v*(v - 1)/2;
  loop invariant l1xk == 8 + v;
  loop invariant l1xk == 8 + uf*v;
  loop invariant 0 <= v <= k;
  loop assigns np, l1xk, v;
*/
while (1) {
      if (!(v<=k-1)) {
          break;
      }
      np += v;
      l1xk = l1xk + uf;
      v++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= l1xk <= 9;
  loop assigns l1xk;
*/
while (1) {
      if (!(l1xk>=1)) {
          break;
      }
      l1xk--;
  }
}
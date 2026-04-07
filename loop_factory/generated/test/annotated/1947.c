int main1(){
  int lt, lyk, uf, vx;
  lt=1+18;
  lyk=0;
  uf=1;
  vx=lyk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uf == 1 + lyk*(vx + 1);
  loop invariant 0 <= lyk;
  loop invariant lyk <= lt;
  loop invariant vx == 0;
  loop assigns lyk, uf;
*/
while (lyk < lt) {
      uf += vx;
      lyk = lyk + 1;
      uf = uf + 1;
  }
}
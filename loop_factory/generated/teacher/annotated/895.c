int main1(int p,int q){
  int n, i, x, v;

  n=(q%36)+11;
  i=0;
  x=q;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == (q % 36) + 11;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == ((\at(q, Pre) % 36) + 11);
  loop invariant n == (\at(q, Pre) % 36) + 11;
  loop invariant ((v - x) - (1 - q)) % 3 == 0;
  loop invariant n == (q%36) + 11;
  loop invariant n == ((\at(q, Pre)) % 36) + 11;
  loop invariant p == \at(p,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant n == (\at(q,Pre) % 36) + 11;
  loop assigns v, x;
*/
while (1) {
      v = v+x;
      x = x*2+3;
  }

}

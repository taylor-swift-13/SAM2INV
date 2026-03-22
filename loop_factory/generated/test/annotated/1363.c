int main1(int b,int u){
  int yc6, e, r, eaiv;
  yc6=u*2;
  e=yc6;
  r=5;
  eaiv=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((eaiv == 0) <==> (r == 5));
  loop invariant (r == 5) || (r == 2);
  loop invariant e <= yc6;
  loop invariant eaiv >= 0;
  loop invariant r >= 0;
  loop invariant yc6 == u*2;
  loop invariant e <= 2 * \at(u, Pre);
  loop assigns eaiv, e, r;
*/
while (e>=1) {
      eaiv = eaiv*eaiv+r;
      r = r%3;
      e = e - 1;
  }
}
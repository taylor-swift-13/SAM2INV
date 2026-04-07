int main1(){
  int f46b, zq, x, bx, q80k, stof, txn, xc;
  f46b=62;
  zq=0;
  x=17;
  bx=10;
  q80k=0;
  stof=f46b;
  txn=f46b;
  xc=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= zq;
  loop invariant zq <= f46b;
  loop invariant q80k == 0;
  loop invariant x == 17 - 3*zq;
  loop invariant bx == (10 + 3*zq);
  loop invariant stof >= (62 + 2*zq);
  loop invariant txn >= (62 + zq);
  loop assigns x, bx, q80k, zq, stof, txn;
*/
while (zq<=f46b-1) {
      if (!(q80k!=0)) {
          x = x - 3;
          bx = bx + 3;
          q80k = 0;
      }
      else {
          x = x + 3;
          bx = bx - 3;
          q80k = 1;
      }
      zq++;
      if (zq+2<=xc+f46b) {
          stof += txn;
      }
      txn = txn + zq;
      stof += 2;
      txn += stof;
  }
}
int main1(){
  int y65, ljz, ya, d, tx, nn;
  y65=1-7;
  ljz=0;
  ya=0;
  d=0;
  tx=ljz;
  nn=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ya == d;
  loop invariant nn == 12 + ((ya*(ya+1))/2);
  loop invariant tx == 0;
  loop invariant ya >= 0;
  loop invariant d >= 0;
  loop invariant nn >= 12;
  loop invariant ya - d == 0;
  loop invariant nn == 12 + d*(d+1)/2;
  loop invariant y65 == (1 - 7);
  loop assigns ya, d, nn, tx;
*/
while (d<y65) {
      ya += 1;
      d++;
      nn += ya;
      tx = tx*2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d >= 0;
  loop invariant tx >= 0;
  loop invariant ljz == 0;
  loop assigns tx, ya, y65, d;
*/
while (ya<=ljz-1) {
      tx += 1;
      ya += 1;
      y65 = y65+(tx%9);
      d = d*2;
  }
}
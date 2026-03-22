int main1(){
  int rli, hwdq, u, mo;
  rli=66;
  hwdq=1;
  u=13;
  mo=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hwdq <= rli;
  loop invariant (hwdq == 1) ==> (u == 13 && mo == 2);
  loop invariant u >= 13;
  loop invariant mo == (u*u + u - 178) / 2;
  loop invariant (hwdq == 1) ==> (mo == 2);
  loop invariant rli - hwdq <= rli - 1;
  loop assigns u, mo, hwdq;
*/
while (hwdq<=rli-1) {
      u = u + 1;
      mo = mo + u;
      hwdq = rli;
  }
}
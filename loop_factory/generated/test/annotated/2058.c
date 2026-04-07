int main1(){
  int jy, ws, k, o, ru;
  jy=1+25;
  ws=0;
  k=ws;
  o=-1;
  ru=jy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ru + ws == jy);
  loop invariant (k == 0);
  loop invariant (0 <= ws && ws <= jy);
  loop invariant (0 <= ru && ru <= jy);
  loop invariant (-1 <= o && o <= -1 + jy * 4);
  loop invariant (-1 <= o && o <= -1 + 4*ws);
  loop assigns ru, ws, k, o;
*/
while (ws < jy) {
      ru--;
      ws = ws + 1;
      k = k*k+k;
      o = o+(ru%5);
  }
}
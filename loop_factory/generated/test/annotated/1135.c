int main1(){
  int sr5t, qxo, sjhh, m7, ufg, nbg, v;
  sr5t=1+4;
  qxo=sr5t;
  sjhh=6;
  m7=6;
  ufg=0;
  nbg=6;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - qxo == -5;
  loop invariant qxo <= sr5t;
  loop invariant qxo - v == sr5t;
  loop invariant ufg <= v;
  loop invariant m7 <= nbg + v;
  loop invariant 0 <= sjhh;
  loop invariant sjhh <= nbg;
  loop invariant 0 <= v <= sr5t;
  loop invariant 0 <= ufg;
  loop invariant ufg <= nbg;
  loop invariant 0 <= m7;
  loop assigns v, qxo, sjhh, ufg, m7;
*/
while (qxo<=sr5t-1) {
      if (qxo%3==0) {
          if (sjhh>0) {
              sjhh--;
              ufg++;
          }
      }
      else {
          if (sjhh<nbg) {
              sjhh = sjhh + 1;
              m7 += 1;
          }
      }
      v++;
      qxo += 1;
  }
}
int main1(){
  int qn, yx4n, c9f, zv7, zrd, b90t;
  qn=1;
  yx4n=-1;
  c9f=0;
  zv7=1;
  zrd=6;
  b90t=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zrd == 6*(b90t + 1);
  loop invariant zv7 > 0;
  loop invariant c9f >= 0;
  loop invariant 0 <= b90t <= qn + 1;
  loop assigns b90t, c9f, zv7, zrd;
*/
while (1) {
      if (!(b90t<=qn)) {
          break;
      }
      c9f = c9f + zv7;
      b90t++;
      zv7 += zrd;
      zv7 = zv7*zv7;
      c9f = c9f + yx4n;
      zrd += 6;
  }
}
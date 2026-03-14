int main1(int x,int m){
  int ow, t, alc, r4;
  ow=(m%39)+18;
  t=0;
  alc=0;
  r4=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (alc == 0) ==> (r4 == 0);
  loop invariant (alc > 0) ==> (r4 == ow - alc);
  loop invariant x == \at(x, Pre) + alc * ow;
  loop invariant 0 <= alc;
  loop assigns alc, x, r4;
*/
while (1) {
      if (!(alc<=ow-1)) {
          break;
      }
      alc++;
      x += ow;
      r4 = (ow)+(-(alc));
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t % 8 == 0;
  loop invariant t <= alc + 7;
  loop invariant t >= 0;
  loop assigns t;
*/
for (; t<=alc-1; t += 8) {
  }
}
int main1(){
  int i5, dg, s, b2at, cjq, erx;
  i5=1;
  dg=i5;
  s=25;
  b2at=0;
  cjq=(1%6)+2;
  erx=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i5 == 1;
  loop invariant b2at <= i5;
  loop invariant (b2at <= i5) &&
                   (dg >= 1) &&
                   (s >= 25) &&
                   (cjq >= 3) &&
                   (erx >= 5) &&
                   (b2at >= 0) &&
                   (i5 == 1);
  loop invariant dg >= 1;
  loop invariant s >= 25;
  loop invariant cjq >= 3;
  loop invariant erx >= 5;
  loop invariant b2at <= i5 &&
                 b2at >= 0 &&
                 s >= 0 &&
                 dg >= 0 &&
                 erx >= 0 &&
                 cjq >= 0;
  loop assigns b2at, cjq, dg, s, erx;
*/
while (1) {
      if (b2at>=i5) {
          break;
      }
      dg = dg*cjq+1;
      s = s*cjq;
      b2at++;
      cjq = cjq + dg;
      erx = erx*2+(s%2)+1;
      cjq = cjq + erx;
  }
}
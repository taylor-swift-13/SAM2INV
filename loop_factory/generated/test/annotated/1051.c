int main1(){
  int d94, yba, r2, p, ntc, yx;
  d94=1+13;
  yba=d94;
  r2=0;
  p=0;
  ntc=yba;
  yx=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 0;
  loop invariant r2 >= 0;
  loop invariant yx >= 3;
  loop invariant yba >= 0;
  loop invariant d94 == 14;
  loop invariant yba <= d94;
  loop invariant ((p == 0 && r2 == 0 && yba == 14 && yx == 3) ||
                    (p == 0 && r2 == 14 && yba == 0 && yx == 4));
  loop invariant p == r2*yba;
  loop assigns p, r2, yx, yba;
*/
while (1) {
      if (!(yba>0)) {
          break;
      }
      p = p+r2*yba;
      yx++;
      r2 += yba;
      yba = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d94 >= 14;
  loop invariant ntc >= 14;
  loop invariant yba == 0;
  loop invariant d94 <= ntc;
  loop assigns d94, ntc;
*/
while (d94<=yba-1) {
      d94 += 1;
      ntc++;
      ntc = ntc*ntc+ntc;
  }
}
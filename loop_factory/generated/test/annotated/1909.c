int main1(){
  int jez, ei, yp, ox, p, ep, gki, fcgf;
  jez=10;
  ei=0;
  yp=0;
  ox=-3;
  p=0;
  ep=8;
  gki=ei;
  fcgf=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yp == ((ei + 1) / 2);
  loop invariant p == ei + 6 * (ei / 7);
  loop invariant gki == (ei / 2);
  loop invariant ox == -3 + 3 * (ei / 2);
  loop invariant fcgf >= 0;
  loop invariant ei <= jez;
  loop invariant ep == 8 + 2 * ((ei + 1) / 2) &&
                   yp == ((ei + 1) / 2);
  loop invariant ep == 8 + ei + (ei % 2);
  loop assigns ei, ep, yp, ox, p, fcgf, gki;
*/
while (ei < jez) {
      if (((ei % 2) == 0)) {
          yp += 1;
          ep += 2;
      }
      else {
          ox = ox + 3;
          gki = gki + 1;
      }
      ei += 1;
      if ((ei%7)==0) {
          p += 6;
      }
      fcgf = fcgf + ep;
      fcgf += fcgf;
      p++;
  }
}
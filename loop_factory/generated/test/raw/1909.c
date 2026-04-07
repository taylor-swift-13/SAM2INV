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

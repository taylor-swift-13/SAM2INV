int main1(){
  int mr6, t7n0, irg, shi, xzmq, lem, on, r, bl2i;

  mr6=75;
  t7n0=0;
  irg=1;
  shi=1;
  xzmq=0;
  lem=7;
  on=0;
  r=4;
  bl2i=1;

  while (1) {
      if (!(t7n0<mr6)) {
          break;
      }
      if (t7n0%3==0) {
          if (irg>0) {
              irg -= 1;
              xzmq += 1;
          }
      }
      else {
          if (irg<lem) {
              irg++;
              shi = shi + 1;
          }
      }
      t7n0 += 1;
      bl2i += irg;
      on += 1;
      r += 2;
      lem = lem + 1;
      r += 4;
  }

}

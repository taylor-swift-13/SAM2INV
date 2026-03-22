int main1(){
  int d94, yba, r2, p, ntc, yx;

  d94=1+13;
  yba=d94;
  r2=0;
  p=0;
  ntc=yba;
  yx=3;

  while (1) {
      if (!(yba>0)) {
          break;
      }
      p = p+r2*yba;
      yx++;
      r2 += yba;
      yba = 0;
  }

  while (d94<=yba-1) {
      d94 += 1;
      ntc++;
      ntc = ntc*ntc+ntc;
  }

}

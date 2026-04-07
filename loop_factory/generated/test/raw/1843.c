int main1(){
  int yts, or, rpt, dw, fy3;

  yts=1;
  or=0;
  rpt=0;
  dw=0;
  fy3=0;

  while (or < yts) {
      rpt = rpt + 2*or + 1;
      fy3++;
      or = or + 1;
      dw = dw+(fy3%3);
  }

}

int main1(){
  int dq, eq, y, hb, m;

  dq=1+14;
  eq=dq+1;
  y=5;
  hb=0;
  m=0;

  while (hb<dq) {
      y++;
      hb++;
      m += hb;
      m += eq;
  }

  while (y*4<=eq) {
      m += hb;
      hb += eq;
      hb = hb*2+3;
      eq = (y*4)-1;
  }

}

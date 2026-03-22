int main1(){
  int ts, y, uwr, zlb, prq;

  ts=(1%25)+17;
  y=0;
  uwr=10;
  zlb=1;
  prq=0;

  while (uwr>0&&zlb<=ts) {
      if (uwr>zlb) {
          uwr -= zlb;
      }
      else {
          uwr = 0;
      }
      y++;
      prq = prq + 1;
      zlb++;
  }

}

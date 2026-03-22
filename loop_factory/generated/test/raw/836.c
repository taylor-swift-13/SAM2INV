int main1(){
  int c, jg, z, hh, v5, px;

  c=1+25;
  jg=c;
  z=c;
  hh=jg;
  v5=jg;
  px=(1%6)+2;

  while (1) {
      if (v5>=c) {
          break;
      }
      z = z*px+1;
      hh = hh*px;
      v5 = v5 + 1;
      px = px + jg;
  }

}

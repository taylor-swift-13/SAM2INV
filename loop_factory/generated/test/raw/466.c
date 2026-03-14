int main1(){
  int xn, xjf, r, ix;

  xn=(1%33)+18;
  xjf=0;
  r=0;
  ix=0;

  while (xjf<=xn-1) {
      if (ix<xn) {
          r = xjf;
      }
      ix += 2;
      xjf++;
  }

  while (ix+6<=xjf) {
      xn += r;
      xjf = (ix+6)-1;
  }

}

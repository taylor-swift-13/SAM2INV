int main1(){
  int ve, xv, h, nu7l, s, c8y, ecvc, ax2;

  ve=1+14;
  xv=ve;
  h=0;
  nu7l=0;
  s=0;
  c8y=(1%18)+5;
  ecvc=-3;
  ax2=xv;

  while (1) {
      if (!(c8y>0)) {
          break;
      }
      c8y--;
      h = h+1*1;
      nu7l = nu7l+1*1;
      s = s+1*1;
      if (xv+2<=ax2+ve) {
          ecvc = ecvc*ax2;
      }
      if ((xv%6)==0) {
          ecvc = ecvc*2;
      }
      ax2 = ax2 + ve;
      ecvc += xv;
      ax2 = ax2*ax2;
      ax2 = ax2+ecvc*ax2;
      if (ax2+1<ve) {
          ax2 = ax2*ecvc;
      }
  }

}

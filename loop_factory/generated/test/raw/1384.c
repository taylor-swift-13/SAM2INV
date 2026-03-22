int main1(){
  int h0, mi1w, odpi, wp, w;

  h0=1*4;
  mi1w=0;
  odpi=1;
  wp=6;
  w=0;

  while (1) {
      if (!(w<=h0)) {
          break;
      }
      w += 1;
      mi1w += odpi;
      odpi = odpi + wp;
      mi1w = mi1w*mi1w+mi1w;
      wp += 2;
      mi1w = mi1w%7;
  }

}

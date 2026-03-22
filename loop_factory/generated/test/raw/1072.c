int main1(int q,int e){
  int yq, h, bm86, vl, lj1p;

  yq=0;
  h=0;
  bm86=0;
  vl=0;
  lj1p=(e%18)+5;

  while (lj1p>0) {
      lj1p--;
      h = h+q*q;
      vl = vl+q*e;
      bm86 = bm86+e*e;
      e = e*4+(h%2)+3;
  }

  while (1) {
      if (!(h>yq)) {
          break;
      }
      h -= yq;
      yq = yq + 1;
      q = q+(yq%3);
      lj1p = lj1p+(yq%7);
      lj1p = lj1p*2;
  }

}

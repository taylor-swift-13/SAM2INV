int main1(){
  int ep, whwd, mb, m, yr, q, p, tm;

  ep=1*2;
  whwd=ep;
  mb=whwd;
  m=whwd;
  yr=ep;
  q=-4;
  p=5;
  tm=2;

  while (1) {
      if (!(whwd-2>=0)) {
          break;
      }
      if (whwd%3==1) {
          mb = mb + 1;
      }
      else {
          m++;
      }
      if (whwd%3==2) {
          yr++;
      }
      else {
      }
      q = (ep)+(q);
      q = q+p+tm;
      p = p + q;
      if ((whwd%7)==0) {
          p += whwd;
      }
      q = m;
      q += whwd;
      p = q-p;
      whwd++;
  }

}

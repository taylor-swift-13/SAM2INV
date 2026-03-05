int main135(int m){
  int g89s, yd5, m9v, u, v1, pb, yw;

  g89s=41;
  yd5=0;
  m9v=0;
  u=(m%28)+10;
  v1=g89s;
  pb=0;
  yw=(m%18)+5;

  while (1) {
      if (!(u>m9v)) {
          break;
      }
      u -= m9v;
      v1 += yd5;
      pb = pb + g89s;
      m9v += 1;
      pb = pb*pb;
  }

  while (1) {
      if (!(yw>0)) {
          break;
      }
      yw = yw+m*m;
      m += yw;
  }

  while (m9v!=0) {
      if (m9v%2==1) {
          g89s += pb;
          m9v = m9v - 1;
      }
      else {
      }
      m9v = m9v/2;
      yd5 = yd5*4+1;
      pb = 2*pb;
      m = m + g89s;
  }

}

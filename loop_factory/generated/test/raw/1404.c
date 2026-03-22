int main1(){
  int n7, n1v, dx, re, y9, i, m;

  n7=61;
  n1v=3;
  dx=n7;
  re=2;
  y9=n1v;
  i=-6;
  m=n7;

  while (1) {
      if (i>n7) {
          break;
      }
      dx = dx + re;
      re += y9;
      m = m+(dx%3);
      i = i + 1;
      y9 += 4;
  }

}

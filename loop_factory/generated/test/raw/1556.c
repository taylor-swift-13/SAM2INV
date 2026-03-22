int main1(){
  int pih, p7, ikl, zr, xg, j4f, te, i6, w2k;

  pih=10;
  p7=0;
  ikl=0;
  zr=0;
  xg=0;
  j4f=0;
  te=0;
  i6=0;
  w2k=0;

  while (p7 < pih) {
      p7 += 1;
      if (p7 % 3 == 0) {
          ikl += 1;
          zr += 2;
      }
      else {
          xg = xg + 3;
      }
      if (p7+5<=i6+pih) {
          j4f += 1;
      }
      te += zr;
      w2k = w2k+(p7%2);
      j4f += 1;
      te += j4f;
  }

}

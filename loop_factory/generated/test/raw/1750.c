int main1(){
  int p9ij, x, ej, e4, fc, pwox;

  p9ij=1;
  x=0;
  ej=0;
  e4=0;
  fc=x;
  pwox=0;

  while (ej<=p9ij-1) {
      e4 = e4 + ej;
      ej = ej + 1;
      fc = fc+(e4%7);
      pwox += 2;
  }

}

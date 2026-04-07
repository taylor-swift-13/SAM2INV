int main1(int h){
  int gr, teu, d, yfdd, cgix;

  gr=77;
  teu=0;
  d=-5;
  yfdd=h;
  cgix=h+1;

  while (teu < gr) {
      yfdd = yfdd + cgix;
      cgix += h;
      d = d+yfdd+cgix;
      teu = gr;
  }

}

int main1(int a){
  int w4n, hg, eu, k, ufa;

  w4n=55;
  hg=0;
  eu=0;
  k=0;
  ufa=0;

  while (hg < w4n) {
      hg = hg + 1;
      eu = eu + ((a + k) % 3 - 1);
      k += 1;
      ufa += eu;
  }

}

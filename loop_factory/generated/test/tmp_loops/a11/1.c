int main1(int f){
  int d, p5gu, ssb0;

  d=100;
  p5gu=0;
  ssb0=5;

  while (p5gu<d) {
      ssb0 = p5gu%5;
      if (p5gu>=ssb0) {
          ssb0 = (p5gu-ssb0)%5;
          ssb0 = ssb0+ssb0-ssb0;
      }
      else {
          ssb0 += ssb0;
      }
      p5gu++;
      f += ssb0;
  }

}

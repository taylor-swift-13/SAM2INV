int main1(int b){
  int byr, vh, l, sb;

  byr=55;
  vh=0;
  l=4;
  sb=-3;

  while (1) {
      sb = sb*sb;
      l += vh;
      vh = vh + 1;
      if (vh>=byr) {
          break;
      }
  }

}

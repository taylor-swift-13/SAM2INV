int main1(int w){
  int s, qt8, q, tgw;

  s=(w%10)+16;
  qt8=-5;
  q=0;
  tgw=0;

  while (tgw<s) {
      tgw += 1;
      q = q + w;
  }

  while (1) {
      if (!(tgw<qt8)) {
          break;
      }
      tgw += 1;
      q = q + w;
  }

}

int main1(){
  int kx1, ua, b, ko;

  kx1=(1%16)+10;
  ua=-5;
  b=3;
  ko=1;

  while (ua<=kx1-1) {
      if (b>=9) {
          ko = -1;
      }
      if (!(b>3)) {
          ko = 1;
      }
      ua++;
      b += ko;
  }

}

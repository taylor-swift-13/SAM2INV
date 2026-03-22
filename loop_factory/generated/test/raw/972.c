int main1(int t){
  int e12, gs, cu, n5;

  e12=t;
  gs=(t%20)+5;
  cu=(t%20)+5;
  n5=(t%20)+5;

  while (gs>0) {
      if (cu>0) {
          if (n5>0) {
              gs = gs - 1;
              cu--;
              n5 -= 1;
          }
      }
      t += e12;
  }

}

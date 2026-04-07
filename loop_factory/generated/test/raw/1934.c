int main1(int d){
  int tw, vx, nbu, bpr;

  tw=d+17;
  vx=0;
  nbu=0;
  bpr=0;

  while (1) {
      if (!(vx < tw)) {
          break;
      }
      vx++;
      bpr = vx % d;
      nbu = vx / d;
  }

}

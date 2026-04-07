int main1(int f){
  int grzc, gyc, h0, we, la;

  grzc=52;
  gyc=0;
  h0=gyc;
  we=gyc;
  la=grzc;

  while (1) {
      if (!(gyc < grzc)) {
          break;
      }
      gyc += 1;
      h0 = h0 + 2*(gyc % 2 == 0) - 1;
      la += grzc;
      we = (we + 2*(gyc % 3 == 0))+(-(1));
  }

}

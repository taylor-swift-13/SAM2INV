int main1(){
  int r, wyu, sf9, l, whd;

  r=(1%18)+16;
  wyu=0;
  sf9=r;
  l=wyu;
  whd=r;

  while (1) {
      if (!(wyu < r)) {
          break;
      }
      sf9 = (sf9+whd)/2;
      wyu = wyu + 1;
      l = (l+sf9)/2;
  }

}

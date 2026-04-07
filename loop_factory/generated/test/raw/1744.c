int main1(int y){
  int rx, h1j, ao, gd, ves;

  rx=y-2;
  h1j=y;
  ao=6;
  gd=4;
  ves=rx;

  while (1) {
      if (ves>rx) {
          break;
      }
      h1j += ao;
      ao = ao + gd;
      ves = (1)+(ves);
      gd += 6;
  }

}

int main1(int z){
  int r, la, wg9;

  r=z+6;
  la=r;
  wg9=4;

  while (la<=r-1) {
      wg9 = la%5;
      if (la>=wg9) {
          wg9 = (la-wg9)%5;
          wg9 = wg9+wg9-wg9;
      }
      else {
          wg9 = wg9 + wg9;
      }
      la++;
      z = z+(la%2);
  }

}

int main1(int g,int z){
  int r, d22x, v5, rm;

  r=g+15;
  d22x=r;
  v5=0;
  rm=1;

  while (d22x<r) {
      if (v5>=9) {
          rm = -1;
      }
      if (!(v5>0)) {
          rm = 1;
      }
      v5 = v5 + rm;
      d22x += 1;
  }

}

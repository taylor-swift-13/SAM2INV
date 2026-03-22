int main1(){
  int h, vn4, md3, kr;

  h=1*2;
  vn4=0;
  md3=0;
  kr=-5;

  while (vn4 < h) {
      vn4++;
      md3 = md3 + kr;
      kr = kr+(md3%6);
  }

}

int main1(){
  int zmc, xyy, wa;

  zmc=3;
  xyy=(1%20)+10;
  wa=(1%15)+8;

  for (; xyy>0&&wa>0; zmc = zmc + 1) {
      if (!(!(zmc%2==0))) {
          xyy = xyy - 1;
      }
      else {
          wa--;
      }
  }

}

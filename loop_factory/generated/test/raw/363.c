int main1(){
  int i9, uwi, bp, ds, ju, i2, mqh;

  i9=30;
  uwi=0;
  bp=0;
  ds=(1%28)+10;
  ju=uwi;
  i2=5;
  mqh=uwi;

  while (1) {
      if (!(ds>bp)) {
          break;
      }
      ds -= bp;
      bp = bp + 1;
      i2 = i2*i2;
      ju = ju + uwi;
      mqh += bp;
  }

  while (1) {
      if (!(i2>=1)) {
          break;
      }
      i2 = i2 - 1;
      ju = ju+1*1;
      i9 = i9+1*1;
      mqh = mqh+1*1;
      bp = bp*2+(ju%6)+3;
  }

}

int main1(int o){
  int nkw, us, am, i5x, jfs;

  nkw=(o%9)+15;
  us=nkw;
  am=-6;
  i5x=0;
  jfs=o;

  while (us>1) {
      i5x = i5x+am*us;
      jfs += us;
      us = 1;
  }

  while (1) {
      if (!(am<us)) {
          break;
      }
      i5x = i5x + o;
      am += 1;
      o += am;
  }

}

int main1(){
  int t9, yi, ro7, zk0, f, zkb9;

  t9=1+14;
  yi=(1%60)+60;
  ro7=(1%9)+2;
  zk0=0;
  f=0;
  zkb9=t9;

  while (1) {
      if (!(yi>ro7*zk0+f)) {
          break;
      }
      if (!(!(f==ro7-1))) {
          f = f + 1;
      }
      else {
          f = 0;
          zk0++;
      }
      zkb9 = zkb9+f-zk0;
  }

}

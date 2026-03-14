int main1(int z,int q){
  int i2w, oj, wkmv, a3, w, u, zh;

  i2w=47;
  oj=0;
  wkmv=0;
  a3=0;
  w=0;
  u=3;
  zh=0;

  while (1) {
      if (!(oj<i2w)) {
          break;
      }
      a3 = oj%5;
      if (oj>=u) {
          w = (oj-u)%5;
          wkmv = wkmv+a3-w;
      }
      else {
          wkmv += a3;
      }
      zh += i2w;
      oj++;
  }

}

int main1(){
  int au, d1y, ur, v;

  au=(1%28)+8;
  d1y=(1%22)+5;
  ur=0;
  v=0;

  while (1) {
      if (!(d1y!=0)) {
          break;
      }
      if (d1y%2==1) {
          ur += au;
          d1y--;
      }
      d1y = d1y/2;
      au = 2*au;
      v += d1y;
  }

}

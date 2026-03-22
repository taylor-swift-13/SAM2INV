int main1(){
  int zibi, yg, l2, v, y;

  zibi=1-4;
  yg=0;
  l2=1;
  v=0;
  y=yg;

  while (1) {
      if (!(l2<=zibi-1)) {
          break;
      }
      v = (1)+(v);
      l2 = 2*l2;
      y = y*3+(l2%5)+3;
  }

}

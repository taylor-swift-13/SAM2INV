int main1(){
  int x8, mtv, b, yi1;

  x8=(1%24)+14;
  mtv=x8;
  b=0;
  yi1=-2;

  while (1) {
      if (!(mtv>0)) {
          break;
      }
      mtv -= 1;
  }

  while (b<x8) {
      b += 1;
      yi1 = x8-b;
      yi1 = yi1 + mtv;
  }

}

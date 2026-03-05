int main1(){
  int b3y, jx, x9;

  b3y=1+15;
  jx=b3y;
  x9=jx;

  while (jx>2) {
      if (jx<b3y/2) {
          x9 = x9 + x9;
      }
      else {
          x9 = x9 + 1;
      }
      x9 += jx;
      x9 = x9 - x9;
  }

}

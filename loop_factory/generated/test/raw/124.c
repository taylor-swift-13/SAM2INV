int main1(int w){
  int a3l, yp, it;

  a3l=w*2;
  yp=0;
  it=a3l;

  while (1) {
      if (!(yp<a3l)) {
          break;
      }
      it = a3l-yp;
      yp += 1;
      w = w + yp;
  }

}

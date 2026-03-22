int main1(int r,int k){
  int mxp, pk2, km;

  mxp=50;
  pk2=0;
  km=5;

  while (pk2<=mxp-1) {
      if (pk2>=mxp/2) {
          km += 2;
      }
      r += km;
      pk2 += 1;
  }

}

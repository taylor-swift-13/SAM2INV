int main1(){
  int ms, j, du, ng, e2k;

  ms=10;
  j=0;
  du=j;
  ng=ms;
  e2k=j;

  while (j < ms) {
      du = du*2 + ng;
      j++;
      ng = ng*2 + e2k;
      e2k = e2k*2;
  }

}

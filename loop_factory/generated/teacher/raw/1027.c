int main1(int m,int n){
  int h, j, v, k;

  h=(m%24)+16;
  j=1;
  v=j;
  k=m;

  while (j<h) {
      v = v*4+4;
      k = k*v+4;
      j = j*3;
  }

}

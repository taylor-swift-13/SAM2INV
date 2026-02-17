int main1(int b,int m,int p,int q){
  int l, i, v, j, d, x;

  l=m+3;
  i=1;
  v=i;
  j=p;
  d=1;
  x=4;

  while (i<l) {
      v = v+i;
      j = j*j;
      d = d+v*j;
      d = j*j;
      if (i+3<=v+l) {
          j = j%8;
      }
      i = i*2;
  }

}

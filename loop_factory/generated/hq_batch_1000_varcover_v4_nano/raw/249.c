int main1(int b,int k,int q){
  int l, i, v, j, d;

  l=40;
  i=0;
  v=8;
  j=6;
  d=b;

  while (i<l) {
      v = v+1;
      j = j+v;
      v = v+1;
      if ((i%7)==0) {
          d = d+1;
      }
      i = i+1;
  }

}

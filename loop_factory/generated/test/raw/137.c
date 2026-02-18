int main1(int a,int b,int p,int q){
  int l, i, v, j, e;

  l=10;
  i=0;
  v=i;
  j=q;
  e=a;

  while (i<l) {
      v = v+j+e;
      v = v+1;
      if ((i%5)==0) {
          v = v+1;
      }
      e = e+i;
      j = j+6;
      e = e+1;
      j = j+i;
      i = i+1;
  }

}

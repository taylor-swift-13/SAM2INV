int main1(int a,int b,int n,int q){
  int l, i, v, j, o, k;

  l=a-5;
  i=0;
  v=3;
  j=l;
  o=q;
  k=0;

  while (i<l) {
      v = v+j;
      j = j+o;
      o = o+1;
      if (j+2<l) {
          v = v%6;
      }
      else {
          v = v%5;
      }
      i = i+3;
  }

}

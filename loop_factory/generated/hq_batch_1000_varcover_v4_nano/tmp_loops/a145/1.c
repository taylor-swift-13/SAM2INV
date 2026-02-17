int main1(int a,int b,int n,int q){
  int l, i, v, w, c, m;

  l=(n%10)+15;
  i=0;
  v=l;
  w=q;
  c=n;
  m=5;

  while (i<l) {
      v = v+4;
      w = w+v;
      c = c+w;
      v = v+1;
      w = w-1;
      if (a<c+3) {
          c = c+i;
      }
      else {
          v = v+1;
      }
      if ((i%8)==0) {
          c = c+w;
      }
  }

}

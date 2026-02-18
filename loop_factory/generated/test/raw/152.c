int main1(int b,int n,int p,int q){
  int l, i, v, y;

  l=54;
  i=0;
  v=l;
  y=p;

  while (i<l) {
      v = v+3;
      y = y+4;
      if (i+2<=b+l) {
          v = v+i;
      }
      else {
          v = y-v;
      }
      v = n;
      y = y+v;
      i = i+1;
  }

}

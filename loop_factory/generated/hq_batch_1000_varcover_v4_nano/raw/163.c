int main1(int a,int b,int q){
  int l, i, v, y;

  l=80;
  i=l;
  v=l;
  y=3;

  while (i>0) {
      v = v+1;
      y = y-1;
      v = v+1;
      y = y+1;
      if (v+4<l) {
          y = y+i;
      }
      i = i-1;
  }

}

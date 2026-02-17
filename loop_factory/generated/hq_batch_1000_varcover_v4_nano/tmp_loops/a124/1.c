int main1(int m,int n,int p,int q){
  int l, i, v, h;

  l=n;
  i=l;
  v=4;
  h=i;

  while (i>0) {
      v = v+1;
      h = h+v;
      if (v+6<l) {
          v = v+h;
      }
      else {
          v = v+4;
      }
      i = i-1;
  }

}

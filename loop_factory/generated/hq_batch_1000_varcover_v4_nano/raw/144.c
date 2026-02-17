int main1(int m,int n,int q){
  int l, i, v, c;

  l=66;
  i=0;
  v=6;
  c=i;

  while (i<l) {
      v = v+1;
      c = c-1;
      if (i<i+2) {
          c = c+v;
      }
      i = i+1;
  }

}

int main1(int b,int k){
  int l, i, v, m;

  l=b+8;
  i=l;
  v=l;
  m=b;

  while (i>0) {
      v = v+1;
      m = m+v;
      i = i-1;
  }

  while (v>0) {
      m = m+m;
      m = m+l;
      v = v-1;
  }

}

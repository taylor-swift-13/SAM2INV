int main1(int m,int p){
  int l, i, v;

  l=m+16;
  i=0;
  v=p;

  while (i<l) {
      if (v*v<=l+4) {
          v = v*v+v;
      }
      if (v+6<l) {
          v = v*v;
      }
      i = i+1;
  }

}

int main1(int a,int k,int m,int p){
  int l, i, v;

  l=p+23;
  i=l;
  v=p;

  while (i>0) {
      v = v+1;
      if (m<l+5) {
          v = v+1;
      }
      else {
          v = v+i;
      }
      if (a<m+4) {
          v = v+i;
      }
      v = v+v;
      i = i-1;
  }

}

int main1(int a,int b,int k,int m){
  int l, i, v;

  l=b+14;
  i=0;
  v=4;

  while (i<l) {
      v = v*v+v;
      v = v+v;
      if (v+4<l) {
          v = v*v+v;
      }
      i = i+1;
  }

}

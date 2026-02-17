int main1(int a,int b,int n,int p){
  int l, i, v;

  l=b;
  i=0;
  v=b;

  while (i<l) {
      v = v+4;
      v = v+v;
      if (a<i+1) {
          v = v+i;
      }
      i = i+1;
  }

}

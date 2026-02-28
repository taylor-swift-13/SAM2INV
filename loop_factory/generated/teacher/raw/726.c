int main1(int b,int k,int n,int q){
  int i, j, v, p;

  i=b+12;
  j=i;
  v=3;
  p=n;

  while (1) {
      if (j>=i) {
          break;
      }
      v = v+2;
      j = j+1;
      v = v+4;
      p = p+v;
  }

}

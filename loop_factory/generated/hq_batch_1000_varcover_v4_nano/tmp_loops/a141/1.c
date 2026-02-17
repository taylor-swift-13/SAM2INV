int main1(int k,int m,int n,int p){
  int l, i, v, j, x, z;

  l=p-10;
  i=l;
  v=n;
  j=k;
  x=m;
  z=n;

  while (i>0) {
      v = v+1;
      j = j+v;
      if (i<z+3) {
          v = v+2;
      }
      i = i-1;
  }

}

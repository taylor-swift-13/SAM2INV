int main1(int a,int b,int p){
  int l, i, v, r, z, f;

  l=60;
  i=l;
  v=b;
  r=b;
  z=1;
  f=0;

  while (i>0) {
      v = v+r;
      r = r+z;
      i = i/2;
  }

}

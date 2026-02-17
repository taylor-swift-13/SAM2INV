int main1(int k,int n,int p,int q){
  int l, i, v, h, z, t;

  l=q;
  i=0;
  v=i;
  h=l;
  z=i;
  t=-6;

  while (i<l) {
      h = h+z;
      z = z+v;
      if (t+7<l) {
          h = n+6;
      }
      else {
          z = h-z;
      }
      t = t+z;
      t = t+i;
      i = i+1;
  }

}

int main1(int k,int m,int p){
  int l, i, v, r, z, e, d;

  l=(p%10)+9;
  i=0;
  v=-3;
  r=-5;
  z=i;
  e=l;
  d=i;

  while (i<l) {
      e = e*e+v;
      v = v%5;
      e = d*d;
      i = i+3;
  }

}

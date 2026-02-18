int main1(int a,int b,int m,int p){
  int l, i, v, s, r;

  l=(p%7)+8;
  i=0;
  v=-8;
  s=3;
  r=p;

  while (i<l) {
      v = v+1;
      s = s+1;
      v = v+1;
      s = s+v;
  }

}

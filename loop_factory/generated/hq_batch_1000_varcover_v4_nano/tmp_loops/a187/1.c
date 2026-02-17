int main1(int a,int k,int m,int p){
  int l, i, v, c, o, r;

  l=p;
  i=0;
  v=-6;
  c=-3;
  o=-8;
  r=a;

  while (i<l) {
      v = v*3;
      c = c/3;
      if (i+4<=p+l) {
          o = o*2;
      }
      else {
          r = r*r+c;
      }
      c = c%2;
      i = i+1;
  }

}

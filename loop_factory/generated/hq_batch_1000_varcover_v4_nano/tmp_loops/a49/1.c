int main1(int k,int m,int n,int p){
  int l, i, v, h, o, e;

  l=p;
  i=0;
  v=5;
  h=1;
  o=i;
  e=i;

  while (i<l) {
      v = v*3+3;
      h = h*v+3;
      if (o+3<l) {
          o = e*e;
      }
      else {
          h = e*e;
      }
      i = i+3;
  }

}

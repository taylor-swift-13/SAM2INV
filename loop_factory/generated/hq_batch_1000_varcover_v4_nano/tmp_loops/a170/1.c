int main1(int a,int b,int k,int q){
  int l, i, v, d, x, f, e;

  l=(k%12)+15;
  i=0;
  v=5;
  d=q;
  x=8;
  f=3;
  e=-5;

  while (i<l) {
      f = f*f+v;
      v = v%5;
      x = x*e;
      if ((i%7)==0) {
          v = v%3;
      }
      else {
          d = d*d+e;
      }
      f = f*f+d;
      i = i+1;
  }

}

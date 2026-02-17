int main1(int a,int k,int n,int p){
  int l, i, v, d, w, h;

  l=a;
  i=l;
  v=-1;
  d=-6;
  w=-5;
  h=n;

  while (i>0) {
      h = h*h+v;
      v = v%4;
      h = h*5;
      w = w*w+v;
      if (d+2<l) {
          v = w*w;
      }
      else {
          h = h%4;
      }
      i = i-1;
  }

}

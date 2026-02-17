int main1(int b,int k,int m,int p){
  int l, i, v, h, r, e;

  l=p-8;
  i=1;
  v=-4;
  h=p;
  r=i;
  e=2;

  while (i<l) {
      v = v*2;
      h = h+v;
      r = r%6;
      h = h*h+v;
      i = i*3;
  }

}

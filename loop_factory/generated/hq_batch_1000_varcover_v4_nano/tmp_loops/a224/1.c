int main1(int b,int k,int p,int q){
  int l, i, v, h, w, x;

  l=k+20;
  i=1;
  v=6;
  h=i;
  w=b;
  x=3;

  while (i<l) {
      v = v*4;
      h = h/4;
      if (h*h<=l+3) {
          x = x*2;
      }
      else {
          w = w*x;
      }
      h = h*2;
      i = i*2;
  }

}

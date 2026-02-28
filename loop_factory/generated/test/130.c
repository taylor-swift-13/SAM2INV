int main130(int k,int p,int q){
  int l, d, v, c;

  l=52;
  d=l+4;
  v=p;
  c=d;

  while (d>0) {
      if (v+5<=l) {
          v = v+5;
      }
      else {
          v = l;
      }
      v = v+d;
      c = c*c;
      c = c+v*c;
      while (d+5<=c) {
          v = l;
          l = l+2;
          l = l*2;
          v = v/2;
          if (d+5<=v+c) {
              l = v+d;
          }
      }
      while (l>=3) {
          c = c*3;
          d = d/3;
          c = c+d;
          d = d+d;
          d = d+4;
      }
  }


  /*@ assert l < 3; */
}

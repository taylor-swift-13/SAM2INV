int main153(int b,int k,int p){
  int g, t, l;

  g=p;
  t=g;
  l=-1;

  while (t-1>=0) {
      l = l+2;
      l = l*2;
  }

  while (l<g) {
      t = t+4;
      t = t*t;
  }

  while (t>=t) {
      l = l+3;
      l = l+l;
      if (k<b+4) {
          l = l+1;
      }
      l = l+l;
  }


  /*@ assert t < t; */
}

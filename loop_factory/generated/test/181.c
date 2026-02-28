int main181(int a,int n,int p){
  int c, t, w, v, d;

  c=n+21;
  t=c;
  w=p;
  v=2;
  d=1;

  while (t-2>=0) {
      if (t%5==4) {
          w = w+1;
      }
      else {
          v = v+1;
      }
      if (t%5==0) {
          d = d+1;
      }
      else {
      }
  }

  while (d-1>=0) {
      c = c*4+1;
      t = t*c+1;
      c = c*v;
      if ((d%5)==0) {
          t = t*t+v;
      }
      d = d-1;
  }

  while (d+3<=t) {
      c = c+w;
  }


  /*@ assert d+3 > t; */
}

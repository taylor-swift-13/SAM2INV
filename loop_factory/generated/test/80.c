int main80(int k,int n,int p){
  int s, t, v, m;

  s=(k%30)+14;
  t=0;
  v=p;
  m=k;

  while (t>=t) {
      v = v+3;
      m = m+3;
      v = v*v+v;
  }

  while (v<m) {
      s = s+1;
      t = t+1;
      s = s+2;
      t = t+1;
  }


  /*@ assert v >= m; */
}

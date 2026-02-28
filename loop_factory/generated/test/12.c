int main12(int a,int k,int p){
  int m, o, t, v;

  m=47;
  o=0;
  t=a;
  v=k;

  while (t<m) {
      if (t<m) {
          t = t+1;
      }
      t = t+v;
      v = v+v;
  }

  while (v+1<=m) {
      o = o+4;
  }

  while (v+4<=m) {
      t = t+4;
      t = t+t;
      if (k<m+5) {
          t = t+1;
      }
      t = t+v;
  }


  /*@ assert v+4 > m; */
}

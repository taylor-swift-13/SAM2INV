int main42(int a,int m,int p){
  int h, t, v, q;

  h=p+22;
  t=0;
  v=m;
  q=p;

  while (1) {
      if (t>=h) {
          break;
      }
      v = v+3;
      t = t+1;
      v = v*3;
      q = q/3;
  }

}

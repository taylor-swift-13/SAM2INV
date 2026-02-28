int main56(int a,int n,int q){
  int s, v, w, p, t;

  s=n;
  v=0;
  w=0;
  p=6;
  t=s;

  while (1) {
      p = s-w;
      w = w+1;
      w = w+5;
      t = t+1;
      if (v+7<=w+s) {
          p = p+w;
      }
  }


  /*@ assert \false; */
}
